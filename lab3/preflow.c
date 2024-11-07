#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <limits.h>
#include <unistd.h>
#include <stdbool.h>

#define PRINT 1   /* enable/disable prints. */
#define TIME 0    /* for timing on power.	*/
#define FORSETE 0 /* enable/disable forsete. */

#if TIME
#include "timebase.h"
#endif

#if PRINT
#define pr(...)                                                                \
    do {                                                                       \
        fprintf(stderr, __VA_ARGS__);                                          \
    } while (0)
#else
#define pr(...) /* no effect at all */
#endif

#define MIN(a, b) (((a) <= (b)) ? (a) : (b))
#define MAX(a, b) (((a) > (b)) ? (a) : (b))

typedef struct graph_t graph_t;
typedef struct node_t node_t;
typedef struct edge_t edge_t;
typedef struct list_t list_t;

typedef struct xedge_t xedge_t;

struct xedge_t {
    int u;
    int v;
    int c;
};

struct list_t {
    edge_t *edge;
    list_t *next;
};

struct node_t {
    int h;                 /* height.			*/
    int e;                 /* excess flow.			*/
    list_t *edge;          /* adjacency list.		*/
    node_t *next;          /* with excess preflow.		*/
    pthread_mutex_t mutex; /* node lock. */
};

struct edge_t {
    node_t *u; /* one of the two nodes.	*/
    node_t *v; /* the other. 			*/
    int f;     /* flow > 0 if from u to v.	*/
    int c;     /* capacity.			*/
};

struct graph_t {
    int n;          /* nodes.			*/
    int m;          /* edges.			*/
    node_t *v;      /* array of n nodes.		*/
    edge_t *e;      /* array of m edges.		*/
    node_t *s;      /* source.			*/
    node_t *t;      /* sink.			*/
    node_t *excess; /* nodes with e > 0 except s,t.	*/
    pthread_mutex_t mutex;
    pthread_barrier_t barrier;
    bool shutdown;
    int nrExcess;
    int nrThreads;
};

typedef struct thread_local_data_t thread_local_data_t;
struct thread_local_data_t {
    int id;
    graph_t *graph;
};

static char *progname;

static int id(graph_t *g, node_t *v) { return v - g->v; }

void error(const char *fmt, ...) {
    va_list ap;
    char buf[BUFSIZ];

    va_start(ap, fmt);
    vsprintf(buf, fmt, ap);

    if (progname != NULL)
        fprintf(stderr, "%s: ", progname);

    fprintf(stderr, "error: %s\n", buf);
    exit(1);
}

static int next_int() {
    int x;
    int c;

    x = 0;
    while (isdigit(c = getchar()))
        x = 10 * x + c - '0';

    return x;
}

static void *xmalloc(size_t s) {
    void *p;

    p = malloc(s);

    if (p == NULL)
        error("out of memory: malloc(%zu) failed", s);

    return p;
}

static void *xcalloc(size_t n, size_t s) {
    void *p;
    p = xmalloc(n * s);
    memset(p, 0, n * s);
    return p;
}

static void add_edge(node_t *u, edge_t *e) {
    list_t *p;
    p = xmalloc(sizeof(list_t));
    p->edge = e;
    p->next = u->edge;
    u->edge = p;
}

static void connect(node_t *u, node_t *v, int c, edge_t *e) {
    e->u = u;
    e->v = v;
    e->c = c;

    add_edge(u, e);
    add_edge(v, e);
}

#if FORSETE

static graph_t *new_graph(int n, int m, int s, int t, xedge_t *e) {
    graph_t *g;
    node_t *u;
    node_t *v;
    int i;
    int a;
    int b;
    int c;

    g = xmalloc(sizeof(graph_t));

    g->n = n;
    g->m = m;

    g->v = xcalloc(n, sizeof(node_t));
    for (i = 0; i < n; ++i) {
        pthread_mutex_init(&g->v[i].mutex, NULL);
    }
    g->e = xcalloc(m, sizeof(edge_t));

    g->s = &g->v[0];
    g->t = &g->v[n - 1];
    g->excess = NULL;

    for (i = 0; i < m; i += 1) {
        a = e[i].u;
        b = e[i].v;
        c = e[i].c;
        u = &g->v[a];
        v = &g->v[b];
        connect(u, v, c, g->e + i);
    }

    return g;
}

#else

static graph_t *new_graph(FILE *in, int n, int m) {
    graph_t *g;
    node_t *u;
    node_t *v;
    int i;
    int a;
    int b;
    int c;

    g = xmalloc(sizeof(graph_t));

    g->n = n;
    g->m = m;

    g->v = xcalloc(n, sizeof(node_t));
    for (i = 0; i < n; ++i) {
        pthread_mutex_init(&g->v[i].mutex, NULL);
    }
    g->e = xcalloc(m, sizeof(edge_t));

    g->s = &g->v[0];
    g->t = &g->v[n - 1];
    g->excess = NULL;

    for (i = 0; i < m; i += 1) {
        a = next_int();
        b = next_int();
        c = next_int();
        u = &g->v[a];
        v = &g->v[b];
        connect(u, v, c, g->e + i);
    }

    return g;
}

#endif

static void relabel_thread(thread_local_data_t *thread_local, node_t *u) {
    assert(u->e > 0);
    u->h += 1;
    assert(u->h <= (2 * thread_local->graph->n) + 1);

    pr("relabel %d now h = %d\n", id(thread_local->graph, u), u->h);
}

static int push(graph_t *g, node_t *u, edge_t *e) {
    int d;
    // int d; /* remaining capacity of the edge. */
    if (u == e->u) {
        d = MIN(u->e, e->c - e->f);
        e->f += d;
    } else {
        d = MIN(u->e, e->c + e->f);
        e->f -= d;
    }

    /* the following are always true. */

    assert(d >= 0);
    assert(abs(e->f) <= e->c);
    return d;
}

static node_t *other(node_t *u, edge_t *e) {
    if (u == e->u)
        return e->v;
    else
        return e->u;
}

static void free_graph(graph_t *g) {
    int i;
    list_t *p;
    list_t *q;

    for (i = 0; i < g->n; i += 1) {
        p = g->v[i].edge;
        pthread_mutex_destroy(&g->v[i].mutex);
        while (p != NULL) {
            q = p->next;
            free(p);
            p = q;
        }
    }
    free(g->v);
    free(g->e);

    pthread_mutex_destroy(&g->mutex);
    pthread_barrier_destroy(&g->barrier);
    free(g);
}

void *thread_work(void *arg) {

    node_t *u; /* active node */
    node_t *v; /* other node in edge */
    edge_t *e; /* current edge */
    list_t *p; /* adjecency list */
    int b;     /* edge direction */
    node_t *excess = NULL;

    int processed_nodes = 0;
    u = NULL;

    thread_local_data_t *thread_local = arg;
    graph_t *g = thread_local->graph;

    while (true) {
        if (excess == NULL) {
            pthread_mutex_lock(&g->mutex);
            if (g->excess != NULL) {
                // for (int i = 0;
                //      i <= MAX(2, (g->nrExcess / g->nrThreads)) && g->excess
                //      != NULL; i++) {
                excess = g->excess;
                excess->next = NULL; 
                // node_t *ne = g->excess;
                g->excess = g->excess->next;
                // ne->next = excess;
                // excess = ne;
                g->nrExcess--;
            }
            pthread_mutex_unlock(&g->mutex);
        }

        // PART 1: Pushing excess flow.
        u = excess;
        if (u != NULL) {
            excess = NULL;
            ++processed_nodes;
#if PRINT
            pthread_mutex_lock(&u->mutex);
            pr("Thread %d selected u = %d with h = %d and e = %d.\n",
               thread_local->id, id(g, u), u->h, u->e);
            pthread_mutex_unlock(&u->mutex);
#endif
            p = u->edge;
            while (p != NULL) {
                e = p->edge;
                p = p->next;

                if (u == e->u) {
                    v = e->v;
                    b = 1;
                } else {
                    v = e->u;
                    b = -1;
                }

                if (u->h > v->h && b * e->f < e->c) {
                    pthread_mutex_lock(&u->mutex);
                    int d = push(g, u, e);
                    u->e -= d;
                    int ue = u->e;
                    assert(u->e >= 0);
                    pthread_mutex_unlock(&u->mutex);
                    pr("push from %d to %d: ue = %d, f = %d, c = %d, so "
                       "pushing %d.\n",
                       id(g, u), id(g, v), ue, e->f, e->c, d);
                    int ve = 0;
                    pthread_mutex_lock(&v->mutex);
                    v->e += d;
                    ve = v->e;
                    pthread_mutex_unlock(&v->mutex);

                    // NOTE(pf): Not source and sink AND didn't previously
                    // have excess add to our excess list. We do not need to
                    // lock the graph here either since only one of the
                    // threads are working.
                    if (v == g->s || v == g->t) {
                        pthread_mutex_lock(&g->mutex);
                        g->shutdown = abs(g->s->e) == g->t->e;
                        if (g->shutdown) {
                            pr("Initiate shutdown.\n");
                        }
                        pthread_mutex_unlock(&g->mutex);
                    } else if (ve == d) {
                        pthread_mutex_lock(&g->mutex);
                        pr("Thread %d add node: %d to excess list.\n",
                           thread_local->id, id(g, v));
                        v->next = g->excess;
                        g->excess = v;
                        ++g->nrExcess;
                        pthread_mutex_unlock(&g->mutex);
                    }

                    if (ue == 0) {
                        u = NULL;
                        pr("Thread %d exits loop.\n", thread_local->id);
                        break;
                    }
                }
            }
        }

        // PART 2: Synchronization and relabeling.
        pr("Thread %d waiting at barrier 2.\n", thread_local->id);
        pthread_barrier_wait(&g->barrier);
        pr("Thread %d start from barrier 2.\n", thread_local->id);
        // Check if we should relabel.
        if (u != NULL && p == NULL) {
            relabel_thread(thread_local, u);
            u->next = excess;
            excess = u;
        }

        pthread_mutex_lock(&g->mutex);
        if (g->shutdown) {
            pthread_mutex_unlock(&g->mutex);
            pr("Thread %d shutdown.\n", thread_local->id);
            break;
        }
        pthread_mutex_unlock(&g->mutex);
    }

    pr("?:D\n");
    pthread_barrier_wait(&g->barrier);
    // #if PRINT
    pthread_mutex_lock(&g->mutex);
    printf("Thread %d ends. Nodes processed %d.\n", thread_local->id,
           processed_nodes);
    pthread_mutex_unlock(&g->mutex);
    // #endif
    return NULL;
}

int xpreflow(graph_t *g) {
    // used for initial pushes.
    node_t *s; /* source */
    node_t *u; /* current node */
    node_t *v; /* target node */
    edge_t *e; /* current edge */
    list_t *p; /* adj. list */

    int i; /* thread loop index		*/
    int n; /* number of nodes in graph */

    n = g->n;
    s = g->s;
    s->h = g->n;
    p = s->edge;

    // NOTE(pf): Initialize source as the negative value of its total flow
    // for the exit condition to work.
    g->shutdown = false;
    // NOTE(pf): Start threads..
    int nrThreads = sysconf(_SC_THREAD_THREADS_MAX);
    if (nrThreads == -1) {
        nrThreads = sysconf(_SC_NPROCESSORS_ONLN);
    }
    g->nrThreads = nrThreads;
    g->nrExcess = 0;

    pthread_mutex_init(&g->mutex, NULL);
    pthread_barrier_init(&g->barrier, NULL, nrThreads);
    // NOTE(pf): Force thread count for now.
    // NOTE(pf): Continue from here, debug the code and hope for the best!
    // nrThreads = 4;
    // nrThreads = nrThreads * 2;

    // NOTE(pf): This lock is to prevent helgrind from complaining.
    pthread_mutex_lock(&g->mutex);
    while (p != NULL) {
        e = p->edge;
        p = p->next;
        s->e -= e->c;
        v = other(s, e);
        v->e += e->c;
        if (v != g->t) {
            pr("Initial add node: %d to excess list.\n", id(g, v));
            v->next = g->excess;
            g->excess = v;
            ++g->nrExcess;
        }
    }

    pr("THREADS INITIALIZED! %d\n", nrThreads);
    pthread_t threads[nrThreads];
    thread_local_data_t thread_local[nrThreads];
    for (i = 0; i < nrThreads; ++i) {
        thread_local[i].id = i;
        thread_local[i].graph = g;
    }
    pthread_mutex_unlock(&g->mutex);
    for (i = 0; i < nrThreads; ++i) {
        // thread_work(&thread_local[i]);
        if (pthread_create(&threads[i], NULL, thread_work, &thread_local[i])) {
            printf("Failed to create a thread at %d.", i);
            break;
        }
    }

    for (i = 0; i < nrThreads; ++i)
        pthread_join(threads[i], NULL);

    return g->t->e;
}

#if FORSETE
int preflow(int n, int m, int s, int t, xedge_t *e) {

    graph_t *g;
    int f;
    double begin;
    double end;

#if TIME
    init_timebase();
    begin = timebase_sec();
#endif
    g = new_graph(n, m, s, t, e);
    f = xpreflow(g);
    free_graph(g);
#if TIME
    end = timebase_sec();
    printf("t = %10.3lf s\n", end - begin);
#endif
    return f;
}
#else
int main(int argc, char *argv[]) {
    FILE *in;   /* input file set to stdin	*/
    graph_t *g; /* undirected graph. 		*/
    int f;      /* output from preflow.		*/
    int n;      /* number of nodes.		*/
    int m;      /* number of edges.		*/

#if TIME
    init_timebase();
    double begin = timebase_sec();
#endif
    progname = argv[0]; /* name is a string in argv[0]. */

    in = stdin; /* same as System.in in Java.	*/

    n = next_int();
    m = next_int();

    /* skip C and P from the 6railwayplanning lab in EDAF05 */
    next_int();
    next_int();

    g = new_graph(in, n, m);
    fclose(in);

    f = xpreflow(g);

    printf("f = %d\n", f);
    // printf("Sanity check\n");

    free_graph(g);

#if TIME
    double end = timebase_sec();
    printf("t = %10.3lf s\n", end - begin);
#endif
    return 0;
}
#endif
