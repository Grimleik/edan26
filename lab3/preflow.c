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
// #include <math.h>

#define PRINT 0   /* enable/disable prints. */
#define TIME 0    /* for timing on power.	*/
#define FORSETE 1 /* enable/disable forsete. */

#if TIME
#include "timebase.h"
#endif

#if PRINT
#define pr(...)                       \
    do                                \
    {                                 \
        fprintf(stderr, __VA_ARGS__); \
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

struct xedge_t
{
    int u;
    int v;
    int c;
};

struct list_t
{
    edge_t *edge;
    list_t *next;
};

struct node_t
{
    int h;        /* height.			*/
    int e;        /* excess flow.			*/
    list_t *edge; /* adjacency list.		*/
    node_t *next; /* with excess preflow.		*/
    // pthread_mutex_t mutex; /* node lock. */
};

struct edge_t
{
    node_t *u; /* one of the two nodes.	*/
    node_t *v; /* the other. 			*/
    int f;     /* flow > 0 if from u to v.	*/
    int c;     /* capacity.			*/
};

struct graph_t
{
    int n;     /* nodes.			*/
    int m;     /* edges.			*/
    node_t *v; /* array of n nodes.		*/
    edge_t *e; /* array of m edges.		*/
    node_t *s; /* source.			*/
    node_t *t; /* sink.			*/
    // node_t *excess; /* nodes with e > 0 except s,t.	*/
    pthread_mutex_t mutex;
    pthread_barrier_t barrier;
    bool shutdown;
    int nrThreads;
};

typedef struct command_t command_t;
struct command_t
{
    node_t *u;
    node_t *v;
    edge_t *e;
};

typedef struct command_queue_t command_queue_t;
struct command_queue_t
{
    command_t *commands;
    int size;
    int capacity;
};

typedef struct thread_local_data_t thread_local_data_t;
struct thread_local_data_t
{
    graph_t *graph;
    command_queue_t *commandQueue;
    int id;
    int start;
    int stop;

    thread_local_data_t *head;
    int nrThreads;
};

static char *progname;

static int id(graph_t *g, node_t *v) { return v - g->v; }

void error(const char *fmt, ...)
{
    va_list ap;
    char buf[BUFSIZ];

    va_start(ap, fmt);
    vsprintf(buf, fmt, ap);

    if (progname != NULL)
        fprintf(stderr, "%s: ", progname);

    fprintf(stderr, "error: %s\n", buf);
    exit(1);
}

static int next_int()
{
    int x;
    int c;

    x = 0;
    while (isdigit(c = getchar()))
        x = 10 * x + c - '0';

    return x;
}

static void *xmalloc(size_t s)
{
    void *p;

    p = malloc(s);

    if (p == NULL)
        error("out of memory: malloc(%zu) failed", s);

    return p;
}

static void *xcalloc(size_t n, size_t s)
{
    void *p;
    p = xmalloc(n * s);
    memset(p, 0, n * s);
    return p;
}

static void add_edge(node_t *u, edge_t *e)
{
    list_t *p;
    p = xmalloc(sizeof(list_t));
    p->edge = e;
    p->next = u->edge;
    u->edge = p;
}

static void connect(node_t *u, node_t *v, int c, edge_t *e)
{
    e->u = u;
    e->v = v;
    e->c = c;

    add_edge(u, e);
    add_edge(v, e);
}

#if FORSETE

static graph_t *new_graph(int n, int m, int s, int t, xedge_t *e)
{
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
    // for (i = 0; i < n; ++i)
    // {
    //     pthread_mutex_init(&g->v[i].mutex, NULL);
    // }
    g->e = xcalloc(m, sizeof(edge_t));

    g->s = &g->v[0];
    g->t = &g->v[n - 1];
    // g->excess = NULL;

    for (i = 0; i < m; i += 1)
    {
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

static graph_t *new_graph(FILE *in, int n, int m)
{
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
    // for (i = 0; i < n; ++i)
    // {
    //     pthread_mutex_init(&g->v[i].mutex, NULL);
    // }
    g->e = xcalloc(m, sizeof(edge_t));

    g->s = &g->v[0];
    g->t = &g->v[n - 1];

    for (i = 0; i < m; i += 1)
    {
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

static void relabel_thread(graph_t *g, node_t *u)
{
    assert(u->e > 0);
    u->h += 1;
    assert(u->h <= (2 * g->n) + 1);

    pr("relabel %d now h = %d\n", id(g, u), u->h);
}

static int push(graph_t *g, node_t *u, node_t *v, edge_t *e)
{
    int d;
    // int d; /* remaining capacity of the edge. */
    if (u == e->u)
    {
        d = MIN(u->e, e->c - e->f);
        e->f += d;
    }
    else
    {
        d = MIN(u->e, e->c + e->f);
        e->f -= d;
    }

    /* the following are always true. */
    assert(d >= 0);
    assert(abs(e->f) <= e->c);
    // TODO(pf): Can we split this into separate threads dealing with this themselves ?
    u->e -= d;
    v->e += d;
    return d;
}

static node_t *other(node_t *u, edge_t *e)
{
    if (u == e->u)
        return e->v;
    else
        return e->u;
}

static void free_graph(graph_t *g)
{
    int i;
    list_t *p;
    list_t *q;

    for (i = 0; i < g->n; i += 1)
    {
        p = g->v[i].edge;
        // pthread_mutex_destroy(&g->v[i].mutex);
        while (p != NULL)
        {
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

void push_command(thread_local_data_t *args, node_t *u)
{
    node_t *v;
    edge_t *e;
    list_t *p;
    int b;
    graph_t *g = args->graph;

    p = u->edge;
    while (p != NULL)
    {
        e = p->edge;
        p = p->next;

        if (u == e->u)
        {
            v = e->v;
            b = 1;
        }
        else
        {
            v = e->u;
            b = -1;
        }

        if (u->h > v->h && b * e->f < e->c)
            break;
        else
            v = NULL;
    }

    if (args->commandQueue->size == args->commandQueue->capacity)
    {
        args->commandQueue->capacity *= 2;
        args->commandQueue->commands = realloc(args->commandQueue->commands, sizeof(command_t) * args->commandQueue->capacity);

        if (args->commandQueue->commands == NULL)
        {
            error("Failed to reallocate command queue.");
        }
    }

    command_t *c = &args->commandQueue->commands[args->commandQueue->size++];
    c->u = u;
    c->e = e;
    c->v = v;
}

/* THOUGHTS:
 * Divide nodes based on cache block, i.e nodes[i % nrThreads].
    * Potential opt.
        * Each thread has a local excess list.
        * If a thread pushes to a region of space where another thread owns,
        then we have to push that to that threads excess list.
 * Do a max of (nrThreads, nrExcess) threads.
 * Command queue of actions to take on our nodes.
 * Master thread who assigns to each other threads excess list from a global queue when the others pushes ?
 * This would require the following phases:
 * 1. Pick current excess and build command queue.
 * Barrier.
 * 2. Execute command queue / Assign to excess list.
 * Barrier.
 */

void *thread_work(void *arg)
{
    node_t *u;        /* active node */
    node_t *v;        /* other node in edge */
    edge_t *e;        /* current edge */
    list_t *p = NULL; /* adjecency list */
    int b;            /* edge direction */
    int i, j;         /* loop index */
    int nrOfProcessedNodes = 0;
    thread_local_data_t *thread_local = arg;
    graph_t *g = thread_local->graph;
    thread_local->commandQueue = malloc(sizeof(command_queue_t));
    thread_local->commandQueue->capacity = 4;
    thread_local->commandQueue->commands = malloc(sizeof(command_t) * thread_local->commandQueue->capacity);
    thread_local->commandQueue->size = 0;
    pthread_barrier_wait(&g->barrier);

    while (!g->shutdown)
    {
        // PART 1: Get command for each node.
        for (i = thread_local->start; i <= thread_local->stop; ++i)
        {
            u = &g->v[i];
            if (u->e == 0)
            {
                continue;
            }
            ++nrOfProcessedNodes;
            push_command(thread_local, u);
        }

        // PART 2: Master thread performs push and relabel as needed.
        int response = pthread_barrier_wait(&g->barrier);
        if (response == PTHREAD_BARRIER_SERIAL_THREAD)
        {
            pr("Thread %d executing command queue.\n", thread_local->id);
            bool exit = true;
            for (i = 0; i < thread_local->nrThreads; ++i)
            {
                command_queue_t *currentQueue = thread_local->head[i].commandQueue;
                for (int j = 0; j < currentQueue->size; ++j)
                {
                    exit = false;
                    command_t *c = &currentQueue->commands[j];
                    if (c->v != NULL)
                    {
                        int d = push(g, c->u, c->v, c->e);

                        pr("push from %d to %d: f = %d, c = %d, so pushing %d.\n",
                           id(g, c->u), id(g, c->v), c->e->f, c->e->c, d);
                        if (c->v == g->s || c->v == g->t)
                        {
                            g->shutdown = abs(g->s->e) == g->t->e;
#if PRINT
                            if (g->shutdown)
                            {
                                pr("Shutdown initiated flow is equal. Flow is %d.\n", g->t->e);
                                i = thread_local->nrThreads;
                                break;
                            }
#endif
                        }
                    }
                    else
                    {
                        relabel_thread(g, c->u);
                    }
                }

                currentQueue->size = 0;
            }

            if (exit)
            {
                g->shutdown = true;
                pr("Shutdown initiated, no more commands. Flow is %d.\n", g->t->e);
            }
        }

        pthread_barrier_wait(&g->barrier);
    }

#if PRINT
    pthread_mutex_lock(&g->mutex);
    printf("Thread %d processed %d nodes.\n", thread_local->id, nrOfProcessedNodes);
    printf("Thread %d started from %d and processed to %d.\n", thread_local->id, thread_local->start, thread_local->stop);
    pthread_mutex_unlock(&g->mutex);
#endif
    free(thread_local->commandQueue->commands);
    free(thread_local->commandQueue);
    return NULL;
}

int xpreflow(graph_t *g)
{
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
    if (nrThreads == -1)
    {
        nrThreads = sysconf(_SC_NPROCESSORS_ONLN);
    }
    nrThreads = MIN(nrThreads, 6);

    // NOTE(pf): One thread is the main thread. -2 for source and sink, -1 for main thread.
    nrThreads = MIN(g->n - 2, nrThreads);
    g->nrThreads = nrThreads;

    pthread_mutex_init(&g->mutex, NULL);
    int response = pthread_barrier_init(&g->barrier, NULL, nrThreads);
    // NOTE(pf): This lock is to prevent helgrind from complaining.
    pthread_mutex_lock(&g->mutex);

    while (p != NULL)
    {
        e = p->edge;
        p = p->next;
        s->e -= e->c;
        v = other(s, e);
        v->e += e->c;
    }

    // TODO(pf): Try this.
    pr("THREADS INITIALIZED: %d.\n", nrThreads);
    pthread_t threads[nrThreads - 1]; // Don't need to start 'main'.
    thread_local_data_t thread_local[nrThreads]; 
    pthread_mutex_unlock(&g->mutex);
    int start = 1;
    int stride = (g->n - 2) / nrThreads; // -2 for source and sink.
    for (i = 0; i < nrThreads - 1; ++i)
    {
        thread_local[i].graph = g;
        thread_local[i].id = i;
        thread_local[i].start = start;
        thread_local[i].stop = start + stride - 1;
        thread_local[i].head = thread_local;
        thread_local[i].nrThreads = nrThreads;
        start += stride;
        // thread_work(&thread_local[i]);
        if (pthread_create(&threads[i], NULL, thread_work, &thread_local[i]))
        {
            printf("Failed to create a thread at %d.", i);
            break;
        }
    }

    // NOTE(pf): Explicit handling of end to ensure we capture all nodes, e.g uneven stride division.
    thread_local[i].graph = g;
    thread_local[i].id = i;
    thread_local[i].start = start;
    thread_local[i].stop = n - 2; // -1 to be in 0..n range and then an additional one to skip the sink.
    thread_local[i].head = thread_local;
    thread_local[i].nrThreads = nrThreads;
    thread_work(&thread_local[i]);

    for (i = 0; i < nrThreads - 1; ++i)
        pthread_join(threads[i], NULL);

    return g->t->e;
}

#if FORSETE
int preflow(int n, int m, int s, int t, xedge_t *e)
{

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
int main(int argc, char *argv[])
{
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

    printf("total nodes %d\n", n);
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
