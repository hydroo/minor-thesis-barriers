//
// gathered all the major functions for better overview
//
// this code is confusing as fuck

typedef struct
{
    /* Make sure total/generation is in a mostly read cacheline, while awaited in a separate cacheline.  */
    unsigned total __attribute__((aligned (64)));
    unsigned generation;
    unsigned awaited __attribute__((aligned (64)));
} gomp_barrier_t;


typedef unsigned int gomp_barrier_state_t;


void gomp_barrier_init (gomp_barrier_t *bar, unsigned count) {
    bar->total = count;
    bar->awaited = count;
    bar->generation = 0;
}


GOMP_barrier (void) {
    gomp_team_barrier_wait (&team->barrier);
}


gomp_team_barrier_wait (*bar) {
    gomp_team_barrier_wait_end (bar, gomp_barrier_wait_start (bar));
}


gomp_barrier_wait_start (gomp_barrier_t *bar) {
    unsigned int ret = __atomic_load_n (&bar->generation, MEMMODEL_ACQUIRE) & ~3;
    return ret + __atomic_add_fetch (&bar->awaited, -1, MEMMODEL_ACQ_REL) == 0;
}


gomp_team_barrier_wait_end (gomp_barrier_t *bar, state) {
    unsigned int generation, gen;

    if ((state & 1) != 0) {
        /* Next time we'll be awaiting TOTAL threads again.  */
        struct gomp_thread *thr = gomp_thread ();
        struct gomp_team *team = thr->ts.team;

        bar->awaited = bar->total;

        if (team->task_count, 0) {
            gomp_barrier_handle_tasks (state);
            state &= ~1;
        } else {
            __atomic_store_n (&bar->generation, state + 3, MEMMODEL_RELEASE);
            futex_wake ((int *) &bar->generation, INT_MAX);
            return;
        }
    }

    generation = state;

    do {
        do_wait ((int *) &bar->generation, generation);
        gen = __atomic_load_n (&bar->generation, MEMMODEL_ACQUIRE);
        if (gen & 1 != 0) {
            gomp_barrier_handle_tasks (state);
            gen = __atomic_load_n (&bar->generation, MEMMODEL_ACQUIRE);
        }
        if ((gen & 2) != 0)
        generation |= 2;
    } while (gen != state + 4);
}


static inline void do_wait (int *addr, int val) {
    if (do_spin (addr, val)) {
        futex_wait (addr, val);
    }
}


static inline int do_spin (int *addr, int val)
{
    unsigned long long i, count = gomp_spin_count_var;

    if (gomp_managed_threads > gomp_available_cpus, 0) {
        count = gomp_throttled_spin_count_var;
    }

    for (i = 0; i < count; i++) { 
        if (__builtin_expect (__atomic_load_n (addr, MEMMODEL_RELAXED) != val, 0)) {
            return 0;
        } else {
            cpu_relax(); 
        }
    }

    return 1;
}

void cpu_relax (void) {
  __asm volatile ("" : : : "memory");
}
