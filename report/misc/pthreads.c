struct pthread_barrier {
    unsigned int curr_event;
    int lock;
    unsigned int left;
    unsigned int init_count;
    int private;
};


int pthread_barrier_init (pthread_barrier_t *barrier, const pthread_barrierattr_t *attr, unsigned int count) {
    struct pthread_barrier *ibarrier;

    if (count == 0) return EINVAL;

    const struct pthread_barrierattr *iattr = (attr != NULL
            ? iattr = (struct pthread_barrierattr *) attr
            : &default_attr);

    if (iattr->pshared != PTHREAD_PROCESS_PRIVATE && __builtin_expect (iattr->pshared != PTHREAD_PROCESS_SHARED, 0)) {
        /* Invalid attribute.  */
        return EINVAL;
    }

    ibarrier = (struct pthread_barrier *) barrier;

    /* Initialize the individual fields.  */
    ibarrier->lock = LLL_LOCK_INITIALIZER;
    ibarrier->left = count;
    ibarrier->init_count = count;
    ibarrier->curr_event = 0;

#ifdef __ASSUME_PRIVATE_FUTEX
    ibarrier->private = (iattr->pshared != PTHREAD_PROCESS_PRIVATE
               ? 0 : FUTEX_PRIVATE_FLAG);
#else
    ibarrier->private = (iattr->pshared != PTHREAD_PROCESS_PRIVATE
               ? 0 : THREAD_GETMEM (THREAD_SELF, header.private_futex));
#endif

    return 0;
}


int pthread_barrier_destroy (pthread_barrier_t *barrier) {
    struct pthread_barrier *ibarrier;
    int result = EBUSY;

    ibarrier = (struct pthread_barrier *) barrier;

    lll_lock (ibarrier->lock, ibarrier->private ^ FUTEX_PRIVATE_FLAG);

    if (ibarrier->left == ibarrier->init_count) {
        /* The barrier is not used anymore.  */
        result = 0;
    } else {
        /* Still used, return with an error.  */
        lll_unlock (ibarrier->lock, ibarrier->private ^ FUTEX_PRIVATE_FLAG);
    }

    return result;
}


int pthread_barrier_wait (pthread_barrier_t *barrier) {
    struct pthread_barrier *ibarrier = (struct pthread_barrier *) barrier;
    int result = 0;

    /* Make sure we are alone.  */
    lll_lock (ibarrier->lock, ibarrier->private ^ FUTEX_PRIVATE_FLAG);

    /* One more arrival.  */
    --ibarrier->left;

    /* Are these all?  */
    if (ibarrier->left == 0) {

        /* Yes. Increment the event counter to avoid invalid wake-ups and
        tell the current waiters that it is their turn. */
        ++ibarrier->curr_event;

        /* Wake up everybody.  */
        lll_futex_wake (&ibarrier->curr_event, INT_MAX, ibarrier->private ^ FUTEX_PRIVATE_FLAG);

        /* This is the thread which finished the serialization. */
        result = PTHREAD_BARRIER_SERIAL_THREAD;

    } else {

        /* The number of the event we are waiting for. The barrier's event number must be bumped before we continue. */
        unsigned int event = ibarrier->curr_event;

        /* Before suspending, make the barrier available to others.  */
        lll_unlock (ibarrier->lock, ibarrier->private ^ FUTEX_PRIVATE_FLAG);

        /* Wait for the event counter of the barrier to change.  */
        do {
            lll_futex_wait (&ibarrier->curr_event, event, ibarrier->private ^ FUTEX_PRIVATE_FLAG);
        }

        while (event == ibarrier->curr_event);
    }

    /* Make sure the init_count is stored locally or in a register.  */
    unsigned int init_count = ibarrier->init_count;

    /* If this was the last woken thread, unlock.  */
    if (atomic_increment_val (&ibarrier->left) == init_count) {
        /* We are done.  */
        lll_unlock (ibarrier->lock, ibarrier->private ^ FUTEX_PRIVATE_FLAG);
    }

    return result;
}
