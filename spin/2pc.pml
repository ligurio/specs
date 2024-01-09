/*
 * Two-phase commit (2PC) is a very simple and elegant protocol
 * that ensures the atomic commitment of distributed transactions.
 */

/* A number of processes. */
#ifndef NPROC
#define NPROC 3
#endif /* NPROC */

mtype = {
	ABORT,
	COMMIT,
	START,
	UNDEFINED
};

/* A channel with messages produced by resource manager. */
chan Mchan = [0] of {mtype};

/* A channel with messages produced by processes. */
chan Pchan = [0] of {mtype};

/* By default global decision is undefined. */
mtype CommonDecision = UNDEFINED;

proctype manager() {
	byte count = 0;
	do
	:: (count < NPROC) -> Mchan ! START; count++;
	:: (count == NPROC) -> break;
	od;

	CommonDecision = COMMIT;
	mtype vote;
	do
	:: (count < 2 * NPROC) -> Pchan ? vote; count++;
	   if
	   :: (vote == ABORT) -> CommonDecision = ABORT;
	   :: (vote == COMMIT) -> skip;
	   fi
	:: (count == 2 * NPROC) -> break;
	od;

	do
	:: (count < 3 * NPROC) -> Mchan ! CommonDecision; count++;
	:: (count == 3 * NPROC) -> break;
	od;
}

proctype proc(byte proc_id) {
	mtype proc_decision = UNDEFINED;
	Mchan ? START ->
	if
	:: Pchan ! ABORT; Mchan ? proc_decision; proc_decision = ABORT;
	:: Pchan ! COMMIT; Mchan ? proc_decision
	fi;
	assert(proc_decision == CommonDecision)
}

init {
	byte started_procs = 0;
	do
	:: (started_procs < NPROC) -> run proc(started_procs); started_procs++;
	:: (started_procs == NPROC) -> break;
	od;

	run manager();
}
