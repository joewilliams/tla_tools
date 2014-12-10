--------------------------- MODULE 3pc ---------------------------
EXTENDS TLC

(* some ideas ripped off of http://brooker.co.za/blog/2013/01/20/two-phase.html *)

(* --algorithm 3pc {

  variables cohort = { "a", "b", "c"}, cohort_state = [ i \in cohort |-> "start" ], k, aborted = FALSE, refused = FALSE;

  macro SetAll(state, k) {
    while (k # {}) {
      with (p \in k) {
        cohort_state[p] := state;
          k := k \ {p};
      };
    };
  }

  process (Transaction \in cohort) {
    cohort_propose:
      await cohort_state[self] = "propose";

      either {
        cohort_state[self] := "yes";
      } or {
        cohort_state[self] := "no";
        refused := TRUE;
      };

    cohort_precommit:
      await (cohort_state[self] = "precommit") \/ (cohort_state[self] = "abort");

      if (cohort_state[self] = "precommit") {
        either {
          cohort_state[self] := "ack";
        } or {
          cohort_state[self] := "abort";
          refused := TRUE;
        };
      } else {
        cohort_state[self] := "abort";
      };

    cohort_commit:
      await (cohort_state[self] = "commit") \/ (cohort_state[self] = "abort");

    if (cohort_state[self] = "commit") {
      assert(refused = FALSE);
    }

  }

  process (Coordinator = "coordinator") {
    start:
      k := cohort;

    coordinator_proposal:
      SetAll("propose", k);
      k := cohort;

    coordinator_proposal_tally:
      while (k # {}) {
        with (p \in k) {
          await (cohort_state[p] = "yes") \/ (cohort_state[p] = "no");

          if (cohort_state[p] = "no") {
            aborted := TRUE;
          };

          k := k \ {p};
        };
      };

    k := cohort;
    if (aborted = TRUE) {
      coordinator_proposal_abort: SetAll("abort", k);
      k := cohort;
    } else {
      coordinator_proposal_approved: SetAll("precommit", k);
      k := cohort;
    };

    coordinator_precommit_tally:
      while (k # {}) {
        with (p \in k) {
          await (cohort_state[p] = "ack") \/ (cohort_state[p] = "abort");

          if (cohort_state[p] = "abort") {
            aborted := TRUE;
          };

          k := k \ {p};
        };
      };

    k := cohort;
    if (aborted = TRUE) {
      coordinator_precommit_abort: SetAll("abort", k);
    } else {
      coordinator_precommit_approved: SetAll("commit", k);
    };
  }

}

*)

\* Invariants

StateOK == /\ (\A i \in cohort: cohort_state[i] \in {"start", "propose",
            "yes", "no", "commit", "abort", "ack"})

FinalState == /\ \/ <>(\A i \in cohort: cohort_state[i] = "commit")
                \/ <>(\A i \in cohort: cohort_state[i] = "abort")
===================================================================

