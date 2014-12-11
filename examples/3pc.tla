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
      await (cohort_state[self] = "precommit") \/ (cohort_state[self] = "proposal_abort");

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
      await (cohort_state[self] = "commit") \/ (cohort_state[self] = "precommit_abort");

    if (cohort_state[self] = "commit") {
      assert(refused = FALSE);
      cohort_state[self] := "committed";
    } else {
      cohort_state[self] := "aborted";
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
      coordinator_proposal_abort: SetAll("proposal_abort", k);
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
      coordinator_precommit_abort: SetAll("precommit_abort", k);
      k := cohort;
    } else {
      coordinator_precommit_approved: SetAll("commit", k);
      k := cohort;
    };

    final_tally:
      while (k # {}) {
        with (p \in k) {
          await (cohort_state[p] = "committed") \/ (cohort_state[p] = "aborted");

          k := k \ {p};
        };
      };
  }

}

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES cohort, cohort_state, k, aborted, refused, pc

vars == << cohort, cohort_state, k, aborted, refused, pc >>

ProcSet == (cohort) \cup {"coordinator"}

Init == (* Global variables *)
        /\ cohort = { "a", "b", "c"}
        /\ cohort_state = [ i \in cohort |-> "start" ]
        /\ k = defaultInitValue
        /\ aborted = FALSE
        /\ refused = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in cohort -> "cohort_propose"
                                        [] self = "coordinator" -> "start"]

cohort_propose(self) == /\ pc[self] = "cohort_propose"
                        /\ cohort_state[self] = "propose"
                        /\ \/ /\ cohort_state' = [cohort_state EXCEPT ![self] = "yes"]
                              /\ UNCHANGED refused
                           \/ /\ cohort_state' = [cohort_state EXCEPT ![self] = "no"]
                              /\ refused' = TRUE
                        /\ pc' = [pc EXCEPT ![self] = "cohort_precommit"]
                        /\ UNCHANGED << cohort, k, aborted >>

cohort_precommit(self) == /\ pc[self] = "cohort_precommit"
                          /\ (cohort_state[self] = "precommit") \/ (cohort_state[self] = "proposal_abort")
                          /\ IF cohort_state[self] = "precommit"
                                THEN /\ \/ /\ cohort_state' = [cohort_state EXCEPT ![self] = "ack"]
                                           /\ UNCHANGED refused
                                        \/ /\ cohort_state' = [cohort_state EXCEPT ![self] = "abort"]
                                           /\ refused' = TRUE
                                ELSE /\ cohort_state' = [cohort_state EXCEPT ![self] = "abort"]
                                     /\ UNCHANGED refused
                          /\ pc' = [pc EXCEPT ![self] = "cohort_commit"]
                          /\ UNCHANGED << cohort, k, aborted >>

cohort_commit(self) == /\ pc[self] = "cohort_commit"
                       /\ (cohort_state[self] = "commit") \/ (cohort_state[self] = "precommit_abort")
                       /\ IF cohort_state[self] = "commit"
                             THEN /\ Assert((refused = FALSE), 
                                            "Failure of assertion at line 48, column 7.")
                                  /\ cohort_state' = [cohort_state EXCEPT ![self] = "committed"]
                             ELSE /\ cohort_state' = [cohort_state EXCEPT ![self] = "aborted"]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << cohort, k, aborted, refused >>

Transaction(self) == cohort_propose(self) \/ cohort_precommit(self)
                        \/ cohort_commit(self)

start == /\ pc["coordinator"] = "start"
         /\ k' = cohort
         /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_proposal"]
         /\ UNCHANGED << cohort, cohort_state, aborted, refused >>

coordinator_proposal == /\ pc["coordinator"] = "coordinator_proposal"
                        /\ IF k # {}
                              THEN /\ \E p \in k:
                                        /\ cohort_state' = [cohort_state EXCEPT ![p] = "propose"]
                                        /\ k' = k \ {p}
                                   /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_proposal"]
                              ELSE /\ k' = cohort
                                   /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_proposal_tally"]
                                   /\ UNCHANGED cohort_state
                        /\ UNCHANGED << cohort, aborted, refused >>

coordinator_proposal_tally == /\ pc["coordinator"] = "coordinator_proposal_tally"
                              /\ IF k # {}
                                    THEN /\ \E p \in k:
                                              /\ (cohort_state[p] = "yes") \/ (cohort_state[p] = "no")
                                              /\ IF cohort_state[p] = "no"
                                                    THEN /\ aborted' = TRUE
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED aborted
                                              /\ k' = k \ {p}
                                         /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_proposal_tally"]
                                    ELSE /\ k' = cohort
                                         /\ IF aborted = TRUE
                                               THEN /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_proposal_abort"]
                                               ELSE /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_proposal_approved"]
                                         /\ UNCHANGED aborted
                              /\ UNCHANGED << cohort, cohort_state, refused >>

coordinator_proposal_abort == /\ pc["coordinator"] = "coordinator_proposal_abort"
                              /\ IF k # {}
                                    THEN /\ \E p \in k:
                                              /\ cohort_state' = [cohort_state EXCEPT ![p] = "proposal_abort"]
                                              /\ k' = k \ {p}
                                         /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_proposal_abort"]
                                    ELSE /\ k' = cohort
                                         /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_precommit_tally"]
                                         /\ UNCHANGED cohort_state
                              /\ UNCHANGED << cohort, aborted, refused >>

coordinator_proposal_approved == /\ pc["coordinator"] = "coordinator_proposal_approved"
                                 /\ IF k # {}
                                       THEN /\ \E p \in k:
                                                 /\ cohort_state' = [cohort_state EXCEPT ![p] = "precommit"]
                                                 /\ k' = k \ {p}
                                            /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_proposal_approved"]
                                       ELSE /\ k' = cohort
                                            /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_precommit_tally"]
                                            /\ UNCHANGED cohort_state
                                 /\ UNCHANGED << cohort, aborted, refused >>

coordinator_precommit_tally == /\ pc["coordinator"] = "coordinator_precommit_tally"
                               /\ IF k # {}
                                     THEN /\ \E p \in k:
                                               /\ (cohort_state[p] = "ack") \/ (cohort_state[p] = "abort")
                                               /\ IF cohort_state[p] = "abort"
                                                     THEN /\ aborted' = TRUE
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED aborted
                                               /\ k' = k \ {p}
                                          /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_precommit_tally"]
                                     ELSE /\ k' = cohort
                                          /\ IF aborted = TRUE
                                                THEN /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_precommit_abort"]
                                                ELSE /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_precommit_approved"]
                                          /\ UNCHANGED aborted
                               /\ UNCHANGED << cohort, cohort_state, refused >>

coordinator_precommit_abort == /\ pc["coordinator"] = "coordinator_precommit_abort"
                               /\ IF k # {}
                                     THEN /\ \E p \in k:
                                               /\ cohort_state' = [cohort_state EXCEPT ![p] = "precommit_abort"]
                                               /\ k' = k \ {p}
                                          /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_precommit_abort"]
                                     ELSE /\ k' = cohort
                                          /\ pc' = [pc EXCEPT !["coordinator"] = "final_tally"]
                                          /\ UNCHANGED cohort_state
                               /\ UNCHANGED << cohort, aborted, refused >>

coordinator_precommit_approved == /\ pc["coordinator"] = "coordinator_precommit_approved"
                                  /\ IF k # {}
                                        THEN /\ \E p \in k:
                                                  /\ cohort_state' = [cohort_state EXCEPT ![p] = "commit"]
                                                  /\ k' = k \ {p}
                                             /\ pc' = [pc EXCEPT !["coordinator"] = "coordinator_precommit_approved"]
                                        ELSE /\ k' = cohort
                                             /\ pc' = [pc EXCEPT !["coordinator"] = "final_tally"]
                                             /\ UNCHANGED cohort_state
                                  /\ UNCHANGED << cohort, aborted, refused >>

final_tally == /\ pc["coordinator"] = "final_tally"
               /\ IF k # {}
                     THEN /\ \E p \in k:
                               /\ (cohort_state[p] = "committed") \/ (cohort_state[p] = "aborted")
                               /\ k' = k \ {p}
                          /\ pc' = [pc EXCEPT !["coordinator"] = "final_tally"]
                     ELSE /\ pc' = [pc EXCEPT !["coordinator"] = "Done"]
                          /\ k' = k
               /\ UNCHANGED << cohort, cohort_state, aborted, refused >>

Coordinator == start \/ coordinator_proposal \/ coordinator_proposal_tally
                  \/ coordinator_proposal_abort
                  \/ coordinator_proposal_approved
                  \/ coordinator_precommit_tally
                  \/ coordinator_precommit_abort
                  \/ coordinator_precommit_approved \/ final_tally

Next == Coordinator
           \/ (\E self \in cohort: Transaction(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants

StateOK == /\ (\A i \in cohort: cohort_state[i] \in {"start", "propose",
            "yes", "no", "commit", "abort", "ack", "proposal_abort",
            "precommit_abort"})

FinalState == /\ \/ <>(\A i \in cohort: cohort_state[i] = "committed")
                \/ <>(\A i \in cohort: cohort_state[i] = "aborted")


===================================================================

