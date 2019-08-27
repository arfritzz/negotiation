Definition my_SA_map_base := SA_record (SA_ID 0) (One (time (1200)))  (SA_empty).
Check my_SA_map_base.

Definition myterm1 := (KIM 3).
Definition myterm2 := (AT 4 (USM 4)).
Definition myterm3 := (SIG (KIM 3)).
Definition myterm4 := (SEQ (KIM 3)).
Definition myterm5 := (PAR (SIG (USM 4))).

Definition myrequest0 := EV (myterm1).
Definition myrequest1 := EV (myterm3).
Definition myrequest2 := SUM (myrequest1) (myrequest0).
Definition myrequest3 := SUM (EV (KIM 3)) (EV (KIM 10)).
Definition myrequest4 := SUM (EV (KIM 10)) (EV (KIM 3)).

Definition myprotocol1 := PAR (KIM 3) (USM 3).

Definition my_protocol_map_base := R_record (R_ID (EV (KIM 3))) (KIM 3) (R_empty).
Definition my_partial_map_1 := R_update (my_protocol_map_base) (R_ID (EV (USM 3))) (SEQ (USM 3) (KIM 3)).
