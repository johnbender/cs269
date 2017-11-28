Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset.

(** Definitions
    - sample space, W : [A]
 *)
Definition Space (A : Set) := Ensemble A.

(** 
    - events, E = Pow(W) : 2^s
      Power_set A W.
 *)
Definition SigAlg (A : Set) := Ensemble (Ensemble A).

Check Ensemble (Ensemble nat).

(** 
    - measurable space, S : { W * E, pow : E = 2^W }
 *)

Record MeasurableSpace {A : Set} : Type := 
  { space: Space A;
    (* sigalg: SigAlg A; *)
    sigalg: Ensemble (Ensemble A);

    (** confine our spaces to the power sets of the sample space *)
    sigalg_pow: sigalg = Power_set A space }.


(** 
    - measurable function, MF { f : S -> S; Pf : preimage }
      - proof, compose f g : MF
 *)

Record MeasurableFunction {A B: Set } (S1 S2 : MeasurableSpace) :=
  {
    f : A -> B;
    preimage:
      forall E2 x, exists E1,
          In (Ensemble A) (sigalg S1) E1
          -> In (Ensemble B) (sigalg S2) E2
          -> In B E2 (f x)
          -> In A E1 x
  }.

(** 
    - probability measure, mu : E -> [0,1]
 *)
(** 
    - probability space, PS : {S, mu}
 *)
(** 
    - push forward, f : (E -> [0,1]) -> (E' -> [0,1])
      - proof, given a measurable function exists a pushforward
 *)
(** 
    - p measurable functions, PMF { MF; f : (E -> [0,1]) -> (E' -> [0,1]) }
      - default f formulation with inverse of f given by preimage constraint
 *)
(** 
    - syntax
    - denotational semantics
      - init statements -> cartesian space
      - composed measurable functions -> single measurable function
      - notation/sugar
    - theorem
      - if <assumptions> then compose f g = compose g f
        - iterate on assumptions
        - 
 *)

