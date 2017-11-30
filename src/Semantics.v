Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset.
Require Import Utheory.

(** Definitions
    - sample space, W : [A]
 *)
Definition Space (A : Set) := Ensemble A.

(** 
    - events, E = Pow(W) : 2^s
      Power_set A W.
 *)
Definition SigAlg (A : Set) := Ensemble (Ensemble A).

(** 
    - measurable space, S : { W * E, pow : E = 2^W }
 *)

Record MS (A : Set) : Type := 
  mkMS {
    carrier := A;
    space : Space A;
    sigalg := Power_set A space
  }.

(** 
    - measurable function, MF { f : S -> S; Pf : preimage }
      - proof, compose f g : MF
 *)

Record MF {A B: Set} (S1 : MS A) (S2 : MS B) :=
  mkMF {
    func : A -> B;
    preimage:
      forall E2,
        In (Ensemble B) (sigalg B S2) E2
        -> sig (fun E1 =>
            (forall x, In B E2 (func x) <-> In A E1 x) /\
            In (Ensemble A) (sigalg A S1) E1)
  }.

(** probability measure, mu : E -> [0,1] *)
Definition Measure {A : Set} (ms : MS A) := forall E, In (Ensemble A) (sigalg A ms) E -> U.

(** probability space, PS : {S, mu} *)
Record PS (A : Set) :=
  mkPS {
    ms : MS A;
    mu : Measure ms
  }.

(**
    - push forward, f : (E -> [0,1]) -> (E' -> [0,1])
      - proof, given a measurable function exists a pushforward
      - alt type : PS A -> MS B -> MF (MS A) (MS B) -> PS B 
 *)

Definition push_forward {A B : Set} (psa : PS A) (msb : MS B) (mf : MF (ms A psa) msb ) : PS B.
  refine (mkPS B msb _).
  refine (_ (mu A psa)).
  unfold Measure.
  intros HmuA E HinB.

  assert (sig (fun E1 =>
                 (forall x, In B E (func (ms A psa) msb mf x) <-> In A E1 x) /\
                 In (Ensemble A) (sigalg A (ms A psa)) E1)) as Hpre.

  apply ((preimage (ms A psa) msb mf) E); auto.
  elim Hpre. intros E1 Hpre'.
  apply (HmuA E1).
  destruct Hpre'; assumption.
Defined.

  (** SigAlg B -> U from 
      SigAlg B -> SigAlg A compose with
      SigAlg A -> U *)


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

