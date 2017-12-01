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
    mf_func : A -> B;
    preimage:
      forall E2,
        In (Ensemble B) (sigalg B S2) E2
        -> sig (fun E1 =>
            (forall x, In B E2 (mf_func x) <-> In A E1 x) /\
            In (Ensemble A) (sigalg A S1) E1)
  }.

(** Literals 0 and 1 need to be from U not nat *)
Open Local Scope U_scope.

(** probability measure, mu : E -> [0,1] *)
Record Measure {A : Set} (ms : MS A) :=
  mkMeasure {
    m_func : Ensemble A -> U;
    empty: m_func (Empty_set A) = 0;
    (** TODO this isn't quite right since we don't want to use the full set of A
        as the domain but rather the full Ensemble of A *)
    full: m_func (Full_set A) = 1;
    addcount:
      forall E1 E2,
        In (Ensemble A) (sigalg A ms) E1
        -> In (Ensemble A) (sigalg A ms) E2
        -> m_func E1 + m_func E2 = m_func (Union A E1 E2)
  }.

(** probability space, PS : {S, mu} *)
Record PS (A : Set) :=
  mkPS {
    ms : MS A;
    mu : Measure ms
  }.

(** push forward, f : (E -> [0,1]) -> (E' -> [0,1]) *)
Definition push_forward {A B : Set} (psa : PS A) (msb : MS B) (mf : MF (ms A psa) msb ) : PS B.
  refine (mkPS B msb _).
  refine (_ (mu A psa)).
  intros HmuA.
  Check mkMeasure B msb.

  assert (forall E, In (Ensemble B) (sigalg B msb) E -> U) as Hmap.
  intros E Heinsig.
  assert (sig (fun E1 =>
                 (forall x, In B E ((mf_func (ms A psa) msb mf) x) <-> In A E1 x) /\
                 In (Ensemble A) (sigalg A (ms A psa)) E1)) as Hpre.

  apply ((preimage (ms A psa) msb mf) E). auto.
  destruct Hpre as [E1 Hfacts].
  apply ((m_func (ms A psa) HmuA) E1).

  refine (mkMeasure B msb (fun Eb : Ensemble B => (m_func (ms A psa) HmuA) (Hmap Eb)) _ _ _).
  
  Defined.

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

Inductive term : Type :=
| term_var : nat -> term
(** x <- flip U *)
| term_flip : term -> U -> term
(** x <- unif n1 n2 *)
| term_unif : term -> nat -> nat -> term
(** x <- mf *)
| term_ms : term -> mf -> term

with mf : Type :=
     | mf_plus : term -> term -> mf.

Definition prod_space {A B : Set} (psa : PS A) (psb : PS B) : PS (prod A B).
  refine (mkPS (A * B)
               (mkMS (A * B)
                     (fun ab =>
                        In A (space A (ms A psa)) (fst ab) /\
                        In B (space B (ms B psb)) (snd ab)))
                (fun msab setab =>  mu A psa ).
  


Fixpoint mkdist {A : Set} (s : Space A) (init_terms : list term) : PS A := mkPS A s.

Record prog :=
  mkProg {
    init : list term;
    init_dist : mkdist 
    statements : list term
  }.

Fixpoint init_ps (p : prog) : PS (:= 
Fixpoint eval : prog -> PS := 