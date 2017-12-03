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

(** NOTE this is normally a requirement of the definition of sigma algebra but
    since we already know it's a powerset we can just do the proof and use it
    so that we can more easily use the measurable space definition later
*)
Lemma space_in_sigalg : forall A ms, In (Space A) (sigalg A ms) (space A ms).
Proof.
  intros A ms.
  apply Definition_of_Power_set.
  unfold Included.
  auto.
Qed.

Lemma elem_sigalg_subset_space :
  forall (A : Set) ms E,
    In (Ensemble A) (sigalg A ms) E
    -> Included A E (space A ms).
Proof.
  intros A ms E Hin.
  Admitted.


Lemma union_in_sigalg :
  forall (A : Set) ms E1 E2,
    In (Ensemble A) (sigalg A ms) E1
    -> In (Ensemble A) (sigalg A ms) E2
    -> In (Ensemble A) (sigalg A ms) (Union A E1 E2).
Proof.
  intros A ms E1 E2 Hin1 Hin2.
  apply Definition_of_Power_set.
  apply Union_minimal; apply elem_sigalg_subset_space; auto.
Qed.


(** probability measure, mu : E -> [0,1] *)
Record Measure {A : Set} (ms : MS A) :=
  mkMeasure {
    m_func : forall E, In (Ensemble A) (sigalg A ms) E -> U;
    empty: m_func (Empty_set A) = 0;
    full: m_func (space A ms) (space_in_sigalg A ms) = 1;
    addcount:
      forall E1 E2 pE1 pE2,
        m_func E1 pE1 + m_func E2 pE2 = m_func (Union A E1 E2)
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