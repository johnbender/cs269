Require Import List.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset.
Require Import Utheory.

(** Definitions
    - sample space, W : [A]
 *)
Definition Space (A : Set) := Ensemble A.

(* https://stackoverflow.com/questions/22353508/how-to-create-ensemble-in-coq#22354969 *)
Fixpoint list_to_ensemble {A:Type} (l : list A) {struct l}: Ensemble A :=
  match l with
    | nil => Empty_set A
    | hd::tl => Add A (list_to_ensemble tl) hd
  end.

(** 
    - events, E = Pow(W) : 2^s
      Power_set A W.
 *)
Definition SigAlg (A : Set) := Ensemble (Ensemble A).

(** 
    - measurable space, S : { W * E, pow : E = 2^W }
 *)

Arguments In [U].
Arguments Included [U].
Arguments Power_set [U].
Arguments Same_set [U].
Arguments Union [U].

Record MS {A : Set} (l : list A): Type := 
  mkMS {
    carrier := A;
    enum := l;
    uniq : NoDup l;
    space := list_to_ensemble l;
    sigalg := Power_set space
  }.

Arguments mkMS [A l].
Arguments uniq [A l].
Arguments space [A l].
Arguments sigalg [A l].

(** 
    - measurable function, MF { f : S -> S; Pf : preimage }
      - proof, compose f g : MF
 *)

Record MF {A B: Set} {l1 l2} (S1 : @MS A l1) (S2 : @MS B l2) :=
  mkMF {
    mf_func : A -> B;
    msa := S1;
    msb := S2;
    preimage:
      forall E2,
        In (sigalg msb) E2
        -> sig (fun E1 =>
            (forall x, In E2 (mf_func x) <-> In E1 x) /\
            In (sigalg msa) E1)
    }.


(** Literals 0 and 1 need to be from U not nat *)
Open Local Scope U_scope.

(** NOTE this is all normally a requirement of the definition of sigma algebra
    but since we already know it's a powerset we can just do the proof and use
    it so that we can more easily use the measurable space definition later *)
Lemma space_in_sigalg : forall { A : Set } {l : list A} ms, In (@sigalg A l ms) (space ms).
Proof.
  intros A l ms.
  apply Definition_of_Power_set.
  unfold Included.
  auto.
Qed.

Lemma elem_sigalg_subset_space :
  forall (A : Set) l ms E,
    In (@sigalg A l ms) E
    -> Included E (space ms).
Proof.
  intros A l ms E Hin.
  unfold sigalg in Hin.
  inversion Hin.
  assumption.
Qed.

Lemma union_in_sigalg :
  forall { A : Set } { l : list A } ms { E1 E2 : Ensemble A },
    In (@sigalg A l ms) E1
    -> In (sigalg ms) E2
    -> In (sigalg ms) (Union E1 E2).
Proof.
  intros A l ms E1 E2 Hin1 Hin2.
  apply Definition_of_Power_set.
  apply Union_minimal; apply elem_sigalg_subset_space; auto.
Qed.

Lemma empty_bot : forall C x, In (Empty_set C) x -> False.
Proof.
  intros.
  unfold In in H.
  contradiction.
Qed.

Lemma union_empty :
  forall A E, Same_set (Union (Empty_set A) E) E.
Proof.
Admitted.

Lemma union_add_left_commute :
  forall A E1 E2 a, Same_set (Union (Add A E1 a) E2) (Add A (Union E1 E2) a).
Proof.
Admitted.

Lemma tail_in_sigalg :
  forall { A : Set } { l l1 : list A } ms a,
    In (@sigalg A l ms) (list_to_ensemble (a::l1))
    -> In (sigalg ms) (list_to_ensemble l1).
Proof.
Admitted.

Lemma concat_in_sigalg :
  forall { A : Set } { l : list A } ms { l1 l2 : list A },
    In (@sigalg A l ms) (list_to_ensemble l1)
    -> In (sigalg ms) (list_to_ensemble l2)
    -> In (sigalg ms) (list_to_ensemble (l1 ++ l2)).
Proof.
  intros A l ms l1 l2 Hin1 Hin2.
  assert ((list_to_ensemble (l1 ++ l2)) = (Union (list_to_ensemble l1) (list_to_ensemble l2))).

  induction l1.
  simpl.

  assert (Same_set (Union (Empty_set A) (list_to_ensemble l2)) (list_to_ensemble l2)).
  apply union_empty.
  apply Extensionality_Ensembles in H.
  rewrite -> H.
  reflexivity.

  simpl.
  assert (Same_set
            (Union (Add A (list_to_ensemble l1) a) (list_to_ensemble l2))
            (Add A (Union (list_to_ensemble l1) (list_to_ensemble l2)) a)).
  apply union_add_left_commute.
  apply Extensionality_Ensembles in H.
  rewrite -> H.

  assert (In (sigalg ms) (list_to_ensemble l1)).
  apply (tail_in_sigalg ms a); auto.
  apply IHl1 in H0.
  rewrite -> H0.
  auto.

  rewrite -> H.
  apply union_in_sigalg; auto.
Qed.


(** probability measure, mu : E -> [0,1] *)
Record Measure {A : Set} { l : list A } (ms : MS l) :=
  mkMeasure {
    m_func : forall { l' }, In (sigalg ms) (list_to_ensemble l') -> U;
    empty: @m_func nil = 0;
    full: m_func (space_in_sigalg ms) = 1;
    addcount:
      forall E1 E2 pE1 pE2,
        @m_func E1 pE1 + @m_func E2 pE2 = m_func (concat_in_sigalg ms pE1 pE2) 
  }.

(** probability space, PS : {S, mu} *)
Record PS { A : Set } (l : list A) :=
  mkPS {
    ms : MS l;
    mu : Measure ms
  }.

Arguments mkPS [A l].
Arguments ms [A l].
Arguments mu [A l].


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

Lemma map_fst_inverse_list_prod : 
  forall A B (l1:list A) (l2:list B) d,
    NoDup l1
    -> nodup d (map fst (list_prod l1 l2)) = l1.
  intros A B l1 l2 Hnodup Hdecide.
  induction l1; auto.

  simpl.
  assert ((map fst (map (fun y : B => (a, y)) l2 ++ list_prod l1 l2)) = (map fst (map (fun y : B => (a, y)) l2)) ++ (map fst (list_prod l1 l2))) as Hmapdist.
  apply map_app.
  rewrite -> Hmapdist.

  assert (
      forall A l1 l2 (a : A) x d1,
        (List.In x l1 -> ~ List.In a l2)
        -> nodup d1 (l1 ++ l2) = nodup d1 l1 ++ nodup d1 l2
    ).

  intros.
  Admitted.

Lemma map_snd_inverse_list_prod :
  forall A B (l1:list A) (l2:list B) d,
    NoDup l2
    -> nodup d (map snd (list_prod l1 l2)) = l2.
  intros A B l1 l2 Hnodup Hdecide.
  Admitted.


Lemma prod_fst_in_space :
  forall A B l1 (l2 : list B) (ps : @PS A l1) da,
    NoDup l1
    -> In (sigalg (ms ps)) (list_to_ensemble (nodup da (map fst (list_prod l1 l2)))).
Proof.
  intros A B l1 l2 ps Hdecide Hnodupl1.
  assert (nodup Hdecide (map fst (list_prod l1 l2)) = l1).
  apply (map_fst_inverse_list_prod). assumption.
  rewrite -> H.
  apply space_in_sigalg.
Qed.

Lemma prod_snd_in_space :
  forall A B (l1 : list A) l2 (ps : @PS B l2) db,
    NoDup l2
    -> In (sigalg (ms ps)) (list_to_ensemble (nodup db (map snd (list_prod l1 l2)))).
Proof.
  intros A B l1 l2 ps Hdecide Hnodupl1.
  assert (nodup Hdecide (map snd (list_prod l1 l2)) = l2).
  apply (map_snd_inverse_list_prod). assumption.
  rewrite -> H.
  apply space_in_sigalg.
Qed.

Definition dec (A : Set) := forall x y : A, {x = y} + {x <> y}.

Lemma dec_prod:
  forall A B,
    dec A
    -> dec B
    -> dec (prod A B).
Proof.
  unfold dec.
  intros A B Hdeca Hdecb.
  intros x y.
  assert ({(fst x) = (fst y)} + {(fst x) <> (fst y)}) as Hdecas.
  apply (Hdeca (fst x) (fst y)).
  assert ({(snd x) = (snd y)} + {(snd x) <> (snd y)}) as Hdecbs.
  apply (Hdecb (snd x) (snd y)).

  case Hdecas.
  case Hdecbs.
  intros.
  left.
  apply injective_projections; auto.

  intros.
  right.
  unfold not.
  intros.
  assert (x = (fst x, snd x)). apply surjective_pairing.
  assert (y = (fst y, snd y)). apply surjective_pairing.
  rewrite -> H0 in H.
  rewrite -> H1 in H.
  inversion H.
  contradiction.


  case Hdecbs.
  intros.
  intros.
  right.
  unfold not.
  intros.
  assert (x = (fst x, snd x)). apply surjective_pairing.
  assert (y = (fst y, snd y)). apply surjective_pairing.
  rewrite -> H0 in H.
  rewrite -> H1 in H.
  inversion H.
  contradiction.

  intros.
  intros.
  intros.
  right.
  unfold not.
  intros.
  assert (x = (fst x, snd x)). apply surjective_pairing.
  assert (y = (fst y, snd y)). apply surjective_pairing.
  rewrite -> H0 in H.
  rewrite -> H1 in H.
  inversion H.
  contradiction.
Qed.




Lemma nodup_prod :
  forall A B (l1 : list A) (l2 : list B),
    NoDup l1
    -> NoDup l2
    -> NoDup (list_prod l1 l2).
Proof.
  intros A B l1 l2 Hnodup1 Hnodup2.
  induction l1; simpl.
  constructor.
  Admitted.


Definition prod_space {A B : Set} {l1 l2} (da : dec A) (db : dec B) (psa : @PS A l1) (psb : @PS B l2) : @PS (prod A B) (list_prod l1 l2).
  refine (
      let decprod := (dec_prod A B da db) in 
      let l := (list_prod l1 l2) in
      let msab := (@mkMS (prod A B) l _) in
      let mua := m_func (ms psa) (mu psa) in
      let mub := m_func (ms psb) (mu psb) in 
      let measure :=
          fun list inab =>
            let las : In (sigalg (ms psa)) (list_to_ensemble (nodup da (map fst l))) :=
                prod_fst_in_space A B l1 l2 psa da (uniq (ms psa))
            in
            let lbs : In (sigalg (ms psb)) (list_to_ensemble (nodup db (map snd l))) :=
                prod_snd_in_space A B l1 l2 psb db (uniq (ms psb))
            in
            (mua las) * (mub lbs)
      in
      mkPS msab (mkMeasure (prod A B) l msab measure _ _ _)
    ).
  Unshelve.
  Focus 4.
  apply nodup_prod.
  exact (uniq (ms psa)).
  exact (uniq (ms psb)).
  


(** push forward, f : (E -> [0,1]) -> (E' -> [0,1]) *) 
Definition push_forward {A B} {l1 l2} (psa : @PS A l1) (msb : @MS B l2) (mf : MF (ms psa) msb) : @PS B l2.
  refine (mkPS msb _).
  refine (_ (mu psa)).
  intros HmuA.

  assert (
      (forall E1,
        In (sigalg msb) E1
        -> sig (fun E2 =>
                 (forall x, In E1 ((mf_func (ms psa) msb mf) x) <-> In E2 x) /\
                 In (sigalg (ms psa)) E2))
      ->

      (forall E1,
        In (sigalg msb) E1
        -> sig (fun E2 => In (sigalg (ms psa)) E2 /\
                      (Same_set E1 (Empty_set B) -> Same_set E2 (Empty_set A)) /\
                      (Same_set E1 (space msb) -> Same_set E2 (space (ms psa)))))


    ) as convertpreimg.

  intros Hpreimg E1 Hinb.
  apply (Hpreimg E1) in Hinb.
  elim Hinb.
  intros E2 Hprefacts.
  destruct Hprefacts as [Hsame Hsiga].
  exists E2.
  split.
  assumption.
  split.
  intro Hempte1.
  apply Extensionality_Ensembles in Hempte1.
  rewrite -> Hempte1 in Hsame.

  unfold Same_set.
  unfold Included.

  split.

  Focus 2.

  intros.
  exfalso.
  apply (empty_bot A) in H; assumption.

  intros.
  destruct (Hsame x).
  apply H1 in H.
  exfalso.
  apply (empty_bot B (mf_func (ms psa) msb mf x)) in H.
  assumption.

  admit.



  assert (
      forall E1,
        In (sigalg msb) E1
        -> sig (fun E2 => In (sigalg (ms psa)) E2 /\
                       (Same_set E1 (Empty_set B) -> Same_set E2 (Empty_set A)) /\
                       (Same_set E1 (space msb) -> Same_set E2 (space (ms psa))))
    ).

  intros.
  apply ((convertpreimg (preimage (ms psa) msb mf) E1)). auto.
  Admitted.
  (* assert (forall E, In (Ensemble B) (sigalg B msb) E -> In (Ensemble B) (sigalg B msb) E) as bfunc. *)

  (* assert (forall E, In (Ensemble B) (sigalg B msb) E -> U) as bfunc. *)
  (* intros E Heinsig. *)
  (* assert (sig (fun E1 => *)
  (*                (forall x, In B E ((mf_func (ms A psa) msb mf) x) <-> In A E1 x) /\ *)
  (*                In (Ensemble A) (sigalg A (ms A psa)) E1)) as Hpre. *)
  (* apply ((preimage (ms A psa) msb mf) E). auto. *)
  (* destruct Hpre as [E1 Hfacts]. *)
  (* apply ((@m_func A (ms A psa) HmuA) E1). *)
  (* destruct Hfacts. *)
  (* assumption. *)

  (* refine (mkMeasure B msb bfunc _ _ _). *)
(* Defined. *)

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
  

Fixpoint mkdist {A : Set} (s : Space A) (init_terms : list term) : PS A := mkPS A s.

Record prog :=
  mkProg {
    init : list term;
    init_dist : mkdist 
    statements : list term
  }.

Fixpoint init_ps (p : prog) : PS (:= 
Fixpoint eval : prog -> PS := 