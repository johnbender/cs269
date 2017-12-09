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
Arguments Disjoint [U].

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
    In (@sigalg A l ms) E -> Included E (space ms).
Proof.
  intros A l ms E Hin.
  unfold sigalg in Hin.
  inversion Hin.
  assumption.
Qed.

Lemma subset_sigalg_in_space :
  forall (A : Set) l ms E,
    Included E (space ms) -> In (@sigalg A l ms) E.
Proof.
  intros A l ms E Hincl.
  apply Definition_of_Power_set; auto.
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

Lemma subset_empty : forall A E, Included (Empty_set A) E.
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
    empty: @m_func nil == 0;
    full: m_func (space_in_sigalg ms) == 1;
    addcount:
      forall l1 l2 pl1 pl2,
        @m_func l1 pl1 + @m_func l2 pl2 == m_func (concat_in_sigalg ms pl1 pl2) 
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

Lemma prod_fst_same_space :
  forall (A : Set) B (l1 : list A) (l2 : list B) (ms : MS l1) da,
    NoDup l1
    -> Same_set (list_to_ensemble (nodup da (map fst (list_prod l1 l2)))) (space ms).
Proof.
  intros A B l1 l2 ps Hdecide Hnodupl1.
  assert (nodup Hdecide (map fst (list_prod l1 l2)) = l1).
  apply (map_fst_inverse_list_prod). assumption.
  rewrite -> H.
  unfold space.
  unfold Same_set.
  unfold Included.
  auto.
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


Lemma prod_snd_same_space :
  forall A (B : Set) (l1 : list A) (l2 : list B) (ms : MS l2) db,
    NoDup l2
    -> Same_set (list_to_ensemble (nodup db (map snd (list_prod l1 l2)))) (space ms) .
Proof.
  intros A B l1 l2 ps Hdecide Hnodupl1.
  assert (nodup Hdecide (map snd (list_prod l1 l2)) = l2).
  apply (map_snd_inverse_list_prod). assumption.
  rewrite -> H.
  unfold space.
  unfold Same_set.
  unfold Included.
  auto.
Qed.

Lemma prod_subset_fst_subset : 
      forall { A B : Set} l la lb msab da,
        In (@sigalg (prod A B) (list_prod la lb) msab) (list_to_ensemble l)
        -> Included (list_to_ensemble (nodup da (map fst l)))
                   (list_to_ensemble (nodup da (map fst (list_prod la lb)))).
Proof.
  intros A B l la lb msab da Hinspace.
  induction l.
  simpl.
  apply subset_empty.
Admitted.


Lemma in_prod_fst_in_space :
  forall { A B : Set} l la lb msab msa da,
    In (@sigalg (prod A B) (list_prod la lb) msab) (list_to_ensemble l)
    ->  In (@sigalg A la msa) (list_to_ensemble (nodup da (map fst l))).
Proof.
  intros A B l la lb msab msa Hda Hinab.
  apply elem_sigalg_subset_space in Hinab.
  unfold space in Hinab.
  assert (Same_set (list_to_ensemble (nodup Hda (map fst (list_prod la lb)))) (space msa)).
  Check prod_fst_in_space.
  apply (prod_fst_same_space A B la lb msa).
  exact (uniq msa).
  apply Extensionality_Ensembles in H.

  assert (Included (list_to_ensemble (nodup Hda (map fst l))) (list_to_ensemble (nodup Hda (map fst (list_prod la lb))))).
  apply (prod_subset_fst_subset l la lb msab Hda).
  apply subset_sigalg_in_space.
  assumption.

  assert (Included (list_to_ensemble (nodup Hda (map fst l))) (list_to_ensemble la)).
  apply (elem_sigalg_subset_space A la msa).
  rewrite -> H in H0.
  apply Definition_of_Power_set.
  assumption.
  rewrite -> H in H0.
  apply Definition_of_Power_set.
  assumption.
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
      let mua := @m_func A l1 (ms psa) (mu psa) in
      let mub := @m_func B l2 (ms psb) (mu psb) in 
      let measure :=
          fun l' inab =>
            let fstlist := nodup da (map fst l') in
            let las : In (sigalg (ms psa)) (list_to_ensemble fstlist) :=
                _ 
                (* prod_fst_in_space A B l1 l2 psa da (uniq (ms psa)) *)
            in
            let sndlist := nodup db (map snd l') in
            let lbs : In (sigalg (ms psb)) (list_to_ensemble sndlist) :=
                _ 
                (* prod_snd_in_space A B l1 l2 psb db (uniq (ms psb)) *)
            in
            (mua fstlist las) * (mub sndlist lbs)
      in
      mkPS msab (mkMeasure (prod A B) l msab measure _ _ _)
    ).
  Unshelve.
  Focus 4.
  apply nodup_prod.
  exact (uniq (ms psa)).
  exact (uniq (ms psb)).
  Focus 4.
  Check in_prod_fst_in_space.
  apply (in_prod_fst_in_space l' l1 l2 msab (ms psa) da); assumption.
  
  (** the ensemble (fst l) subset of ensemble l1 (1, admitted)
      the subset of the space is in msab (assumption inab)
        then ensemble l' is a subset of ensemble l
        then ensemble (fst l')  is a subset of ensemble (fst l) (by list_prod l1 l2)
        then by 1 + trans, ensemble (fst l) is subset of ensemble l1
        then since ensemble l1 is the space of msa we're done
   *)

  Admitted.

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
  

Inductive init_term : Type :=
(** x <- flip U *)
| init_flip : nat -> U -> init_term
(** x <- unif n1 n2 *)
| init_unif : nat -> nat -> nat -> init_term.

Inductive term : Type :=
| term_var : nat -> term
| term_lit : nat -> term
| term_plus : term -> term -> term.


Record prog :=
  mkProg {
    init : list init_term;
    statements : list term
  }.


Require Import Coq.Bool.Bool.
Require Import Uprop.

Definition bool_space := true::false::nil.

Fixpoint bool_measure_func (u : U) (l : list bool) : U :=
  match l with
  | nil => 0
  | false::l' => [1-]u + bool_measure_func u l'
  | true::l' => u + bool_measure_func u l'
  end.

Definition bool_ms : MS bool_space := 
  mkMS (NoDup_nodup bool_dec (nodup bool_dec bool_space)).

Check mkPS.
Check mkMeasure.

Definition bool_measure (u : U) : Measure bool_ms.
  intros.
  refine (
      let measure := fun list Plistinspace => bool_measure_func u list in
      mkMeasure bool bool_space bool_ms measure _ _ _
    ).
  unfold measure.
  unfold bool_measure_func.
  auto.
  unfold bool_space.
  unfold measure.
  simpl.
  Usimpl.
  apply Uinv_opp_right.
  intros.
  induction l1.
  unfold measure.
  unfold bool_measure_func.
  simpl.
  Usimpl.
  reflexivity.
  simpl.
  unfold measure.
  case a.
  - simpl.
    unfold measure in IHl1.
    assert ((u + (bool_measure_func u l1 + bool_measure_func u l2)) == (u + bool_measure_func u l1 + bool_measure_func u l2)).
    apply Uplus_assoc.
    rewrite <- H.
    apply Uplus_eq_compat_right.
    assert (In (sigalg bool_ms) (list_to_ensemble l1)).
    apply (tail_in_sigalg bool_ms a); assumption.
    apply (IHl1 H0).
  - simpl.
    unfold measure in IHl1.
    assert (([1-]u + (bool_measure_func u l1 + bool_measure_func u l2)) == ([1-]u + bool_measure_func u l1 + bool_measure_func u l2)).
    apply Uplus_assoc.
    rewrite <- H.
    apply Uplus_eq_compat_right.
    assert (In (sigalg bool_ms) (list_to_ensemble l1)).
    apply (tail_in_sigalg bool_ms a); assumption.
    apply (IHl1 H0).
Qed.

Check mkMeasure.

Fixpoint init_prog (i : list init_term) : (@PS bool bool_space) :=
  match i with
  | (init_flip n u) :: nil => 
    let measure := bool_measure u in
    mkPS (mkMS (NoDup_nodup bool_dec (nodup bool_dec bool_space))) measure
  | _ =>
    let measure := bool_measure 0 in
    mkPS (mkMS (NoDup_nodup bool_dec (nodup bool_dec bool_space))) measure
  end.

Fixpoint eval : prog -> PS :=

                                      