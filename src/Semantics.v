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

Lemma empty_in_sigalg :
  forall A l ms, In (@sigalg A l ms) (Empty_set A).
Proof.
  intros.
  apply Definition_of_Power_set.
  unfold Included.
  intros.
  unfold In in H.
  contradiction.
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
  unfold Same_set.
  intros.
  unfold Included.
  split.
  unfold In.
  intros.
  inversion H.
  apply empty_bot in H0.
  exfalso.
  auto.
  assumption.
  unfold In.
  intros.
  apply Union_intror.
  assumption.
Qed.

Lemma union_add_left_commute :
  forall A E1 E2 a, Same_set (Union (Add A E1 a) E2) (Add A (Union E1 E2) a).
Proof.
  intros.
  unfold Same_set.
  unfold Included.
  unfold In.
  split.
  - intros.
    unfold Add.
    unfold Add in H.
    inversion H.
    unfold In in H0.
    inversion H0.
    apply Union_introl.
    unfold In.
    apply Union_introl.
    assumption.
    apply Union_intror.
    assumption.
    apply Union_introl.
    apply Union_intror.
    assumption.
  - intros.
    unfold Add.
    unfold Add in H.
    inversion H.
    unfold In in H0.
    inversion H0.
    apply Union_introl.
    unfold In.
    apply Union_introl.
    assumption.
    apply Union_intror.
    assumption.
    apply Union_introl.
    apply Union_intror.
    assumption.
Qed.

Lemma subset_empty : forall A E, Included (Empty_set A) E.
Proof.
  intros.
  unfold Included.
  intros.
  apply empty_bot in H.
  exfalso.
  auto.
Qed.

Lemma tail_in_sigalg :
  forall { A : Set } { l l1 : list A } ms a,
    In (@sigalg A l ms) (list_to_ensemble (a::l1))
    -> In (sigalg ms) (list_to_ensemble l1).
Proof.
  unfold sigalg.
  intros.
  simpl in H.
  inversion H.
  apply Definition_of_Power_set.
  Check Inclusion_is_transitive.
  apply (Inclusion_is_transitive A (list_to_ensemble l1) (Add A (list_to_ensemble l1) a)); auto.
  unfold Add.
  unfold Included.
  intros.
  apply Union_introl; auto.
Qed.

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
    (* TODO the following is only supposed to be true in the case of disjoint l1 l2 *)
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

Lemma nodup_disj_dist :
  forall A l1 l2 d1,
    (forall a:A, List.In a l1 -> ~ List.In a l2)
    -> nodup d1 (l1 ++ l2) = nodup d1 l1 ++ nodup d1 l2.
Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.

  simpl.
  
  case (in_dec d1 a l1).
  intros.
  assert (List.In a (l1 ++ l2)).
  apply in_or_app. left. auto.
  simpl.
  Check (in_dec d1 a (l1 ++ l2)).
  case (in_dec d1 a (l1 ++ l2)).
  intros.
  apply IHl1.
  intros.
  apply H.
  apply in_cons. auto.
  intros.
  contradiction.
  intros.
  case (in_dec d1 a (l1 ++ l2)).
  Focus 2.
  intros.
  assert ((a :: nodup d1 l1) ++ nodup d1 l2 =  (a :: (nodup d1 l1 ++ nodup d1 l2))).
  apply app_comm_cons; assumption.
  rewrite -> H0.
  assert (nodup d1 (l1 ++ l2) = nodup d1 l1 ++ nodup d1 l2).
  apply IHl1.
  intros.
  apply H.
  apply in_cons. auto.
  rewrite -> H1.
  reflexivity.
  intros.

  apply in_app_or in i.
  case i.
  intros. contradiction.
  intros.
  assert (~List.In a l2).
  apply H.
  apply in_eq.
  contradiction.
Qed.

Lemma in_map_fst_singleton_eq :
  forall A B a1 a2 (l : list B),
    List.In (a1 : A) (map fst (map (fun y : B => (a2, y)) l))
    -> a1 = a2.
Proof.
  intros.
  induction l.
  simpl in H. contradiction.
  simpl in H.
  case H; auto.
Qed.

Lemma not_in_not_in_fst_prod:
  forall A B (l1 : list A) (l2 : list B) a,
    ~ List.In a l1 ->
    ~ List.In a (map fst (list_prod l1 l2)).
Proof.
  intros.
  induction l1.
  simpl. auto.
  simpl.

  assert (map fst (map (fun y : B => (a0, y)) l2 ++ list_prod l1 l2) =
          map fst (map (fun y : B => (a0, y)) l2) ++ (map fst (list_prod l1 l2))).
  apply map_app.
  rewrite -> H0.
  unfold not.
  intros.

  apply in_app_or in H1.
  apply not_in_cons in H.
  case H1.
  intros.
  assert (a = a0).
  destruct H; auto.
  apply (in_map_fst_singleton_eq A B a a0 l2); assumption.
  destruct H; auto.
  intro.
  destruct H.
  apply IHl1 in H3.
  contradiction.
Qed.

Lemma map_fst_in_list_not_empty :
  forall A B (a : A) l, List.In a (map fst (map (fun y : B => (a, y)) l)) -> l <> nil.
Proof.
  intros.
  induction l.
  contradiction.
  discriminate.
Qed.

Lemma map_fst_no_in_list_empty :
  forall A B (a : A) l, (~ List.In a (map fst (map (fun y : B => (a, y)) l))) -> l = nil.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl in H.
  unfold not in H.
  exfalso.
  apply H.
  left.
  auto.
Qed.

Lemma nodup_singleton_prod_singleton :
  forall A B (a : A) (l : list B) d,
    l <> nil 
    -> nodup d (map fst (map (fun y : B => (a, y)) l)) = a::nil.
Proof.
  intros.
  induction l.
  contradiction.
  simpl.
  case (in_dec d a (map fst (map (fun y : B => (a, y)) l))).
  intros.

  assert (List.In a (map fst (map (fun y : B => (a, y)) l)) -> l <> nil).
  apply map_fst_in_list_not_empty.
  apply H0 in i.
  apply IHl in i.
  assumption.

  intros.

  assert (~List.In a (map fst (map (fun y : B => (a, y)) l)) -> l = nil).
  apply map_fst_no_in_list_empty.
  apply H0 in n.
  rewrite -> n.
  simpl.
  reflexivity.
Qed.

Lemma map_fst_inverse_list_prod : 
  forall A B (l1:list A) (l2:list B) d,
    l2 <> nil
    -> NoDup l1
    -> nodup d (map fst (list_prod l1 l2)) = l1.
  intros A B l1 l2 Hdecide Hl2notempty Hnodup.
  induction l1; auto.

  simpl.
  assert ((map fst (map (fun y : B => (a, y)) l2 ++ list_prod l1 l2)) =
          (map fst (map (fun y : B => (a, y)) l2)) ++ (map fst (list_prod l1 l2))) as Hmapdist.
  apply map_app.
  rewrite -> Hmapdist.

  
  assert (nodup Hdecide (map fst (map (fun y : B => (a, y)) l2) ++ map fst (list_prod l1 l2)) =
          nodup Hdecide (map fst (map (fun y : B => (a, y)) l2)) ++ nodup Hdecide (map fst (list_prod l1 l2))).

  apply nodup_disj_dist.
  intros.

  assert (a0 = a).
  apply (in_map_fst_singleton_eq A B a0 a l2); assumption.

  rewrite -> H0 in H.
  inversion Hnodup.
  rewrite -> H0.

  assert (forall A B (l1 : list A) (l2 : list B) a, ~ List.In a l1 ->  ~ List.In a (map fst (list_prod l1 l2))).
  apply not_in_not_in_fst_prod.

  apply H5. assumption.
  rewrite -> H.

  assert (nodup Hdecide (map fst (map (fun y : B => (a, y)) l2)) = a::nil) as Hfactor.
  apply nodup_singleton_prod_singleton.
  assumption.

  rewrite -> Hfactor.

  assert (NoDup l1).

  assert (NoDup (a::l1) -> ~ List.In a l1 /\ NoDup l1).
  apply NoDup_cons_iff.
  apply H0 in Hnodup.
  destruct Hnodup. auto.

  apply IHl1 in H0.
  rewrite -> H0.
  auto.
Qed.

Lemma map_snd_inverse_list_prod :
  forall A B (l1:list A) (l2:list B) d,
    NoDup l2
    -> nodup d (map snd (list_prod l1 l2)) = l2.
  intros A B l1 l2 Hnodup Hdecide.
  Admitted.

Lemma empty_pair_fst_empty_nodup :
  forall A B (l : list A) d, nodup d (map fst (list_prod l (nil : list B))) = nil.
Proof.
  intros.
  induction l.
  simpl.
  auto.

  simpl.
  rewrite -> IHl.
  auto.
Qed.

Lemma prod_fst_in_space :
  forall A B l1 (l2 : list B) (ps : @PS A l1) da,
    NoDup l1
    -> In (sigalg (ms ps)) (list_to_ensemble (nodup da (map fst (list_prod l1 l2)))).
Proof.
  intros A B l1 l2 ps Hdecide Hnodupl1.
  induction l2.
  assert ((nodup Hdecide (map fst (list_prod l1 (nil : list B)))) = nil).
  apply empty_pair_fst_empty_nodup.
  rewrite -> H.
  simpl.
  apply empty_in_sigalg.

  assert (nodup Hdecide (map fst (list_prod l1 (a::l2))) = l1).
  apply (map_fst_inverse_list_prod).
  discriminate.
  assumption.
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

Require Import Coq.Bool.Bool.
Require Import Uprop.

Definition bool_space := false::true::nil.

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

(** TODO the content of this proof is suspect since it doesn't rely on the disjointness
    of the lists
*)
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
  apply Uinv_opp_left.
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

Definition bool_ps (u : U) :=
  mkPS (mkMS (NoDup_nodup bool_dec (nodup bool_dec bool_space))) (bool_measure u).

Inductive term : Type :=
| term_and : nat -> nat -> nat -> term.

Record prog :=
  mkProg {
    init : list init_term;
    statements : list term
    }.

Require Import FSets.FMapList.
Require Import Structures.OrderedTypeEx.
Require Import OrderedType.
Require Import Decidable.

Module Import VarMap := FMapList.Make Nat_as_OT.

Definition spaces := VarMap.t (@PS bool bool_space).

Notation "k |-> v" := (pair k v) (at level 60).

Definition update_space (p: nat * (@PS bool bool_space)) (m: spaces) :=
  VarMap.add (fst p) (snd p) m.
Notation "[ ]init" := (VarMap.empty (@PS bool bool_space)).
Notation "[ p1 , .. , pn ]init" :=
  (update_space p1 .. (update_space pn (VarMap.empty (@PS bool bool_space))) .. ).

Fixpoint init_prog ( l : list init_term ) : spaces :=
  match l with
  | nil => []init
  | (init_flip n u) :: ini => update_space (n, bool_ps u) (init_prog ini)
  (* TODO handle uniform distr *)                                        
  | _ => []init
  end.

Definition compose_mf (p : prog) (s : spaces) : spaces.
  refine (
      match (statements p) with
      | term_and nvar n1 n2 :: nil =>
        let optspacen1 := VarMap.find n1 s in
        let optspacen2 := VarMap.find n2 s in
        match (optspacen1, optspacen2) with
        | (Some spacen1, Some spacen2) => 
          if eq_nat_dec n1 n2 then
            update_space (nvar, spacen1) s
          else
            let truen1 := (m_func (ms spacen1) (mu spacen1)) _ in
            let truen2 := (m_func (ms spacen2) (mu spacen2)) _ in
            let newspace := bool_ps (truen1 * truen2) in
            update_space (nvar, newspace) s
        | _ => s
        end
      | _ => s
      end
    ).
  Unshelve.
  Focus 2.
  exact (true::nil).
  Focus 3.
  exact (true::nil).
  apply (tail_in_sigalg bool_ms false).
  unfold space.
  assert (list_to_ensemble (nodup bool_dec bool_space) = list_to_ensemble (false::true::nil)).
  simpl. auto.
  rewrite <- H.
  apply space_in_sigalg.
  apply (tail_in_sigalg bool_ms false).
  unfold space.
  assert (list_to_ensemble (nodup bool_dec bool_space) = list_to_ensemble (false::true::nil)).
  simpl. auto.
  rewrite <- H.
  apply space_in_sigalg.
Qed.

Definition eval (p : prog) : spaces := compose_mf p (init_prog (init p)).
