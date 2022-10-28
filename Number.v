(* 4 Natural Numbers Theory *)

Require Export Ensemble.

(* 4.1 Natural number *)
Definition Suc n := n ⋃ [n].
Notation "n ⁺" := (Suc n) (at level 8).

Fact sucEns : ∀ n, Ensemble n → Ensemble n⁺.
Proof. intros. unfold Suc; ens. Qed.

Fact suc_has_n : ∀ n, Ensemble n → n ∈ n⁺.
Proof. intros. unfold Suc; ens. Qed.

Fact suc_neq_0 : ∀ n, Ensemble n → n⁺ ≠ ∅.
Proof.
  intros n Hn H. apply EmptyNE in H; auto.
  exists n. apply suc_has_n; auto.
Qed.
Hint Resolve sucEns suc_has_n suc_neq_0 : Ens_hint.

Definition inductive A := ∅ ∈ A ∧ (∀ a, a ∈ A → a⁺ ∈ A).
Definition is_nat n := ∀ A, inductive A → n ∈ A.
Definition ω := \{λ n, is_nat n\}.

Fact ωEns : Ensemble ω.
Proof.
  destruct InfAx as [A [He Hp]]. assert (inductive A); auto.
  assert (ω ⊂ A). intros n Hn; AppC Hn. eens.
Qed.

Fact ω_has_0 : ∅ ∈ ω.
Proof. AppCG; ens. intros n []; auto. Qed.

Fact ω_has_suc : ∀ a, a ∈ ω → a⁺ ∈ ω.
Proof.
  intros. AssE a. AppC H. AppCG; ens. intros A Ha; apply Ha; auto.
Qed.
Hint Resolve ωEns ω_has_0 ω_has_suc : Ens_hint.

Fact ω_inductive : inductive ω.
Proof. split; ens. Qed.
Ltac ind := apply ω_inductive; eauto.

Fact ω_ind : ∀ A, A ⊂ ω → inductive A → A = ω.
Proof. intros. AppE; auto. AppC H1. Qed.

Ltac ω_induction n := pattern n;
  match goal with H : n ∈ ω |- ?G _ => let N := fresh "N" in
  set \{λ n, n ∈ ω ∧ G n\} as N; simpl in N; cut (N = ω);
  [intros ?Heq; rewrite <- Heq in H; AppC H; andH; auto|apply ω_ind;
    [intros ?t ?Ht; AppC Ht; andH; auto|split;
      [AppCG; [apply EmptyEns|]; split; [apply ω_has_0|]|]];
      [|intros ?k ?Hk; AppC Hk; destruct Hk as [?Hk ?IH]; AssE k;
      AppCG; [apply sucEns; Ens|]; split; [ind|]]]; clear N; simpl end.

Definition trans A := ∀ x a, x ∈ a → a ∈ A → x ∈ A.

Theorem nat_trans : ∀ n, n ∈ ω → trans n.
Proof.
  intros. ω_induction n. intros x a Hx Ha; exfalso0.
  unfold trans, Suc in *; intros. unH. eens. sing H2; ens.
Qed.

Fixpoint iter (n : nat) {X : Type} (f : X → X) (x : X) :=
  match n with
  | O => x
  | S n' => f (iter n' f x)
  end.

Coercion Embed n := iter n Suc ∅.

Fact pred : ∀ n, Embed n =
  match n with | O => ∅ | S n' => (Embed n')⁺ end.
Proof. intros. destruct n; auto. Qed.

Fact embed_ran : ∀ n : nat, n ∈ ω.
Proof. induction n; ens. ind. Qed.

Fact natEns : ∀ n : nat, Ensemble n.
Proof. intros. pose proof (embed_ran n). Ens. Qed.
Hint Immediate embed_ran natEns : Ens_hint.

Delimit Scope Nat_scope with n.
Open Scope Nat_scope.

Notation "a ≤ b" := (a ∈ b ∨ a = b) (at level 70) : Nat_scope.

Fact leq_iff_lt_suc : ∀ m n, m ∈ ω → n ∈ ω → m ≤ n ↔ m ∈ n⁺.
Proof.
  intros * Hm Hn. AssE n. unfold Suc. split; intros.
  destruct H0; subst; ens. unH; auto; sing H0.
Qed.

Close Scope Nat_scope.

Fact suc_has_0 : ∀ n, n ∈ ω → 0 ∈ n⁺.
Proof. intros. ω_induction n. ens. apply leq_iff_lt_suc; ens. Qed.
Hint Resolve suc_has_0 : Ens_hint.

Fact suc_preserve_lt : ∀ m n, m ∈ ω → n ∈ ω → m ∈ n ↔ m⁺ ∈ n⁺.
Proof.
  intros * Hm Hn. split; intros.
  - generalize dependent m. ω_induction n; intros. exfalso0.
    apply leq_iff_lt_suc in H0 as []; auto.
    AssE m; AppCG; ens. subst; AssE k; ens.
  - AssE m. assert (m ∈ m⁺); ens. apply leq_iff_lt_suc in H as [];
    [eapply nat_trans|subst| |]; ens.
Qed.

Fact lt_irrefl : ∀ n, n ∈ ω → n ∉ n.
Proof.
  intros. ω_induction n; intro. exfalso0.
  elim IH; apply suc_preserve_lt; auto.
Qed.

(* 4.2 Finite *)
Definition Equinumerous A B := ∃ F, bijection F A B.
Notation "A ≈ B" := (Equinumerous A B) (at level 70).
Notation "A ≉ B" := (~Equinumerous A B) (at level 70).

Fact eqnumRefl : ∀ A, A ≈ A.
Proof. intros. exists ∆(A). apply ident_bijective. Qed.

Fact eqnumSymm : ∀ A B, A ≈ B → B ≈ A.
Proof. intros * [f H]. exists (f⁻¹). apply inv_bijection; auto. Qed.

Fact eqnumTran   : ∀ A B C, A ≈ B → B ≈ C → A ≈ C.
Proof.
  intros * [f Hf] [g Hg]. exists (g∘f). eapply compo_bijection; eauto.
Qed.

Fact empty_eqnum : ∀ A, A ≈ ∅ ↔ A = ∅.
Proof.
  split; intros; [|subst; apply eqnumRefl].
  destruct H as [f Hf]. eapply empty_bijective; eauto.
Qed.

Fact eqnum_suc_ne : ∀ A, ∀ n, n ∈ ω → A ≈ n⁺ → ⦿A.
Proof.
  intros * Hn Ha. apply EmptyNE. DC (A = ∅); auto. subst.
  apply eqnumSymm, empty_eqnum in Ha. eapply suc_neq_0 in Ha; Ens.
Qed.

Fact img_eqnum : ∀ F A, injective F → A ⊂ dom(F) → A ≈ F\(A\).
Proof.
  intros * Hi Hsub. exists (F↾A). split. apply restr_injective; auto.
  andG. apply restr_dom; auto. apply Hi. AppE. ran H. AppC' H; andH.
  eens. AppCG. Ens. image H. exists x0. AppCG'; Ens.
Qed.

Fact psubω_eqnum : ∀ n, n ∈ ω → ∀ C, C ⊊ n → ∃ m, m ∈ ω ∧ m ∈ n ∧ C ≈ m.
Proof.
  intros n Hn. ω_induction n; intros C [Hsub Hnq].
  - exfalso. apply Hnq. AppE. auto. exfalso0.
  - DC (C = k). exists k. andG; ens. subst. apply eqnumRefl.
    DC (k ∈ C); revgoals.
    + assert (Hps: C ⊊ k).
      { split; auto. intros x Hx. apply Hsub in Hx as Hxk.
        AppC Hxk; orH; auto. exfalso; sing H2. }
      apply IH in Hps as [m [Hmw [Hmk Hqn]]].
      exists m. andG; auto. unfold Suc. unG; auto.
    + assert (HC : C = (C ∩ k) ⋃ [k]).
      { AppE; [|unH; inH; auto; sing H2].
        DC (x = k). apply UnionI'. subst. ens. unG. inG; auto.
        apply Hsub in H2. AppC H2; orH; auto. exfalso; sing H2. }
      assert (Hps: C ∩ k ⊊ k).
      { split. intros x Hx; inH; andH; auto. intro. assert (k ⊂ C).
        rewrite <- H2; intros x Hx; inH; tauto. apply Hnq. AppE.
        apply Hsub in H4; auto. AppC H4; orH; auto; sing H4. }
      apply IH in Hps as [m [Hmw [Hmk [f Hf]]]]. exists (m⁺). andG.
      ens. apply suc_preserve_lt in Hmk; auto. exists (f ⋃ [[k,m]]).
      rewrite HC. apply bijection_add_point; Ens; apply DisjointI;
      intros [x []]; sing H3;[inH| |Ens];
      eapply lt_irrefl; revgoals; eauto.
Qed.

Fact eqnum_smpoint_eqnum : ∀ A B a b, Ensemble a → Ensemble b →
  A ⋃ [a] ≈ B ⋃ [b] → Disjoint A ([a]) → Disjoint B ([b]) → A ≈ B.
Proof.
  intros * Hae Hbe [f Hf] Hdja Hdjb. pose proof Hf as Hf'.
  destruct Hf' as [Hi [Hd Hr]]. set (FuncSwapValue f a f⁻¹[b]) as g.
  assert (Ha: a ∈ A ⋃ [a]); ens. assert (Hbr: b ∈ ran(f)). rewrite Hr;ens.
  assert (Hb : f⁻¹[b] ∈ A ⋃ [a]).
  { destruct Hi as [Hff Hs]. rewrite <- Hd, <- ranInv. eapply ap_ran.
    split; andG; ens. apply singrootE; auto. rewrite domInv; auto. }
  apply (bijection_swap_value _ _ _ _ _ Ha Hb) in Hf as Hg.
  assert (Hga : g[a] = b).
  { apply func_ap. apply Hg. AppCG'; andG; ens. rewrite Hd; AppCG';
    andG; ens. destruct (classicT (a = a)); [|elim n; auto].
    rewrite inv_ran_reduction; auto. } clear Hf Hi Hd Hr Ha Hbr Hb.
  destruct Hg as [Hi [Hd Hr]]. assert (Hi' := Hi). destruct Hi as [Hg Hs].
  exists (g↾A). split; [|split]. apply restr_injective; auto.
  apply restr_dom; auto. intros x Hx; subst g; rewrite Hd; ens.
  apply ExtAx; intros y; split; intros Hy.
  - ran Hy; restr H. apply ranI in H as Hy. subst g; rewrite Hr in Hy.
    unH; auto. sing H1. apply func_ap in H; auto. rewrite <- H in Hga at 2.
    assert (a = x). eapply injectiveE; eauto; rewrite Hd; ens.
    subst a. exfalso. eapply DisjointE; [apply Hdja|..]; eens.
  - assert (y ∈ ran(g)). subst g; rewrite Hr; ens. ran H.
    apply domI in H as Hx. subst g. rewrite Hd in Hx. unH. eapply ranI;
    apply RestrI; eauto. sing H0; apply func_ap in H; auto. rewrite <- H,
      Hga in Hy. exfalso. eapply DisjointE; [apply Hdjb|..]; eens.
Qed.

Definition Finite X := ∃ n, n ∈ ω ∧ X ≈ n.
Definition inFinite X := ~Finite X.

Fact nat_finite : ∀ n, n ∈ ω → Finite n.
Proof. intros n Hn. exists n. andG; auto. apply eqnumRefl. Qed.

Fact sin_finite : ∀ a, Ensemble a → Finite ([a]).
Proof.
  intros. exists 1. andG; ens. exists ([[a,∅]]). rewrite pred; unfold Suc.
  rewrite CommuU, EmptyU. apply single_ord_bijective; ens.
Qed.

Fact fin_sub_fin : ∀ A B, A ⊂ B → Finite B → Finite A.
Proof.
  intros * Hs [n [Hn [f [Hi [Hd Hr]]]]]. subst B.
  apply img_eqnum in Hs; auto. pose proof (RanSub f A).
  rewrite Hr in H. DC (f\(A\) = n).
  - exists n. rewrite <- H0 at 2; auto.
  - assert (f\(A\) ⊊ n). split; auto.
    apply psubω_eqnum in H1 as [m [Hm [Hmn He]]]; auto.
    exists m. andG; auto. eapply eqnumTran; eauto.
Qed.

Fact fin_addone_fin : ∀ A a, Ensemble a → Finite A → Finite (A ⋃ [a]).
Proof.
  intros * Hae Hf. DC (Disjoint A ([a])).
  - destruct Hf as [m [Hm Ha]]. exists m⁺. andG; ens.
    destruct Ha as [f Hf]. exists (f ⋃ [[a,m]]). 
    apply bijection_add_point; Ens. AppE; [|exfalso0].
    inH. sing H1; Ens. apply RegAxP in H0; elim H0.
  - apply EmptyNE in H as [b Hb]. inH; sing H0.
    replace (A ⋃ [a]) with A; auto. AppE; ens. unH; auto. sing H0.
Qed.

Fact fin_smpoint_fin : ∀ A a, Ensemble a →
  ∀ n, n ∈ ω → (A - [a]) ⋃ [a] ≈ n⁺ → A - [a] ≈ n.
Proof.
  intros * Hae * Hn Hqn. AssE n. eapply eqnum_smpoint_eqnum;
  [apply Hae|apply H|apply Hqn|..]; apply DisjointI; intros [x []].
  smH; auto. sing H1; Ens; eapply RegAxP; eauto.
Qed.

Fact un_finite : ∀ A B, Finite A → Finite B → Finite (A ⋃ B).
Proof.
  intros * Hfa Hfb. rewrite <- UnionSetmin. assert (Hfc: Finite (B - A)).
  { apply (fin_sub_fin _ B); auto. apply SetminSub; ens. }
  assert (Hdj : Disjoint A (B - A)).
  { apply DisjointI. intros [x []]; smH; auto. } remember (B - A) as C.
  clear HeqC Hfb B. destruct Hfc as [n [Hn Hc]]. generalize dependent C.
  generalize dependent A. ω_induction n; intros A Hfa C Hc Hdj.
  apply empty_eqnum in Hc; subst C; rewrite EmptyU; auto.
  pose proof Hc. apply eqnum_suc_ne in Hc as [c Hc]; auto. AssE c.
  apply split_one_elem in Hc. rewrite Hc in H0.
  rewrite CommuU in Hc. rewrite Hc, <- AssocU. apply IH.
  apply fin_addone_fin; auto. apply fin_smpoint_fin; auto.
  apply DisjointI; intros [x []]. smH; unH; auto. eapply DisjointE; eauto.
Qed.