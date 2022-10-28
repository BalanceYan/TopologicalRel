(* 5 Topological Concepts *)

Require Export Number.

(* 5.1 Topological Spaces *)
Definition Topology X cT := cT ⊂ cP(X) ∧
  X ∈ cT ∧ ∅ ∈ cT ∧ (∀ A B, A ∈ cT → B ∈ cT → A ∩ B ∈ cT) ∧
  (∀ cT1, cT1 ⊂ cT → ∪cT1 ∈ cT).

Fact TopologyP : ∀ X cT, Ensemble X → Topology X cT →
  ∀ cT1, ⦿ cT1 → Finite cT1 → cT1 ⊂ cT → ⋂cT1 ∈ cT.
Proof.
  intros * Hxe Htp * Hne [n [Hn He]] Hs. apply eqnumSymm in He as [f].
  apply bijection_is_func in H; andH. apply MapMapR1 in H.
  edestruct MarFamUIEq as [_ Hp]. split; eauto.
  apply Mapping6 in H; subst; auto. rewrite <- Hp; clear Hp.
  generalize dependent f. generalize dependent cT1.
  ω_induction n; intros * Hne Hs * Hf Hi Hr.
  - destruct Hne as [A Ha], Hi as [_ Hi]. rewrite <- Hr in Ha. apply Hi in
      Ha. destruct Ha as [[x Ha] _]. apply Hf in Ha. cprod Ha; exfalso0.
  - assert (Hki : k ∈ k⁺). ens. assert (Hke : f[k] ∈ cT1).
    eapply ValueP1; eauto. assert (Hks : k ⁺ - [k] = k).
    { AppE. smH. AppC H0. orH; auto. sing H0. apply SingNE in H1; auto.
      elim H1; auto. smG. AppCG; Ens. apply SingNI; auto. intro.
      subst. apply RegAxP in H0; auto. } DC (k = ∅).
    { subst k; apply Hs. assert (MarkFamI f ∅ ⁺ = f[∅]).
      { AppE. AppC H0; apply H0; ens. AppCG; Ens. intros; AppC H1. orH.
      exfalso0. sing H1. } rewrite H0. eapply ValueP1; eens. }
    apply Mapping5 in Hf as Hfd. apply MapMapR in Hf as Hff.
    assert (Hfb : bijection f k⁺ cT1). apply bijection_is_func; auto.
    assert (Hp : ∀ x, x ∈ k⁺ → x ≠ k → f[x] ≠ f[k]).
    { intros. AppC H1. orH; [|sing H1].
      assert ([x,f[x]] ∈ f ∧ [k,f[k]] ∈ f). andG; eapply ValueP; eauto.
      AppCG; Ens. andH. intro. rewrite H5 in H3. assert (x = k).
      eapply Hi; eauto. rewrite Hr; auto. auto. }
    pose proof (bijection_sm_point _ _ _ _ Hfb Hki Hp) as Hfb'.
    set (f-[[k,f[k]]]) as f'. assert (MarkFamI f k⁺ = MarkFamI f' k∩f[k]).
    { apply IncAsym; intros x Hx; AssE x; AppCG.
      - AppC Hx. andG; [|apply Hx; ens]. AppCG; intros. AppCG; intros.
        AppC H3. AppC H3; andH. eapply ValueP2 in H3; eauto;
        [|AppCG; Ens]. subst; apply Hx; AppCG; Ens.
      - inH. intros. AppC H4; orH; [|sing H4]. DC (γ = k).
        subst; apply RegAxP in H4; elim H4. AppC H2.
        assert ([γ,f[γ]] ∈ f ∧ [k,f[k]] ∈ f).
        { andG; eapply ValueP; eauto. AppCG; Ens. }
        destruct H6 as [Hgc Hkc]. assert (Ensemble f[γ] ∧ Ensemble f[k]).
        { AssE [γ,f[γ]]; AssE [k,f[k]]. apply OrdEns2 in H6.
          apply OrdEns2 in H7; auto. } destruct H6 as [Hgb Hkb].
        apply H2 in H4 as Hg. AppC Hg. apply Hg. AppCG. AppCG; andG; Ens.
        apply SingNI; ens. intro. apply ordEq in H6; andH; Ens. }
    rewrite H1. apply Htp; [|apply Hs; eapply ValueP1; eens].
    apply bijection_is_func in Hfb'; andH. apply MapMapR1 in H2.
    rewrite Hks in H2. apply (IH (cT1 - [f[k]])); auto;
    [|intros A Ha; smH; auto]. destruct Hne as [A Ha]. rewrite <- Hr in Ha.
    exists f[∅]. smG. eapply ValueP1; eens. apply SingNI; Ens. intro.
    assert ([∅,f[∅]] ∈ f ∧ [k,f[k]] ∈ f). andG; eapply ValueP; eens.
    andH. rewrite H5 in H6. assert (k = ∅).
    eapply Hi; revgoals; eauto. rewrite Hr; auto. auto.
Qed.

Definition inDiscrete X := [X] ⋃ [∅].
Definition Discrete X := cP(X).

Example inDiscreteT : ∀ X, Ensemble X → Topology X (inDiscrete X).
Proof.
  intros. unfold inDiscrete. repeat split; intros.
  intros x Hx; unH; sing H0; ens. AppCG; ens. apply EmptySub.
  AppCG; ens. AppCG; ens. apply IntSinEm; auto. apply EleUSinEm; auto.
Qed.

Example DiscreteT : ∀ X, Ensemble X → Topology X (Discrete X).
Proof.
  intros. unfold Discrete; repeat split; ens; intros.
  apply PowerI; auto; apply EmptySub. pow H0; pow H1. AppCG.
  apply InterEns; eens. intros x Hx; inH; auto.
  AppCG. eens. intros x Hx; eleU Hx; apply H0 in H2; pow H2.
Qed.

(* 5.2 Neighborhoods and neighborhood system *)
Definition TNeigh x U X cT := Topology X cT ∧ x ∈ X ∧ U ⊂ X ∧
  ∃ V, V ∈ cT ∧ x ∈ V ∧ V ⊂ U.
Definition TNeighS x X cT := \{λ U, TNeigh x U X cT\}.
Definition TONeigh x U X cT := TNeigh x U X cT ∧ x ∈ U ∧ U ∈ cT.

Lemma TNeighP : ∀ x U X cT,
  Topology X cT → x ∈ U → U ∈ cT → TNeigh x U X cT.
Proof.
  intros. assert (U ⊂ X). apply H in H1; pow H1.
  red; andG; auto. exists U; andG; ens.
Qed.

Lemma TNeighP1 : ∀ x U X cT,
  Ensemble X → TNeigh x U X cT ↔ U ∈ TNeighS x X cT.
Proof. split; intros. AppCG. eapply SubAxP; eauto. apply H0. AppC H0. Qed.

Definition EleUx x U cT := ∪\{λ V, x ∈ U ∧ V ∈ cT ∧ x ∈ V ∧ V ⊂ U \}.

Lemma Le_NeFa : ∀ U, U = ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}).
Proof.
  intro. AppE; AssE x. AppCG. exists [x]. andG; ens. AppCG; ens.
  eleU H. AppC H1; destruct H1; andH. subst. sing H; Ens.
Qed.

Fact Neighbor_F : ∀ U X cT, Ensemble X → Topology X cT → U ⊂ X →
  (U ∈ cT ↔ ∀ x, x ∈ U → U ∈ TNeighS x X cT).
Proof.
  intros * Hxe Ht Hs. split; intros Hp.
  - intros. apply TNeighP1, TNeighP; auto.
  - DC (U = ∅). subst; apply Ht. set (∪(\{λ t, ∃ x, x ∈ U ∧
      t = EleUx x U cT\})) as Hmi.
    assert (H1 : ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}) ⊂ Hmi).
    { intros z Hz; eleU Hz. AppC H1; destruct H1; andH. subst.
      sing H0; Ens. apply Hp in H1 as Hu. AppC Hu. AppCG; Ens.
      exists (EleUx x0 U cT). andG. AppCG; Ens. destruct Hu as
        [_ [_ [_ [V [Hv []]]]]]. exists V. andG; auto. AppCG; Ens. AppCG.
      apply (SubAxP U); eens. intros z Hz. eleU Hz. AppC H2; andH; auto. }
    rewrite <- Le_NeFa in H1. assert (H2 : Hmi ⊂ U).
    { intros z Hz. eleU Hz. AppC H2; destruct H2; andH.
      subst. eleU H0; AppC H3; andH; auto. } assert (U = Hmi). eens.
    rewrite H0. apply Ht; intros V Hv. AppC Hv; destruct Hv; andH.
    subst V. apply Ht. intros z Hz; AppC Hz; tauto.
Qed.

Fact Neighbors_Fa : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U V, U ∈ TNeighS x X cT → V ∈ TNeighS x X cT →
  U ∩ V ∈ TNeighS x X cT.
Proof.
  intros * Hxe Ht Hx * Hu Hv.
  apply TNeighP1 in Hu as [_ [_ [Hux [U0 [Ho1 []]]]]]; auto.
  apply TNeighP1 in Hv as [_ [_ [Hvx [V0 [Ho2 []]]]]]; auto.
  apply TNeighP1; auto. red; andG; auto. intros z Hz; inH; auto.
  exists (U0 ∩ V0). andG; ens. apply Ht; auto. intros z Hz; inH; ens.
Qed.

Fact Neighbors_Fb : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U V, U ∈ TNeighS x X cT → V ⊂ X → U ⊂ V → V ∈ TNeighS x X cT.
Proof.
  intros * Hxe Ht Hx * Hu Hv Huv.
  apply TNeighP1 in Hu as [_ [_ [Hux [U0 [Ho1 []]]]]]; auto.
  apply TNeighP1; auto. red; andG; auto. exists U0; andG; eens.
Qed.

Fact Neighbors_Fc : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U, U ∈ TNeighS x X cT → ∃ V, V ∈ TNeighS x X cT ∧ V ⊂ U ∧
  (∀ y, y ∈ V → V ∈ TNeighS y X cT).
Proof.
  intros. apply TNeighP1 in H2 as [_[_[Hu [V [Ho []]]]]]; auto. exists V.
  andG; auto. apply TNeighP1, TNeighP; auto. apply Neighbor_F; eens.
Qed.

(* 5.3 Derived, Closed, Closure *)
Definition Cluster x A X cT := Topology X cT ∧ A ⊂ X ∧ x ∈ X ∧
  ∀ U, TNeigh x U X cT → U ∩ (A - [x]) ≠ ∅.
Definition Derived A X cT := \{λ x, Cluster x A X cT\}.

Lemma DerivedP : ∀ A X cT, Derived A X cT ⊂ X.
Proof. intros * x Hx. AppC Hx. apply Hx. Qed.

Lemma DerivedP1 : ∀ x A X cT, Cluster x A X cT ↔ x ∈ Derived A X cT.
Proof. split; intros. AppCG; exists X; apply H. AppC H. Qed.

Lemma DerivedP2 : ∀ x A X cT, Topology X cT → A ⊂ X → x ∈ X →
  x ∉ Derived A X cT → ∃ U, TNeigh x U X cT ∧ U ∩ (A - [x]) = ∅.
Proof.
  intros * Ht Hs Hx Hp. DC (∃ U, TNeigh x U X cT ∧ U ∩ (A - [x]) = ∅).
  auto. elim Hp; apply DerivedP1; red; andG; eauto.
Qed.

Fact Derived_Fa : ∀ A B X cT,
  B ⊂ X → A ⊂ B → Derived A X cT ⊂ Derived B X cT.
Proof.
  intros * Hb Hs x Hx. apply DerivedP1 in Hx. red in Hx; andH.
  apply DerivedP1. red; andG; auto. intros U Hu. apply H2 in Hu.
  apply EmptyNE in Hu as [y]. inH; smH.
  apply EmptyNE. exists y; inG; smG; auto.
Qed.

Fact Derived_Fb : ∀ A B X cT, Ensemble X → A ⊂ X → B ⊂ X →
  Derived (A ⋃ B) X cT = Derived A X cT ⋃ Derived B X cT.
Proof.
  intros * Hxe Ha Hb. apply IncAsym.
  - intros x Hx. pose proof Hx as Hx'. apply DerivedP1 in Hx as
      [Ht [_ [Hx _]]]. DC (x ∈ Derived A X cT ⋃ Derived B X cT); auto.
    apply UnionNE in H; andH. apply DerivedP2 in H as [U [Hun Hu]];
    apply DerivedP2 in H0 as [V [Hvn Hv]]; auto.
    assert (x ∉ Derived (A ⋃ B) X cT).
    { intro. apply DerivedP1 in H as [_ [_ [_ Hp]]]. set (U ∩ V) as D.
      assert (D ∈ TNeighS x X cT). apply Neighbors_Fa; auto;
      apply TNeighP1; auto. apply TNeighP1, Hp in H; auto.
      assert (D ∩ (A ⋃ B) - [x] = ∅).
      { assert ((A ⋃ B) - [x] = A - [x] ⋃ B - [x]). AppE. smH; unH; ens.
        unH; smH; smG; ens. rewrite H0, DistribuLI. AppE; [|exfalso0].
        rewrite <- Hu, <- (EmptyU (U ∩ A - [x])), <- Hv.
        unH;inH;smH;AppC H1; andH; [unG|apply UnionI']; inG; smG; auto. }
       auto. } tauto.
  - assert (Derived A X cT ⊂ Derived (A ⋃ B) X cT ∧
      Derived B X cT ⊂ Derived (A ⋃ B) X cT).
    { andG; apply Derived_Fa; intros x Hx; unH; ens. }
    andH; intros x Hx; unH; auto.
Qed.

Fact Derived_Fc : ∀ A X cT, Ensemble X → A ⊂ X →
  Derived (Derived A X cT) X cT ⊂ A ⋃ Derived A X cT.
Proof.
  intros * Hxe Ha x Hx. pose proof Hx as Hx'. apply DerivedP1 in Hx as
    [Ht [_ [Hx _]]]. DC (x ∈ A ⋃ Derived A X cT); auto. exfalso.
  apply UnionNE in H as [Hxa Hxd]. apply DerivedP2 in Hxd as
    [U [Hun Hue]]; auto. apply TNeighP1 in Hun as Hun'; auto.
  apply Neighbors_Fc in Hun' as [V [Hvn [Hvu Hp]]]; auto.
  apply Neighbor_F in Hp as Hp'; auto; [|apply TNeighP1 in Hvn; auto;
  eapply IncTran; eauto; apply Hun]. assert (V ∩ A - [x] = ∅).
  { AppE; [|exfalso0]. rewrite <- Hue. inH; smH. inG; smG; auto. }
  assert (V ∩ A = ∅). { eapply InterEqEmI; revgoals; eauto; Ens. }
  assert (∀ y, y ∈ V → y ∉ A).
  { intros * Hy H1. assert (y ∈ V ∩ A); ens. rewrite H0 in H2. exfalso0. }
  assert (∀ y, y ∈ V → V ∩ A - [y] = ∅).
  { intros. AppE; [|exfalso0]. inH; smH. apply H1 in H3; tauto. }
  assert (∀ y, y ∈ V → y ∉ Derived A X cT).
  { intros * Hy H3. apply H2 in Hy as Hyp. apply DerivedP1 in H3.
    apply Hp, TNeighP1, H3 in Hy; auto. }
  assert (V ∩ Derived A X cT - [x] = ∅).
  { AppE; [|exfalso0]. inH; smH. exfalso. apply H3 in H4; auto. }
  apply DerivedP1 in Hx' as [_ [_ [_ Hx']]].
  AppC Hvn. apply Hx' in Hvn; auto.
Qed.

Definition Closed A X cT := Topology X cT ∧ A ⊂ X ∧ Derived A X cT ⊂ A.

Fact Closed_F1 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closed A X cT ↔ X - A ∈ cT.
Proof.
  intros * Hxe Ht Hs. pose proof (SetminSubI A X). split; intros Hp.
  - eapply Neighbor_F; eauto. intros. smH. assert (x ∉ Derived A X cT).
    { intro. apply Hp in H2; tauto. } apply DerivedP2 in H2 as
      [U [Hun Hue]]; auto. apply InterEqEmI in Hue; Ens. 
    apply TNeighP1; auto. red; andG; auto. destruct Hun as
      [_ [_ [Hu [V [Hv [Hxv Hvu]]]]]]. exists V. andG; auto.
    eapply IncTran; eauto. intros z Hz. smG; auto. intro.
    assert (z ∈ U ∩ A); ens. rewrite Hue in H3; exfalso0.
  - red; andG; auto. intros x Hx. DC (x ∈ A); auto. exfalso.
    assert (x ∈ X - A). { AppC Hx. smG; auto. apply Hx. }
    eapply Neighbor_F, TNeighP1 in H1; eauto. pose proof Hx.
    apply DerivedP1 in Hx as [_ [_ [_ Hx]]]. apply Hx in H1.
    assert (X-A ∩ A-[x] = ∅). AppE; [|exfalso0]; inH; smH; tauto. auto.
Qed.

Corollary Co_ClFa1 : ∀ A X cT,
  Ensemble X → Topology X cT → A ⊂ X → A ∈ cT → Closed (X - A) X cT.
Proof.
  intros. apply Closed_F1; auto.
  apply SetminSubI. rewrite TwoCompl; auto.
Qed.

Definition TcF X cT := \{λ U, U ⊂ X ∧ X - U ∈ cT\}.

Fact cFP : ∀ X cT, TcF X cT ⊂ cP(X).
Proof. intros * U Hu. AppCG; Ens. AppC Hu; tauto. Qed.

Fact Closed_F2a : ∀ X cT, Ensemble X → Topology X cT →
  X ∈ TcF X cT ∧ ∅ ∈ TcF X cT.
Proof.
  intros. andG; AppCG; ens; andG; ens;
  [rewrite SetminId|apply EmptySub|rewrite SetminEm]; apply H0.
Qed.

Fact Closed_F2b : ∀ cF1 X cT, Ensemble X → Topology X cT →
  cF1 ≠ ∅ → cF1 ⊂ TcF X cT → ⋂cF1 ∈ TcF X cT.
Proof.
  intros * Hxe Ht Hne Hs. set \{λ A, A ⊂ X ∧ X - A ∈ cF1\} as cT1.
  assert (HcT : cT1 ⊂ cT).
  { intros A Ha. AppC Ha; andH. apply Hs in H0. AppC H0; andH.
    rewrite TwoCompl in H1; auto. }
  apply Ht in HcT. assert (H1 : (X - ∪cT1) ∈ TcF X cT).
  { AppCG; ens. andG. apply SetminSubI. rewrite TwoCompl; auto.
    apply Ht in HcT; pow HcT. }
  assert (H2 : (X - ∪(AAr X cF1)) = X - ∪cT1).
  { AppE; smH; smG; auto; intro; elim H0; eleU H2.
    - AppC H3; andH. AppCG; Ens. exists (X - (X - x0)). andG.
      rewrite TwoCompl; auto. AppCG; ens.
    - pose proof H3; AppC H3; destruct H3 as [T []]. AppCG; Ens.
      exists x0. andG; auto. AppCG; Ens. subst; rewrite TwoCompl.
      andG; auto. apply SetminSubI. apply Hs in H3; AppC H3; tauto. }
  rewrite DeMorganUI in H2; try apply AArP; auto.
  assert (⋂ cF1 = ⋂ AAr X (AAr X cF1)).
  { AppE; AssE x; AppC H; AppCG; intros.
    - AppC H3; destruct H3 as [B [Hb Heq]]. AppC Hb; destruct Hb as
        [C [Hc Heq1]]. subst. rewrite TwoCompl; auto.
      apply Hs in Hc. AppC Hc; tauto.
    - apply H. AppCG; Ens. exists (X - y). pose proof H3; apply Hs in H3.
      AppC H3; andH. rewrite TwoCompl; auto. andG; auto. AppCG;Ens. }
  rewrite H, H2; auto.
Qed.

Definition Closure A X cT := A ⋃ Derived A X cT.

Lemma ClosureP : ∀ A X cT, A ⊂ X → Closure A X cT ⊂ X.
Proof.
  intros * Ha x Hx. AppC Hx; orH; auto. apply DerivedP in H; auto.
Qed.

Fact Closure_Fa : ∀ A B X cT, Ensemble X → Topology X cT →
  A ⊂ X → B ⊂ X → Closure (A ⋃ B) X cT = Closure A X cT ⋃ Closure B X cT.
Proof.
  intros * Hxe Ht Ha Hb. unfold Closure. rewrite Derived_Fb,
    AssocU, (CommuU B), <- AssocU,
    <- AssocU, AssocU, (CommuU _ B); auto.
Qed.

Fact Closure_Fb : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure (Closure A X cT) X cT = Closure A X cT.
Proof.
  intros * He Ht Hs. unfold Closure at 2. rewrite Closure_Fa; auto;
  [|apply DerivedP]. unfold Closure. rewrite AssocU,
    <- (AssocU (Derived A X cT) _ _), IdemU,
    <- AssocU, UnionSub; auto. apply Derived_Fc; auto.
Qed.

Fact Re1_CloClo : ∀ A X cT, Topology X cT → A ⊂ X →
  Closed A X cT ↔ A = Closure A X cT.
Proof.
  intros * Ht Hs. split.
  - intros [_ [_ Hp]]. unfold Closure. AppE; [|unH]; ens.
  - intros. red; andG; auto. rewrite H at 2; intros z HZ; AppCG; Ens.
Qed.

Fact Re2_CloClo : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closed (Closure A X cT) X cT.
Proof.
  intros * Hxe Ht Hs. apply Re1_CloClo; auto.
  apply ClosureP; auto. rewrite Closure_Fb; auto.
Qed.

Lemma Le_Re3CC : ∀ A B X cT, Topology X cT →
  A ⊂ B → Closed B X cT → Closure A X cT ⊂ B.
Proof.
  intros * Ht Hab Hb z Hz. AppC Hz; orH; auto.
  eapply Derived_Fa in H; eauto; apply Hb; auto.
Qed.

Fact Re3_CloClo : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure A X cT = ⋂\{λ B, B ∈ TcF X cT ∧ A ⊂ B \}.
Proof.
  intros * Hxe Ht Hs. set (\{λ B, B ∈ TcF X cT ∧ A ⊂ B\}) as cB.
  assert (A ⊂ ⋂cB ∧ ⋂cB ∈ TcF X cT).
  { andG. intros x Hx. AppCG; Ens. intros B Hb. AppC Hb; andH; auto.
    apply Closed_F2b; auto. apply EmptyNE. exists X; AppCG; andG;
    auto. apply Closed_F2a; auto. intros B Hb; AppC Hb; tauto. }
  destruct H as [Ha Hb]. apply IncAsym.
  - AppC Hb; andH. apply Closed_F1 in H0; auto. apply Le_Re3CC; auto.
  - intros z Hz. AppC Hz. assert (Closure A X cT ∈ cB).
    { eapply ClosureP in Hs as Hc; eauto. AppCG; andG; eens.
      AppCG; andG; eens. apply Closed_F1, Re2_CloClo; auto.
      intros x Hx. AppCG; Ens. } auto.
Qed.

(* 5.4 Interior, External, Boundary *)
Definition Interiorp x A X cT := TNeigh x A X cT.
Definition Interior A X cT := \{λ x, Interiorp x A X cT \}.
Definition External A X cT := Interior (X - A) X cT.

Lemma InteriorP : ∀ A X cT, Interior A X cT ⊂ X.
Proof.
  unfold Interior, Interiorp, TNeigh.
  intros * z Hz. AppC Hz. andH. destruct H2; andH; auto.
Qed.

Fact Interior_F1a : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Interior A X cT = X - (Closure (X - A) X cT).
Proof.
  intros * Hxe Ht Hs. apply IncAsym; intros x Hx.
  - AppC Hx. assert (Hx' := Hx).
    destruct Hx as [_ [Hx [_ [V [Hv [Hxv Hva]]]]]]. apply Hva in Hxv.
    AppCG; andG; Ens. intro. AppC H; orH. smH; auto. apply DerivedP1 in H.
    apply H in Hx'. elim Hx'. AppE. inH; smH; tauto. exfalso0.
  - smH. apply UnionNE in H0 as [Hxi Hc]. apply DerivedP2 in Hc as
      [V [Hnv Hc]]; auto; [|apply SetminSubI]. apply InterEqEmI in Hc; Ens.
    apply InterSetmin in Hc; [|apply Hnv]. AppCG; Ens.
    eapply TNeighP1, Neighbors_Fb; eauto. apply TNeighP1; auto.
Qed.

Fact Interior_F1b : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure A X cT = X - (Interior (X - A) X cT).
Proof.
  intros * Hxe Ht Hs. pose proof (SetminSubI A X) as Hc.
  eapply Interior_F1a in Hc; eauto. erewrite TwoCompl in Hc; auto.
  apply (SetminEq _ _ X) in Hc. erewrite TwoCompl in Hc; auto.
  apply ClosureP; auto.
Qed.

Fact Interior_F2 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Interior (Interior A X cT) X cT = Interior A X cT.
Proof.
  intros *Hxe Ht Ha. pose proof SetminSubI A X as Ha'.
  rewrite Interior_F1a, Interior_F1a, TwoCompl, Closure_Fb;
  auto. apply ClosureP; auto. apply InteriorP.
Qed.

Fact Re1_OpeInt : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  A ∈ cT ↔ A = Interior A X cT.
Proof.
  intros * Hxe Ht Ha. pose proof SetminSubI A X as Hc. split; intros Hp.
  - eapply Co_ClFa1 in Hp as Hp'; eauto.
    apply Re1_CloClo, (SetminEq _ _ X) in Hp'; auto.
    rewrite TwoCompl in Hp'; auto. rewrite Interior_F1a; auto.
  - rewrite Interior_F1a in Hp; auto. apply (SetminEq _ _ X) in Hp.
    rewrite TwoCompl in Hp; [|apply ClosureP]; auto.
    apply Re1_CloClo, Closed_F1 in Hp; auto.
    rewrite TwoCompl in Hp; auto.
Qed.

Fact Re2_OpeInt : ∀ A X cT,
  Ensemble X → Topology X cT → A ⊂ X → Interior A X cT ∈ cT.
Proof.
  intros * Hxe Ht Ha. eapply Re1_OpeInt; eauto.
  apply InteriorP. symmetry; apply Interior_F2; auto.
Qed.

Fact Re3_OpeInt : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Interior A X cT = ∪\{λ B, B ∈ cT ∧ B ⊂ A\}.
Proof.
  intros * Hxe Ht Ha. pose proof SetminSubI A X as Ha'.
  rewrite Interior_F1a, Re3_CloClo, DeMorganIU; auto. AppE; eleU H.
  - AppC H0; destruct H0 as [r [Hr Hb]]. subst. AppC Hr; andH. AppC H0.
    andH. AppCG; Ens. exists (X - r). andG; auto. AppCG; Ens. andG; auto.
    eapply SetminSub2 in H1. rewrite TwoCompl in H1; auto.
  - AppC H0; destruct H0 as [Hb Hs]. AppCG; Ens. exists x0. andG; auto.
    AppCG; Ens. exists (X - x0). rewrite TwoCompl; eens. andG; auto.
    assert (X - x0 ⊂ X). apply SetminSubI. AppCG; eens.
    andG; [|apply SetminSub2; auto]. AppCG; andG; eens.
    rewrite TwoCompl; eens.
Qed.

Definition Boundp x A X cT := Topology X cT ∧ A ⊂ X ∧ x ∈ X ∧
  ∀ U, TNeigh x U X cT → U ∩ A ≠ ∅ ∧ U ∩ X - A ≠ ∅.
Definition Bound A X cT := \{λ x, Boundp x A X cT\}.

Fact Re1_ClInBo : ∀ A X cT, Topology X cT → A ⊂ X →
  Bound A X cT = Closure A X cT ∩ Closure (X - A) X cT.
Proof.
  intros * Ht Ha. pose proof SetminSubI A X as Ha'. AppE.
  - AppC H. red in H; andH. AppCG; Ens. andG; AppCG; Ens;
    [DC (x ∈ A); auto|DC (x ∈ X - A); auto]; right; apply DerivedP1;
    red; andG; auto; intros; [apply H2 in H4 as [Hl _]|
    apply H2 in H4 as [_ Hl]]; intro; elim Hl; eapply InterEqEmI; Ens.
  - inH. AppCG; Ens. red; andG; auto. eapply ClosureP; eauto. intros.
    AppC H; AppC H0; orH; [smH; tauto|apply DerivedP1 in H|
    apply DerivedP1 in H0|].
    + andG. apply H in H1; intro; elim H1; apply InterEqEmE; auto.
      destruct H1 as [_ [_ [_ [V [_ [Hv Hvu]]]]]]. intro.
      assert (x ∈ U ∩ X - A); ens. rewrite H1 in H2; exfalso0.
    + andG; [|apply H0 in H1; intro; elim H1; apply InterEqEmE; auto].
      destruct H1 as [_ [_ [_ [V [_ [Hv Hvu]]]]]]. intro.
      assert (x ∈ U ∩ A); ens. rewrite H1 in H2; exfalso0.
    + apply DerivedP1 in H; apply DerivedP1 in H0. andG; [apply H in H1|
      apply H0 in H1]; intro; elim H1; apply InterEqEmE; auto.
Qed.

Fact Re2_ClInBo : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure A X cT ∩ Closure (X - A) X cT =
  X - (Interior A X cT ⋃ Interior (X - A) X cT).
Proof.
  intros * Hxe Ht Ha. rewrite Interior_F1b, Interior_F1b,
    TwoCompl, <- UnionCompl, CommuU;
  try apply InteriorP; auto. apply SetminSubI.
Qed.

Fact Re3_ClInBo : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  X - (Interior A X cT ⋃ Interior (X - A) X cT) = Bound (X - A) X cT.
Proof.
  intros * Hxe Ht Ha. rewrite Re1_ClInBo, TwoCompl,
    CommuI, Re2_ClInBo; auto. apply SetminSubI.
Qed.

Corollary BoundP : ∀ A X cT, Topology X cT → A ⊂ X →
  Closure A X cT = A ⋃ Bound A X cT.
Proof.
  intros. rewrite Re1_ClInBo, DistribuLU, IncU; auto;
  [|intros x Hx; unfold Closure; ens]. assert (A ⋃ Closure (X-A) X cT = X).
  { AppE. unH; auto. AppC H1; orH. smH; auto. AppC H1; apply H1.
    DC (x ∈ A); ens. apply UnionI'; unfold Closure; ens. }
  rewrite H1, IncI; [|apply ClosureP]; auto.
Qed.

(* 5.5 Base, *)
Definition Base cB X cT := Topology X cT ∧ cB ⊂ cT ∧
  ∀ U, U ∈ cT → ∃ cB1, cB1 ⊂ cB ∧ U = ∪cB1.
Definition SubBase cS X cT := Topology X cT ∧ cS ⊂ cT ∧
  Base (\{λ U, ∃ cN, ⦿ cN ∧ Finite cN ∧ cN ⊂ cS ∧ U = ⋂cN\}) X cT.

Fact BaseP : ∀ X cT, Topology X cT → Base cT X cT.
Proof.
  split; andG; ens. intros. exists [U]. andG. intros z Hz.
  sing Hz; Ens. rewrite EleUSin; Ens.
Qed.

Fact NeFiSuP1 : ∀ cS,
  cS ⊂ \{λ U, ∃ cN, ⦿ cN ∧ Finite cN ∧ cN ⊂ cS ∧ U = ⋂cN\}.
Proof.
  intros * U Hu; AssE U. AppCG. exists [U]. andG. exists U; ens.
  apply sin_finite; auto. intros x Hx; sing Hx. rewrite EleISin; auto.
Qed.