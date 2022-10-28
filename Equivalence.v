(* 6 Equivalence proof *)

Require Export Topology.

(* 6.1 Neighborhood systems *)
Theorem Theorem1 : ∀ X f, Ensemble X → Mapping f X cP(cP(X)) →
  (∀ x, x ∈ X → f[x] ≠ ∅ ∧ (∀ U, U ∈ f[x] → x ∈ U) ∧
  (∀ U V, U ∈ f[x] → V ∈ f[x] → U ∩ V ∈ f[x]) ∧
  (∀ U V, U ∈ f[x] → V ⊂ X → U ⊂ V → V ∈ f[x]) ∧
  (∀ U, U ∈ f[x] → ∃ V, V ∈ f[x] ∧ V ⊂ U ∧ (∀ y, y ∈ V → V ∈ f[y]))) →
  exists! cT, (Topology X cT ∧ ∀ x, x ∈ X → f[x] = TNeighS x X cT).
Proof.
  intros * Hxe Hf Hp. set (cT := \{λ U, U⊂X ∧ ∀ x, x ∈ U → U ∈ f[x]\}).
  exists cT. assert (Hs : cT ⊂ cP( X)). intros A Ha; AppC Ha; andH; ens.
  assert (Hvs : ∀ x, x ∈ X → f[x] ⊂ cP( X)).
  intros; eapply ValueP1 in H; eauto; pow H. assert (Ht : Topology X cT).
  { repeat split; auto.
    - AppCG. andG; ens. intros. apply Hvs in H as Hv.
      apply Hp in H as [H1 [_ [_ [H3 _]]]]. apply EmptyNE in H1 as [U H1].
      pose proof H1. apply Hv in H; pow H. eapply H3; eens.
    - AppCG; ens. split; intros z Hz; exfalso0.
    - intros * Ha Hb. AppC Ha; AppC Hb; andH. assert (A ∩ B ⊂ X).
      intros x Hx; inH; auto. AppCG; andG; eens. intros.
      assert (x ∈ X); auto. inH; apply Hp; auto.
    - intros * Htt. assert (Htx : ∪cT1 ⊂ X). intros x Hx; eleU Hx;
      apply Htt, Hs in H0; pow H0. AppCG; andG; eens. intros. eleU H.
      assert (H0' := H0). apply Htt in H0. AppC H0; andH.
      apply H1 in H as Hfx. assert (x0 ⊂ ∪cT1).
      apply EleUEleSub; auto. eapply Hp in H2; eauto. }
  assert (Htp : ∀ x, x ∈ X → f[x] = TNeighS x X cT).
  { intros. pose proof H; apply Hp in H0; andH. apply IncAsym.
    - intros U Hu. pose proof Hu as Hu'. apply Hvs in Hu; auto; pow Hu.
      apply H4 in Hu' as [V [Hv []]]. assert (V ∈ cT). AppCG; eens.
      apply TNeighP1; auto. red; andG; eauto.
    - intros U Hu. apply TNeighP1 in Hu as [_ [_ [Hu [V [Hv []]]]]];
      auto. AppC Hv; andH. eapply H3; eauto. } split; auto.
  intros cT1 [Ht1 Htp1]. apply IncAsym; intros W Hw. AppC Hw; andH.
  eapply Neighbor_F; eauto. intros; rewrite <- Htp1; auto.
  apply Ht1 in Hw as Hwx; pow Hwx. AppCG; andG; Ens.
  intros. eapply Neighbor_F in H as Hn; eauto. rewrite Htp1; auto.
Qed.

(* 6.2 Closure *)
Definition Kuratowski X c := Mapping c cP(X) cP(X) ∧
  (c[∅] = ∅) ∧ (∀ A, A ∈ cP(X) → A ⊂ c[A]) ∧
  (∀ A B, A ∈ cP(X) → B ∈ cP(X) → c[A ⋃ B] = c[A] ⋃ c[B]) ∧
  (∀ A, A ∈ cP(X) → c[c[A]] = c[A]).

Theorem Theorem2 : ∀ X c, Ensemble X → Kuratowski X c →
  exists! cT, Topology X cT ∧ (∀ A, A ⊂ X → c[A] = Closure A X cT).
Proof.
  intros * Hxe [Hf [H1 [H2 [H3 H4]]]].
  set (cT := \{λ U, U ⊂ X ∧ c[X - U] = X - U\}). assert (He : ∅ ∈ cT).
  { AppCG; andG; ens. apply EmptySub. rewrite SetminEm.
    apply IncAsym. eapply PowerE, ValueP1; eens. apply H2; ens. }
  exists cT. assert (Ht : Topology X cT).
  { repeat split; auto.
    - intros A Ha. AppC Ha; andH; ens.
    - AppCG; andG; ens. rewrite SetminId; auto.
    - intros * Ha Hb. AppC Ha; AppC Hb; andH. AppCG; andG.
      apply InterEns; eens. intros z Hz; inH; auto.
      rewrite TwoDMI. rewrite <- H6, <- H0 at 2.
      apply H3; apply PowerI; auto; apply SetminSubI.
    - assert (Hab : ∀ A B, A ⊂ X → B ⊂ X → A ⊂ B → c[A] ⊂ c[B]).
      { intros. assert (B = A ⋃ B - A).
        { AppE. DC (x ∈ A); ens. unH; [|smH]; auto. }
        rewrite H6, H3; try apply PowerI; auto. intros x Hx; ens.
        intros x Hx; smH; auto. }
      intros cT1 Hs. assert (Ht : ∪ cT1 ⊂ X).
      { intros x Hx. eleU Hx. apply Hs in H0. AppC H0; andH; auto. }
      AppCG; andG; auto. eapply SubAxP; eauto. DC (cT1 = ∅).
      { subst. rewrite EleUEm. AppC He; tauto. } apply IncAsym.
        + assert (∀ A1, A1 ∈ cT1 → X - (∪cT1) ⊂ X - A1).
          { intros. rewrite DeMorganUI; auto. apply EleIEle. AppCG.
            eapply SubAxP; eauto; apply SetminSubI. }
          assert (∀ A1, A1 ∈ cT1 → c[X - (∪ cT1)] ⊂ X - A1).
          { intros. pose proof H5. apply Hs in H5. AppC H5; andH.
            rewrite <- H7. apply Hab; auto; apply SetminSubI. }
          rewrite DeMorganUI at 2; auto. intros z Hz. AppCG; Ens. intros.
          AppC H6; destruct H6 as [A1 []]. apply H5 in H6. subst; auto.
        + apply H2. apply PowerI; auto. apply SetminSubI. }
  assert (Htp : ∀ A, A ⊂ X → c[A] = Closure A X cT).
  { intros. assert (c[A] ⊂ X).
    eapply PowerE, ValueP1; eens. apply IncAsym.
    - assert (Closed (Closure A X cT) X cT). apply Re2_CloClo; auto.
      assert (Closure A X cT ⊂ X). apply ClosureP; auto.
      apply Closed_F1 in H5; auto. AppC H5; andH.
      rewrite TwoCompl in H7; auto. unfold Closure in *.
      rewrite <- H7, H3; ens. intros z Hz; ens.
      apply PowerI; auto. apply DerivedP.
    - rewrite Re3_CloClo; auto. apply EleIEle. AppCG; eens.
      andG; [|apply H2; ens]. AppCG; andG; eens.
      assert (X - c[A] ⊂ X). apply SetminSubI.
      AppCG; andG; eens. rewrite TwoCompl; ens. } split; auto.
  intros cT1 [Ht1 Htp1]. apply ExtAx; intros A. split; intros Hp;
  pose proof SetminSubI A X as Ha.
  - AppC Hp; andH. rewrite <- (TwoCompl A X); auto.
    apply Closed_F1; auto. apply Re1_CloClo; auto.
    apply Htp1 in Ha. rewrite H0 in Ha;auto.
  - apply Ht1 in Hp as Ha'; pow Ha'. AppCG; andG; eens.
    rewrite Htp1; auto. symmetry; apply Re1_CloClo, Closed_F1; auto.
    rewrite TwoCompl; auto.
Qed.

(* 6.3 Closed *)
Theorem Theorem3 : ∀ X cF, Ensemble X → cF ⊂ cP(X) → (X ∈ cF ∧ ∅ ∈ cF ∧
  (∀ A B, A ∈ cF → B ∈ cF → A ⋃ B ∈ cF) ∧
  (∀ cF1, cF1 ≠ ∅ → cF1 ⊂ cF → ⋂cF1 ∈ cF)) →
  exists! cT, (Topology X cT ∧ cF = TcF X cT).
Proof.
  intros * Hxe Hf Hp. set (cT := \{λ U, U ⊂ X ∧ X - U ∈ cF\}).
  exists cT. assert (Hs : cT ⊂ cP(X)). intros A Ha; AppC Ha; andH; ens.
  assert (Ht : Topology X cT ∧ cF = TcF X cT).
  { repeat split; auto.
    - AppCG; andG; ens. rewrite SetminId; apply Hp.
    - AppCG; andG; ens. apply EmptySub. rewrite SetminEm; apply Hp.
    - intros. AppC H; AppC H0; andH. assert (A ∩ B ⊂ X). intros x Hx.
      inH; auto. AppCG; andG; eens. rewrite InterCompl; auto.
    - intros. AppCG; andG; eens. intros x Hx; eleU Hx. apply H, Hs in H1.
      pow H1. DC (cT1 = ∅). subst; rewrite EleUEm, SetminEm; apply Hp.
      rewrite DeMorganUI; auto. apply Hp. apply AArP; auto. intros A Ha.
      AppC Ha. destruct Ha; andH. subst. apply H in H1. AppC H1; tauto.
    - apply IncAsym; intros A Ha.
      + apply Hf in Ha as Hx; pow Hx. AppCG; andG; Ens. assert (X-A ⊂ X).
        apply SetminSubI. AppCG; andG; ens. rewrite TwoCompl; auto.
      + AppC Ha; andH. AppC H0. rewrite TwoCompl in H0; tauto. }
  split; auto. intros cT1 [Ht1 Htp1]. apply IncAsym; intros A Ha.
  - AppC Ha; andH. rewrite Htp1 in H0. AppC H0.
    rewrite TwoCompl in H0; tauto.
  - apply Ht1 in Ha as Hx; pow Hx. AppCG; andG; Ens. rewrite Htp1.
    assert (X - A ⊂ X). apply SetminSubI. AppCG; andG; ens.
    rewrite TwoCompl; auto.
Qed.

(* 6.4 Interior *)
Definition InteriorAri X i := Mapping i cP(X) cP(X) ∧
  (i[X] = X) ∧ (∀ A, A ∈ cP(X) → i[A] ⊂ A) ∧
  (∀ A B, A ∈ cP(X) → B ∈ cP(X) → i[A ∩ B] = i[A] ∩ i[B]) ∧
  (∀ A, A ∈ cP(X) → i[i[A]] = i[A]).

Theorem Theorem4 : ∀ X i, Ensemble X → InteriorAri X i →
  exists! cT, Topology X cT ∧ (∀ A, A ⊂ X → i[A] = Interior A X cT).
Proof.
  intros. red in H0; andH. set (cT := \{λ U, U ⊂ X ∧ i[U] = U\}).
  assert (Hts : cT ⊂ cP(X)). { intros A Ha; AppC Ha; andH; ens. }
  exists cT. assert (Topology X cT).
  { repeat split; auto. AppCG; andG; ens. pose proof EmptySub X; AppCG;
    andG; ens. apply IncAsym. apply H2; ens. apply EmptySub.
    intros; AppC H5; AppC H6; andH. AppCG; andG. apply InterEns; eens.
    intros z Hz; inH; auto. rewrite H3, H7, H8; ens.
    intros. assert (∪cT1 ⊂ X). intros z Hz; eleU Hz; apply H5 in H7;
    AppC H7; andH; auto. AppCG; andG; eens. apply IncAsym.
    apply H2; ens. intros x Hx; eleU Hx. pose proof H8; apply H5 in H8;
    AppC H8; andH. rewrite <- H10 in H7. assert (i[x0] ⊂ i[∪cT1]).
    { rewrite <- (IncI x0 (∪cT1)), H3; ens.
      intros z Hz; inH; auto. intros z Hz; AppCG; Ens. } auto. }
  assert (Htp : ∀ A, A ⊂ X → i[A] = Interior A X cT).
  { intros A Ha. assert (Ha' : A ∈ cP(X)); ens.
    rewrite Re3_OpeInt; auto. apply IncAsym.
    - intros x Hx. AppCG; Ens; andG. exists i[A]; andG; auto.
      AppCG; eens; andG; auto. AppCG; eens; andG.
    - intros x Hx. eleU Hx. AppC H7; andH. AppC H7; andH.
      assert (x0 ⊂ i[A]). { apply IncInteq in H8 as Hx0.
        pose proof H9 as H9'. rewrite <- Hx0, H3, H9' in H9 at 1; ens.
        rewrite <- H9; intros z Hz; inH; auto. } auto. } split; auto.
  intros cT1 [Ht1 Htp1]. apply ExtAx; intros A. split; intros Hp.
  - AppC Hp; andH. rewrite <- H7, Htp1; auto. apply Re2_OpeInt; auto.
  - assert (A ⊂ X). apply Ht1 in Hp; pow Hp. AppCG; andG; Ens.
    rewrite Htp1; auto. symmetry. apply Re1_OpeInt; auto.
Qed.

(* 6.5 External *)
Definition ExterAri X e := Mapping e cP(X) cP(X) ∧ e[∅] = X ∧ e[X] = ∅ ∧
  (∀ A B, A ∈cP(X) → B ∈ cP(X) → e[A ⋃ B] = e[A] ∩ e[B]) ∧
  (∀ A B, A ∈ cP(X) → B ∈ cP(X) → A ⊂ B → e[B] ⊂ e[A]) ∧
  (∀ A, A ∈ cP(X) → e[e[A]] ⊂ A ∧ e[X - e[A]] = e[A]) ∧
  (∀ A, A ∈ cP(X) → e[A] ⊂ X - A).

Theorem Theorem5 : ∀ X e, Ensemble X → ExterAri X e →
  exists! cT, Topology X cT ∧ (∀ A, A ⊂ X → e[A] = External A X cT).
Proof.
  intros. red in H0; andH. set (cT := \{λ U, U ⊂ X ∧ e[X - U] = U\}).
  assert (Hs : cT ⊂ cP(X)). { intros A Ha; AppC Ha; andH; ens. }
  exists cT. assert (Ht : Topology X cT).
  { repeat split; auto.
    - AppCG; andG; ens. rewrite SetminId; auto.
    - AppCG; andG; ens. apply EmptySub. rewrite SetminEm; auto.
    - intros. AppC H7; AppC H8; andH. assert (A ∩ B ⊂ X).
      intros z Hz; inH; auto. AppCG; andG; eens. rewrite TwoDMI,
        H3, H9, H10; auto; apply PowerI, SetminSub; ens.
    - intros * Ht1. set (∪cT1) as B. assert (Hb : B ⊂ X).
      { intros z Hz; eleU Hz; apply Ht1 in H8. AppC H8; andH; auto. }
      pose proof SetminSubI B X as Hbc. assert (Hbi : B ∈ cP( X)); ens.
      AppCG; andG; eens. apply IncAsym.
      + apply H6, H4 in Hbi; eens.
        eapply IncTran; eauto. apply H5; ens.
      + intros x Hx. eleU Hx. assert (x0 ⊂ B). intros z Hz; AppCG; Ens.
        apply Ht1 in H8; AppC H8; andH. eapply SetminSub2, H4 in H9;
        try apply PowerI, SetminSubI; auto. rewrite H10 in H9; auto. }
  assert (Htp : ∀ A, A ⊂ X → e[A] = External A X cT).
  { intros * Ha. pose proof SetminSubI A X as Hac. assert (A ∈ cP(X)).
    ens. unfold External; rewrite Re3_OpeInt; auto. apply IncAsym.
    - intros x Hx. AppCG; Ens. exists (e[A]). andG; auto.
      AppCG; andG; eens. AppCG; andG; eens. apply H5; ens.
    - intros x Hx. AppC Hx; destruct Hx as [C []]. AppC H9; andH.
      eapply SetminSub2 in H10. rewrite TwoCompl in H10; auto.
      apply H4 in H10; try apply PowerI; auto; [|apply SetminSubI].
      AppC H9; andH. rewrite H11 in H10; auto. } split; auto.
  intros cT1 [Ht1 Htp1]. apply ExtAx; intros A. split; intros Hp.
  - AppC Hp; andH. rewrite Htp1 in H8; auto; [|apply SetminSubI].
    eapply Re1_OpeInt; eauto. unfold External in H8.
    rewrite TwoCompl in H8; auto.
  - AppCG; Ens. apply Ht1 in Hp as Hax; pow Hax. andG; auto.
    rewrite Htp1; [|apply SetminSubI]. unfold External.
    rewrite TwoCompl; auto. symmetry; eapply Re1_OpeInt; auto.
Qed.

(* 6.6 Boundary *)
Definition BoundAri X b := Mapping b cP(X) cP(X) ∧ (b[X] = ∅) ∧
  (∀ A B, A∈cP(X) → B∈cP(X) → A ∩ B ∩ b[A ∩ B] = A ∩ B ∩ (b[A] ⋃ b[B])) ∧
  (∀ A B, A ∈ cP(X) → B ∈ cP(X) → b[A ⋃ B] ⊂ b[A] ⋃ b[B]) ∧
  (∀ A, A ∈ cP(X) → b[b[A]] ⊂ b[A]) ∧
  (∀ A B, A ∈ cP(X) → B ∈ cP(X) → A ⋃ b[A] ⊂ A ⋃ B ⋃ b[A ⋃ B]) ∧
  (∀ A, A ∈ cP(X) → b[X - A] = b[A]).

Theorem Theorem6 : ∀ X b, Ensemble X → BoundAri X b →
  exists! cT, Topology X cT ∧ (∀ A, A ⊂ X → b[A] = Bound A X cT).
Proof.
  intros. red in H0; andH. set (cT := \{λ U, U ⊂ X ∧ b[U] ⊂ X - U\}).
  assert (Hu : ∀ A, A ∈ cT → A ∩ b[A] = ∅).
  intros; AppC H7; andH. AppE. inH; apply H8 in H10; smH; tauto. exfalso0.
  assert (Hs : cT ⊂ cP(X)). { intros A Ha; AppC Ha; andH; ens. }
  exists cT. assert (Ht : Topology X cT).
  { repeat split; auto.
    - AppCG; andG; ens. rewrite H1. apply EmptySub.
    - pose proof EmptySub X;  AppCG; andG; ens. rewrite SetminEm.
      apply PowerE. apply PowerI in H7; auto. eapply ValueP1; eauto.
    - intros; AppC H7; AppC H8; andH. assert (A ∩ B ⊂ X). intros z Hz;
      inH; auto. AppCG; andG; eens. assert (A ∩ B ∩ b[A ∩ B] = ∅).
      { assert (A ∩ b[A] = ∅ ∧ B ∩ b[B] = ∅).
        { andG; rewrite Hu; auto; AppCG; eens. } andH.
        rewrite H2, DistribuLI, DistribuLI, H13, (CommuI B),
          <- AssocI, H12, CommuI, EmptyI,
          EmptyI, EmptyU; ens. } intros z Hz; smG.
      eapply PowerI, ValueP1 in H11; eauto; pow H11. intro. assert (z ∈
        A ∩ B ∩ b[A ∩ B]). inH; inG; auto. rewrite H12 in H14; exfalso0.
    - intros. set (∪cT1) as B. assert (Hb : B ⊂ X).
      { intros z Hz; eleU Hz; apply H7 in H9. AppC H9; andH; auto. }
      assert (∀ A, A ∈ cT1 → A ∩ b[B] = ∅).
      { intros. pose proof H8; apply H7, Hs in H8. assert (A ∩ B = A).
        AppE. inH; auto. inG; [|AppCG]; Ens. apply (H2 A B) in H8; ens.
        rewrite <- AssocI, <- AssocI, H10, DistribuLI, Hu,
          CommuU, EmptyU in H8; auto. } AppCG; andG; auto.
      eapply SubAxP; eauto. intros z Hz; smG. eapply PowerI,ValueP1 in Hb;
      eauto; pow Hb. intro; eleU H9. apply H8 in H10.
      assert (z ∈ x ∩ b[B]). ens. rewrite H10 in H11; exfalso0. }
  assert (Htp : ∀ A, A ⊂ X → b[A] = Bound A X cT).
  { intros B Hb. pose proof (SetminSubI B X) as Hbc.
    assert (He : ∀ A B C, A ⋃ B ⊂ A ⋃ C → ∀ x, x ∉ A → x ∈ B → x ∈ C).
    { intros. assert (B0 ⊂ A ⋃ B0). intros z Hz; ens.
      apply H10, H7 in H9. unH; tauto. } apply IncAsym.
    - assert (Hp : ∀ A, A ⊂ X → A ⋃ b[A] ⊂ A ⋃ Bound A X cT).
      { intros * Ha. assert (Ha1 : A ∈ cP(X)); ens.
        assert (Hp1 : ∀ B, A ⊂ B → Closed B X cT → A ⋃ b[A] ⊂ B).
        { intros * Hb0 Hp. assert (Hbi : B0 ⊂ X). apply Hp.
          apply (IncTran _ (A ⋃ B0 ⋃ b[A ⋃ B0]) _). apply H5; ens.
          rewrite (IncU A B0), IncU; ens;
          [|intros z Hz; ens]. rewrite CommuU, IncU; ens.
          apply Closed_F1 in Hp; auto. AppC Hp; andH.
          rewrite TwoCompl, H6 in H8; ens. }
        apply Hp1. intros x Hx; ens. rewrite <- BoundP; auto.
        apply Re1_CloClo; auto. apply ClosureP; auto.
        symmetry; apply Closure_Fb; auto. } apply Hp in Hb as Hp1.
      apply Hp in Hbc as Hp2. rewrite H6, <- Re3_ClInBo,
        <- Re2_ClInBo, <- Re1_ClInBo in Hp2; ens. intros x Hx.
      DC (x ∈ B); [apply (He _ _ _ Hp2)|apply (He _ _ _ Hp1)]; auto.
      intro; smH; tauto.
    - assert (Hp : ∀ A, A ⊂ X → A ⋃ Bound A X cT ⊂ A ⋃ b[A]).
      { intros * Ha. assert (Ha1 : A ∈ cP(X)); ens.
        eapply ValueP1 in Ha1 as Hv; eauto. pose proof Hv as Hb1; pow Hv.
        assert (Hab : A ⋃ b[A] ⊂ X). { intros x Hx; unH; auto. }
        assert (Hao : X - (A ⋃ b [A]) ∈ cT).
        { assert (X - (A⋃b[A]) ⊂ X). apply SetminSubI. AppCG; andG; eens.
          rewrite TwoCompl; auto. rewrite H6; ens.
          eapply IncTran; eauto. rewrite (UnionSub b[A]).
          intros z Hz; ens. apply H4; auto. }
        apply Closed_F1, Re1_CloClo in Hao; auto.
        rewrite Hao, Closure_Fa, BoundP; auto. intros z Hz; ens. }
      apply Hp in Hb as Hp1. apply Hp in Hbc as Hp2.
      rewrite H6, <- Re3_ClInBo, <- Re2_ClInBo, <- Re1_ClInBo
        in Hp2; ens. intros x Hx. DC (x ∈ B); [apply (He _ _ _ Hp2)|
      apply (He _ _ _ Hp1)];auto. intro; smH; tauto. }
  split; auto. intros cT1 [Ht1 Htp1].
  apply ExtAx; intros A. split; intros Hp.
  - AppC Hp; andH. pose proof (SetminSubI A X) as Hac.
    rewrite Htp1 in H8; auto. rewrite <- (TwoCompl A X); auto.
    apply Closed_F1, Re1_CloClo; auto. rewrite BoundP,
      <- Re3_ClInBo, <- Re2_ClInBo, <- Re1_ClInBo,
      CommuU, IncU; auto.
  - AppCG; Ens. apply Ht1 in Hp as Hax; pow Hax. andG; auto.
    pose proof (SetminSubI A X) as Hac. rewrite Htp1; auto.
    eapply Co_ClFa1, Re1_CloClo in Hp; eauto. rewrite BoundP in Hp;
    auto. rewrite Re1_ClInBo, Re2_ClInBo, Re3_ClInBo; auto.
    rewrite Hp at 2. intros z Hz; apply UnionI'; auto.
Qed.

(* 6.7 Bases *)
Definition cB12 cB1 cB2 :=
  \{λ t, ∃ B1 B2, B1 ∈ cB1 ∧ B2 ∈ cB2 ∧ t = B1 ∩ B2\}.

Lemma LeTh7 : ∀ cB1 cB2, (∪cB1) ∩ (∪cB2) = ∪(cB12 cB1 cB2).
Proof.
  intros. AppE. inH; eleU H; eleU H0. AppCG; Ens. exists (x0 ∩ x1).
  andG; ens. AppCG; apply InterEns; Ens. eleU H; AppC H0.
  destruct H0, H0; andH. subst; inH. inG; AppCG; Ens.
Qed.

Lemma Le1Th7 : ∀ cW cB, Ensemble cW → Ensemble cB →
  (∀ T, T ∈ cW → ∃ cBu, cBu ⊂ cB ∧ T = ∪cBu) →
  (∃ cBv, cBv ⊂ cB ∧ ∪cW = ∪cBv).
Proof.
  intros * Hwe Hbe Hp. assert (Hpc : ∀ T, T ∈ cW →
     ∃ cBu, [T,cBu] ∈ \{\λ m n, n ⊂ cB ∧ m = ∪n\}\).
  { intros. AssE T. apply Hp in H as [cBu []]. exists cBu. AppCG'.
    apply OrdEns; eens. } assert (Ensemble \{\λ m n, n ⊂ cB ∧ m = ∪n\}\).
  { assert (\{\λ m n, n ⊂ cB ∧ m = ∪n\}\ ⊂ cP(∪cB) × cP(cB)).
    intros z Hz; AssE z. PP Hz a b; andH. AppCG'; andG; ens.
    subst; apply EleUSub in H0; ens. eapply SubAxP; revgoals; eauto.
    apply CProdEns; ens. } destruct (ChoAx1 _ _ H Hpc) as [f [Hf Hfp]].
  set (cBv := ∪\{λ Z, ∃ T, T ∈ cW ∧ Z = f[T]\}). exists cBv. andG.
  - intros A Ha. eleU Ha. AppC H1; destruct H1; andH. subst.
    apply Hfp in H1. AppC' H1; andH; auto.
  - AppE; eleU H0.
    + pose proof H1; apply Hfp in H1; AppC' H1; andH. rewrite H3 in H0.
      eleU H0. AppCG; Ens. exists x1. andG; auto. AppCG; Ens. exists f[x0].
      andG; auto. AppCG; apply ValueEns; erewrite Mapping5; eauto.
    + eleU H1. AppC H2; destruct H2; andH. AppCG; Ens.
      pose proof H2. apply Hfp in H2; AppC' H2; andH. exists x2.
      andG; auto. rewrite H5. AppCG; Ens. rewrite H3 in H1; eauto.
Qed.

Theorem Theorem7 : ∀ X cB, Ensemble X → cB ⊂ cP(X) → ∪cB = X →
  (∀ B1 B2, B1 ∈ cB → B2 ∈ cB → ∀ x, x ∈ B1 ∩ B2 →
  ∃ B, B ∈ cB ∧ x ∈ B ∧ B ⊂ B1 ∩ B2) → exists! cT, Base cB X cT.
Proof.
  intros * Hxe Hs Hp1 Hp2. set (cT :=
    \{λ U, U ⊂ X ∧ ∃ cBu, cBu ⊂ cB ∧ U = ∪cBu\}).
  assert (Hbb : ∀ B1 B2, B1 ∈ cB → B2 ∈ cB → B1 ∩ B2 ∈ cT).
  { intros * Hb1 Hb2. set (B1 ∩ B2) as D.
    pose proof (Hp2 _ _ Hb1 Hb2) as Hp. assert (Hpc : ∀ x, x ∈ D →
       ∃ B, [x,B] ∈ \{\λ m n, n ∈ cB ∧ m ∈ n ∧ n ⊂ D\}\).
    { intros. apply Hp in H as [B]; andH. exists B.
      AppCG'. apply OrdEns; Ens. }
    assert (Hce : Ensemble \{\λ m n, n ∈ cB ∧ m ∈ n ∧ n ⊂ D\}\).
    { assert (\{\λ m n, n ∈ cB ∧ m ∈ n ∧ n ⊂ D\}\ ⊂ X × cB).
      { intros z Hz; clear Hp1. PP Hz a b; andH. AppCG'; andG; auto.
        apply OrdEns; Ens. apply Hs in H; pow H. }
      eapply SubAxP; revgoals; eauto. apply CProdEns; eens. }
    destruct (ChoAx1 _ _ Hce Hpc) as [W [Hw Hwp]].
    set (\{λ U, ∃ x, x ∈ D ∧ U = W[x]\}) as Wx. assert (Gr : ∪Wx ⊂ D).
    { intros x Hx. eleU Hx. AppC H0; destruct H0; andH. subst.
      apply Hwp in H0. AppC' H0; apply H0; auto. }
    AppCG. apply InterEns; Ens. andG. intros z Hz; AppC Hz; andH;
    apply Hs in Hb1; pow Hb1. exists Wx; andG. intros A Ha; AppC Ha;
    destruct Ha; andH. subst. apply Hwp in H; AppC' H; tauto.
    apply IncAsym; auto. rewrite (Le_NeFa D). intros x Hx.
    eleU Hx; AppC H0; destruct H0. andH. subst; sing H; Ens.
    apply Hwp in H0; AppC' H0; andH. AppCG; Ens.
    exists W[x1]; andG; auto. AppCG; Ens. }
  exists cT. assert (Ht : Topology X cT).
  { repeat split. intros A Ha; AppC Ha; andH; ens.
    - AppCG. andG; ens. exists cB. andG; ens.
    - pose proof EmptySub. AppCG; andG;ens. exists ∅. rewrite EleUEm;ens.
    - intros * Ha Hb. AppC Ha; AppC Hb; andH. destruct H2 as [cB1 []],
        H0 as [cB2 []]. assert (Hab : A ∩ B ⊂ X). intros x Hx; inH; auto.
      AppCG; andG; eens. rewrite H3, H4. rewrite LeTh7.
      assert (Hbe : cB12 cB1 cB2 ⊂ cP(X)).
      { intros C Hc. AppC Hc; destruct Hc as [B1 [B2]]; andH. subst C.
        apply PowerI; auto. intros x Hx. assert (B1 ∩ B2 ⊂ B1).
        intros z Hz; inH; ens. apply H7 in Hx. apply H2, Hs in H5; pow H5. }
      apply Le1Th7; eens. intros * Ht. AppC Ht.
      destruct Ht as [B1 [B2 [Hb1 [Hb2 Heq]]]].
      apply H2 in Hb1; apply H0 in Hb2. subst.
      pose proof Hbb _ _ Hb1 Hb2. AppC H3; tauto.
    - intros * Ht1. assert (Hsx : ∪cT1 ⊂ X). { intros x Hx; eleU Hx.
        apply Ht1 in H0; AppC H0; andH; auto. } AppCG; andG; auto.
      eapply SubAxP; eauto. assert (cT1 ⊂ cP(X)).
      { eapply IncTran; eauto. intros U Hu. AppC Hu; andH; ens. }
      apply Le1Th7; eens. intros; apply Ht1 in H0; AppC H0; tauto. }
  assert (Htp : Base cB X cT).
  { red; andG; auto; [|intros; AppC H; tauto]. intros A Ha.
    pose proof Hbb _ _ Ha Ha. rewrite IdemI in H; auto. }
  split; auto. intros cT1 Htp1. pose proof Htp1 as [Ht1 _]. AppE.
  - pose proof Htp1 as [_ [Hbs _]]. AppC H; destruct H as [_ [cBu []]].
    subst. apply Ht1. eapply IncTran; eauto.
  - apply Ht1 in H as Ha; AppC Ha. apply Htp1 in H. AppCG; eens.
Qed.

(* 6.8 SubBases *)
Theorem Theorem8 : ∀ X cS, Ensemble X → cS ⊂ cP(X) → X = ∪cS →
  exists! cT, SubBase cS X cT.
Proof.
  intros * Hxe Hs Heq. set (cB :=
    \{λ U, ∃ cN, ⦿ cN ∧ Finite cN ∧ cN ⊂ cS ∧ U = ⋂cN\}).
  assert (Hg0 : cB ⊂ cP(X)).
  { intros A Ha. AppCG; Ens. AppC Ha; destruct Ha as [cN [[B Hb] [_ []]]].
    rewrite H0. intros x Hx. AppC Hx. apply H in Hb as Hb'.
    apply Hs in Hb'; pow Hb'. } assert (Hg1 : ∪cB = X).
  { apply IncAsym; [|subst; apply EleUSub, NeFiSuP1].
    intros x Hx; eleU Hx. AppC H0; destruct H0 as [cN [[B Hb] [_ []]]].
    rewrite H1 in H. AppC H. apply H0 in Hb as Hb'.
    apply Hs in Hb'; pow Hb'. }
  assert (Hg2 : ∀ B1 B2, B1 ∈ cB → B2 ∈ cB → ∀ x, x ∈ B1 ∩ B2 →
    ∃ B, B ∈ cB ∧ x ∈ B ∧ B ⊂ B1 ∩ B2).
  { intros * Hb1 Hb2 * Hx. AppC Hb1; AppC Hb2. destruct Hb1 as
      [cN1 [He1 [Hf1 [Hs1 Hb1]]]], Hb2 as [cN2 [He2 [Hf2 [Hs2 Hb2]]]].
    exists (⋂ (cN1 ⋃ cN2)). subst B1 B2. andG.
    - destruct He1 as [A]. AppCG. apply EleIEns, EmptyNE; exists A; ens.
      exists (cN1 ⋃ cN2). andG; auto. exists A; ens.
      apply un_finite; auto. intros B Hb; unH; auto.
    - inH. AppCG; Ens. intros. AppC H; AppC H0. unH; auto.
    - intros y Hy; AppCG; Ens.
      andG; AppCG; Ens; intros; AppC Hy; apply Hy; ens. }
  pose proof Theorem7 _ _ Hxe Hg0 Hg1 Hg2 as [cT [Hb Hbp]].
  assert (Hbs : SubBase cS X cT). { split. apply Hb. andG; auto.
    eapply IncTran. apply NeFiSuP1. apply Hb. } exists cT.
  split; auto. intros. destruct H as [_ [_ H]]. apply Hbp in H; auto.
Qed.