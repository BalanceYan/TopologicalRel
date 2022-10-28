(* 3 Set theory *)

Require Import Classical.
Require Import Coq.Logic.Epsilon.

(* symbol *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope.
Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : type_scope.
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'λ' x .. y ']' , '/' t ']'").

Notation "x ∧ y" := (x /\ y)
  (at level 80, right associativity) : type_scope.
Notation "x ∨ y" := (x \/ y)
  (at level 85, right associativity) : type_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Ltac PreandH := match goal with H : ?a ∧ ?b |- _ => destruct H end.
Ltac andH := repeat PreandH.

Ltac PreandG := match goal with |- ?a ∧ ?b => split end.
Ltac andG := repeat PreandG.

Ltac PreorH := match goal with H : ?a ∨ ?b |- _ => destruct H end.
Ltac orH := repeat PreorH.

(* Some logic *)
(* Axiom classic : ∀ P, P ∨ ~P. *)
Ltac DC P := destruct (classic P).

Fact classicT : ∀ P, {P} + {~P}.
Proof.
  intros. assert {x : bool | if x then P else ~P}.
  { apply constructive_indefinite_description.
    DC P; [exists true|exists false]; auto. } destruct H, x; auto.
Qed.

(* Logical property *)
Proposition NNPP : ∀ P, (~(~P) ↔ P).
Proof. intros; DC P; tauto. Qed.

Proposition inp : ∀ P Q : Prop, (P ↔ Q) → (~P → ~Q).
Proof. intros; intro. pose proof H1. elim H0. apply H; auto. Qed.

(* Class *)
Parameter Class : Type.

(* Two primitive(undefined) constants *)
Parameter In : Class → Class → Prop.
Notation "a ∈ A" := (In a A)(at level 70).
Notation "a ∉ A" := (~(a ∈ A))(at level 70).

Parameter Classifier : ∀ P : Class → Prop, Class.
Notation "\{ P \}" := (Classifier P)(at level 0).

Axiom ExtAx : ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.
Ltac AppE := apply ExtAx; split; intros.

Definition Ensemble x := ∃ y, x ∈ y.
Ltac Ens := unfold Ensemble; eauto.
Ltac AssE x := assert (Ensemble x); Ens.

Axiom ClaAx : ∀ x P, x ∈ \{P\} ↔ Ensemble x ∧ P x.
Ltac AppCG := apply ClaAx; split; eauto.
Ltac AppC H := apply ClaAx in H as [_ H]; eauto.

Definition NoEmpty A := ∃ x, x ∈ A.
Notation "⦿ A" := (NoEmpty A) (at level 45).

Definition Empty := \{ λ x, x ≠ x \}.
Notation " ∅ " := Empty.

Fact EmptyNI : ∀ x, x ∉ ∅.
Proof. intros x H. AppC H. Qed.
Hint Resolve EmptyNI : Ens_hint.
Ltac exfalso0 := exfalso; eapply EmptyNI; eauto.

Fact EmptyEq : ∀ x, x = ∅ ↔ ~ (⦿ x).
Proof.
  split; intros. subst x. intros [x H]. exfalso0.
  AppE. elim H. exists x0; auto. exfalso0.
Qed.

Fact EmptyNE : ∀ x, x ≠ ∅ ↔ ⦿ x.
Proof.
  intros. pose proof EmptyEq. split; intros.
  apply (inp _ (~(⦿ x))) in H; auto. apply -> NNPP in H; auto.
  intro; apply H in H0; auto.
Qed.

Definition μ := \{ λ x, x = x \}.
Fact UniveI : ∀ x, Ensemble x → x ∈ μ.
Proof. intros. AppCG. Qed.
Hint Immediate UniveI : Ens_hint.

Ltac ens := auto with Ens_hint.
Ltac eens := eauto with Ens_hint.

Definition Singleton x := \{ λ z, x ∈ μ → z = x \}.
Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Fact SingI : ∀ x, Ensemble x → ∀ y, y = x → y ∈ [x].
Proof. intros. subst. AppCG. Qed.
Hint Resolve SingI : Ens_hint.

Fact SingE : ∀ x, Ensemble x → ∀ y, y ∈ [x] → y = x.
Proof. intros. AppC H0; ens. Qed.
Ltac sing H := apply SingE in H; try (subst; eauto).

Fact SingNI : ∀ x y, Ensemble y → x ≠ y → x ∉ [y].
Proof. intros * Hx Hn H. apply Hn. sing H. Qed.

Fact SingNE : ∀ x y, Ensemble x → y ∉ [x] → y ≠ x.
Proof. intros * Hx Hy Heq. apply Hy. ens. Qed.

Definition Included A B := ∀ x, x ∈ A → x ∈ B.
Notation "A ⊂ B" := (Included A B)(at level 70).

Definition ProperSub A B := A ⊂ B ∧ A ≠ B.
Notation "A ⊊ B" := (ProperSub A B)(at level 70).

Axiom SubAx : ∀ x, Ensemble x → ∃ y, Ensemble y ∧ (∀z, z ⊂ x → z ∈ y).

Fact SubAxP : ∀ x, Ensemble x → ∀ z, z ⊂ x → Ensemble z.
Proof. intros. apply SubAx in H as [y []]. Ens. Qed.
Hint Resolve SubAxP : Ens_hint.

Fact EmptySub : ∀ A, ∅ ⊂ A.
Proof. intros A x Hx. exfalso0. Qed.

Fact IncRef : ∀ A, A ⊂ A.
Proof. intros * x; auto. Qed.

Fact IncAsym : ∀ A B, A ⊂ B → B ⊂ A → A = B.
Proof. intros. AppE; auto. Qed.

Fact IncTran : ∀ A B C, A ⊂ B → B ⊂ C → A ⊂ C.
Proof. intros * Ha Hb x Hx. auto. Qed.
Hint Resolve IncRef IncAsym IncTran : Ens_hint.

Definition PowerSet X := \{λ A, A ⊂ X \}.
Notation " cP( X )" := (PowerSet X)(at level 9, right associativity).

Fact PowerI : ∀ X, Ensemble X → ∀ Y, Y ⊂ X → Y ∈ cP(X).
Proof. intros. AppCG. eens. Qed.

Fact PowerE : ∀ X Y, Y ∈ cP(X) → Y ⊂ X.
Proof. intros. AppC H. Qed.
Ltac pow H := apply PowerE in H; eauto.

Fact PowerEns : ∀ X, Ensemble X → Ensemble cP(X).
Proof.
  intros. apply SubAx in H as [B [Hbe Hb]].
  assert (cP(X) ⊂ B). { intros z Hz. pow Hz. } eens.
Qed.
Hint Resolve PowerI PowerEns : Ens_hint.

Fact UniveEns : ~Ensemble μ.
Proof.
  set \{λ x, x ∉ x\} as R. assert (~Ensemble R).
  { DC (R ∈ R). pose proof H; AppC H. intro; elim H; AppCG. }
  assert (R ⊂ μ). intros z Hz. AssE z; ens. intro; eens.
Qed.

Fact SingEns : ∀ x, Ensemble x → Ensemble [x].
Proof.
  intros. assert ([x] ⊂ cP(x)). { intros z Hz. sing Hz. ens. }
  apply PowerEns in H; eens.
Qed.

Fact SingEns' : ∀ x, Ensemble [x] → Ensemble x.
Proof.
  intros. DC (Ensemble x); auto. assert ([x] = μ).
  { apply (inp _ (x ∈ μ)) in H0. AppE; AssE x0. ens. AppCG.
    intro; tauto. split; ens. intro; Ens. }
  rewrite H1 in H. pose proof UniveEns. tauto.
Qed.
Hint Resolve SingEns SingEns' : Ens_hint.

Definition Union A B := \{λ x, x ∈ A ∨ x ∈ B\}.
Notation "A ⋃ B" := (Union A B)(at level 65, right associativity).

Fact UnionI : ∀ x A, x ∈ A → ∀ B, x ∈ A ⋃ B.
Proof. intros. AppCG; Ens. Qed.

Fact UnionI' : ∀ x B, x ∈ B → ∀ A, x ∈ A ⋃ B.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve UnionI UnionI' : Ens_hint.

Fact UnionE : ∀ x A B, x ∈ A ⋃ B → x ∈ A ∨ x ∈ B.
Proof. intros. AppC H. Qed.

Ltac PreunH := match goal with H : ?c ∈ ?a ⋃ ?b
  |- _ => apply UnionE in H as [] end.
Ltac unH := repeat PreunH.

Ltac PreunG := match goal with
  |- ?c ∈ ?a ⋃ ?b => apply UnionI end.
Ltac unG := repeat PreunG.

Fact UnionNE : ∀ x A B, x ∉ A ⋃ B → x ∉ A ∧ x ∉ B.
Proof. intros. split; intro; ens. Qed.

Axiom UnionAx : ∀ x y, Ensemble x → Ensemble y → Ensemble (x ⋃ y).

Fact UnionEns : ∀ x y, Ensemble (x ⋃ y) → Ensemble x ∧ Ensemble y.
Proof.
  intros. assert (x ⊂ x ⋃ y ∧ y ⊂ x ⋃ y).
  split; intros z Hz; ens. andH. split; eens.
Qed.

Definition Inter A B := \{λ x, x ∈ A ∧ x ∈ B\}.
Notation "A ∩ B" := (Inter A B)(at level 60, right associativity).

Fact InterI : ∀ x A B, x ∈ A → x ∈ B → x ∈ A ∩ B.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve InterI : Ens_hint.

Fact InterE : ∀ x A B, x ∈ A ∩ B → x ∈ A ∧ x ∈ B.
Proof. intros. AppC H. Qed.

Ltac PreinH := match goal with H : ?c ∈ ?a ∩ ?b
  |- _ => apply InterE in H as [] end.
Ltac inH := repeat PreinH.

Ltac PreinG := match goal with
  |- ?c ∈ ?a ∩ ?b => apply InterI end.
Ltac inG := repeat PreinG.

Fact InterEns : ∀ x y, Ensemble x → Ensemble y → Ensemble (x ∩ y).
Proof.
  intros. assert (x ∩ y ⊂ x). intros z Hz. AppC Hz; tauto. eens.
Qed.

Axiom RegAx : ∀ x, x ≠ ∅ → ∃ y, y ∈ x ∧ x ∩ y = ∅.

Fact RegAxP : ∀ x, x ∉ x.
Proof.
  intros * Hp. AssE x. assert (x ∈ ([x] ∩ x)); ens. assert ([x] ≠ ∅).
  { apply EmptyNE. exists x; ens. } apply RegAx in H1 as [y []].
  sing H1. rewrite H2 in H0. exfalso0.
Qed.

Definition Setmin A B := \{λ x, x ∈ A ∧ x ∉ B\}.
Notation "A - B" := (Setmin A B).

Fact SetminI : ∀ x A B, x ∈ A → x ∉ B → x ∈ A - B.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve SetminI : Ens_hint.

Fact SetminE : ∀ x A B, x ∈ A - B → x ∈ A ∧ x ∉ B.
Proof. intros. AppC H. Qed.

Ltac PresmH := match goal with H : ?c ∈ ?a - ?b
  |- _ => apply SetminE in H as [] end.
Ltac smH := repeat PresmH.

Ltac PresmG := match goal with
  |- ?c ∈ ?a - ?b => apply SetminI end.
Ltac smG := repeat PresmG.

Fact SetminNI : ∀ x A X, x ∈ A → x ∉ X - A.
Proof. intros * Hx Hs. smH; tauto. Qed.

Fact SetminId : ∀ X, X - X = ∅.
Proof. intro. AppE. smH; tauto. exfalso0. Qed.

Fact SetminEm : ∀ X, X - ∅ = X.
Proof. intro. AppE. smH; tauto. ens. Qed.

Fact SetminEq : ∀ A B X, A = B → X - A = X - B.
Proof. intros. subst. auto. Qed.

Fact SetminSubI : ∀ A X, X - A ⊂ X.
Proof. intros * x Hx. smH; tauto. Qed.

Fact split_one_elem : ∀ A a, a ∈ A → A = (A - [a]) ⋃ [a].
Proof.
  intros. AppE; [|unH; smH; auto; sing H0; Ens].
  DC (x = a). subst; AssE a; ens. apply SingNI in H1; Ens; ens.
Qed.

Fact SetminEns : ∀ x, Ensemble x → ∀ y, Ensemble (x - y).
Proof. intros. pose proof (SetminSubI y x). eens. Qed.
Hint Resolve UnionAx InterEns SetminEns : Ens_hint.

Definition Disjoint A B := A ∩ B = ∅.

Fact DisjointI : ∀ A B, (~ ∃ x, x ∈ A ∧ x ∈ B) → Disjoint A B.
Proof. intros. AppE. inH; elim H; eauto. exfalso0. Qed.

Fact DisjointE : ∀ A B x, Disjoint A B → x ∈ A → x ∈ B → False.
Proof. intros. assert (x ∈A ∩ B); ens. rewrite H in H2; exfalso0. Qed.

Fact UnionSub : ∀ A B, B ⊂ A → A ⋃ B = A.
Proof. intros. AppE. unH; auto. ens. Qed.

Fact InterSub : ∀ A B, A ⊂ B → A ∩ B = A.
Proof. intros. AppE; [inH|inG]; auto. Qed.

Fact UnionSetmin: ∀ A B, A ⋃ (B - A) = A ⋃ B.
Proof. intros. AppE. unH; ens. smH; ens. unH; ens. DC (x ∈ A); ens. Qed.

Fact InterSetmin : ∀ A B X, B ⊂ X → B ∩ X - A = ∅ → B ⊂ A.
Proof.
  intros * Hs Hp z Hz. assert (z ∉ X - A).
  { intro. assert (z ∈ B ∩ X - A); ens. rewrite Hp in H0; exfalso0. }
  DC(z ∈ A); auto. elim H; ens.
Qed.

Fact InterEqEmI : ∀ x U A, Ensemble x →
  U ∩ A - [x] = ∅ → x ∉ A → U ∩ A = ∅.
Proof.
  intros. assert (A - [x] = A). { AppE. smH; tauto.
  assert (x0 ∉ [x]). intro; sing H3. ens. } rewrite H2 in H0; auto.
Qed.

Fact InterEqEmE : ∀ x U A, U ∩ A = ∅ → U ∩ A - [x] = ∅.
Proof.
  intros. AppE; [|exfalso0]. inH. smH.
  assert (x0 ∈ U ∩ A); ens. rewrite H in H3; exfalso0.
Qed.

Fact SetminSub : ∀ A B X, A ⊂ X → A - B ⊂ X.
Proof. intros * Ha z Hz. smH; auto. Qed.

Fact SetminSub1 : ∀ A B C, A ⊂ B → A - C ⊂ B - C.
Proof. intros * Hab z Hz. smH; ens. Qed.

Fact SetminSub2 : ∀ A B X, A ⊂ B → X - B ⊂ X - A.
Proof. intros * Hab z Hz. smH; ens. Qed.

Fact IdemU : ∀ A, A ⋃ A = A.
Proof. intros. AppE. unH; auto. ens. Qed.

Fact IdemI : ∀ A, A ∩ A = A.
Proof. intros. AppE; inH; ens. Qed.

Fact CommuU : ∀ A B, A ⋃ B = B ⋃ A.
Proof. intros. AppE; unH; ens. Qed.

Fact CommuI : ∀ A B, A ∩ B = B ∩ A.
Proof. intros. AppE; inH; ens. Qed.

Fact AssocU : ∀ A B C, (A ⋃ B) ⋃ C = A ⋃ (B ⋃ C).
Proof. intros. AppE; unH; ens. Qed.

Fact AssocI : ∀ A B C, (A ∩ B) ∩ C = A ∩ (B ∩ C).
Proof. intros. AppE; inH; ens. Qed.

Fact DistribuU : ∀ A B C, (A ∩ B) ⋃ C = (A ⋃ C) ∩ (B ⋃ C).
Proof. intros. AppE. unH; inH; ens. inH; unH; ens. Qed.

Fact DistribuI : ∀ A B C, (A ⋃ B) ∩ C = (A ∩ C) ⋃ (B ∩ C).
Proof. intros. AppE. inH; unH; ens. unH; inH; ens. Qed.

Fact TwoDMU : ∀ A B C, A - (B ⋃ C) = (A - B) ∩ (A - C).
Proof.
  intros. AppE. smH; inG; ens. inH; smH. smG; auto. intro; unH; auto.
Qed.

Fact TwoDMI : ∀ A B C, A - (B ∩ C) = (A - B) ⋃ (A - C).
Proof.
  intros. AppE. smH; DC (x ∈ C); ens. unG; ens.
  unH; smH; smG; auto; intro; inH; auto.
Qed.

Fact DistribuLI : ∀ A B C, A ∩ (B ⋃ C) = A ∩ B ⋃ A ∩ C.
Proof.
  intros. rewrite CommuI, DistribuI,
    CommuI, (CommuI A C); auto.
Qed.

Fact DistribuLU : ∀ A B C, A ⋃ (B ∩ C) = (A ⋃ B) ∩ (A ⋃ C).
Proof.
  intros. rewrite CommuU, DistribuU,
    CommuU, (CommuU C A); auto.
Qed.

Fact IncInteq : ∀ A B : Class, A ⊂ B → A ∩ B = A.
Proof. intros. AppE. inH; auto. ens. Qed.

Fact EmptyU : ∀ A, A ⋃ ∅ = A.
Proof. intros. AppE. unH; auto. exfalso0. ens. Qed.

Fact EmptyI : ∀ A, A ∩ ∅ = ∅.
Proof. intros. AppE. inH; auto. exfalso0. Qed.

Fact IncU : ∀ A X, A ⊂ X → A ⋃ X = X.
Proof. intros. AppE. unH; auto. ens. Qed.

Fact IncI : ∀ A X, A ⊂ X → A ∩ X = A.
Proof. intros. AppE. inH; auto. ens. Qed.

Fact UnionCompl : ∀ A B X, A ⊂ X → B ⊂ X →
  X - (A ⋃ B) = X - A ∩ X - B.
Proof. intros. rewrite TwoDMU; auto. Qed.

Fact InterCompl : ∀ A B X, A ⊂ X → B ⊂ X →
  X - (A ∩ B) = X - A ⋃ X - B.
Proof. intros. rewrite TwoDMI; auto. Qed.

Fact TwoCompl : ∀ A X, A ⊂ X → X - (X - A) = A.
Proof.
  intros. AppE. smH. DC (x ∈ A); auto. elim H1; ens.
  smG; auto. intro; smH; auto.
Qed.

Definition EleU x := \{λ z, ∃ y, z ∈ y ∧ y ∈ x\}.
Notation "∪ x" := (EleU x)(at level 66).

Fact EleUI : ∀ x y z, x ∈ y → y ∈ z → x ∈ ∪z.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve EleUI : Ens_hint.

Fact EleUE : ∀ x z, x ∈ ∪z → ∃ y, x ∈ y ∧ y ∈ z.
Proof. intros. AppC H. Qed.
Ltac eleU H := apply EleUE in H as [? []]; eauto.

Axiom EleUAx : ∀ x, Ensemble x → Ensemble (∪x).
Hint Resolve EleUAx : Ens_hint.

Axiom InfAx : ∃ y, Ensemble y ∧ ∅ ∈ y ∧ (∀ x, x ∈ y → (x ⋃ [x]) ∈ y).

Fact EmptyEns : Ensemble ∅.
Proof. destruct InfAx as [x [_ [He _]]]; Ens. Qed.
Hint Resolve EmptyEns : Ens_hint.

Fact EleUEm : ∪∅ = ∅.
Proof. AppE; [|exfalso0]. eleU H; exfalso0. Qed.

Fact EleUSin : ∀ x, Ensemble x → ∪[x] = x.
Proof. intros. AppE. eleU H0; sing H1. eens. Qed.

Fact EleUEleSub : ∀ A B, A ∈ B → A ⊂ ∪B.
Proof. intros * Ha x Hx. eens. Qed.

Fact EleUSub: ∀ A B, A ⊂ B → ∪A ⊂ ∪B.
Proof. intros * H x Hx. eleU Hx. eens. Qed.

Fact EleUTwoUn : ∀ a b, ∪(a ⋃ b) = (∪a) ⋃ (∪b).
Proof. intros. AppE. eleU H; unH; eens. unH; eleU H; eens. Qed.

Fact IntSinEm : ∀ A B C, Ensemble C →
  A ∈ [C] ⋃ [∅] → B ∈ [C] ⋃ [∅] → A ∩ B ∈ [C] ⋃ [∅].
Proof.
  intros. unH; sing H0; sing H1; ens; try (rewrite EmptyI); ens;
  [rewrite IdemI|rewrite CommuI, EmptyI]; ens.
Qed.

Fact EleUSinEm : ∀ a T, Ensemble a → T ⊂ [a] ⋃ [∅] → ∪T ∈ [a] ⋃ [∅].
Proof.
  intros * Hae Ht. assert (Hte : Ensemble T).
  { assert (Ensemble ([a] ⋃ [∅])). ens. eens. }
  assert (T ∈ cP([a] ⋃ [∅])). eens.
  assert (∀ c d, Ensemble c → Ensemble d → cP([c] ⋃ [d]) =
    \{ λ Z, Z = ∅ ∨ Z = [c] ∨ Z = [d] ∨ Z = [c] ⋃ [d] \}).
  { intros. AppE.
    - AppCG; Ens. pow H2. DC (c ∈ x); DC (d ∈ x);
      [right; right; right|right; left|right; right; left|left].
      + apply IncAsym; auto; intros z Hz; unH; sing H5.
      + AppE; [|sing H5]; AppCG; Ens;
        assert (H5' := H5); apply H2 in H5; unH; sing H5; tauto.
      + AppE; [|sing H5]. AppCG; Ens.
        assert (H5' := H5); apply H2 in H5; unH; sing H5; tauto.
      + AppE; [|exfalso0].
        assert (H5' := H5); apply H2 in H5; unH; sing H5; tauto.
    - AppCG; Ens. intros z Hz. AppC H2.
      orH; subst; [exfalso0| | |auto]; ens. }
  rewrite H0 in H; ens. AppC H; orH; subst; try rewrite EleUSin; eens.
  rewrite EleUEm; ens. assert (∪[a]⋃[∅] = a).
  { rewrite EleUTwoUn, EleUSin, EleUSin, EmptyU; ens. }
  rewrite H; ens.
Qed.

Definition EleI x := \{λ z, ∀ y, y ∈ x → z ∈ y\}.
Notation "⋂ x" := (EleI x)(at level 66).

Fact EleISin : ∀ x, Ensemble x → ⋂[x] = x.
Proof.
  intros. AppE. AppC H0; apply H0; ens. AppCG; Ens. intros; sing H1.
Qed.
Hint Immediate EleUSin EleISin : Ens_hint.

Fact EleIEle : ∀ A B, A ∈ B → ⋂B ⊂ A.
Proof. intros. intros x Hx. AppC Hx. Qed.

Fact EleIEns : ∀ cA, cA ≠ ∅ → Ensemble (⋂cA).
Proof.
  intros. apply EmptyNE in H as [A]. apply EleIEle in H as H'.
  assert (Ensemble A). Ens. eens.
Qed.
Hint Resolve EleIEns : Ens_hint.

Definition AAr A B := \{λ z, ∃ Ar, Ar ∈ B ∧ z = A - Ar\}.
Fact AArP : ∀ A B, Ensemble A → B ≠ ∅ → AAr A B ≠ ∅.
Proof.
  intros. apply EmptyNE in H0 as [Ar]. apply EmptyNE.
  exists (A - Ar). AppCG. eens.
Qed.

Fact DeMorganUI : ∀ A B, Ensemble A → B ≠ ∅ → (A - ∪B) = ⋂AAr A B.
Proof.
  intros. AppE. smH; AppCG; Ens. intros. AppC H3.
  destruct H3 as [C [Hc Heq]]; subst; eens.
  apply EmptyNE in H0 as [Ar]. AppC H1. assert (A - Ar ∈ AAr A B).
  AppCG; eens. apply H1 in H2. smH. smG; auto. intro; eleU H4.
  assert (A - x0 ∈ AAr A B). AppCG; eens. apply H1 in H6; smH; auto.
Qed.

Fact DeMorganIU : ∀ A B, Ensemble A → (A - ⋂B) = ∪(AAr A B).
Proof.
  intros. AppE. smH; AppCG; Ens. DC (∃ Ar, Ar ∈ B ∧ x ∉ Ar).
  destruct H2 as [Ar [Har Harn]]; exists (A - Ar); andG; [|AppCG]; eens.
  elim H1; AppCG; Ens; intros; DC (x ∈ y); auto; elim H2; eauto.
  eleU H0. AppC H1; destruct H1 as [r [Hr Heq]]; subst; smH.
  smG; auto; intro; AppC H2.
Qed.

Definition Unorder x y := [x] ⋃ [y].
Notation "[ x | y ] " := (Unorder x y) (at level 0).

Fact UnordIE : ∀ x y, Ensemble x → Ensemble y →
  ∀ z, z ∈ [x|y] ↔ z = x ∨ z = y.
Proof.
  intros. unfold Unorder. split; intros. unH; sing H1. orH; subst; ens.
Qed.

Fact UnordEns : ∀ x y, Ensemble x → Ensemble y → Ensemble [x|y].
Proof. intros. unfold Unorder. ens. Qed.
Hint Resolve UnordEns : Ens_hint.

Fact unord1 : ∀ x y, Ensemble x → Ensemble y → ∪[x|y] = x ⋃ y.
Proof.
  intros. unfold Unorder. AppE. eleU H1; unH; sing H2; ens.
  unH; eapply EleUI; eauto; ens.
Qed.

Fact unord2 : ∀ x y, Ensemble x → Ensemble y → ⋂[x|y] = x ∩ y.
Proof.
  intros. unfold Unorder. AppE. AppC H1; ens.
  inH. AppCG; Ens. intros. unH; sing H3.
Qed.

Definition Order x y := [ [x] | [x | y] ].
Notation "[ x , y , .. , z ]" :=
  (Order .. (Order x y ) .. z ) (z at level 69).

Fact OrdEns : ∀ x y, Ensemble x → Ensemble y → Ensemble [x,y].
Proof. intros. unfold Order. ens. Qed.

Fact OrdEns0 : ∀ x y, Ensemble [x,y] → Ensemble x ∧ Ensemble y.
Proof.
  intros. apply UnionEns in H as [].
  apply SingEns', UnionEns in H0 as []; ens.
Qed.

Fact OrdEns1 : ∀ x y, Ensemble [x,y] → Ensemble x.
Proof. intros. apply OrdEns0 in H; tauto. Qed.

Fact OrdEns2 : ∀ x y, Ensemble [x,y] → Ensemble y.
Proof. intros. apply OrdEns0 in H; tauto. Qed.

Fact OrdEns3 : ∀ x y, Ensemble [x,y] → Ensemble [y,x].
Proof. intros. apply OrdEns0 in H as []. apply OrdEns; auto. Qed.
Hint Resolve OrdEns OrdEns3 : Ens_hint.

Ltac orde1 := match goal with H : Ensemble [?x,?y]
  |- Ensemble ?x => eapply OrdEns1; eauto end.
Ltac orde2 := match goal with H : Ensemble [?x,?y]
  |- Ensemble ?y => eapply OrdEns2; eauto end.
Ltac orde := try orde1; try orde2.

Fact ord1 : ∀ x y, Ensemble x → Ensemble y → ∪[x,y] = [x|y].
Proof.
  intros. unfold Order. rewrite unord1; ens.
  AppE; ens. unH; unfold Unorder; ens.
Qed.

Fact ord2 : ∀ x y, Ensemble x → Ensemble y → ⋂[x,y] = [x].
Proof.
  intros. unfold Order. rewrite unord2; ens.
  AppE. inH; auto. unfold Unorder; ens.
Qed.

Fact ord3 : ∀ x y, Ensemble x → Ensemble y → ∪(⋂[x,y]) = x.
Proof. intros. rewrite ord2; ens. Qed.

Fact ord4 : ∀ x y, Ensemble x → Ensemble y → ⋂(⋂[x,y]) = x.
Proof. intros. rewrite ord2; ens. Qed.

Fact ord5 : ∀ x y, Ensemble x → Ensemble y → ∪(∪[x,y]) = x ⋃ y.
Proof. intros. rewrite ord1, unord1; ens. Qed.

Fact ord6 : ∀ x y, Ensemble x → Ensemble y → ⋂(∪[x,y]) = x ∩ y.
Proof. intros. rewrite ord1, unord2; ens. Qed.

Definition π1 z := ⋂⋂z.
Definition π2 z := (⋂∪z)⋃(∪∪z)-(∪⋂z).

Fact ordFis : ∀ x y, Ensemble x → Ensemble y → π1 [x,y] = x.
Proof. intros. apply ord4; ens. Qed.

Fact ordSec : ∀ x y, Ensemble x → Ensemble y → π2 [x,y] = y.
Proof.
  intros. unfold π2. rewrite ord6, ord5, ord3; ens.
  assert ((x ⋃ y) - x = y - x). { AppE; smH; ens. unH. tauto. ens. }
  rewrite H1, CommuI. AppE; [|DC (x0 ∈ x); ens].
  unH. inH; auto. smH; auto.
Qed.
Hint Rewrite ordFis ordSec : ord_hint.
Ltac ordrewrite := autorewrite with ord_hint in *; try congruence.

Fact ordEq : ∀ x y a b, Ensemble x → Ensemble y →
  [x,y] = [a,b] ↔ x = a ∧ y = b.
Proof.
  split; intros; [|destruct H1; subst; auto]. assert (Ensemble [x,y]).
  eens. rewrite H1 in H2. apply OrdEns0 in H2 as [].
  rewrite <- (ordFis x y), H1, <- (ordSec x y), H1, ordFis, ordSec; auto.
Qed.

Fact ordNEq : ∀ x y a b, Ensemble x → Ensemble y →
  [x,y] ≠ [a,b] ↔ x ≠ a ∧ y ≠ b ∨ x ≠ a ∧ y = b ∨ x = a ∧ y ≠ b.
Proof.
  intros * Hx Hy. split; intro.
  - DC (x = a); [|DC (y = b); [right|]; left; auto]. right; right.
    andG; auto. intro. assert ([x,y] = [a,b]). subst; auto. auto.
  - orH; andH; intro; apply ordEq in H1; andH; auto.
Qed.

Notation " \{\ P \}\ " :=
  \{λ z, ∃ x y, z = [x,y] ∧ P x y \}(at level 0).
Ltac PP H a b := apply ClaAx in H as [_ [a [b [? H]]]]; subst; eauto.

Fact ClaAx' : ∀ x y P, [x,y] ∈ \{\P\}\ ↔ Ensemble [x,y] ∧ (P x y).
Proof.
  split; intros. AssE [x,y]. PP H a b. apply ordEq in H1 as []; orde.
  subst; auto. destruct H; AppCG; eauto.
Qed.
Ltac AppCG' := apply ClaAx'; split; eauto.
Ltac AppC' H := apply ClaAx' in H as [_ H]; eauto.

Definition Cartesian X Y := \{\ λ x y, x ∈ X ∧ y ∈ Y\}\.
Notation " X × Y " := (Cartesian X Y)(at level 2, right associativity).

Fact CProdI : ∀ A B a b, a ∈ A → b ∈ B → [a,b] ∈ A × B.
Proof. intros * Ha Hb. AppCG'. apply OrdEns; Ens. Qed.
Hint Resolve CProdI : Ens_hint.

Fact CProdE : ∀ A B a b, [a,b] ∈ A × B → a ∈ A ∧ b ∈ B.
Proof. intros. AppC' H. Qed.
Ltac cprod H := apply CProdE in H as []; eauto.

Definition Relation R X Y := R ⊂ X × Y.
Definition relation R := ∀ z, z ∈ R → ∃ x y, z = [x,y].

Definition Image A R := \{λ y, ∃ x, x ∈ A ∧ [x,y] ∈ R\}.
Notation "R \( A \) " := (Image A R)(at level 5).

Fact ImageI : ∀ x A, x ∈ A → ∀ y R, [x,y] ∈ R → y ∈ R\(A\).
Proof. intros. AssE [x,y]. AppCG; orde. Qed.

Fact ImageE : ∀ y A R, y ∈ R\(A\) → ∃ x, x ∈ A ∧ [x,y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac image H := apply ImageE in H as [? []]; eauto.

Fact ImageEns : ∀ R X Y, Ensemble Y → R ⊂ X × Y → ∀ A, Ensemble R\(A\).
Proof.
  intros. assert (R\(A\) ⊂ Y).
  { intros y Hy. image Hy. apply H0 in H2. cprod H2. } eens.
Qed.
Hint Resolve ImageI ImageEns : Ens_hint.

Definition Range R := \{λ y, ∃ x, [x,y] ∈ R\}.
Notation " ran( R )" := (Range R)(at level 5).

Fact ranI : ∀ R x y, [x,y] ∈ R → y ∈ ran(R).
Proof. intros. AssE [x,y]. AppCG; orde. Qed.
Hint Resolve ranI : Ens_hint.

Fact ranE : ∀ R y, y ∈ ran(R) → ∃ x, [x,y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac ran H := apply ranE in H as [?]; eauto.

Fact RanSub : ∀ R A, R\(A\) ⊂ ran(R).
Proof. intros * y Hy. image Hy. eens. Qed.

Definition Inverse R := \{\λ y x, [x,y] ∈ R \}\.
Notation "R ⁻¹" := (Inverse R)(at level 5).

Fact InverI : ∀ F x y, [x,y] ∈ F → [y,x] ∈ F⁻¹.
Proof. intros. AssE [x,y]. AppCG'; ens. Qed.
Hint Resolve InverI : Ens_hint.

Fact InverE : ∀ F x y, [y,x] ∈ F⁻¹ → [x,y] ∈ F.
Proof. intros. AppC' H. Qed.
Ltac inver H := apply InverE in H; eauto.

Fact inv_inv : ∀ F, relation F → (F⁻¹)⁻¹ = F.
Proof.
  intros. AppE. AppC H0; destruct H0 as [a [b []]]. subst.
  apply InverE; auto. pose proof H0; apply H in H0 as [a [b Heq]].
  subst; apply InverI, InverI; auto.
Qed.

Definition OrigImage B R := \{λ x, ∃ y, y ∈ B ∧ [x,y] ∈ R\}.

Fact OriImI : ∀ y B, y ∈ B → ∀ x R, [x,y] ∈ R → x ∈ OrigImage B R.
Proof. intros. AssE [x,y]. AppCG; orde. Qed.
Hint Resolve OriImI : Ens_hint.

Fact OriImE : ∀ x B R, x ∈ OrigImage B R → ∃ y, y ∈ B ∧ [x,y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac oriim H := apply OriImE in H as [? []]; eauto.

Definition Domain R := \{λ x, ∃ y, [x,y] ∈ R\}.
Notation " dom( R )" := (Domain R)(at level 5).

Fact domI : ∀ R x y, [x,y] ∈ R → x ∈ dom(R).
Proof. intros. AssE [x,y]. AppCG; orde. Qed.
Hint Resolve domI : Ens_hint.

Fact domE : ∀ R x, x ∈ dom(R) → ∃ y, [x, y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac dom H := apply domE in H as [?]; eauto.

Fact domInv : ∀ R, dom(R⁻¹) = ran(R).
Proof.
  intros. AppE; [apply domE in H as [y Hp]|apply ranE in H as [w Hp]].
  apply InverE in Hp. eens. eens.
Qed.

Fact ranInv : ∀ R, ran(R⁻¹) = dom(R).
Proof. intros. AppE; [ran H|dom H]. inver H; eens. eens. Qed.

Definition Composition R S : Class :=
  \{\ λ x z, ∃ y, [x,y] ∈ R ∧ [y,z] ∈ S \}\.
Notation "S ∘ R" := (Composition R S) (at level 50, no associativity).

Fact CompoI : ∀ R S x y t, [x,t] ∈ S → [t,y] ∈ R → [x,y] ∈ (R∘S).
Proof. intros. AssE [x,t]; AssE [t,y]. AppCG'. apply OrdEns; orde. Qed.
Hint Resolve CompoI : Ens_hint.

Fact CompoE : ∀ R S x y, [x,y] ∈ (R∘S) → ∃ t, [x,t] ∈ S ∧ [t,y] ∈ R.
Proof. intros. AppC' H. Qed.
Ltac compo H := apply CompoE in H as [? []]; eauto.

Definition IdenR X := \{\λ x y, x ∈ X ∧ y ∈ X ∧ x = y \}\.
Notation "∆ ( X )" := (IdenR X)(at level 5).

Fact IdentI : ∀ X a, a ∈ X → [a,a] ∈ ∆(X).
Proof. intros * Ha. AssE a. AppCG'; ens. Qed.
Hint Resolve IdentI : Ens_hint.

Fact IdentE : ∀ a b X, [a,b] ∈ ∆(X) → a ∈ X ∧ a = b.
Proof. intros. AppC' H; tauto. Qed.
Ltac ident H := apply IdentE in H as []; subst; eauto.

Fact IdentDom : ∀ X, dom(∆(X)) = X.
Proof. intros. AppE; eens. dom H. ident H. Qed.

Fact IdentRan : ∀ X, ran(∆(X)) = X.
Proof. intros. AppE; eens. ran H. ident H. Qed.

Definition Function f :=
  relation f ∧ ∀ x y z, [x,y] ∈ f ∧ [x,z] ∈ f → y = z.

Axiom RepAx : ∀ f, Function f → Ensemble dom(f) → Ensemble ran(f).
Hint Resolve RepAx : Ens_hint.

Fact CProdEns0 : ∀ u y, Ensemble u → Ensemble y → Ensemble ([u] × y).
Proof.
  intros. set \{\λ w z, w ∈ y ∧ z = [u,w]\}\ as f.
  assert (Function f ∧ dom(f) = y ∧ ran(f) = [u] × y).
  { andG. split. intros z Hz; PP Hz a b. intros * [].
    AppC' H1; AppC' H2; andH. subst; auto.
    - AppE. dom H1; AppC' H1; tauto. AssE x; eapply domI; AppCG; eens.
    - AppE. ran H1; AppC' H1; andH. subst; ens. PP H1 a b; andH.
      sing H1. AssE b. AppCG; ens. exists b. AppCG'; eens. }
  andH. rewrite <- H2 in H0. rewrite <- H3. ens.
Qed.

Fact CProdEns : ∀ x y, Ensemble x → Ensemble y → Ensemble x × y.
Proof.
  intros. set \{\λ u z, u ∈ x ∧ z = [u] × y\}\ as f.
  assert (Function f ∧ dom(f) = x ∧
    ran(f) = \{λ z, ∃ u, u ∈ x ∧ z = [u] × y\}).
  { repeat split. intros z Hz; PP Hz a b.
    intros * []; AppC' H1; AppC' H2; andH. subst; auto.
    - AppE. dom H1. AppC' H1; tauto. AssE x0; eapply domI; AppCG'.
      apply OrdEns; auto. apply CProdEns0; auto.
    - AppE. ran H1; AppC' H1; andH; subst. AssE x1; AppCG.
      apply CProdEns0; auto. AppC H1. destruct H1; andH. subst. AssE x1.
      eapply ranI; AppCG. apply OrdEns; auto. apply CProdEns0; auto. }
  assert (∪ran(f) = x × y).
  { AppE. eleU H2; ran H3; AppC' H3; destruct H3. AssE x2; subst.
    PP H2 a b; destruct H2; sing H2; ens. pose proof H2. PP H2 a b; andH.
    AssE a; AppCG; Ens. exists [a] × y. split; ens. eapply ranI.
    AppCG'; eauto; ens. apply OrdEns; auto. apply CProdEns0; auto. }
  andH. rewrite <- H2. rewrite <- H3 in H. ens.
Qed.
Hint Resolve CProdEns : Ens_hint.

Definition Mapping F X Y := Relation F X Y ∧
  (∀ x, x ∈ X → (∃ y, [x,y] ∈ F)) ∧
  (∀ x y1 y2, [x,y1] ∈ F → [x,y2] ∈ F → y1 = y2 ).

Definition Value F x := ⋂\{λ y, [x,y] ∈ F\}.
Notation "F [ x ]" := (Value F x)(at level 5).

Fact ValueEns :∀ f x, x ∈ dom(f) → Ensemble f[x].
Proof.
  intros. unfold Value. assert (\{λ y, [x,y] ∈ f\} ≠ ∅).
  { dom H. apply EmptyNE. exists x0. AssE [x,x0]. AppCG; orde. } ens.
Qed.

Fact ValueP : ∀ f X Y, Mapping f X Y → ∀ x, x ∈ X → [x,f[x]] ∈ f.
Proof.
  intros * [Hr [He Hu]] * Hx. apply He in Hx as [y]. assert (y = f[x]).
  { AssE [x,y]. AppE. AppCG; Ens. intros; AppC H2. assert (y = y0).
    eapply Hu; eauto. subst; auto. AppC H1; apply H1; AppCG; orde. }
  subst; auto.
Qed.
Hint Resolve ValueEns ValueP : Ens_hint.

Fact ValueP1 : ∀ f X Y, Mapping f X Y → ∀ x, x ∈ X → f[x] ∈ Y.
Proof. intros. assert ([x,f[x]] ∈ f). eens. apply H in H1. cprod H1. Qed.

Fact ValueP2 : ∀ f X Y,
  Mapping f X Y → ∀ x y, x ∈ X → [x,y] ∈ f → y = f[x].
Proof. intros. eapply H; eens. Qed.
Hint Resolve ValueP1 ValueP2 : Ens_hint.

Fact MapOri : ∀ f X Y, Mapping f X Y → ∀ B, OrigImage B f ⊂ X.
Proof. intros * Hf * x Hx. oriim Hx. apply Hf in H0. cprod H0. Qed.

Fact MapOriIm : ∀ B f X Y, Mapping f X Y → f\(OrigImage B f\) ⊂ B.
Proof.
  intros * Hf x Hx. image Hx. oriim H. assert (x = x1).
  eapply Hf; eauto. subst; auto.
Qed.

Fact MapOriSm : ∀ B f X Y, Mapping f X Y →
  OrigImage (Y - B) f = X - OrigImage B f.
Proof.
  intros * Hf. AppE.
  - oriim H. smH; smG. pose proof H0 as Hc. apply Hf in H0; cprod H0.
    intro. oriim H2. assert (x0 = x1). eapply Hf; eauto. subst; auto.
  - smH. eapply OriImI; [|eapply ValueP; eauto]. smG. eapply ValueP1;
    eauto. intro. elim H0. eapply OriImI; eauto. eapply ValueP; eauto.
Qed.

Fact Mapping1 : ∀ F G X Y Z,
  Mapping F X Y → Mapping G Y Z → Relation (G∘F) X Z.
Proof.
  intros * Hf Hg c Hc. PP Hc x z; destruct Hc; andH.
  apply Hf in H; cprod H. apply Hg in H0; cprod H0. eens.
Qed.

Fact Mapping5 : ∀ F X Y, Mapping F X Y → dom(F) = X.
Proof. intros. AppE; eens. dom H0. apply H in H0. cprod H0. Qed.

Fact Mapping6 : ∀ F X Y, Mapping F X Y → ran(F) = F\(X\).
Proof.
  intros. AppE; [|image H0; eens]. ran H0. assert (x0 ∈ X).
  apply H in H0; cprod H0. eens.
Qed.

Fact CompoMap : ∀ F G X Y Z,
  Mapping F X Y → Mapping G Y Z → Mapping (G ∘ F) X Z.
Proof.
  intros. repeat split; intros. eapply Mapping1; eauto.
  apply H in H1 as [y]; apply H in H1 as Hxy; cprod Hxy; eens.
  compo H1. compo H2. assert (x0 = x1). eapply H; eauto.
  subst. eapply H0; eauto.
Qed.

Definition FullM f X Y := Mapping f X Y ∧ f\(X\) = Y.

Definition Restriction f A := \{\λ a b, [a,b] ∈ f ∧ a ∈ A\}\.
Notation "f ↾ A" := (Restriction f A)(at level 30).

Fact RestrI : ∀ f a b A, [a,b] ∈ f → a ∈ A → [a,b] ∈ f↾A.
Proof. intros. AppCG'; Ens. Qed.
Hint Resolve RestrI : Ens_hint.

Fact RestrE : ∀ f A a b, [a,b] ∈ f↾A → [a,b] ∈ f ∧ a ∈ A.
Proof. intros. AppC' H. Qed.
Ltac restr H := apply RestrE in H as []; eauto.

Fact RestrDom : ∀ F A, dom(F↾A) ⊂ dom(F).
Proof. intros * x H. dom H. restr H. eens. Qed.

Fact RestrM : ∀ f X Y, Mapping f X Y → ∀ A, A ⊂ X → Mapping (f↾A) A Y.
Proof.
  intros. split; [|split; intros; eens]. intros z Hz; PP Hz a b; andH.
  apply H in H1; cprod H1; ens. restr H1; restr H2; eapply H; eauto.
Qed.

Fact RestrValue : ∀ f X Y, Mapping f X Y → ∀ A, A ⊂ X →
  ∀ a, a ∈ A → f[a] = (f↾A)[a].
Proof.
  intros. AppE; AppCG; Ens; AppC H2; intros; AssE y;
  AppC H3; [restr H3|]; apply H2; AppCG; ens.
Qed.

Definition MarkFam φ Γ := \{\λ γ A, γ ∈ Γ ∧ A = φ[γ]\}\.
Definition MarkFamU φ Γ := \{λ x, ∃ γ, γ ∈ Γ ∧ x ∈ φ[γ]\}.
Definition MarkFamI φ Γ := \{λ x, ∀ γ, γ ∈ Γ → x ∈ φ[γ]\}.

Fact MarFamUIEq : ∀ f Γ cA, FullM f Γ cA →
  MarkFamU f Γ = ∪cA ∧ MarkFamI f Γ = ⋂cA.
Proof.
  intros * [H Heq]. andG.
  - AppE; AppCG; Ens. AppC H0; destruct H0 as [n []];
    exists f[n]; andG; eens. eleU H0; rewrite <- Heq in H1; image H1.
    exists x1; andG; auto. erewrite <- ValueP2; eauto.
  - AppE; AppCG; Ens; AppC H0; intros. rewrite <- Heq in H1; image H1.
    apply H0 in H1 as Hx. erewrite ValueP2; eauto.
    apply H0; rewrite <- Heq; eens.
Qed.

Definition neSub X := cP(X) - [∅].
Notation " X ^ " := (neSub X) (at level 0).

Fact neSubEm : ∅^ = ∅.
Proof.
  unfold neSub. AppE; [|exfalso0]. smH. pow H. assert (x ≠ ∅).
  { intro. subst. ens. } elim H1. AppE. auto. exfalso0.
Qed.

Definition ChoiceF ε X := Mapping ε X^ X ∧ ∀ A, A ∈ X^ → ε[A] ∈ A.

Axiom ChoiceAx : ∀ X, ∃ ε, ChoiceF ε X.

Fact ChoAx : ∀ cA, ∅ ∉ cA →
  (∃ ν, Mapping ν cA (∪cA) ∧ (∀ A, A ∈ cA → ν[A] ∈ A )).
Proof.
  intros * Hn. set (X := ∪cA). assert (cA ⊂ X^).
  { intros A Ha. AppCG; andG; Ens. AppCG; Ens.
    intros x Hx; AppCG; Ens. intro; sing H; ens. }
  pose proof (ChoiceAx X) as [ε [Hf Hp]]. set (ν := ε↾cA).
  exists ν. andG. eapply RestrM; eauto. intros. assert (ε[A] = ν[A]).
  eapply RestrValue; eauto. rewrite <- H1. apply Hp. auto.
Qed.

Fact ChoAx1 : ∀ U P, Ensemble P → (∀ x, x ∈ U → ∃ y, [x,y] ∈ P) →
  ∃ f, Mapping f U \{λ z, ∃ x, x ∈ U ∧ [x,z] ∈ P\} ∧
  (∀ x, x ∈ U → [x,f[x]] ∈ P).
Proof.
  intros * Hpe Hp. DC (U = ∅).
  - subst. set (\{\λ u v, u ∈ ∅\}\) as f. exists f. andG; [split|].
    intros z Hz; PP Hz a b; exfalso0. andG. intros; exfalso0.
    intros; AppC' H0; exfalso0. intros; exfalso0.
  - set (\{λ Y, ∃ x, x ∈ U ∧ Y = \{λ y, [x,y] ∈ P\} \}) as cA.
    assert (Hp1 : ∅ ∉ cA). { intro He. AppC He; destruct He as
      [x [Hx Hm]], (Hp _ Hx) as [y Hxy].
    AssE [x,y]; apply OrdEns2 in H0. assert (y ∈ ∅).
    rewrite Hm; AppCG. exfalso0. }
    assert (Hxf : ∀ x, x ∈ U → \{λ y, [x,y] ∈ P\} ∈ cA).
    { intros. AppCG. set \{\ λ a b, ∃ x, [x,b] ∈ P ∧ a = [x,b]\}\ as f.
      assert (\{λ y, [x, y] ∈ P \} ⊂ ran(f)).
      { intros y Hy. AssE y; AppC Hy. AppCG. exists ([x,y]).
        AppCG'. apply OrdEns; Ens. }
      eapply SubAxP; revgoals; eauto. apply RepAx.
      - split. intros z Hz; PP Hz a b. intros * []; AppC' H2; AppC' H3.
        destruct H2, H3; andH. subst. AssE [x1,y].
        apply OrdEns0 in H5; andH. apply ordEq in H4; tauto.
      - assert (dom(f) ⊂ P). intros z Hz. dom Hz. AppC' H2.
        destruct H2; andH. subst; auto. eens. }
    destruct (ChoAx _ Hp1) as [c [Hc Hcp]]. set \{\λ u v, u ∈ U ∧
      v = c[\{λ y, [u,y] ∈ P\}]\}\ as ν. exists ν. andG; [split; andG|].
    + intros z Hz. AssE z; PP Hz u v; andH. AppCG'. apply OrdEns2 in H0.
      andG; auto. AppCG. exists u. andG; auto.
      apply Hxf, Hcp in H1. rewrite <- H2 in H1. AppC H1.
    + intros. AssE x. exists c[\{λ y, [x,y] ∈ P\}]. AppCG'. apply OrdEns;
      auto. apply ValueEns. erewrite Mapping5; eauto.
    + intros. AppC' H0; AppC' H1; andH. subst; auto.
    + intros * Hx. pose proof Hx as Hx'; apply Hxf, Hcp in Hx. AppC Hx.
      assert (c[\{λ y, [x,y] ∈ P\}] = ν [x]).
      { AppE; AppCG; Ens; AppC H0; intros * Hy; apply H0; AppCG; Ens.
        - AppC Hy. AppC' Hy; andH. subst y. eapply ValueP; eauto.
        - AppCG'; andG; auto. apply OrdEns; Ens. AppC Hy.
          eapply ValueP2; eauto. } rewrite <- H0; auto.
Qed.

(* Concepts in Elements of Set Theory *)
Definition PRelation P A B := \{\λ x y, [x,y] ∈ A × B ∧ P x y\}\.

Fact PRelI : ∀ x y A B (P : Class → Class → Prop),
  [x,y] ∈ A × B → P x y → [x,y] ∈ PRelation P A B.
Proof. intros. AppCG. Ens. Qed.
Hint Resolve PRelI : Ens_hint.

Fact PRelE : ∀ x y A B P,
  [x,y] ∈ PRelation P A B → [x,y] ∈ A × B ∧ P x y.
Proof. intros. AppC' H. Qed.
Ltac prel H := apply PRelE in H as []; eauto.

Definition exu (P : Class → Prop) :=
  (∃ x, P x) ∧ (∀ x y, P x → P y → x = y).
Notation "∃! x , P" := (exu (λ x, P)) (at level 200, x ident).

Definition is_function F :=
  relation F ∧ ∀ x, x ∈ dom(F) → ∃! y, [x,y] ∈ F.

Fact funcfunR : ∀ f, is_function f ↔ Function f.
Proof.
  split; intros; destruct H; split; auto.
  - intros * []. eapply H0; eauto; eens.
  - intros. split. dom H1. intros; eapply H0; eauto.
Qed.

Fact func_ap : ∀ F x y, is_function F → [x,y] ∈ F → F[x] = y.
Proof.
  intros * Hf Hp. AssE [x,y]. AppE. AppC H0; apply H0; AppCG; orde.
  AppCG; Ens. intros. AppC H1. assert (y=y0).
  eapply Hf; eens. subst; auto.
Qed.

Fact func_dom : ∀ F x, is_function F → x ∈ dom(F) → [x,F[x]] ∈ F.
Proof.
  intros * Hf Hx. dom Hx. apply func_ap in H as Hap; auto. subst; auto.
Qed.
Hint Resolve func_ap func_dom : Ens_hint.

Fact restr_func : ∀ F A, is_function F → is_function (F↾A).
Proof.
  intros. split. intros r Hr; PP Hr a b. intros. split. dom H0; auto.
  intros y1 y2 H1 H2. AppC' H1; AppC' H2. andH; eapply H; eens.
Qed.

Fact restr_dom : ∀ F A, is_function F → A ⊂ dom(F) ↔ dom(F↾A) = A.
Proof.
  intros * Hf. split; intros; [|rewrite <- H; apply RestrDom].
  AppE. dom H0; AppC' H0. tauto. eens.
Qed.

Fact ident_func : ∀ A, is_function ∆(A).
Proof.
  repeat split. intros x Hx; PP Hx a b. dom H.
  intros y1 y2 Hy1 Hy2. ident Hy1; ident Hy2.
Qed.

Fact compo_func : ∀ F G,
  is_function F → is_function G → is_function (F∘G).
Proof.
  repeat split. intros x Hx; PP Hx a b. dom H1.
  intros y1 y2 Hy1 Hy2. compo Hy1; compo Hy2. assert (x0 = x1).
  eapply H0; eens. subst. eapply H; eens.
Qed.

Definition single_rooted F := ∀ y, y ∈ ran(F) → ∃! x, [x,y] ∈ F.

Fact singrootE : ∀ F, single_rooted F → is_function F⁻¹.
Proof.
  intros. split; intros x Hx. PP Hx a b. split. dom Hx.
  intros. inver H0; inver H1. eapply H; eens.
Qed.

Fact singrootE1 : ∀ F a b c, single_rooted F →
  [a,c] ∈ F → [b,c] ∈ F → a = b.
Proof.
  intros.  apply ranI in H0 as Hr. apply H in Hr as [_ Hu]. auto.
Qed.

Fact singroot_ident : ∀ A, single_rooted (∆(A)).
Proof. split. ran H. intros. ident H0; ident H1. Qed.

Fact inv_func_iff_sr : ∀ F, is_function F⁻¹ ↔ single_rooted F.
Proof.
  intro. split; intros.
  - split. ran H0. intros. apply InverI in H1; apply InverI in H2.
    eapply H; eauto. eens.
  - split. intros p Hp. PP Hp a b. split. dom H0. intros.
    inver H1; inver H2. eapply H; [rewrite <- domInv|..]; eauto.
Qed.

Fact inv_sr_iff_func : ∀ F,
  (relation F ∧ single_rooted F⁻¹) ↔ is_function F.
Proof.
  split; intros; split; try apply H. split. dom H0.
  intros; eapply H; eens. intros y Hy. ran Hy. split; eauto.
  intros. inver H1; inver H2. eapply H; eens.
Qed.

Definition injective F := is_function F ∧ single_rooted F.

Fact injectiveE : ∀ F, injective F →
  ∀ a b, a ∈ dom(F) → b ∈ dom(F) → F[a] = F[b] → a = b.
Proof.
  intros * [Hf Hs] * Ha Hb H. apply func_dom in Ha; auto.
  apply func_dom in Hb; auto. rewrite H in Ha. eapply Hs; eens.
Qed.

Fact inv_dom_reduction : ∀ F, injective F →
  ∀ x, x ∈ dom(F) → F⁻¹[F[x]] = x.
Proof.
  intros * [Hf Hs] * Hx. apply func_dom in Hx; auto.
  apply func_ap; ens. apply inv_func_iff_sr; auto.
Qed.

Fact inv_ran_reduction : ∀ F, injective F →
  ∀ y, y ∈ ran(F) → F[F⁻¹[y]] = y.
Proof.
  intros * [Hf Hs] y Hy. rewrite <- domInv in Hy. cut (injective F⁻¹).
  intros Hi. pose proof (inv_dom_reduction F⁻¹ Hi y Hy).
  rewrite inv_inv in H; [|apply Hf]; auto.
  split; [apply inv_func_iff_sr|apply inv_sr_iff_func]; auto.
Qed.

Fact restr_injective : ∀ F, injective F → ∀ A, injective (F↾A).
Proof.
  intros * [Hf Hs]. split. apply restr_func; auto. split. ran H.
  intros x x1 H1 H2. restr H1; restr H2. eapply Hs; eens.
Qed.

Fact em_injective : injective ∅.
Proof.
  split. red; andG. intros x Hx; exfalso0. split. dom H.
  intros; exfalso0. split. ran H. intros; exfalso0.
Qed.

Fact ident_injective : ∀ A, injective ∆(A).
Proof. split. apply ident_func. apply singroot_ident. Qed.

Fact compo_injective: ∀ F G, injective F → injective G → injective (F∘G).
Proof.
  intros * [Hff Hsf] [Hfg Hsg]. split. apply compo_func; auto.
  intros y Hy. split. ran Hy. intros. compo H; compo H0.
  assert (x0 = x1). eapply Hsf; eens. subst. eapply Hsg; eens.
Qed.

Fact domInv_reduction : ∀ F, injective F →
  ∀ x, x ∈ dom(F) → F⁻¹[F[x]] = x.
Proof.
  intros * [Hf Hs] * Hx. apply func_ap; eens. apply singrootE; auto.
Qed.

Fact compo_ran : ∀ F G, injective F → is_function G →
  ran(F∘G) = \{λ x, x ∈ ran(F) ∧ F⁻¹[x] ∈ ran(G)\}.
Proof.
  intros * [Hf Hs] Hg. AppE; AssE x.
  - ran H; compo H. AppCG. split; eens. apply InverI, func_ap in H1.
    subst; eens. apply singrootE; auto.
  - AppC H; andH. ran H; ran H1. apply InverI in H as H'.
    assert ((F⁻¹)[x] = x0). apply singrootE in Hs; eens. subst; eens.
Qed.

Fact sm_func : ∀ f g,
  is_function f → is_function g → is_function (f - g).
Proof.
  intros * Hf Hg. repeat split. intros z Hz; smH; apply Hf in H; auto.
  dom H. dom H; intros y1 y2 Hy1 Hy2; smH; eapply Hf; eens.
Qed.

Fact sm_injective : ∀ f g, injective f → injective g → injective (f - g).
Proof.
  intros * [Hf Hfs] [Hg Hgs]. split. apply sm_func; auto.
  intros y Hy. split. ran Hy. intros x1 x2 H1 H2; smH. eapply Hfs; eens.
Qed.

Fact bunion_func : ∀ f g, is_function f → is_function g →
  (∀ x, x ∈ dom(f) ∩ dom(g) → f[x] = g[x]) ↔ is_function (f ⋃ g).
Proof.
  intros * Hf Hg. split; intros.
  - repeat split. intros x Hx; unH; [apply Hf in H0|apply Hg in H0]; auto.
    dom H0. intros y1 y2 H1 H2. unH.
    + apply domI in H1 as Hfd. apply Hf in Hfd. apply Hfd; auto.
    + apply domI in H1 as Hfd; apply domI in H2 as Hgd.
      apply func_ap in H1; apply func_ap in H2; auto. assert (f[x]=g[x]).
      apply H; inG; auto. congruence.
    + apply domI in H1 as Hfd; apply domI in H2 as Hgd.
      apply func_ap in H1; apply func_ap in H2; auto. assert (f[x]=g[x]).
      apply H; inG; auto. rewrite <- H1, <- H2; auto.
    + apply domI in H1 as Hgd. apply Hg in Hgd. apply Hgd; auto.
  - inH. apply func_dom in H0; apply func_dom in H1; auto.
    eapply H. eapply domI; unG; eauto. unG; auto. apply UnionI'; auto.
Qed.

Fact bunion_injective : ∀ f g, injective f → injective g →
  ((∀ x, x ∈ dom(f) ∩ dom(g) → f[x] = g[x]) ∧
  (∀ y, y ∈ ran(f) ∩ ran(g) → f⁻¹[y] = g⁻¹[y])) ↔ injective (f ⋃ g).
Proof.
  intros * [Hf Hfs] [Hg Hgs]. split.
  - intros [Hreq Hdeq]. split. apply bunion_func; auto.
    intros y Hy. split. ran Hy. intros x1 x2 H1 H2.
    unH; [eapply (singrootE1 f)| | |eapply (singrootE1 g)]; eauto.
    + assert ((f⁻¹)[y] = (g⁻¹)[y]). apply Hdeq; inG; eapply ranI; eauto.
      apply InverI in H; apply InverI in H0.
      apply func_ap in H. apply func_ap in H0. congruence.
      apply inv_func_iff_sr; auto. apply inv_func_iff_sr; auto.
    + assert ((f⁻¹)[y] = (g⁻¹)[y]). apply Hdeq; inG; eapply ranI; eauto.
      apply InverI in H; apply InverI in H0.
      apply func_ap in H. apply func_ap in H0. congruence.
      apply inv_func_iff_sr; auto. apply inv_func_iff_sr; auto.
  - intros [Hu Hus]. andG. apply bunion_func; auto. intros y Hy. inH.
    ran H; ran H0. apply InverI in H; apply InverI in H0.
    apply func_ap in H as H1. apply func_ap in H0 as H2. subst.
    eapply singrootE1; [apply Hus|unG|apply UnionI']; apply InverE; eauto.
    apply inv_func_iff_sr; auto. apply inv_func_iff_sr; auto.
Qed.

Definition maps_into F A B := is_function F ∧ dom(F) = A ∧ ran(F) ⊂ B.
Notation "F : A => B" := (maps_into F A B) (at level 60).

Definition maps_onto F A B := is_function F ∧ dom(F) = A ∧ ran(F) = B.
Notation "F : A ==> B" := (maps_onto F A B) (at level 60).

Definition injection F A B :=
  injective F ∧ dom(F) = A ∧ ran(F) ⊂ B.
Notation "F : A <=> B" := (injection F A B) (at level 60).

Definition bijection F A B := injective F ∧ dom(F) = A ∧ ran(F) = B.
Notation "F : A <==> B" := (bijection F A B) (at level 60).

Corollary MapMapR : ∀ F A B, Mapping F A B → maps_into F A B.
Proof.
  intros; pose proof H as [Hr [He Ht]]. split; split. intros z Hz.
  apply H in Hz; PP Hz a b. intros; split. dom H0. intros; eens.
  eapply Mapping5; eauto. intros z Hz. ran Hz. apply H in H0. cprod H0.
Qed.

Corollary MapMapR1 : ∀ F A B, maps_into F A B → Mapping F A B.
Proof.
  intros; pose proof H as [Hr [He Ht]]. split. intros z Hz.
  pose proof Hz. apply Hr in Hz as [x [y Hz]]. subst; eens.
  split; intros. subst; dom H0. eapply Hr; eens.
Qed.

Fact ap_ran : ∀ A B F, maps_into F A B → ∀ x, x ∈ A → F[x] ∈ B.
Proof. intros. eapply ValueP1; eauto. apply MapMapR1; auto. Qed.
Hint Resolve ap_ran : Ens_hint.

Fact compo_maps_into : ∀ F G A B C,
  maps_into F A B → maps_into G B C → maps_into (G∘F) A C.
Proof.
  intros. apply MapMapR1 in H. apply MapMapR1 in H0.
  apply MapMapR. eapply CompoMap; eauto.
Qed.

Fact injection_is_func : ∀ F A B,
  injection F A B ↔ maps_into F A B ∧ injective F.
Proof.
  split. intros [Hi [Hd Hr]]. split; auto. destruct Hi. split; auto.
  intros [[_ [Hd Hr]] Hi]. split; auto.
Qed.

Fact compo_injection : ∀ F G A B C, injection F A B →
  injection G B C → injection (G ∘ F) A C.
Proof.
  intros * Hf Hg. apply injection_is_func. split.
  - eapply compo_maps_into; apply injection_is_func; eauto.
  - destruct Hf, Hg. apply compo_injective; auto.
Qed.

Fact bijection_is_func : ∀ F A B,
  bijection F A B ↔ maps_into F A B ∧ injective F ∧ ran(F) = B.
Proof.
  split. intros [Hi [Hd Hr]]. split; auto. destruct Hi.
  split; subst; ens. intros [[Hf [Hd _]] [Hi Hr]]. split; auto.
Qed.

Fact bijection_is_injection : ∀ F A B,
  bijection F A B ↔ injection F A B ∧ ran(F) = B.
Proof.
  split. intros [Hi [Hd Hr]]. split;[split;[|split]|]; subst; ens.
  intros [[Hi [Hd Hr]] Heq]. split; auto.
Qed.

Fact ident_bijective : ∀ A, bijection  ∆(A) A A.
Proof.
  intros. split. apply ident_injective.
  split. apply IdentDom. apply IdentRan.
Qed.

Fact inv_bijection : ∀ F A B, bijection F A B → bijection F⁻¹ B A.
Proof.
  intros * [[Hf Hs] [Hd Hr]]. split; [| rewrite domInv, ranInv; auto].
  split. apply singrootE; auto. apply inv_sr_iff_func; auto.
Qed.

Fact empty_bijective : ∀ F A, bijection F A ∅ → A = ∅.
Proof.
  intros * [Hi [Hd Hr]]. AppE; [|exfalso0]. subst A.
  dom H; apply ranI in H. rewrite Hr in H; exfalso0.
Qed.

Fact compo_bijection : ∀ F G A B C,
  bijection F A B → bijection G B C → bijection (G∘F) A C.
Proof.
  intros * Hf Hg. apply bijection_is_injection in Hf as [Hf Hfr].
  apply bijection_is_injection in Hg as [Hg Hgr].
  apply bijection_is_injection. split. eapply compo_injection; eauto.
  rewrite compo_ran; [|destruct Hg as []|destruct Hf as [[]]]; auto.
  AppE. AppC H; andH. subst; auto. destruct Hg as [[Hfg Hsg] [Hdg _]].
  AppCG; Ens. subst. andG; auto. rewrite <- Hdg, <- ranInv. eapply ranI.
  apply func_dom. apply singrootE; auto. rewrite domInv; auto.
Qed.

Fact single_ord_is_func : ∀ a b,
  Ensemble a → Ensemble b → is_function ([[a,b]]).
Proof.
  intros. repeat split. intros x Hx; sing Hx; ens. dom H1.
  intros y1 y2 Hy1 Hy2. sing Hy1; ens. sing Hy2; ens.
  symmetry in Hy1, Hy2. apply ordEq in Hy1; auto.
  apply ordEq in Hy2; auto. andH. subst; auto.
Qed.

Fact single_ord_injective : ∀ a b,
  Ensemble a → Ensemble b → injective ([[a,b]]).
Proof.
  intros. split. apply single_ord_is_func; auto. split. ran H1.
  intros x1 x2 Hx1 Hx2. sing Hx1; ens.  sing Hx2; ens.
  symmetry in Hx1, Hx2. apply ordEq in Hx1; auto.
  apply ordEq in Hx2; auto. andH. subst; auto.
Qed.

Fact dom_of_single_ord : ∀ a b,
  Ensemble a → Ensemble b → dom([[a,b]]) = [a].
Proof.
  intros. AppE. dom H1. sing H1; ens. symmetry in H1.
  apply ordEq in H1; auto; andH; ens. sing H1. eapply domI; ens.
Qed.

Fact ran_of_single_ord : ∀ a b,
  Ensemble a → Ensemble b → ran([[a,b]]) = [b].
Proof.
  intros. AppE. ran H1. sing H1; ens. symmetry in H1.
  apply ordEq in H1; auto; andH; ens. sing H1. eapply ranI; ens.
Qed.

Fact single_ord_bijective : ∀ a b,
  Ensemble a → Ensemble b → bijection ([[a,b]]) ([a]) ([b]).
Proof.
  intros. split. apply single_ord_injective; auto. andG;
  [apply dom_of_single_ord|apply ran_of_single_ord]; auto.
Qed.

Fact func_sm_point : ∀ f A B a, maps_into f A B → a ∈ A →
  (∀ x, x ∈ A → x ≠ a → f[x] ≠ f[a]) →
  maps_into (f - [[a,f[a]]]) (A - [a]) (B - [f[a]]).
Proof.
  intros * [Hf [Hd Hr]] Ha Hp. assert (Hb : f[a] ∈ B).
  { apply Hr. subst. apply func_dom in Ha; eens. } AssE a; AssE f[a].
  rename H into Hae; rename H0 into Hbe.
  pose proof (single_ord_bijective a f[a] Hae Hbe) as [[Hf' _] [Hd' Hr']].
  assert (Hfs : is_function (f - [[a,f[a]]])).
  { apply sm_func; auto. } split; [|split]; auto.
  - AppE.
    + dom H. smH. smG. rewrite <- Hd; eens. apply SingNE in H0; ens.
      apply SingNI; auto. AssE [x,x0]; apply OrdEns0 in H1; andH.
      apply ordNEq in H0; auto. orH; andH; auto.
      apply func_ap in H; auto. subst; auto.
    + smH. apply SingNE in H0; auto. rewrite <- Hd in H; dom H.
      AssE [x,x0]; apply OrdEns0 in H1; andH. eapply domI. smG; eauto.
      apply SingNI; ens. apply ordNEq; auto. apply func_ap in H; auto.
      subst x0. DC (f[x] = f[a]); [right|]; left; auto.
  - intros y Hy. ran Hy. smH. smG. apply Hr; eens. apply SingNE in H0;
    ens. apply SingNI; auto. AssE [x,y]; apply OrdEns0 in H1; andH.
    apply func_ap in H as Hy; auto; subst y. apply ordNEq in H0; auto.
    orH; andH; auto. apply Hp; auto. subst; eens.
Qed.

Fact bijection_sm_point : ∀ f A B a, bijection f A B → a ∈ A →
  (∀ x, x ∈ A → x ≠ a → f[x] ≠ f[a]) →
  bijection (f - [[a,f[a]]]) (A - [a]) (B - [f[a]]).
Proof.
  intros * [Hf [Hd Hr]] Ha Hp. assert (Hb : f[a] ∈ B).
  { subst. apply func_dom in Ha; eens. apply Hf. } AssE a; AssE f[a].
  rename H into Hae; rename H0 into Hbe. assert (Hm : maps_into f A B).
  { split. apply Hf. andG; auto. rewrite Hr; ens. } pose proof
    (func_sm_point _ _ _ _ Hm Ha Hp) as [Hfu [Hud Hur]].
  pose proof (single_ord_bijective a f[a]) as [[Hs Hss] [Hsd Hsr]]; auto.
  split; [|andG]; auto. apply sm_injective; auto.
  apply single_ord_injective; auto.
  apply IncAsym; auto. intros y Hy.
  smH. rewrite <- Hr in H; ran H. apply SingNE in H0; ens. eapply ranI.
  smG; eauto. apply SingNI; ens. AssE [x,y]; apply OrdEns0 in H1; andH.
  apply ordNEq; auto. DC (x = a). right; right; auto. left; auto.
Qed.

Fact func_add_point : ∀ F A B a b, maps_into F A B →
  Ensemble a → Ensemble b → Disjoint (A) ([a]) → Disjoint (B) ([b]) →
  maps_into (F ⋃ [[a,b]]) (A ⋃ [a]) (B ⋃ [b]).
Proof.
  intros * [Hf [Hd Hr]] Hae Hbe Hdj1 Hdj2.
  pose proof (single_ord_bijective a b Hae Hbe) as [[Hf' _] [Hd' Hr']].
  split; [|split].
  - apply bunion_func; auto. intros x Hx. exfalso. inH.
    rewrite Hd in H; rewrite Hd' in H0.
    eapply DisjointE; [apply Hdj1|..]; eauto.
  - AppE. dom H; unH. apply domI in H; rewrite <- Hd; unG; auto.
    sing H; ens. symmetry in H; apply ordEq in H; andH; ens.
    unH; eapply domI; [unG|apply UnionI']; apply func_dom; auto;
    [rewrite Hd|rewrite Hd']; auto.
  - intros y Hy. ran Hy. unH. unG; apply Hr; eens.
    sing H; ens. symmetry in H; apply ordEq in H; andH; ens.
Qed.

Fact bijection_add_point : ∀ F A B a b, bijection F A B →
  Ensemble a → Ensemble b → Disjoint (A) ([a]) → Disjoint (B) ([b]) →
  bijection (F ⋃ [[a,b]]) (A ⋃ [a]) (B ⋃ [b]).
Proof.
  intros * [Hf [Hfd Hfr]] Hae Hbe Hdj1 Hdj2.
  assert (Hm : maps_into F A B).
  { split. apply Hf. andG; auto. rewrite Hfr; ens. } pose proof
    (func_add_point _ _ _ _ _ Hm Hae Hbe Hdj1 Hdj2) as [Hfu [Hud Hur]].
  pose proof (single_ord_bijective a b) as [[Hs Hss] [Hsd Hsr]]; auto.
  split; [|andG]; auto. apply bunion_injective; auto.
  apply single_ord_injective; auto. andG; intros x Hx;
  [rewrite Hfd, Hsd in Hx|rewrite Hfr, Hsr in Hx]; inH; exfalso;
  eapply DisjointE; [apply Hdj1| | |apply Hdj2|..]; eauto.
  apply IncAsym; auto. intros y Hy. unH; [rewrite <- Hfr in H|
    rewrite <- Hsr in H]; ran H; eapply ranI; [unG|apply UnionI']; eauto.
Qed.

Definition Func F A B := PRelation (λ x y, y = F x) A B.

Fact func_is_func : ∀ F A B, is_function (Func F A B).
Proof.
  intros. repeat split. intros z Hz. PP Hz a b. dom H.
  intros. prel H0; prel H1. subst; auto.
Qed.

Fact meta_dom : ∀ A B F, (∀ x, x ∈ A → F x ∈ B) → dom(Func F A B ) = A.
Proof.
  intros. AppE. dom H0; prel H0; cprod H0.
  apply H in H0 as Hr. eapply domI. apply PRelI; eens.
Qed.

Fact meta_maps_into : ∀ A B F, (∀x, x ∈ A → F x ∈ B) →
  maps_into (Func F A B) A B.
Proof.
  intros. split. apply func_is_func. split. apply meta_dom; auto.
  intros y Hy. ran Hy; prel H0; cprod H0.
Qed.

Fact meta_injective : ∀ A B F, (∀ x, x ∈ A → F x ∈ B) →
  (∀ x1 x2, x1 ∈ A → x2 ∈ A → F x1 = F x2 → x1 = x2) →
  injection (Func F A B) A B.
Proof.
  intros * Hf Hp. apply meta_maps_into in Hf as [Hf [Hd Hr]].
  split; split; auto. intros y Hy. split. ran Hy.
  intros. prel H; prel H0. cprod H; cprod H0. subst. auto.
Qed.

Fact meta_surjective : ∀ A B F, (∀ x, x ∈ A → F x ∈ B) →
  (∀ y, y ∈ B → ∃ x, x ∈ A ∧ F x = y) → maps_onto (Func F A B) A B.
Proof.
  intros * Hf Hp. apply meta_maps_into in Hf as [Hf [Hd Hr]].
  split; [|split]; auto. apply IncAsym; auto.
  intros y Hy. pose proof Hy. apply Hp in H as [x []].
  eapply ranI. apply PRelI; eens.
Qed.

Fact meta_bijective : ∀ A B F, (∀x, x ∈ A → F x ∈ B) →
  (∀ x1 x2, x1 ∈ A → x2 ∈ A → F x1 = F x2 → x1 = x2) →
  (∀ y, y ∈ B → ∃ x, x ∈ A ∧ F x = y) → bijection (Func F A B) A B.
Proof.
  intros. apply (meta_injective A B) in H0 as [Hi [Hd _]]; auto.
  apply (meta_surjective A B) in H1 as [_ [_ Hr]]; auto. red; andG; auto.
Qed.

Definition FuncSwapValue f a b :=
  Func (λ x, match classicT (x = a) with
      | left _ => f[b]
      | right _ =>
        match classicT (x = b) with
        | left _ => f[a]
        | right _ => f[x]
        end
    end) (dom(f)) (ran(f)).

Fact func_swap_value : ∀ F A B a b, a ∈ A → b ∈ A →
  maps_into F A B → let F' := FuncSwapValue F a b in
  maps_into F' A B ∧ ran(F') = ran(F).
Proof.
  intros * Ha Hb [Hf [Hd Hr]] F'. assert (Hreq: ran(F') = ran(F)).
  { AppE. ran H; AppC' H; andH; cprod H.
    assert (H' := H). ran H. apply domI in H as Hx. AssE x.
    apply func_ap in H; auto. DC (x0 = a); [|DC (x0 = b)]; eapply ranI.
    - AssE b. AppCG'. apply OrdEns; eauto. andG. rewrite Hd; ens.
      destruct (classicT (b = a)). rewrite e, <- H1; auto.
      destruct (classicT (b = b)). subst; auto. tauto.
    - AssE a. AppCG'. apply OrdEns; eauto. andG. rewrite Hd; ens.
      destruct (classicT (a = a)); congruence.
    - AppCG'; andG; [|apply CProdI; eauto|]. apply OrdEns; Ens.
      destruct (classicT (x0 = a)). tauto.
      destruct (classicT (x0 = b)). tauto. auto. } andG; auto.
  cut (maps_into F' A ran(F)).
  { intros [Hf' [Hd' Hr']]. split; andG; auto. rewrite Hreq; auto. }
  subst F'. unfold FuncSwapValue. rewrite Hd. apply meta_maps_into.
  intros x Hx. destruct (classicT (x = a)). eapply ap_ran; eauto.
  split; andG; ens. destruct (classicT (x = b)). eapply ap_ran; eauto.
  split; andG; ens. eapply ap_ran; eauto. split; andG; ens.
Qed.

Fact injection_swap_value : ∀ F A B a b, a ∈ A → b ∈ A →
  injection F A B → let F' := FuncSwapValue F a b in
  injection F' A B ∧ ran(F') = ran(F).
Proof.
  intros * Ha Hb [Hf [Hd Hr]] F'. assert (Hmap: maps_into F A B).
  split; auto; apply Hf. apply (func_swap_value _ _ _ _ _ Ha Hb) in Hmap
    as [[Hf' [Hd' Hr']] Hreq]. andG; auto. split; split; auto.
  split. ran H. intros x1 x2 H1 H2. AppC' H1; AppC' H2; andH.
  cprod H1; cprod H0.
  destruct (classicT (x1 = a)); destruct (classicT (x2 = a));
  destruct (classicT (x1 = b)), (classicT (x2 = b)); try congruence;
  [..|eapply injectiveE; eauto; congruence]; exfalso;
  [| |apply n1| | | | |apply n]; try apply n0;
  eapply injectiveE; eauto; congruence.
Qed.

Fact bijection_swap_value : ∀ F A B a b, a ∈ A → b ∈ A →
  bijection F A B → bijection (FuncSwapValue F a b) A B.
Proof.
  intros * Ha Hb [Hf [Hd Hr]]. assert (Hmap : injection F A B).
  split; andG; subst; ens. apply (injection_swap_value _ _ _ _ _ Ha Hb)
    in Hmap as [[Hf' [Hd' Hr']] Hreq]. subst. split; andG; auto.
Qed.