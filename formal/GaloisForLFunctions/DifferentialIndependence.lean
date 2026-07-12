import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.Tactic

/-!
# Differential algebraic independence

This file supplies the field-relative notion needed by the multiple-elliptic-gamma matroid theorem.
A family is differentially algebraically independent exactly when the family of all its algebraic
jets is algebraically independent.  This avoids replacing the final theorem by the older
function-level `DifferentiallyAlgebraic` predicate over `ℂ(z)`.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The `n`th algebraic derivative of an element of a differential ring. -/
def differentialJet {K : Type*} [CommRing K] [Differential K] (n : ℕ) (x : K) : K :=
  (Differential.deriv^[n]) x

@[simp]
theorem differentialJet_zero {K : Type*} [CommRing K] [Differential K] (x : K) :
    differentialJet 0 x = x := by
  simp [differentialJet]

theorem differentialJet_add {K : Type*} [CommRing K] [Differential K]
    (m n : ℕ) (x : K) :
    differentialJet (m + n) x = differentialJet m (differentialJet n x) := by
  exact Function.iterate_add_apply Differential.deriv m n x

@[simp]
theorem differentialJet_succ {K : Type*} [CommRing K] [Differential K]
    (n : ℕ) (x : K) :
    differentialJet (n + 1) x = (differentialJet n x)′ := by
  exact Function.iterate_succ_apply' Differential.deriv n x

/-- A family in a differential field is differentially algebraically independent over `F` when
the family of all of its jets is algebraically independent over `F`. -/
def DifferentialIndependent (F : Type*) {K : Type*} [CommRing F] [CommRing K]
    [Algebra F K] [Differential K] {ι : Type*} (x : ι → K) : Prop :=
  AlgebraicIndependent F (fun p : ι × ℕ => differentialJet p.2 (x p.1))

/-- An element is differentially algebraic over `F` exactly when its full jet family is
algebraically dependent over `F`. -/
def DifferentialAlgebraicOver (F : Type*) {K : Type*} [CommRing F] [CommRing K]
    [Algebra F K] [Differential K] (x : K) : Prop :=
  ¬ DifferentialIndependent F (fun _ : Unit => x)

/-- Hypertranscendence over a differential-field base is the negation of differential
algebraicity over that base. -/
def HypertranscendentalOver (F : Type*) {K : Type*} [CommRing F] [CommRing K]
    [Algebra F K] [Differential K] (x : K) : Prop :=
  ¬ DifferentialAlgebraicOver F x

theorem hypertranscendentalOver_iff_differentialIndependent_singleton
    (F : Type*) {K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    (x : K) :
    HypertranscendentalOver F x ↔ DifferentialIndependent F (fun _ : Unit => x) := by
  simp [HypertranscendentalOver, DifferentialAlgebraicOver]

/-- Differential independence passes to an injectively indexed subfamily. -/
theorem DifferentialIndependent.comp
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {ι ι' : Type*} {x : ι → K} (hx : DifferentialIndependent F x)
    (f : ι' → ι) (hf : Function.Injective f) :
    DifferentialIndependent F (x ∘ f) := by
  let g : ι' × ℕ → ι × ℕ := fun p => (f p.1, p.2)
  have hg : Function.Injective g := by
    rintro ⟨i, n⟩ ⟨j, m⟩ h
    simp only [g, Prod.mk.injEq] at h ⊢
    exact ⟨hf h.1, h.2⟩
  unfold DifferentialIndependent at hx ⊢
  simpa only [Function.comp_apply, g] using AlgebraicIndependent.comp hx g hg

/-- Differential independence implies ordinary algebraic independence of the order-zero
coordinates. -/
theorem DifferentialIndependent.algebraicIndependent
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {ι : Type*} {x : ι → K} (hx : DifferentialIndependent F x) :
    AlgebraicIndependent F x := by
  unfold DifferentialIndependent at hx
  have h := AlgebraicIndependent.comp hx (fun i : ι => (i, 0)) (by
    intro i j h
    exact congrArg Prod.fst h)
  simpa using h

/-- A differentially independent family is faithfully indexed: two equal members have equal
indices.  In orbit applications this says that differential freeness forces the acting palette to
have trivial stabilizer on the chosen source. -/
theorem DifferentialIndependent.injective
    {F K : Type*} [CommRing F] [Nontrivial F] [CommRing K]
    [Algebra F K] [Differential K]
    {ι : Type*} {x : ι → K} (hx : DifferentialIndependent F x) :
    Function.Injective x :=
  hx.algebraicIndependent.injective

/-- Translation of every variable by a coefficient defines an automorphism of the multivariable
polynomial algebra. -/
def mvPolynomialBaseTranslation
    {R : Type*} [CommRing R] {ι : Type*} (c : ι → R) :
    MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R := by
  let f : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    MvPolynomial.bind₁ fun i => MvPolynomial.X i + MvPolynomial.C (c i)
  let g : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    MvPolynomial.bind₁ fun i => MvPolynomial.X i - MvPolynomial.C (c i)
  exact AlgEquiv.ofAlgHom f g (by
    ext i
    simp [f, g]) (by
    ext i
    simp [f, g])

@[simp]
theorem mvPolynomialBaseTranslation_X
    {R : Type*} [CommRing R] {ι : Type*} (c : ι → R) (i : ι) :
    mvPolynomialBaseTranslation c (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (c i) := by
  simp [mvPolynomialBaseTranslation]

/-- Algebraic independence is invariant under coordinatewise translation by elements of the
coefficient ring. -/
theorem AlgebraicIndependent.add_algebraMap
    {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    {ι : Type*} {x : ι → K} (hx : AlgebraicIndependent R x) (c : ι → R) :
    AlgebraicIndependent R (fun i => x i + algebraMap R K (c i)) := by
  have hpoly : AlgebraicIndependent R
      (fun i : ι => MvPolynomial.X i + MvPolynomial.C (c i)) := by
    have h := (AlgHom.algebraicIndependent_iff
      (mvPolynomialBaseTranslation c).toAlgHom
      (mvPolynomialBaseTranslation c).injective).2
      (MvPolynomial.algebraicIndependent_X ι R)
    simpa [Function.comp_def] using h
  have h := hx.aeval_of_algebraicIndependent hpoly
  simpa using h

@[simp]
theorem differentialJet_add_algebraMap
    {F K : Type*} [CommRing F] [CommRing K]
    [Algebra F K] [Differential F] [Differential K] [DifferentialAlgebra F K]
    (n : ℕ) (x : K) (c : F) :
    differentialJet n (x + algebraMap F K c) =
      differentialJet n x + algebraMap F K (differentialJet n c) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, differentialJet_succ,
        ih, map_add, deriv_algebraMap]

/-- Differential independence is preserved by coordinatewise translation by elements of the base
differential ring.  This is the exact algebraic form of rational-gauge invariance. -/
theorem DifferentialIndependent.addBase
    {F K : Type*} [CommRing F] [CommRing K]
    [Algebra F K] [Differential F] [Differential K] [DifferentialAlgebra F K]
    {ι : Type*} {x : ι → K} (hx : DifferentialIndependent F x) (c : ι → F) :
    DifferentialIndependent F (fun i => x i + algebraMap F K (c i)) := by
  unfold DifferentialIndependent at hx ⊢
  have h := AlgebraicIndependent.add_algebraMap hx
    (fun p : ι × ℕ => differentialJet p.2 (c p.1))
  simpa only [differentialJet_add_algebraMap] using h

/-- Coordinatewise base translation preserves differential independence in both directions. -/
theorem differentialIndependent_addBase_iff
    {F K : Type*} [CommRing F] [CommRing K]
    [Algebra F K] [Differential F] [Differential K] [DifferentialAlgebra F K]
    {ι : Type*} (x : ι → K) (c : ι → F) :
    DifferentialIndependent F (fun i => x i + algebraMap F K (c i)) ↔
      DifferentialIndependent F x := by
  constructor
  · intro h
    have h' := h.addBase fun i => -c i
    simpa only [map_neg, add_neg_cancel_right] using h'
  · exact fun h => h.addBase c

/-- Algebraic jets preserve addition. -/
theorem differentialJet_add_apply
    {K : Type*} [CommRing K] [Differential K] (n : ℕ) (x y : K) :
    differentialJet n (x + y) = differentialJet n x + differentialJet n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, differentialJet_succ, ih, map_add]

/-- Differential independence is preserved by adding a family whose every jet remains in the
image of the coefficient ring.  Unlike `DifferentialIndependent.addBase`, this form does not ask
the coefficient ring itself to carry a chosen differential structure. -/
theorem DifferentialIndependent.addOfJetsInBase
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {ι : Type*} {x c : ι → K} (hx : DifferentialIndependent F x)
    (hc : ∀ i n, ∃ b : F, differentialJet n (c i) = algebraMap F K b) :
    DifferentialIndependent F (fun i => x i + c i) := by
  choose b hb using hc
  unfold DifferentialIndependent at hx ⊢
  have h := AlgebraicIndependent.add_algebraMap hx (fun p : ι × ℕ => b p.1 p.2)
  simpa only [differentialJet_add_apply, hb] using h

/-- Replacing each member of a differentially independent family by any fixed derivative of that
member preserves differential independence. -/
theorem DifferentialIndependent.jetShift
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {ι : Type*} {x : ι → K} (hx : DifferentialIndependent F x) (m : ι → ℕ) :
    DifferentialIndependent F (fun i => differentialJet (m i) (x i)) := by
  let g : ι × ℕ → ι × ℕ := fun p => (p.1, p.2 + m p.1)
  have hg : Function.Injective g := by
    rintro ⟨i, n⟩ ⟨j, p⟩ h
    simp only [g, Prod.mk.injEq] at h ⊢
    rcases h with ⟨rfl, h⟩
    exact ⟨rfl, Nat.add_right_cancel h⟩
  unfold DifferentialIndependent at hx ⊢
  have h := AlgebraicIndependent.comp hx g hg
  simpa only [Function.comp_apply, g, ← differentialJet_add] using h

/-- Ordinary algebraic extension of the coefficient field preserves differential independence.
This is the algebraic part of the base-change step used in constant extension. -/
theorem DifferentialIndependent.extendScalars
    {F S K : Type*} [Field F] [Field S] [Field K]
    [Algebra F S] [Algebra S K] [Algebra F K] [IsScalarTower F S K]
    [Differential K] [Algebra.IsAlgebraic F S]
    {ι : Type*} {x : ι → K} (hx : DifferentialIndependent F x) :
    DifferentialIndependent S x := by
  unfold DifferentialIndependent at hx ⊢
  exact AlgebraicIndependent.extendScalars S hx

/-- The set of all derivatives of elements of `s`. -/
def differentialJetSet {K : Type*} [CommRing K] [Differential K] (s : Set K) : Set K :=
  {y | ∃ x ∈ s, ∃ n : ℕ, differentialJet n x = y}

/-- The differential field generated by `s`, realized as the ordinary field generated by all
jets of `s`. -/
def differentialAdjoin (F : Type*) {K : Type*} [Field F] [Field K]
    [Algebra F K] [Differential K] (s : Set K) : IntermediateField F K :=
  IntermediateField.adjoin F (differentialJetSet s)

theorem subset_differentialAdjoin (F : Type*) {K : Type*} [Field F] [Field K]
    [Algebra F K] [Differential K] (s : Set K) :
    s ⊆ differentialAdjoin F s := by
  intro x hx
  exact IntermediateField.subset_adjoin F _ ⟨x, hx, 0, by simp⟩

theorem differentialJet_mem_differentialAdjoin (F : Type*) {K : Type*}
    [Field F] [Field K] [Algebra F K] [Differential K]
    {s : Set K} {x : K} (hx : x ∈ s) (n : ℕ) :
    differentialJet n x ∈ differentialAdjoin F s :=
  IntermediateField.subset_adjoin F _ ⟨x, hx, n, rfl⟩

/-- Adding a family whose jets lie in the coefficient field does not change the embedded
differential field generated by the family. -/
theorem differentialAdjoin_addOfJetsInBase
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    {ι : Type*} (x c : ι → K)
    (hc : ∀ i n, ∃ b : F, differentialJet n (c i) = algebraMap F K b) :
    differentialAdjoin F (Set.range fun i => x i + c i) =
      differentialAdjoin F (Set.range x) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨z, ⟨i, rfl⟩, n, rfl⟩
    obtain ⟨b, hb⟩ := hc i n
    rw [differentialJet_add_apply, hb]
    exact IntermediateField.add_mem _
      (differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n)
      (IntermediateField.algebraMap_mem _ b)
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨z, ⟨i, rfl⟩, n, rfl⟩
    obtain ⟨b, hb⟩ := hc i n
    have hy := differentialJet_mem_differentialAdjoin F
      (s := Set.range fun i => x i + c i) (Set.mem_range_self i) n
    rw [differentialJet_add_apply, hb] at hy
    simpa using IntermediateField.sub_mem _ hy (IntermediateField.algebraMap_mem _ b)

/-- A field inside a differential field is derivation-closed when it contains the derivative of
each of its elements. -/
def DerivationClosed {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) : Prop :=
  ∀ ⦃x : K⦄, x ∈ L → x′ ∈ L

/-- The field generated by all jets is closed under the derivation. -/
theorem derivationClosed_differentialAdjoin
    (F : Type*) {K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] (s : Set K) :
    DerivationClosed (differentialAdjoin F s) := by
  intro x hx
  apply IntermediateField.adjoin_induction F (s := differentialJetSet s) (p := fun y _ => y′ ∈
    differentialAdjoin F s)
  · rintro y ⟨z, hz, n, rfl⟩
    rw [← differentialJet_succ]
    exact differentialJet_mem_differentialAdjoin F hz (n + 1)
  · intro c
    rw [deriv_algebraMap]
    exact IntermediateField.algebraMap_mem _ _
  · intro a b ha hb hda hdb
    rw [map_add]
    exact IntermediateField.add_mem _ hda hdb
  · intro a ha hda
    rw [Derivation.leibniz_inv]
    have hainv : a⁻¹ ∈ differentialAdjoin F s := IntermediateField.inv_mem _ ha
    have hasq : a⁻¹ ^ (2 : ℕ) ∈ differentialAdjoin F s := by
      simpa [pow_two] using IntermediateField.mul_mem _ hainv hainv
    exact IntermediateField.mul_mem _ (IntermediateField.neg_mem _ hasq) hda
  · intro a b ha hb hda hdb
    rw [Derivation.leibniz]
    exact IntermediateField.add_mem _
      (IntermediateField.mul_mem _ ha hdb) (IntermediateField.mul_mem _ hb hda)
  exact hx

/-- Minimality of differential adjunction: every derivation-closed intermediate field containing
`s` contains the field generated by all jets of `s`. -/
theorem differentialAdjoin_le
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    {s : Set K} {L : IntermediateField F K}
    (hsL : s ⊆ L) (hL : DerivationClosed L) :
    differentialAdjoin F s ≤ L := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro y ⟨x, hx, n, rfl⟩
  induction n with
  | zero => simpa using hsL hx
  | succ n ih =>
      rw [differentialJet_succ]
      exact hL ih

/-- Restrict the ambient derivation to a derivation-closed intermediate field. -/
@[reducible]
noncomputable def derivationClosedDifferential
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L) : Differential L where
  deriv :=
    { toLinearMap :=
        { toFun := fun x => ⟨x.1′, hL x.2⟩
          map_add' := fun x y => Subtype.ext (Differential.deriv.map_add x.1 y.1)
          map_smul' := fun n x => Subtype.ext (Differential.deriv.map_smul n x.1) }
      map_one_eq_zero' := Subtype.ext Differential.deriv.map_one_eq_zero
      leibniz' := fun x y => Subtype.ext (Differential.deriv.leibniz x.1 y.1) }

@[simp]
theorem derivationClosedDifferential_apply
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L) (x : L) :
    letI := derivationClosedDifferential L hL
    ((x′ : L) : K) = x.1′ :=
  rfl

/-- The differential field generated by a set inherits the ambient derivation. -/
noncomputable instance differentialAdjoin.instDifferential
    (F : Type*) {K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] (s : Set K) :
    Differential (differentialAdjoin F s) :=
  derivationClosedDifferential _ (derivationClosed_differentialAdjoin F s)

/-- Differential adjunction is a differential algebra over the base field. -/
instance differentialAdjoin.instDifferentialAlgebra
    (F : Type*) {K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] (s : Set K) :
    DifferentialAlgebra F (differentialAdjoin F s) where
  deriv_algebraMap c := by
    apply Subtype.ext
    exact deriv_algebraMap c

end

end GaloisForLFunctions
