import GaloisForLFunctions.HTGeometry.Critical.Normal.ClosureSchurValuation
import GaloisForLFunctions.HTGeometry.NonautonomousFinitePuiseuxAlgebraicEmbedding

/-!
# A compatible valuation flag on the finite nonautonomous branch field

The finite actual derivative-branch field already embeds, generator by generator on the state
field, into the algebraic closure of the generic multigraded Hahn field.  This module extends the
full lexicographic Hahn valuation ring to that algebraic closure by Krull domination and pulls the
chosen extension back to the actual finite branch field.

The contraction theorem is exact: the chosen upper valuation ring restricts to precisely the
original Hahn valuation ring.  Consequently every actual clock/state generator has exactly the
same valuation-ring membership as its prescribed Hahn coordinate.  Thus all nested state weights
live on one compatible valuation flag; no independent coordinate places are chosen.

This is the valuative compatibility part of finite branch selection.  It does not assert that the
images of the derivative branches have prescribed nonzero output-linear initial coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-! ## The valuation ring of a Hahn fraction field -/

/-- Valuation subring cut out by the full multiplicative Hahn valuation on its fraction field. -/
noncomputable def hahnFractionValuationSubring
    (K Γ : Type*) [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] : ValuationSubring (HahnFraction Γ K) where
  toSubring := (hahnFractionValuation (Γ := Γ) (R := K)).integer
  mem_or_inv_mem' := fun x => by
    change hahnFractionValuation x ≤ 1 ∨ hahnFractionValuation x⁻¹ ≤ 1
    rw [Valuation.map_inv]
    rcases le_total (hahnFractionValuation (Γ := Γ) (R := K) x) 1 with h | h
    · exact Or.inl h
    · exact Or.inr (inv_le_one_of_one_le₀ h)

theorem mem_hahnFractionValuationSubring_iff
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (x : HahnFraction Γ K) :
    x ∈ hahnFractionValuationSubring K Γ ↔
      hahnFractionValuation (Γ := Γ) (R := K) x ≤ 1 := by
  exact Valuation.mem_integer_iff _ _

/-! ## Exact extension to the algebraic closure -/

/-- Krull domination extends the full Hahn valuation ring to the algebraic closure. -/
theorem exists_hahnAlgebraicClosureValuationSubring
    (K Γ : Type*) [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] :
    ∃ (A : ValuationSubring (AlgebraicClosure (HahnFraction Γ K)))
      (hmem : ∀ x : hahnFractionValuationSubring K Γ,
        algebraMap (HahnFraction Γ K) (AlgebraicClosure (HahnFraction Γ K)) x ∈ A),
      IsLocalHom (((algebraMap (HahnFraction Γ K)
        (AlgebraicClosure (HahnFraction Γ K))).comp
          (hahnFractionValuationSubring K Γ).subtype).codRestrict A.toSubring hmem) := by
  exact IsLocalRing.exists_factor_valuationRing
    ((algebraMap (HahnFraction Γ K) (AlgebraicClosure (HahnFraction Γ K))).comp
      (hahnFractionValuationSubring K Γ).subtype)

/-- Chosen extension of the full Hahn valuation ring to the algebraic closure. -/
noncomputable def hahnAlgebraicClosureValuationSubring
    (K Γ : Type*) [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] :
    ValuationSubring (AlgebraicClosure (HahnFraction Γ K)) :=
  (exists_hahnAlgebraicClosureValuationSubring K Γ).choose

theorem hahnAlgebraicClosureValuationSubring_algebraMap_mem
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (x : hahnFractionValuationSubring K Γ) :
    algebraMap (HahnFraction Γ K) (AlgebraicClosure (HahnFraction Γ K)) x ∈
      hahnAlgebraicClosureValuationSubring K Γ :=
  (exists_hahnAlgebraicClosureValuationSubring K Γ).choose_spec.choose x

noncomputable instance hahnAlgebraicClosureValuationSubring_isLocalHom
    (K Γ : Type*) [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] :
    IsLocalHom (((algebraMap (HahnFraction Γ K)
      (AlgebraicClosure (HahnFraction Γ K))).comp
        (hahnFractionValuationSubring K Γ).subtype).codRestrict
          (hahnAlgebraicClosureValuationSubring K Γ).toSubring
          hahnAlgebraicClosureValuationSubring_algebraMap_mem) :=
  (exists_hahnAlgebraicClosureValuationSubring K Γ).choose_spec.choose_spec

/-- The chosen algebraic-closure valuation restricts to exactly the full Hahn valuation ring. -/
theorem hahnAlgebraicClosureValuationSubring_comap
    (K Γ : Type*) [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] :
    (hahnAlgebraicClosureValuationSubring K Γ).comap
        (algebraMap (HahnFraction Γ K) (AlgebraicClosure (HahnFraction Γ K))) =
      hahnFractionValuationSubring K Γ := by
  exact ValuationSubring.comap_eq_of_local_codRestrict
    (hahnFractionValuationSubring K Γ)
    (hahnAlgebraicClosureValuationSubring K Γ)
    (algebraMap (HahnFraction Γ K) (AlgebraicClosure (HahnFraction Γ K)))
    hahnAlgebraicClosureValuationSubring_algebraMap_mem

theorem mem_hahnAlgebraicClosureValuationSubring_algebraMap_iff
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (x : HahnFraction Γ K) :
    algebraMap (HahnFraction Γ K) (AlgebraicClosure (HahnFraction Γ K)) x ∈
        hahnAlgebraicClosureValuationSubring K Γ ↔
      x ∈ hahnFractionValuationSubring K Γ := by
  change x ∈ (hahnAlgebraicClosureValuationSubring K Γ).comap
      (algebraMap (HahnFraction Γ K) (AlgebraicClosure (HahnFraction Γ K))) ↔ _
  rw [hahnAlgebraicClosureValuationSubring_comap]

/-! ## Pullback to the finite actual branch field -/

/-- One compatible lexicographic valuation flag on the actual finite derivative-branch field. -/
noncomputable def nonautonomousFiniteCascadeBranchValuationSubring
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin N → ℕ) (hr : ∀ i, 0 < r i) :
    ValuationSubring (NonautonomousFiniteCascadeBranchField hfan N) :=
  (hahnAlgebraicClosureValuationSubring (RatFunc ℂ) (mgDeg N)).comap
    (nonautonomousFiniteCascadeBranchAlgebraicClosureEmbedding
      hfan hall h1 r hr).toRingHom

/-- Every actual clock/state generator has precisely the valuation-ring membership of its
prescribed Hahn clock/state coordinate. -/
theorem nonautonomousFiniteCascadeStateInBranchField_mem_valuationSubring_iff
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin N → ℕ) (hr : ∀ i, 0 < r i) (i : Fin (N + 1)) :
    nonautonomousFiniteCascadeStateInBranchField hfan N i ∈
        nonautonomousFiniteCascadeBranchValuationSubring hfan hall h1 r hr ↔
      nonautonomousHahnClockCoordinateFamily (C := ℂ) r i ∈
        hahnFractionValuationSubring (RatFunc ℂ) (mgDeg N) := by
  rw [nonautonomousFiniteCascadeBranchValuationSubring, ValuationSubring.mem_comap]
  change nonautonomousFiniteCascadeBranchAlgebraicClosureEmbedding
      hfan hall h1 r hr
        (nonautonomousFiniteCascadeStateInBranchField hfan N i) ∈
      hahnAlgebraicClosureValuationSubring (RatFunc ℂ) (mgDeg N) ↔ _
  rw [nonautonomousFiniteCascadeBranchAlgebraicClosureEmbedding_apply_state]
  exact mem_hahnAlgebraicClosureValuationSubring_algebraMap_iff _

end

end GaloisForLFunctions.HTGeometry
