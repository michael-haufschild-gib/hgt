import GaloisForLFunctions.RHTower.SourceHorizontalSharedReservoirAmplification
import GaloisForLFunctions.HTGeometry.StokesGlobalPuiseuxWittLaw

/-!
# Shared-reservoir obstruction to simultaneous Stokes landing

Every coefficient-generated global Stokes Witt form is nonnegative after adding one square.
Pullback preserves this one-port property.  A source-horizontal shared-reservoir form and its
reflection, however, have opposite exact inertias; off the critical line one orientation has
`m - 1` negative directions.  For `m ≥ 3` the two orientations therefore cannot both land
quadratic-form-faithfully in one Stokes Witt carrier.

This is an unconditional cross-corpus obstruction theorem.  It isolates the remaining producer:
a source-derived simultaneous reflected landing would force critical-line placement, but that
landing is not asserted here.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

theorem sigNeg_le_one_of_onePort_pullback
    {V M : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup M] [Module ℝ M]
    (S : QuadraticForm ℝ V) (Q : QuadraticForm ℝ M)
    (f : V →ₗ[ℝ] M) (ell : M →ₗ[ℝ] ℝ)
    (hQ : ∀ y, 0 ≤ Q y + (ell y) ^ (2 : ℕ))
    (hpull : ∀ x, S x = Q (f x)) :
    sigNeg S ≤ 1 := by
  apply GaloisForLFunctions.sigNeg_le_one_of_add_sq_nonneg S (ell.comp f)
  intro x
  rw [hpull]
  exact hQ (f x)

theorem not_onePort_pullback_of_sourceZeroHorizontal_right
    {m : ℕ} (hm : 3 ≤ m) (q : XiZeroCopy)
    (hright : 1 / 2 < (q.1 : ℂ).re) (p : Fin m → Nat.Primes)
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (f : (Fin m → ℝ) →ₗ[ℝ] M)
    (ell : M →ₗ[ℝ] ℝ) (hQ : ∀ y, 0 ≤ Q y + (ell y) ^ (2 : ℕ)) :
    ¬ ∀ x, (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
      Q (f x) := by
  intro hpull
  have hle := sigNeg_le_one_of_onePort_pullback
    (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm'
    Q f ell hQ hpull
  have hsig :=
    (sourceZeroHorizontalSharedReservoirMatrix_inertia_of_right q hright p (by omega)).2.1
  omega

theorem sourceZeroHorizontal_reflection_right_of_left
    (q : XiZeroCopy) (hleft : (q.1 : ℂ).re < 1 / 2) :
    1 / 2 < ((xiZeroCopyLineConjEquiv q).1 : ℂ).re := by
  change 1 / 2 < (1 - (starRingEnd ℂ) (q.1 : ℂ)).re
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  linarith

theorem sourceZeroHorizontalSharedReservoir_twoOrientation_onePort_obstruction
    {m : ℕ} (hm : 3 ≤ m) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) (p : Fin m → Nat.Primes)
    {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module ℝ M₁] [AddCommGroup M₂] [Module ℝ M₂]
    (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂)
    (f₁ : (Fin m → ℝ) →ₗ[ℝ] M₁) (f₂ : (Fin m → ℝ) →ₗ[ℝ] M₂)
    (ell₁ : M₁ →ₗ[ℝ] ℝ) (ell₂ : M₂ →ₗ[ℝ] ℝ)
    (hQ₁ : ∀ y, 0 ≤ Q₁ y + (ell₁ y) ^ (2 : ℕ))
    (hQ₂ : ∀ y, 0 ≤ Q₂ y + (ell₂ y) ^ (2 : ℕ)) :
    ¬ ((∀ x, (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          Q₁ (f₁ x)) ∧
        (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x = Q₂ (f₂ x))) := by
  rintro ⟨hforward, hreflected⟩
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · exact not_onePort_pullback_of_sourceZeroHorizontal_right hm
      (xiZeroCopyLineConjEquiv q)
      (sourceZeroHorizontal_reflection_right_of_left q hleft) p Q₂ f₂ ell₂ hQ₂ hreflected
  · exact not_onePort_pullback_of_sourceZeroHorizontal_right hm q hright p
      Q₁ f₁ ell₁ hQ₁ hforward

namespace GlobalPuiseuxWittLanding

open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

noncomputable def rankCorrection {k : ℕ}
    {n r K N : Fin (k + 1) → ℕ}
    (genus : ℕ) (d : LocalData k n r K N) :
    compatibleCharges d →ₗ[ℝ] ℝ :=
  (LinearMap.lsmul ℝ ℝ
    (Real.sqrt (max 0 (-globalRankCoefficient genus d)))).comp
      (commonRankLinear d)

theorem globalWittForm_add_rankCorrection_nonneg {k : ℕ}
    {n r K N : Fin (k + 1) → ℕ}
    (genus : ℕ) (d : LocalData k n r K N)
    (x : compatibleCharges d) :
    0 ≤ globalWittForm genus d x + (rankCorrection genus d x) ^ (2 : ℕ) := by
  rw [globalWittForm_eq_positive_add_oneRank]
  change 0 ≤ globalPositiveForm d x + globalRankCoefficient genus d *
      commonRankLinear d x ^ (2 : ℕ) +
    (Real.sqrt (max 0 (-globalRankCoefficient genus d)) *
      commonRankLinear d x) ^ (2 : ℕ)
  rw [mul_pow, Real.sq_sqrt (le_max_left 0 (-globalRankCoefficient genus d))]
  by_cases hcoeff : 0 ≤ globalRankCoefficient genus d
  · rw [max_eq_left (neg_nonpos.mpr hcoeff)]
    nlinarith [globalPositiveForm_nonneg d x,
      mul_nonneg hcoeff (sq_nonneg (commonRankLinear d x))]
  · rw [max_eq_right (neg_nonneg.mpr (le_of_not_ge hcoeff))]
    nlinarith [globalPositiveForm_nonneg d x]

/-- An off-line source class and its reflection cannot both have quadratic-form-preserving
landings in one coefficient-generated Stokes Witt carrier.  This is the exact non-additive
two-orientation obstruction: Stokes supplies one nonpositive port, whereas source reflection
forces one member of every shared-reservoir pair to have at least two negative directions. -/
theorem not_both_sourceZeroHorizontal_orientations_land_in_globalWitt
    {m : ℕ} (hm : 3 ≤ m) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) (p : Fin m → Nat.Primes)
    {k : ℕ} {n r K N : Fin (k + 1) → ℕ}
    (genus : ℕ) (d : LocalData k n r K N)
    (forward reflected : (Fin m → ℝ) →ₗ[ℝ] compatibleCharges d) :
    ¬ ((∀ x, (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          globalWittForm genus d (forward x)) ∧
        (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
            globalWittForm genus d (reflected x))) := by
  exact sourceZeroHorizontalSharedReservoir_twoOrientation_onePort_obstruction
    hm q hoff p (globalWittForm genus d) (globalWittForm genus d)
      forward reflected (rankCorrection genus d) (rankCorrection genus d)
      (globalWittForm_add_rankCorrection_nonneg genus d)
      (globalWittForm_add_rankCorrection_nonneg genus d)

end GlobalPuiseuxWittLanding

end

end RHTower
