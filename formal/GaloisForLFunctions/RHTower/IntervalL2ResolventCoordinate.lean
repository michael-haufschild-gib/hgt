import GaloisForLFunctions.RHTower.HilbertBasisMultiplierOperator
import GaloisForLFunctions.HTGeometry.IntervalL2Density

/-!
# A compact resolvent coordinate on `L²` of the interval

With a countable Hilbert basis of `L²[-a,a]` available, the diagonal model transports there: a
nonnegative, nowhere vanishing multiplier tending to zero gives a compact, self-adjoint, injective
operator with spectrum in `Icc 0 M`.  That is a genuine resolvent coordinate on the space where the
edge pairing weights live, in place of the identity.

Injectivity and the real spectrum transport along the coordinate isometry for the same reason
compactness does: conjugation by an equivalence is a ring isomorphism of the operator algebras.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology GaloisForLFunctions.HTGeometry _root_.RHTower

section Transport

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- Injectivity transports along conjugation. -/
theorem injective_conjugateOperator_iff (u : E' ≃L[ℂ] K) (T : K →L[ℂ] K) :
    Function.Injective (conjugateOperator u T) ↔ Function.Injective T := by
  constructor
  · intro h y₁ y₂ hy
    have : conjugateOperator u T (u.symm y₁) = conjugateOperator u T (u.symm y₂) := by
      simp only [conjugateOperator, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
      exact congrArg _ hy
    have := h this
    simpa using congrArg u this
  · intro h x₁ x₂ hx
    simp only [conjugateOperator, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe] at hx
    have := h (u.symm.injective hx)
    exact u.injective this

theorem conjugateOperator_real_smul (u : E' ≃L[ℂ] K) (r : ℝ) (T : K →L[ℂ] K) :
    conjugateOperator u (r • T) = r • conjugateOperator u T := by
  ext x
  simp [conjugateOperator]

/-- **The real spectrum is invariant under conjugation.** -/
theorem spectrum_real_conjugateOperator (u : E' ≃L[ℂ] K) (T : K →L[ℂ] K) :
    spectrum ℝ (conjugateOperator u T) = spectrum ℝ T := by
  have hr : ∀ r : ℝ, algebraMap ℝ (E' →L[ℂ] E') r - conjugateOperator u T
      = conjugateOperator u (algebraMap ℝ (K →L[ℂ] K) r - T) := by
    intro r
    rw [conjugateOperator_sub, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, conjugateOperator_real_smul, conjugateOperator_one]
  ext r
  simp only [spectrum.mem_iff, hr r, isUnit_conjugateOperator_iff]

end Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The real spectrum of a multiplier operator along a basis is that of the diagonal model. -/
theorem spectrum_real_basisMultiplierOperator (b : HilbertBasis ℕ ℂ E) (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) :
    spectrum ℝ (basisMultiplierOperator b (fun n => (r n : ℂ)) hC)
      = spectrum ℝ (diagonalOperator (fun n => (r n : ℂ)) hC) :=
  spectrum_real_conjugateOperator (basisCoordEquiv b) _

omit [CompleteSpace E] in
/-- The multiplier operator along a basis is injective when the multiplier never vanishes. -/
theorem injective_basisMultiplierOperator (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℂ) {C : ℝ}
    (hC : ∀ n, ‖lam n‖ ≤ C) (hne : ∀ n, lam n ≠ 0) :
    Function.Injective (basisMultiplierOperator b lam hC) :=
  (injective_conjugateOperator_iff (basisCoordEquiv b) (diagonalOperator lam hC)).mpr
    (injective_diagonalOperator lam hC hne)

/-- **A compact resolvent coordinate on `L²[-a,a]`.**  The harmonic multiplier along the
polynomial Hilbert basis gives a compact, self-adjoint, injective operator with nonnegative bounded
spectrum — a genuine resolvent coordinate on the interval space. -/
def intervalHarmonicCoordinate (a : ℝ) (ha : 0 < a) :
    IntervalL2 a →L[ℂ] IntervalL2 a :=
  basisMultiplierOperator (intervalL2Basis a ha)
    (fun n => ((harmonicMultiplier n : ℝ) : ℂ)) norm_harmonicMultiplier_le

theorem isSelfAdjoint_intervalHarmonicCoordinate (a : ℝ) (ha : 0 < a) :
    IsSelfAdjoint (intervalHarmonicCoordinate a ha) :=
  isSelfAdjoint_basisMultiplierOperator _ _ norm_harmonicMultiplier_le

theorem injective_intervalHarmonicCoordinate (a : ℝ) (ha : 0 < a) :
    Function.Injective (intervalHarmonicCoordinate a ha) :=
  injective_basisMultiplierOperator _ _ norm_harmonicMultiplier_le
    (fun n => Complex.ofReal_ne_zero.mpr (harmonicMultiplier_ne_zero n))

theorem isCompactOperator_intervalHarmonicCoordinate (a : ℝ) (ha : 0 < a) :
    IsCompactOperator (intervalHarmonicCoordinate a ha) :=
  isCompactOperator_basisMultiplierOperator _ _ norm_harmonicMultiplier_le
    tendsto_harmonicMultiplier_zero

/-- The spectrum of the coordinate is nonnegative and bounded. -/
theorem spectrum_intervalHarmonicCoordinate_subset (a : ℝ) (ha : 0 < a) :
    spectrum ℝ (intervalHarmonicCoordinate a ha)
      ⊆ Set.Icc 0 ‖diagonalOperator (fun n => ((harmonicMultiplier n : ℝ) : ℂ))
          norm_harmonicMultiplier_le‖ := by
  intro x hx
  have h := spectrum_real_basisMultiplierOperator (intervalL2Basis a ha) harmonicMultiplier
    norm_harmonicMultiplier_le
  have hx' : x ∈ spectrum ℝ (diagonalOperator
      (fun n => ((harmonicMultiplier n : ℝ) : ℂ)) norm_harmonicMultiplier_le) := h ▸ hx
  exact spectrum_diagonalOperator_ofReal_subset _ norm_harmonicMultiplier_le
    harmonicMultiplier_nonneg hx'

end GaloisForLFunctions.RHTower
