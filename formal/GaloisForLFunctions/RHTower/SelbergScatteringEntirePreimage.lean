import GaloisForLFunctions.RHTower.SelbergScatteringEntireTransform
import GaloisForLFunctions.RHTower.XiWardSpectralBudgetSumRule

/-!
# Unique real native preimages of the entire scattering transform

In the open Xi strip at nonzero height, `F(lam) = F(k(z))` for real `lam`
holds exactly when `z` is real and `lam = 1/4 + (Re z)²/4`. This supplies
both existence on the critical line and uniqueness of the real native parameter.
Applied to actual Xi zeros at native scattering parameter `s = rho/2`, existence
of any such real preimage is equivalent to critical placement of that zero.

These statements classify a proposed occurrence interface. They do not assert
that the preimages exist for all Xi zeros or that they are Maass eigenvalues.
-/

open Complex
open RHTower.SelbergScatteringPolynomialReality

namespace RHTower.SelbergScatteringEntireTransform
noncomputable section

/-- The unique candidate real native energy paired with a critical scattering ordinate. -/
def nativePartner (t : ℝ) : ℝ := 1 / 4 + t ^ 2 / 4

/-- Every nonzero critical ordinate gives a partner strictly above the quarter. -/
theorem nativePartner_gt_quarter (t : ℝ) (ht : t ≠ 0) :
    1 / 4 < nativePartner t := by
  dsimp [nativePartner]
  nlinarith [sq_pos_of_ne_zero ht]

/-- Constructive equality of transformed critical scattering energy and its real native partner. -/
theorem casimirTransform_nativePartner (t : ℝ) :
    casimirTransform (nativePartner t) = casimirTransform (criticalCasimir t) := by
  have harg : (nativePartner t : ℂ) = 1 / 4 + ((t : ℂ) / 2) ^ 2 := by
    simp only [nativePartner]
    push_cast
    ring
  rw [harg, casimirTransform_sq, casimirTransform_criticalCasimir]
  congr 1
  ring

/-- Exact existence and uniqueness classifier for real native preimages throughout the open Xi strip. -/
theorem real_native_preimage_iff (z : ℂ) (hre : z.re ≠ 0)
    (hlo : -(1 / 2 : ℝ) < z.im) (hhi : z.im < 1 / 2) (lam : ℝ) :
    casimirTransform lam = casimirTransform (criticalCasimir z) ↔
      z.im = 0 ∧ lam = nativePartner z.re := by
  constructor
  · intro hm
    have hz : z.im = 0 := (critical_strip_range_iff z hre hlo hhi).mp (by
      rw [← hm]
      exact casimirTransform_real_range lam)
    have hzreal : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
    have hval : casimirTransform lam = (Real.cosh (4 * Real.pi * z.re) : ℂ) := by
      rw [hm, hzreal, casimirTransform_critical_real]
      rfl
    have hgt : 1 < (casimirTransform lam).re := by
      rw [hval, Complex.ofReal_re, Real.one_lt_cosh]
      exact mul_ne_zero (by positivity) hre
    have hlam := (one_lt_casimirTransform_iff lam).mp hgt
    rw [casimirTransform_of_ge_quarter lam hlam.le] at hval
    have heq := Complex.ofReal_injective hval
    have habs : |8 * Real.pi * Real.sqrt (lam - 1 / 4)| = |4 * Real.pi * z.re| :=
      le_antisymm (Real.cosh_le_cosh.mp heq.le) (Real.cosh_le_cosh.mp heq.ge)
    have hs := congrArg (fun x : ℝ => x ^ 2) habs
    simp only [sq_abs, mul_pow, Real.sq_sqrt (sub_nonneg.mpr hlam.le)] at hs
    have he : (16 * Real.pi ^ 2) * (4 * (lam - 1 / 4) - z.re ^ 2) = 0 := by
      nlinarith [hs]
    have hd := (mul_eq_zero.mp he).resolve_left (by positivity)
    refine ⟨hz, ?_⟩
    dsimp [nativePartner]
    linarith
  · rintro ⟨hz, rfl⟩
    have hzreal : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
    rw [hzreal]
    exact casimirTransform_nativePartner _

/-- In the original exponent coordinate, the entire Casimir transform is an explicit cosine. -/
theorem casimirTransform_casimir (s : ℂ) :
    casimirTransform (s * (1 - s)) = Complex.cos (8 * Real.pi * (s - 1 / 2)) := by
  have ha : s * (1 - s) = 1 / 4 + ((s - 1 / 2) * I) ^ 2 := by
    ring_nf
    rw [I_sq]
    ring
  rw [ha, casimirTransform_sq, ← mul_assoc, Complex.cosh_mul_I]

/-- The centered scattering parabola is the original Casimir at exponent `rho/2`. -/
theorem criticalCasimir_centered_argument (rho : ℂ) :
    criticalCasimir ((rho - 1 / 2) * (-I)) = (rho / 2) * (1 - rho / 2) := by
  unfold criticalCasimir
  ring_nf
  rw [I_sq]
  ring

/-- For each actual Xi zero, a real native preimage exists exactly on the critical line and has a unique value. -/
theorem xi_real_native_preimage_iff (q : XiZeroCopy) (lam : ℝ) :
    casimirTransform lam =
      casimirTransform (((q.1 : ℂ) / 2) * (1 - (q.1 : ℂ) / 2)) ↔
      (q.1 : ℂ).re = 1 / 2 ∧ lam = nativePartner (q.1 : ℂ).im := by
  have hr : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have hre : (xiSpectralPoint q).re ≠ 0 := by
    rw [hr]
    exact xi_divisor_support_im_ne_zero q.1
  have hi : (xiSpectralPoint q).im = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
    simp [xiSpectralPoint]
    constructor <;> intro h <;> linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)
  rw [← criticalCasimir_centered_argument]
  change casimirTransform lam = casimirTransform (criticalCasimir (xiSpectralPoint q)) ↔ _
  rw [real_native_preimage_iff (xiSpectralPoint q) hre hlo hhi lam, hi, hr]

/-- Admitting any real native preimage for an actual Xi zero is exactly its critical-placement assertion. -/
theorem xi_exists_real_native_preimage_iff (q : XiZeroCopy) :
    (∃ lam : ℝ, casimirTransform lam =
      casimirTransform (((q.1 : ℂ) / 2) * (1 - (q.1 : ℂ) / 2))) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨lam, h⟩
    exact ((xi_real_native_preimage_iff q lam).mp h).1
  · intro h
    exact ⟨nativePartner (q.1 : ℂ).im,
      (xi_real_native_preimage_iff q _).mpr ⟨h, rfl⟩⟩

end
end RHTower.SelbergScatteringEntireTransform
