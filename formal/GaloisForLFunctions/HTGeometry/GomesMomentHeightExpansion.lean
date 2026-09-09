import GaloisForLFunctions.HTGeometry.GomesMomentQuotientGeometry
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Strict projective height expansion in concrete moment systems

Further internal-frame consequences of https://arxiv.org/abs/2404.10461 and
https://arxiv.org/abs/2607.24901. The positive observation kernel forces every
higher consecutive-polynomial quotient to increase distance from the real
boundary strictly at nonreal points. The first level preserves height exactly.
The same quotients satisfy conjugation symmetry and are holomorphic on both
half-planes, with no supplied positivity or nonvanishing premises.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The first projective level preserves height exactly. -/
theorem gomesMomentQuotientWeight_zero (M : GomesMomentModel) (z : ℂ) :
    gomesMomentQuotientWeight M 0 z = 1 := by
  have h0 : momentInner M.moments 1 1 ≠ 0 := by
    simpa using (gomesMomentModel_norm_pos M 0).ne'
  simp [gomesMomentQuotientWeight,gomesMomentKernel,monicOrthoC,h0]

/-- Every later level has strictly greater than unit height weight precisely away from its denominator zeros. -/
theorem gomesMomentQuotientWeight_succ_gt_one_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    1 < gomesMomentQuotientWeight M (n+1) z ↔ monicOrthoC M.moments (n+1) z ≠ 0 := by
  constructor
  · intro h
    exact (gomesMomentQuotientWeight_pos_iff M (n+1) z).mp (by linarith)
  · intro h
    have hN := Complex.normSq_pos.mpr h
    have hh := gomesMomentModel_norm_pos M (n+1)
    have he : gomesMomentQuotientWeight M (n+1) z = 1 +
        gomesMomentKernel M n z *
          momentInner M.moments (monicOrtho M.moments (n+1)) (monicOrtho M.moments (n+1)) /
            Complex.normSq (monicOrthoC M.moments (n+1) z) := by
      unfold gomesMomentQuotientWeight
      rw [gomesMomentKernel,Finset.sum_range_succ]
      change ((gomesMomentKernel M n z + _)*_)/_ = _
      field_simp [hN.ne',hh.ne']
      ring
    rw [he]
    exact lt_add_of_pos_right 1 (div_pos (mul_pos (gomesMomentKernel_pos M n z) hh) hN)

/-- Unit height weight is a universal lower bound whenever the projective coordinate is defined. -/
theorem gomesMomentQuotientWeight_ge_one_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    1 ≤ gomesMomentQuotientWeight M n z ↔ monicOrthoC M.moments n z ≠ 0 := by
  constructor
  · intro h
    exact (gomesMomentQuotientWeight_pos_iff M n z).mp (by linarith)
  · intro h
    cases n with
    | zero => simp [gomesMomentQuotientWeight_zero]
    | succ n => exact ((gomesMomentQuotientWeight_succ_gt_one_iff M n z).mpr h).le

/-- Projectivizing consecutive levels never reduces distance from the real boundary. -/
theorem gomesMomentQuotient_abs_im_ge (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    |z.im| ≤ |(gomesMomentQuotient M n z).im| := by
  rw [gomesMomentQuotient_im,abs_mul,abs_of_nonneg (gomesMomentQuotientWeight_nonneg M n z)]
  by_cases hz : z.im = 0
  · simp [hz]
  · have hn := (gomesMomentQuotient_denominator M n z).resolve_right hz
    have hw := (gomesMomentQuotientWeight_ge_one_iff M n z).mpr hn
    simpa using mul_le_mul_of_nonneg_right hw (abs_nonneg z.im)

/-- Beyond the first level, boundary distance expands strictly at exactly the nonreal points. -/
theorem gomesMomentQuotient_succ_abs_im_gt_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    |z.im| < |(gomesMomentQuotient M (n+1) z).im| ↔ z.im ≠ 0 := by
  rw [gomesMomentQuotient_im,abs_mul,
    abs_of_nonneg (gomesMomentQuotientWeight_nonneg M (n+1) z)]
  constructor
  · intro h hz
    simp [hz] at h
  · intro hz
    have hn := (gomesMomentQuotient_denominator M (n+1) z).resolve_right hz
    have hw := (gomesMomentQuotientWeight_succ_gt_one_iff M n z).mpr hn
    simpa using mul_lt_mul_of_pos_right hw (abs_pos.mpr hz)

/-- The field quotient has the expected conjugation symmetry even at its real poles. -/
theorem gomesMomentQuotient_conj (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    gomesMomentQuotient M n (starRingEnd ℂ z) = starRingEnd ℂ (gomesMomentQuotient M n z) := by
  simp [gomesMomentQuotient,monicOrthoC_conj]

/-- The projective quotient is holomorphic throughout both open half-planes. -/
theorem gomesMomentQuotient_differentiableOn_nonreal (M : GomesMomentModel) (n : ℕ) :
    DifferentiableOn ℂ (gomesMomentQuotient M n) {z : ℂ | z.im ≠ 0} := by
  intro z hz
  have hn := (gomesMomentQuotient_denominator M n z).resolve_right hz
  exact ((monicOrtho M.moments (n+1)).differentiableAt_aeval.div
    (monicOrtho M.moments n).differentiableAt_aeval hn).differentiableWithinAt

end GaloisForLFunctions.HTGeometry
