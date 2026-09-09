import GaloisForLFunctions.HTGeometry.GomesMomentModels
import GaloisForLFunctions.HTGeometry.MomentRealRootedness

/-!
# Exact half-plane geometry of actual moment quotients

Application of internal-frame geometry from https://arxiv.org/abs/2404.10461
and retained-invariant questions from https://arxiv.org/abs/2607.24901.
Consecutive orthogonal-polynomial levels define a projective coordinate.
The corpus's complex Christoffel--Darboux identity computes its imaginary part
as source height times an explicit positive-kernel multiplier. All three
concrete moment families preserve the two half-planes and their real boundary;
positivity and nonreal denominator exclusion are discharged internally.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The existing Christoffel kernel evaluated on a concrete moment model. -/
def gomesMomentKernel (M : GomesMomentModel) (n : ℕ) (z : ℂ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), Complex.normSq (monicOrthoC M.moments k z) /
    momentInner M.moments (monicOrtho M.moments k) (monicOrtho M.moments k)

/-- The projective coordinate of two consecutive orthogonal-polynomial levels. -/
def gomesMomentQuotient (M : GomesMomentModel) (n : ℕ) (z : ℂ) : ℂ :=
  monicOrthoC M.moments (n+1) z / monicOrthoC M.moments n z

/-- The exact height multiplier exposed by the positive internal-frame kernel. -/
def gomesMomentQuotientWeight (M : GomesMomentModel) (n : ℕ) (z : ℂ) : ℝ :=
  gomesMomentKernel M n z *
    momentInner M.moments (monicOrtho M.moments n) (monicOrtho M.moments n) /
      Complex.normSq (monicOrthoC M.moments n z)

/-- The constant polynomial makes every finite kernel strictly positive at every complex point. -/
theorem gomesMomentKernel_pos (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    0 < gomesMomentKernel M n z := by
  apply Finset.sum_pos'
  · intro k hk
    exact div_nonneg (Complex.normSq_nonneg _) (gomesMomentModel_norm_pos M k).le
  · refine ⟨0,by simp,?_⟩
    simpa [monicOrthoC] using inv_pos.mpr (gomesMomentModel_norm_pos M 0)

/-- Every possible zero denominator is confined to the real axis, by the existing real-root theorem. -/
theorem gomesMomentQuotient_denominator (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    monicOrthoC M.moments n z ≠ 0 ∨ z.im = 0 := by
  by_cases hz : z.im = 0
  · exact Or.inr hz
  · left
    cases n with
    | zero => simp [monicOrthoC]
    | succ n => exact monicOrtho_aeval_ne_zero (gomesMomentModel_positive M) n hz

/-- The height multiplier is nonnegative even at real zeros, where Lean's field quotient is zero. -/
theorem gomesMomentQuotientWeight_nonneg (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    0 ≤ gomesMomentQuotientWeight M n z :=
  div_nonneg (mul_pos (gomesMomentKernel_pos M n z) (gomesMomentModel_norm_pos M n)).le
    (Complex.normSq_nonneg _)

/-- Strictly positive height weight is equivalent to a nonzero projective denominator. -/
theorem gomesMomentQuotientWeight_pos_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    0 < gomesMomentQuotientWeight M n z ↔ monicOrthoC M.moments n z ≠ 0 := by
  constructor
  · intro h he
    simp [gomesMomentQuotientWeight,he] at h
  · intro h
    exact div_pos (mul_pos (gomesMomentKernel_pos M n z) (gomesMomentModel_norm_pos M n))
      (Complex.normSq_pos.mpr h)

/-- The projective height is exactly the source height times a positive-kernel multiplier. -/
theorem gomesMomentQuotient_im (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentQuotient M n z).im = gomesMomentQuotientWeight M n z * z.im := by
  have hq : ∀ u v : ℂ, (u/v).im = (u*starRingEnd ℂ v).im / Complex.normSq v := by
    intro u v
    simp [Complex.div_im,Complex.mul_im]
    ring
  rw [gomesMomentQuotient,hq,← kernelSum_mul_im (gomesMomentModel_positive M) n z]
  unfold gomesMomentQuotientWeight gomesMomentKernel
  ring

/-- Every concrete moment quotient preserves exactly the open upper half-plane. -/
theorem gomesMomentQuotient_im_pos_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    0 < (gomesMomentQuotient M n z).im ↔ 0 < z.im := by
  rw [gomesMomentQuotient_im]
  constructor
  · intro h
    exact pos_of_mul_pos_right h (gomesMomentQuotientWeight_nonneg M n z)
  · intro h
    have hn := (gomesMomentQuotient_denominator M n z).resolve_right h.ne'
    exact mul_pos ((gomesMomentQuotientWeight_pos_iff M n z).mpr hn) h

/-- The same exact projective law preserves the open lower half-plane. -/
theorem gomesMomentQuotient_im_neg_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentQuotient M n z).im < 0 ↔ z.im < 0 := by
  rw [gomesMomentQuotient_im]
  constructor
  · intro h
    by_contra he
    exact not_lt_of_ge (mul_nonneg (gomesMomentQuotientWeight_nonneg M n z) (le_of_not_gt he)) h
  · intro h
    have hn := (gomesMomentQuotient_denominator M n z).resolve_right h.ne
    exact mul_neg_of_pos_of_neg ((gomesMomentQuotientWeight_pos_iff M n z).mpr hn) h

/-- The real boundary is also exact, including the field convention at real poles. -/
theorem gomesMomentQuotient_im_zero_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentQuotient M n z).im = 0 ↔ z.im = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy z.im 0 with he | he | he
    · have hh := (gomesMomentQuotient_im_neg_iff M n z).mpr he
      linarith
    · exact he
    · have hh := (gomesMomentQuotient_im_pos_iff M n z).mpr he
      linarith
  · intro h
    simp [gomesMomentQuotient_im,h]

end GaloisForLFunctions.HTGeometry
