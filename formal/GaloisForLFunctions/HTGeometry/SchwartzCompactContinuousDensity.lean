import GaloisForLFunctions.HTGeometry.SchwartzCompactDiagonalOrderZero
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Uniform compact-cutoff polynomial density

Every compactly supported continuous real function is uniformly approximated by polynomial
multiples of one fixed smooth cutoff.  The approximants are real Schwartz functions with one common
compact support.  This is the density input for extending the local order-zero diagonal functional
to `C_c(ℝ, ℝ)`.
-/

open Complex Function Filter Set
open scoped SchwartzMap FourierTransform Topology Polynomial ContDiff CompactlySupported

noncomputable section

namespace SchwartzMap

@[simp] theorem realCompactIntervalCutoff_le_one (R : ℝ) (t : ℝ) :
    realCompactIntervalCutoff R t ≤ 1 := by
  rw [realCompactIntervalCutoff]
  let b : ContDiffBump (0 : ℝ) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  exact b.le_one

/-- A polynomial localized by the canonical real cutoff. -/
def realPolynomialCutoff (P : ℝ[X]) (R : ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t => P.eval t) (realCompactIntervalCutoff R)

@[simp] theorem realPolynomialCutoff_apply (P : ℝ[X]) (R t : ℝ) :
    realPolynomialCutoff P R t = P.eval t * realCompactIntervalCutoff R t := by
  rw [realPolynomialCutoff, SchwartzMap.smulLeftCLM_apply_apply
    (polynomial_eval_hasTemperateGrowth P)]
  simp only [smul_eq_mul]

/-- Polynomial cutoffs have the support of the fixed cutoff, independently of degree. -/
theorem realPolynomialCutoff_tsupport_subset (P : ℝ[X]) (R : ℝ) :
    tsupport (realPolynomialCutoff P R) ⊆ {t : ℝ | |t| ≤ |R| + 2} := by
  rw [← realCompactIntervalCutoff_tsupport R]
  rw [tsupport, tsupport]
  apply closure_mono
  intro t ht
  simp only [Function.mem_support] at ht ⊢
  intro hzero
  rw [realPolynomialCutoff_apply, hzero, mul_zero] at ht
  exact ht rfl

/-- A cutoff whose core contains a compact packet acts as one on that packet globally. -/
theorem realCompactIntervalCutoff_mul_eq
    (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hf : tsupport f ⊆ {t : ℝ | |t| ≤ R}) (t : ℝ) :
    realCompactIntervalCutoff R t * f t = f t := by
  by_cases ht : t ∈ tsupport f
  · have hcore : |t| ≤ |R| + 1 := by
      have habs : |t| ≤ R := hf ht
      rw [abs_of_nonneg hR]
      linarith
    rw [realCompactIntervalCutoff_apply_of_abs_le_add_one R hcore, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]

/-- **Uniform compact-cutoff polynomial density.** Every compactly supported continuous real
function is uniformly approximated by real Schwartz maps with one fixed compact support. -/
theorem exists_realPolynomialCutoff_uniform_near
    (f : C_c(ℝ, ℝ)) {R ε : ℝ} (hR : 0 ≤ R)
    (hf : tsupport f ⊆ {t : ℝ | |t| ≤ R}) (hε : 0 < ε) :
    ∃ P : ℝ[X], ∀ t : ℝ, |realPolynomialCutoff P R t - f t| < ε := by
  have hinterval : -(R + 2) ≤ R + 2 := by linarith
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn
    (-(R + 2)) (R + 2) f f.continuous_toFun.continuousOn ε hε
  refine ⟨P, ?_⟩
  intro t
  by_cases ht : |t| ≤ R + 2
  · have htIcc : t ∈ Icc (-(R + 2)) (R + 2) :=
      ⟨neg_le_of_abs_le ht, le_of_abs_le ht⟩
    have hnear := hP t htIcc
    have hχnonneg := realCompactIntervalCutoff_nonnegative R t
    have hχle := realCompactIntervalCutoff_le_one R t
    rw [realPolynomialCutoff_apply]
    calc
      |P.eval t * realCompactIntervalCutoff R t - f t| =
          |realCompactIntervalCutoff R t * (P.eval t - f t)| := by
            rw [mul_sub, realCompactIntervalCutoff_mul_eq f hR hf]
            ring_nf
      _ = |realCompactIntervalCutoff R t| * |P.eval t - f t| := abs_mul _ _
      _ ≤ 1 * |P.eval t - f t| := by
        have habsχ : |realCompactIntervalCutoff R t| ≤ 1 := by
          rw [abs_of_nonneg hχnonneg]
          exact hχle
        exact mul_le_mul_of_nonneg_right habsχ (abs_nonneg _)
      _ < ε := by simpa using hnear
  · have ht' : R + 2 < |t| := lt_of_not_ge ht
    have hχnot : t ∉ tsupport (realCompactIntervalCutoff R) := by
      rw [realCompactIntervalCutoff_tsupport]
      simpa [abs_of_nonneg hR] using ht
    have hχzero : realCompactIntervalCutoff R t = 0 :=
      image_eq_zero_of_notMem_tsupport hχnot
    have hfnot : t ∉ tsupport f := by
      intro htf
      have hle : |t| ≤ R := hf htf
      linarith
    have hfzero : f t = 0 := image_eq_zero_of_notMem_tsupport hfnot
    rw [realPolynomialCutoff_apply, hχzero, mul_zero, hfzero, sub_zero, abs_zero]
    exact hε

/-- A single polynomial-cutoff sequence approximates a compactly supported continuous function
uniformly, while every approximant stays in one fixed compact packet. -/
theorem exists_realPolynomialCutoff_sequence_uniform
    (f : C_c(ℝ, ℝ)) {R : ℝ} (hR : 0 ≤ R)
    (hf : tsupport f ⊆ {t : ℝ | |t| ≤ R}) :
    ∃ P : ℕ → ℝ[X],
      (∀ n t, |realPolynomialCutoff (P n) R t - f t| < 1 / (n + 1 : ℝ)) ∧
      ∀ n, tsupport (realPolynomialCutoff (P n) R) ⊆ {t : ℝ | |t| ≤ R + 2} := by
  have hexists (n : ℕ) :
      ∃ P : ℝ[X], ∀ t, |realPolynomialCutoff P R t - f t| < 1 / (n + 1 : ℝ) := by
    apply exists_realPolynomialCutoff_uniform_near f hR hf
    positivity
  choose P hP using hexists
  refine ⟨P, hP, ?_⟩
  intro n
  have hs := realPolynomialCutoff_tsupport_subset (P n) R
  simpa [abs_of_nonneg hR] using hs

end SchwartzMap
