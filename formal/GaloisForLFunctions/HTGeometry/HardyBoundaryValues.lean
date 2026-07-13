import Mathlib
import GaloisForLFunctions.HTGeometry.FourierParseval

/-!
# `L²` boundary values of Hardy `H²` functions

For an analytic (`H²`) coefficient sequence `a ∈ ℓ²(ℤ)` supported on nonnegative frequencies, its
Fourier synthesis `g = ∑ aₙ e^{inθ} ∈ L²` is the `L²` limit of the radial dilates
`F_r = ∑ aₙ rⁿ e^{inθ}` as `r → 1⁻`.  Concretely:

* `hardy_boundary_L2_eq` — for `r ∈ [0,1]`, `‖F_r - g‖² = ∑ₙ ‖(rⁿ-1)aₙ‖²` (Parseval);
* `tendsto_radial_defect` — that defect tends to `0` as `r → 1⁻` (dominated convergence).

Together they give the existence of `L²` boundary values, an input of the Riesz factorization
behind the F.&M. Riesz theorem.
-/

open scoped ENNReal
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The radial multiplier: `rⁿ` on nonnegative frequencies, `0` on negative ones. -/
noncomputable def radialMult (r : ℝ) (n : ℤ) : ℂ := if 0 ≤ n then (r : ℂ) ^ n.toNat else 0

theorem norm_radialMult_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℤ) :
    ‖radialMult r n‖ ≤ 1 := by
  unfold radialMult
  split_ifs with h
  · rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact pow_le_one₀ hr0 hr1
  · simp

/-- Multiplying an `ℓ²` sequence pointwise by a sequence bounded by `1` keeps it in `ℓ²`. -/
theorem memLp_mul_of_bounded {a : lp (fun _ : ℤ => ℂ) 2} {c : ℤ → ℂ} (hc : ∀ n, ‖c n‖ ≤ 1) :
    Memℓp (fun n => c n * a n) 2 :=
  (lp.memℓp a).mono' (fun n => by
    rw [norm_mul]
    calc ‖c n‖ * ‖a n‖ ≤ 1 * ‖a n‖ := mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)
      _ = ‖(a : ℤ → ℂ) n‖ := one_mul _)

/-- **Parseval identification of the radial `L²` defect.**  For `r ∈ [0,1]` the squared `L²`
distance between the radial dilate `F_r` and the boundary function `g` equals `∑ₙ ‖(rⁿ-1)aₙ‖²`. -/
theorem hardy_boundary_L2_eq (a : lp (fun _ : ℤ => ℂ) 2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖(fourierBasis.repr.symm (⟨fun n => radialMult r n * a n,
          memLp_mul_of_bounded (norm_radialMult_le_one hr0 hr1)⟩ : lp (fun _ : ℤ => ℂ) 2) :
        Lp ℂ 2 (@AddCircle.haarAddCircle 1 ⟨one_pos⟩)) - fourierBasis.repr.symm a‖ ^ 2
      = ∑' n : ℤ, ‖(radialMult r n - 1) * a n‖ ^ 2 := by
  rw [norm_sub_repr_symm_sq]
  refine tsum_congr (fun n => ?_)
  show ‖radialMult r n * a n - a n‖ ^ 2 = ‖(radialMult r n - 1) * a n‖ ^ 2
  rw [show radialMult r n * a n - a n = (radialMult r n - 1) * a n from by ring]

/-- **The radial `L²` defect vanishes at the boundary.**  For an analytic (`H²`) sequence `a`,
`∑ₙ ‖(rⁿ-1)aₙ‖² → 0` as `r → 1⁻` — the radial dilates converge to the boundary function in `L²`. -/
theorem tendsto_radial_defect (a : lp (fun _ : ℤ => ℂ) 2)
    (ha0 : ∀ n : ℤ, n < 0 → a n = 0) :
    Tendsto (fun r : ℝ => ∑' n : ℤ, ‖(radialMult r n - 1) * a n‖ ^ 2) (𝓝[<] 1) (𝓝 0) := by
  have hsum : Summable (fun n : ℤ => (4 : ℝ) * ‖a n‖ ^ 2) := by
    have h := (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat] at h
    have h2 : Summable (fun n : ℤ => ‖a n‖ ^ 2) := by
      convert h using 2 with n; rw [← Real.rpow_natCast]; norm_num
    exact h2.mul_left 4
  have hzero : (0 : ℝ) = ∑' _n : ℤ, (0 : ℝ) := by simp
  rw [hzero]
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro n
    by_cases hn : 0 ≤ n
    · have hc : Continuous (fun r : ℝ => ‖(radialMult r n - 1) * a n‖ ^ 2) := by
        simp only [radialMult, if_pos hn]
        fun_prop
      have hlim : ‖(radialMult 1 n - 1) * a n‖ ^ 2 = 0 := by simp [radialMult, if_pos hn]
      have ht := hc.tendsto 1
      rw [hlim] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    · have haz : a n = 0 := ha0 n (lt_of_not_ge hn)
      simp only [haz, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact tendsto_const_nhds
  · have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
      rw [← Set.Ioi_inter_Iio]
      exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with r hr n
    rw [Set.mem_Ioo] at hr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, mul_pow]
    have hb : ‖radialMult r n - (1 : ℂ)‖ ≤ 2 :=
      le_trans (norm_sub_le _ _) (by
        rw [norm_one]; linarith [norm_radialMult_le_one hr.1.le hr.2.le n])
    have hb2 : ‖radialMult r n - (1 : ℂ)‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (radialMult r n - 1)]
    calc ‖radialMult r n - 1‖ ^ 2 * ‖a n‖ ^ 2 ≤ 4 * ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hb2 (by positivity)
      _ = 4 * ‖a n‖ ^ 2 := rfl

end GaloisForLFunctions.HTGeometry
