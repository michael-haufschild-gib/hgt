import GaloisForLFunctions.HTGeometry.DigammaAsymptotic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The cubic Taylor bound for the complex logarithm, and the one-step Stirling defect

The Stirling ladder for `ψ = Γ'/Γ` is built from the functional equation `ψ(z+1) = ψ(z) + 1/z`.
Writing `g(z) = ψ(z) - log z + 1/(2z)` for the *Stirling defect*, the equation becomes

```text
g(z+1) - g(z) = 1/z - log(1 + 1/z) - 1/(2 z (z+1)),
```

whose right-hand side is `O(|z|^{-3})` — one order better than either term separately, because the
quadratic parts cancel.  That single cubic gain is what makes the telescoping series converge and
produce `ψ(z) = log z - 1/(2z) + O(|z|^{-2})`.

The cubic Taylor bound `‖log(1+u) - u + u²/2‖ ≤ ‖u‖³` on `‖u‖ ≤ 1/2` is proved from mathlib's
`Complex.hasSum_taylorSeries_log` by dropping the first two terms of the series.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-! ## The cubic Taylor bound -/

theorem norm_log_one_add_sub_taylor_two_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u) - u + u ^ 2 / 2‖ ≤ ‖u‖ ^ 3 := by
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hsum := Complex.hasSum_taylorSeries_log hu1
  have hsummable : Summable (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * u ^ n / (n : ℂ)) := hsum.summable
  have hsplit := hsummable.sum_add_tsum_nat_add 3
  have hlog : Complex.log (1 + u) = ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * u ^ n / (n : ℂ) :=
    hsum.tsum_eq.symm
  have hfirst : ∑ n ∈ Finset.range 3, (-1 : ℂ) ^ (n + 1) * u ^ n / (n : ℂ) = u - u ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
    ring
  have htail : Complex.log (1 + u) - u + u ^ 2 / 2
      = ∑' n : ℕ, (-1 : ℂ) ^ (n + 3 + 1) * u ^ (n + 3) / ((n + 3 : ℕ) : ℂ) := by
    rw [hlog, ← hsplit, hfirst]
    ring
  have hbound : ∀ n : ℕ, ‖(-1 : ℂ) ^ (n + 3 + 1) * u ^ (n + 3) / ((n + 3 : ℕ) : ℂ)‖
      ≤ (‖u‖ ^ 3 / 3) * ‖u‖ ^ n := by
    intro n
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    rw [hcast]
    have hden : (3 : ℝ) ≤ (n : ℝ) + 3 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hnum : ‖u‖ ^ (n + 3) = ‖u‖ ^ 3 * ‖u‖ ^ n := by
      rw [pow_add]
      ring
    rw [hnum]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 3)]
    have hpos : (0 : ℝ) ≤ ‖u‖ ^ 3 * ‖u‖ ^ n := by positivity
    nlinarith [hpos, hden]
  have hgeo : Summable (fun n : ℕ => (‖u‖ ^ 3 / 3) * ‖u‖ ^ n) :=
    (summable_geometric_of_lt_one hu0 hu1).mul_left _
  have hnormsummable : Summable (fun n : ℕ =>
      ‖(-1 : ℂ) ^ (n + 3 + 1) * u ^ (n + 3) / ((n + 3 : ℕ) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgeo
  rw [htail]
  refine le_trans (norm_tsum_le_tsum_norm hnormsummable) ?_
  refine le_trans (hnormsummable.tsum_le_tsum hbound hgeo) ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hu0 hu1]
  rw [div_mul_eq_mul_div, mul_comm]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [hinv, pow_nonneg hu0 3]

/-! ## The logarithm is additive along the right half-plane shift -/

theorem log_add_one_sub_log {z : ℂ} (hz : 0 < z.re) :
    Complex.log (z + 1) - Complex.log z = Complex.log (1 + 1 / z) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have : (z + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at this
    linarith
  have harg : |Complex.arg z| < Real.pi / 2 := by
    rw [abs_lt]
    exact ⟨Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz),
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)⟩
  have hz1re : 0 < (z + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have harg1 : |Complex.arg (z + 1)| < Real.pi / 2 := by
    rw [abs_lt]
    exact ⟨Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz1re),
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz1re)⟩
  have hquot : (1 : ℂ) + 1 / z = (z + 1) / z := by
    field_simp
  have hpi := Real.pi_pos
  obtain ⟨hargl, hargu⟩ := abs_lt.mp harg
  obtain ⟨harg1l, harg1u⟩ := abs_lt.mp harg1
  have hargz : Complex.arg z ≠ Real.pi := by
    intro h
    rw [h] at hargu
    linarith
  have hinvarg : Complex.arg z⁻¹ = -Complex.arg z := by
    have h := congrArg Complex.im (Complex.log_inv z hargz)
    simpa [Complex.log_im] using h
  have hmul : Complex.log ((z + 1) * z⁻¹) = Complex.log (z + 1) + Complex.log z⁻¹ := by
    refine Complex.log_mul hz1 (inv_ne_zero hz0) ?_
    rw [hinvarg]
    exact ⟨by linarith, by linarith⟩
  rw [hquot, div_eq_mul_inv, hmul, Complex.log_inv z hargz]
  ring

/-! ## The Stirling defect and its one-step gain -/

/-- The Stirling defect of the digamma function: what is left of `ψ` after the two leading terms
of the Stirling expansion are removed. -/
def digammaStirlingDefect (z : ℂ) : ℂ := Complex.digamma z - Complex.log z + 1 / (2 * z)

theorem digammaStirlingDefect_step {z : ℂ} (hz : 0 < z.re) :
    digammaStirlingDefect (z + 1) - digammaStirlingDefect z
      = 1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre : (z + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at hre
    linarith
  have hdig : Complex.digamma (z + 1) = Complex.digamma z + z⁻¹ := by
    refine Complex.digamma_apply_add_one z fun m => ?_
    intro h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [digammaStirlingDefect, digammaStirlingDefect, hdig, ← log_add_one_sub_log hz]
  field_simp
  ring

theorem norm_digammaStirlingDefect_step_le {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖digammaStirlingDefect (z + 1) - digammaStirlingDefect z‖ ≤ 2 / ‖z‖ ^ 3 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at h2
    simp at h2
    linarith
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre : (z + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at hre
    linarith
  set u : ℂ := 1 / z with hudef
  have hunorm : ‖u‖ = 1 / ‖z‖ := by rw [hudef, norm_div, norm_one]
  have huhalf : ‖u‖ ≤ 1 / 2 := by
    rw [hunorm]
    rw [div_le_div_iff₀ hzpos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hsplit : 1 / z - Complex.log (1 + 1 / z) - 1 / (2 * z * (z + 1))
      = -(Complex.log (1 + u) - u + u ^ 2 / 2) + 1 / (2 * z ^ 2 * (z + 1)) := by
    rw [hudef]
    field_simp
    ring
  rw [digammaStirlingDefect_step hz, hsplit]
  have hcube := norm_log_one_add_sub_taylor_two_le huhalf
  have hz1norm : ‖z‖ / 2 ≤ ‖z + 1‖ := by
    have h := norm_sub_le (z + 1) (1 : ℂ)
    rw [add_sub_cancel_right, norm_one] at h
    linarith
  have hz1pos : (0 : ℝ) < ‖z + 1‖ := by linarith
  have hsecond : ‖(1 : ℂ) / (2 * z ^ 2 * (z + 1))‖ ≤ 1 / ‖z‖ ^ 3 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_pow]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hz1norm, hzpos, pow_pos hzpos 2, pow_pos hzpos 3, sq_nonneg ‖z‖]
  have hfirst : ‖-(Complex.log (1 + u) - u + u ^ 2 / 2)‖ ≤ 1 / ‖z‖ ^ 3 := by
    rw [norm_neg]
    refine le_trans hcube (le_of_eq ?_)
    rw [hunorm, div_pow, one_pow]
  refine le_trans (norm_add_le _ _) ?_
  have : (1 : ℝ) / ‖z‖ ^ 3 + 1 / ‖z‖ ^ 3 = 2 / ‖z‖ ^ 3 := by ring
  linarith [hfirst, hsecond]

end

end GaloisForLFunctions.HTGeometry
