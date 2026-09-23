/-
# Existence of the entire regularized determinant

The finite truncations of a Hilbert–Schmidt kernel converge to it in Hilbert–Schmidt norm, and the
determinant exponent is Lipschitz in that norm with an *explicit* constant: on `‖z‖ ≤ r`, with
`M = ‖K‖_HS` and `rM < 1`,

  `‖fredholmExp A z − fredholmExp B z‖ ≤ ‖A − B‖_HS · r²M/(1 − rM)`,

because the factor `k+2` in the Lipschitz estimate for the power traces cancels the `1/(k+2)` of
the exponent series.  Hence the truncated determinants converge uniformly on a closed disc around
the origin.

Main results:
* `norm_fredholmExp_le`, `norm_fredholmExp_sub_le` — the exponent bounds.
* `norm_fredholmDet_sub_le` — the determinant difference on a closed disc.
-/
import GaloisForLFunctions.HTGeometry.FiniteDeterminantLogSeries
import GaloisForLFunctions.HTGeometry.EntireOrderTwoSeries
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantEntire
import Mathlib.Analysis.Complex.Exponential

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Metric Filter

variable {ι : Type*}

/-- The geometric majorant of the exponent series. -/
theorem norm_fredholmExp_le {K : ι × ι → ℂ} (hK : IsHS K) {M r : ℝ} (hr : 0 ≤ r)
    (hKM : hsNorm K ≤ M) (hM : 0 ≤ M) (hrM : r * M < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖fredholmExp K z‖ ≤ (r * M) ^ (2 : ℕ) / (1 - r * M) := by
  have hrM0 : 0 ≤ r * M := mul_nonneg hr hM
  have hzK : ‖z‖ * hsNorm K < 1 :=
    lt_of_le_of_lt (mul_le_mul hz hKM (hsNorm_nonneg K) hr) hrM
  have hgeom : Summable fun k : ℕ => (r * M) ^ (k + 2) :=
    ((summable_geometric_of_lt_one hrM0 hrM).mul_left ((r * M) ^ (2 : ℕ))).congr
      fun k => by rw [pow_add]; ring
  have hterm : ∀ k : ℕ,
      ‖z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (∑' i, hsPow K (k + 1) (i, i))‖ ≤ (r * M) ^ (k + 2) := by
    intro k
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have hcn : ‖∑' i, hsPow K (k + 1) (i, i)‖ ≤ hsNorm K ^ (k + 2) := hsTrace_hsPow_norm_le hK k
    have hden : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      push_cast
      linarith
    have hzp : ‖z‖ ^ (k + 2) ≤ r ^ (k + 2) := pow_le_pow_left₀ (norm_nonneg z) hz _
    calc ‖z‖ ^ (k + 2) / ((k + 2 : ℕ) : ℝ) * ‖∑' i, hsPow K (k + 1) (i, i)‖
        ≤ r ^ (k + 2) * M ^ (k + 2) := by
          refine mul_le_mul ((div_le_self (by positivity) hden).trans hzp)
            (hcn.trans (pow_le_pow_left₀ (hsNorm_nonneg K) hKM _)) (norm_nonneg _) (by positivity)
      _ = (r * M) ^ (k + 2) := by rw [mul_pow]
  have hnorm : Summable fun k : ℕ =>
      ‖z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (∑' i, hsPow K (k + 1) (i, i))‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hgeom
  calc ‖fredholmExp K z‖ ≤ ∑' k : ℕ, (r * M) ^ (k + 2) :=
        (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hterm hnorm hgeom)
    _ = (r * M) ^ (2 : ℕ) / (1 - r * M) := by
        rw [show (fun k : ℕ => (r * M) ^ (k + 2)) = fun k : ℕ => (r * M) ^ (2 : ℕ) * (r * M) ^ k from
          funext fun k => by rw [pow_add]; ring, tsum_mul_left,
          tsum_geometric_of_lt_one hrM0 hrM, ← div_eq_mul_inv]

/-- **The exponent is Lipschitz in the Hilbert–Schmidt norm**, with the factor `k+2` of the trace
estimate cancelling the `1/(k+2)` of the series. -/
theorem norm_fredholmExp_sub_le {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) {M r : ℝ}
    (hr : 0 ≤ r) (hAM : hsNorm A ≤ M) (hBM : hsNorm B ≤ M) (hM : 0 ≤ M) (hrM : r * M < 1)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖fredholmExp A z - fredholmExp B z‖ ≤ hsNorm (A - B) * (r ^ (2 : ℕ) * M / (1 - r * M)) := by
  have hrM0 : 0 ≤ r * M := mul_nonneg hr hM
  have hzA : ‖z‖ * hsNorm A < 1 := lt_of_le_of_lt (mul_le_mul hz hAM (hsNorm_nonneg A) hr) hrM
  have hzB : ‖z‖ * hsNorm B < 1 := lt_of_le_of_lt (mul_le_mul hz hBM (hsNorm_nonneg B) hr) hrM
  have hsA := fredholmExp_summable hA z hzA
  have hsB := fredholmExp_summable hB z hzB
  have hgeom : Summable fun k : ℕ => hsNorm (A - B) * (r ^ (2 : ℕ) * M * (r * M) ^ k) := by
    refine Summable.mul_left _ (Summable.mul_left _ (summable_geometric_of_lt_one hrM0 hrM))
  have hterm : ∀ k : ℕ,
      ‖z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (∑' i, hsPow A (k + 1) (i, i))
        - z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (∑' i, hsPow B (k + 1) (i, i))‖
        ≤ hsNorm (A - B) * (r ^ (2 : ℕ) * M * (r * M) ^ k) := by
    intro k
    rw [← mul_sub, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have hdiff := hsTrace_hsPow_sub_norm_le hA hB hAM hBM k
    have hzp : ‖z‖ ^ (k + 2) ≤ r ^ (k + 2) := pow_le_pow_left₀ (norm_nonneg z) hz _
    have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    calc ‖z‖ ^ (k + 2) / ((k + 2 : ℕ) : ℝ)
            * ‖(∑' i, hsPow A (k + 1) (i, i)) - ∑' i, hsPow B (k + 1) (i, i)‖
        ≤ r ^ (k + 2) / ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℝ) * M ^ (k + 1) * hsNorm (A - B)) := by
          refine mul_le_mul (by gcongr) hdiff (norm_nonneg _) (by positivity)
      _ = hsNorm (A - B) * (r ^ (2 : ℕ) * M * (r * M) ^ k) := by
          have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
          rw [hcast]
          field_simp
          ring
  have hnorm : Summable fun k : ℕ =>
      ‖z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (∑' i, hsPow A (k + 1) (i, i))
        - z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (∑' i, hsPow B (k + 1) (i, i))‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hgeom
  rw [fredholmExp, fredholmExp, ← hsA.tsum_sub hsB]
  calc ‖∑' k : ℕ, (z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (∑' i, hsPow A (k + 1) (i, i))
          - z ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (∑' i, hsPow B (k + 1) (i, i)))‖
      ≤ ∑' k : ℕ, hsNorm (A - B) * (r ^ (2 : ℕ) * M * (r * M) ^ k) :=
        (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hterm hnorm hgeom)
    _ = hsNorm (A - B) * (r ^ (2 : ℕ) * M / (1 - r * M)) := by
        rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hrM0 hrM, ← div_eq_mul_inv]

/-- **The determinants differ by at most a constant times the Hilbert–Schmidt distance**, uniformly
on the closed disc, provided the exponent difference is at most one. -/
theorem norm_fredholmDet_sub_le {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) {M r : ℝ}
    (hr : 0 ≤ r) (hAM : hsNorm A ≤ M) (hBM : hsNorm B ≤ M) (hM : 0 ≤ M) (hrM : r * M < 1)
    {z : ℂ} (hz : ‖z‖ ≤ r)
    (hsmall : hsNorm (A - B) * (r ^ (2 : ℕ) * M / (1 - r * M)) ≤ 1) :
    ‖fredholmDet A z - fredholmDet B z‖
      ≤ 2 * Real.exp ((r * M) ^ (2 : ℕ) / (1 - r * M)) * (hsNorm (A - B) * (r ^ (2 : ℕ) * M / (1 - r * M))) := by
  have hEdiff := norm_fredholmExp_sub_le hA hB hr hAM hBM hM hrM hz
  have hEB := norm_fredholmExp_le hB hr hBM hM hrM hz
  have hfactor : fredholmDet A z - fredholmDet B z
      = Complex.exp (-fredholmExp B z) * (Complex.exp (fredholmExp B z - fredholmExp A z) - 1) := by
    rw [fredholmDet, fredholmDet, mul_sub, mul_one, ← Complex.exp_add]
    ring_nf
  rw [hfactor, norm_mul]
  have h1 : ‖Complex.exp (-fredholmExp B z)‖ ≤ Real.exp ((r * M) ^ (2 : ℕ) / (1 - r * M)) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    calc (-fredholmExp B z).re ≤ ‖-fredholmExp B z‖ := Complex.re_le_norm _
      _ = ‖fredholmExp B z‖ := norm_neg _
      _ ≤ (r * M) ^ (2 : ℕ) / (1 - r * M) := hEB
  have hnormsub : ‖fredholmExp B z - fredholmExp A z‖
      ≤ hsNorm (A - B) * (r ^ (2 : ℕ) * M / (1 - r * M)) := by
    rw [← norm_neg]
    simpa using hEdiff
  have h2 : ‖Complex.exp (fredholmExp B z - fredholmExp A z) - 1‖
      ≤ 2 * (hsNorm (A - B) * (r ^ (2 : ℕ) * M / (1 - r * M))) :=
    le_trans (Complex.norm_exp_sub_one_le (le_trans hnormsub hsmall))
      (by linarith [hnormsub])
  calc ‖Complex.exp (-fredholmExp B z)‖ * ‖Complex.exp (fredholmExp B z - fredholmExp A z) - 1‖
      ≤ Real.exp ((r * M) ^ (2 : ℕ) / (1 - r * M))
          * (2 * (hsNorm (A - B) * (r ^ (2 : ℕ) * M / (1 - r * M)))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_nonneg _)
    _ = 2 * Real.exp ((r * M) ^ (2 : ℕ) / (1 - r * M))
          * (hsNorm (A - B) * (r ^ (2 : ℕ) * M / (1 - r * M))) := by ring

end GaloisForLFunctions.HTGeometry
