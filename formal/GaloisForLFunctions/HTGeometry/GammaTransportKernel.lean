import Mathlib

/-!
# The Gamma transport kernel

The transport operator of the completed Gamma problem is the second-difference average

`(R F)(L) = ∫_0^∞ [2F(L) − F(L+s) − F(L−s)] / (e^s − 1) ds`.

Its kernel `1/(e^s − 1)` is singular like `1/s` at the origin and decays like `e^{−s}` at infinity.
Neither tail obstructs convergence: at the origin the second difference of a `C²` profile vanishes
to second order, which beats the simple pole, and at infinity the second difference is merely
bounded while the kernel is exponentially small.

This file establishes the two kernel bounds and the exponential tail.  They are what makes the
transport operator well defined on bounded profiles with bounded second derivative.
-/

open MeasureTheory Set Real

namespace GaloisForLFunctions.HTGeometry

/-- The Gamma transport kernel `1/(e^s − 1)`. -/
noncomputable def gammaTransportKernel (s : ℝ) : ℝ := 1 / (Real.exp s - 1)

/-- On the positive ray the kernel is positive. -/
theorem gammaTransportKernel_pos {s : ℝ} (hs : 0 < s) : 0 < gammaTransportKernel s := by
  unfold gammaTransportKernel
  have hexp : 1 < Real.exp s := by
    have h := Real.exp_lt_exp.mpr hs
    rwa [Real.exp_zero] at h
  exact div_pos zero_lt_one (by linarith)

/-- **The simple pole at the origin.**  Since `s + 1 ≤ e^s`, the kernel is bounded by `1/s`. -/
theorem gammaTransportKernel_le_inv {s : ℝ} (hs : 0 < s) : gammaTransportKernel s ≤ 1 / s := by
  unfold gammaTransportKernel
  have hlin : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
  have hpos : 0 < Real.exp s - 1 := by
    have h := Real.exp_lt_exp.mpr hs
    rw [Real.exp_zero] at h
    linarith
  exact one_div_le_one_div_of_le hs (by linarith)

/-- **The exponential tail.**  Beyond `s = 1` the kernel is at most `2 e^{−s}`, because `e^s ≥ 2`
there, so subtracting one costs at most a factor two. -/
theorem gammaTransportKernel_le_two_mul_exp_neg {s : ℝ} (hs : 1 ≤ s) :
    gammaTransportKernel s ≤ 2 * Real.exp (-s) := by
  unfold gammaTransportKernel
  have hexp2 : (2 : ℝ) ≤ Real.exp s := by
    have h1 : Real.exp 1 ≤ Real.exp s := Real.exp_le_exp.mpr hs
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    linarith
  have hpos : 0 < Real.exp s - 1 := by linarith
  have hhalf : Real.exp s / 2 ≤ Real.exp s - 1 := by linarith
  have hexppos : 0 < Real.exp s := Real.exp_pos s
  have hrw : 2 * Real.exp (-s) = 2 / Real.exp s := by
    rw [Real.exp_neg]
    ring
  rw [hrw, div_le_div_iff₀ hpos hexppos]
  nlinarith [hhalf, hexppos]

/-- The kernel is measurable. -/
theorem measurable_gammaTransportKernel : Measurable gammaTransportKernel := by
  unfold gammaTransportKernel
  fun_prop

/-- **The kernel is integrable past the origin.**  Its exponential decay dominates. -/
theorem integrableOn_gammaTransportKernel_Ioi_one :
    IntegrableOn gammaTransportKernel (Ioi 1) := by
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi 1) := by
    have h := exp_neg_integrableOn_Ioi (1 : ℝ) zero_lt_one
    simpa only [neg_one_mul] using h
  have hdom : IntegrableOn (fun s : ℝ => 2 * Real.exp (-s)) (Ioi 1) := hbase.const_mul 2
  refine MeasureTheory.Integrable.mono' hdom
    measurable_gammaTransportKernel.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
  rw [Real.norm_eq_abs, abs_of_pos (gammaTransportKernel_pos (by linarith))]
  exact gammaTransportKernel_le_two_mul_exp_neg hs1

/-! ## The second difference kills the pole -/

/-- The symmetric second difference of a profile. -/
noncomputable def secondDifference (F : ℝ → ℝ) (L s : ℝ) : ℝ :=
  2 * F L - F (L + s) - F (L - s)

/-- The second difference of a bounded profile is bounded by four times the bound. -/
theorem abs_secondDifference_le_of_bounded {F : ℝ → ℝ} {M : ℝ} (hF : ∀ x, |F x| ≤ M)
    (L s : ℝ) : |secondDifference F L s| ≤ 4 * M := by
  unfold secondDifference
  have h1 := abs_le.mp (hF L)
  have h2 := abs_le.mp (hF (L + s))
  have h3 := abs_le.mp (hF (L - s))
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **The transport integrand is dominated past the origin.**  A bounded profile gives an
integrand bounded by `8M e^{−s}`, which is integrable on `(1, ∞)`. -/
theorem integrableOn_transport_integrand_Ioi_one {F : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ x, |F x| ≤ M) (hmeas : Measurable F) (L : ℝ) :
    IntegrableOn (fun s => secondDifference F L s * gammaTransportKernel s) (Ioi 1) := by
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi 1) := by
    have h := exp_neg_integrableOn_Ioi (1 : ℝ) zero_lt_one
    simpa only [neg_one_mul] using h
  have hdom : IntegrableOn (fun s : ℝ => 4 * M * (2 * Real.exp (-s))) (Ioi 1) :=
    (hbase.const_mul 2).const_mul (4 * M)
  have hsd : Measurable fun s => secondDifference F L s := by
    unfold secondDifference
    fun_prop
  refine MeasureTheory.Integrable.mono' hdom
    (hsd.mul measurable_gammaTransportKernel).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
  have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos (by linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hkpos]
  exact mul_le_mul (abs_secondDifference_le_of_bounded hF L s)
    (gammaTransportKernel_le_two_mul_exp_neg hs1) hkpos.le (by linarith)

end GaloisForLFunctions.HTGeometry
