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

/-! ## The near-origin half

At the origin the second difference vanishes to first order already, which is enough: paired
against a simple pole it leaves a *bounded* integrand.  Second-order vanishing is not needed, so a
Lipschitz profile suffices and no second derivative enters.
-/

/-- **The second difference of a Lipschitz profile vanishes linearly.**  Grouping the three terms
into two increments gives `|2F(L) − F(L+s) − F(L−s)| ≤ 2K|s|`. -/
theorem abs_secondDifference_le_of_lipschitz {F : ℝ → ℝ} {K : ℝ}
    (hK : ∀ x y, |F x - F y| ≤ K * |x - y|) (L s : ℝ) :
    |secondDifference F L s| ≤ 2 * K * |s| := by
  unfold secondDifference
  have hd1 : |L - (L + s)| = |s| := by
    rw [show L - (L + s) = -s by ring, abs_neg]
  have hd2 : |L - (L - s)| = |s| := by
    rw [show L - (L - s) = s by ring]
  have h1 : |F L - F (L + s)| ≤ K * |s| := by
    have h := hK L (L + s)
    rwa [hd1] at h
  have h2 : |F L - F (L - s)| ≤ K * |s| := by
    have h := hK L (L - s)
    rwa [hd2] at h
  have hsplit : 2 * F L - F (L + s) - F (L - s)
      = (F L - F (L + s)) + (F L - F (L - s)) := by ring
  rw [hsplit]
  calc |(F L - F (L + s)) + (F L - F (L - s))|
      ≤ |F L - F (L + s)| + |F L - F (L - s)| := abs_add_le _ _
    _ ≤ K * |s| + K * |s| := add_le_add h1 h2
    _ = 2 * K * |s| := by ring

/-- **The near half of well-definedness.**  On `(0,1)` the transport integrand of a Lipschitz
profile is bounded by the constant `2K`: the linear vanishing of the second difference exactly
cancels the simple pole. -/
theorem integrableOn_transport_integrand_Ioo_zero_one {F : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x y, |F x - F y| ≤ K * |x - y|) (hmeas : Measurable F) (L : ℝ) :
    IntegrableOn (fun s => secondDifference F L s * gammaTransportKernel s) (Ioo 0 1) := by
  have hsd : Measurable fun s => secondDifference F L s := by
    unfold secondDifference
    fun_prop
  have hdom : IntegrableOn (fun _ : ℝ => 2 * K) (Ioo 0 1) := by
    have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
      constructor
      simp
    exact integrable_const _
  refine MeasureTheory.Integrable.mono' hdom
    (hsd.mul measurable_gammaTransportKernel).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hspos : (0 : ℝ) < s := hs.1
  have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hspos
  have habs : |s| = s := abs_of_pos hspos
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hkpos]
  have hbd : |secondDifference F L s| * gammaTransportKernel s ≤ 2 * K * |s| * (1 / s) := by
    refine mul_le_mul (abs_secondDifference_le_of_lipschitz hK L s)
      (gammaTransportKernel_le_inv hspos) hkpos.le ?_
    rw [habs]
    positivity
  calc |secondDifference F L s| * gammaTransportKernel s
      ≤ 2 * K * |s| * (1 / s) := hbd
    _ = 2 * K := by rw [habs]; field_simp

/-- **The transport operator is well defined on Lipschitz profiles.**  Both tails converge, so the
integrand is integrable on the whole positive ray.  The kernel's simple pole is cancelled by the
second difference at the origin and its exponential decay handles infinity. -/
theorem integrableOn_transport_integrand_Ioi_zero {F : ℝ → ℝ} {K M : ℝ} (hK0 : 0 ≤ K) (hM : 0 ≤ M)
    (hK : ∀ x y, |F x - F y| ≤ K * |x - y|) (hF : ∀ x, |F x| ≤ M) (hmeas : Measurable F) (L : ℝ) :
    IntegrableOn (fun s => secondDifference F L s * gammaTransportKernel s) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro hx
      rcases lt_or_ge x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h1)
      · exact h1
      · linarith
  have hIci : IntegrableOn (fun s => secondDifference F L s * gammaTransportKernel s) (Ici 1) :=
    (integrableOn_transport_integrand_Ioi_one hM hF hmeas L).congr_set_ae Ioi_ae_eq_Ici.symm
  rw [hsplit]
  exact (integrableOn_transport_integrand_Ioo_zero_one hK0 hK hmeas L).union hIci

/-! ## The kernel has a finite first moment

The pairing that produces the averaged trace converges because `∫_0^∞ s k(s) ds < ∞`.  Near the
origin the simple pole is exactly cancelled by the factor `s`, leaving a bounded integrand; past
`s = 1` the exponential decay wins against the linear factor.
-/

/-- Past the origin the linear factor is absorbed by half the exponential decay. -/
theorem id_mul_gammaTransportKernel_le {s : ℝ} (hs : 1 ≤ s) :
    s * gammaTransportKernel s ≤ 4 * Real.exp (-(s / 2)) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hker := gammaTransportKernel_le_two_mul_exp_neg hs
  have hlin : s ≤ 2 * Real.exp (s / 2) := by
    have h := Real.add_one_le_exp (s / 2)
    linarith
  have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs0
  have hE : Real.exp (-s) = Real.exp (-(s / 2)) * Real.exp (-(s / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hinv : Real.exp (s / 2) * Real.exp (-(s / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hepos : 0 < Real.exp (-(s / 2)) := Real.exp_pos _
  have hkey : s * Real.exp (-(s / 2)) ≤ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hlin hepos.le
    rwa [mul_assoc, hinv, mul_one] at hmul
  calc s * gammaTransportKernel s
      ≤ s * (2 * Real.exp (-s)) := mul_le_mul_of_nonneg_left hker hs0.le
    _ = 2 * (s * Real.exp (-(s / 2))) * Real.exp (-(s / 2)) := by rw [hE]; ring
    _ ≤ 2 * 2 * Real.exp (-(s / 2)) := by nlinarith [hkey, hepos]
    _ = 4 * Real.exp (-(s / 2)) := by ring

/-- **The first moment converges past the origin.** -/
theorem integrableOn_id_mul_gammaTransportKernel_Ioi_one :
    IntegrableOn (fun s => s * gammaTransportKernel s) (Ioi 1) := by
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-(s / 2))) (Ioi 1) := by
    have h := exp_neg_integrableOn_Ioi (1 : ℝ) (by norm_num : (0:ℝ) < 1/2)
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    ring_nf
  have hdom : IntegrableOn (fun s : ℝ => 4 * Real.exp (-(s / 2))) (Ioi 1) := hbase.const_mul 4
  refine MeasureTheory.Integrable.mono' hdom
    ((measurable_id.mul measurable_gammaTransportKernel)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
  have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos (by linarith)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact id_mul_gammaTransportKernel_le hs1

/-- **The first moment converges at the origin**, where the factor `s` exactly cancels the pole. -/
theorem integrableOn_id_mul_gammaTransportKernel_Ioo :
    IntegrableOn (fun s => s * gammaTransportKernel s) (Ioo 0 1) := by
  have hdom : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 1) := by
    have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
      constructor
      simp
    exact integrable_const _
  refine MeasureTheory.Integrable.mono' hdom
    ((measurable_id.mul measurable_gammaTransportKernel)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hspos : (0 : ℝ) < s := hs.1
  have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hspos
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hbd : s * gammaTransportKernel s ≤ s * (1 / s) :=
    mul_le_mul_of_nonneg_left (gammaTransportKernel_le_inv hspos) hspos.le
  calc s * gammaTransportKernel s ≤ s * (1 / s) := hbd
    _ = 1 := by field_simp

/-- **The kernel has a finite first moment.**  This is what makes the bounded-variation pairing
that produces the averaged trace absolutely convergent. -/
theorem integrableOn_id_mul_gammaTransportKernel_Ioi_zero :
    IntegrableOn (fun s => s * gammaTransportKernel s) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro hx
      rcases lt_or_ge x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h1)
      · exact h1
      · linarith
  have hIci : IntegrableOn (fun s => s * gammaTransportKernel s) (Ici 1) :=
    integrableOn_id_mul_gammaTransportKernel_Ioi_one.congr_set_ae Ioi_ae_eq_Ici.symm
  rw [hsplit]
  exact integrableOn_id_mul_gammaTransportKernel_Ioo.union hIci

/-- The Gamma transport operator. -/
noncomputable def gammaTransport (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), secondDifference F L s * gammaTransportKernel s

end GaloisForLFunctions.HTGeometry
