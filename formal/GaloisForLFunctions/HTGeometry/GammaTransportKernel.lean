import Mathlib
import GaloisForLFunctions.HTGeometry.PenalizedMaximum

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

/-! ## The exact tail integral

The kernel has an elementary primitive: `log(1 − e^{−s})` differentiates to `1/(e^s − 1)`.  So the
tail integral is exactly `q(L) = −log(1 − e^{−L})`.  This identity is what makes the boundary
correction of the half-line operator precisely the missing negative half-line of the
translation-invariant one.
-/

/-- **The kernel's primitive.**  `log(1 − e^{−s})` differentiates to the transport kernel. -/
theorem hasDerivAt_log_one_sub_exp_neg {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => Real.log (1 - Real.exp (-t))) (gammaTransportKernel s) s := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-s)) s := by
    have h := (hasDerivAt_neg s).exp
    have hv : Real.exp (-s) * (-1) = -Real.exp (-s) := by ring
    rwa [hv] at h
  have hinner : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-s)) s := by
    have h := (hasDerivAt_const s (1 : ℝ)).sub hexp
    have hv : (0 : ℝ) - -Real.exp (-s) = Real.exp (-s) := by ring
    rwa [hv] at h
  have hgt : 1 < Real.exp s := by
    have h : Real.exp 0 < Real.exp s := Real.exp_lt_exp.mpr hs
    rwa [Real.exp_zero] at h
  have hne : 1 - Real.exp (-s) ≠ 0 := by
    have hlt : Real.exp (-s) < 1 := by
      have h : Real.exp (-s) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      rwa [Real.exp_zero] at h
    linarith
  have hcomp := (Real.hasDerivAt_log hne).comp s hinner
  have hval : (1 - Real.exp (-s))⁻¹ * Real.exp (-s) = gammaTransportKernel s := by
    unfold gammaTransportKernel
    have hprod : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add]
      simp
    have hne2 : Real.exp s - 1 ≠ 0 := by linarith
    rw [inv_mul_eq_div, div_eq_div_iff hne hne2]
    linear_combination hprod
  rwa [hval] at hcomp

/-- The kernel is integrable on every ray that stays off the pole. -/
theorem integrableOn_gammaTransportKernel_Ioi {L : ℝ} (hL : 0 < L) :
    IntegrableOn gammaTransportKernel (Ioi L) := by
  rcases lt_or_ge L 1 with h | h
  case inr =>
    exact integrableOn_gammaTransportKernel_Ioi_one.mono_set fun x hx => lt_of_le_of_lt h hx
  · have hsplit : Ioi L = Ioc L 1 ∪ Ioi 1 := by
      ext x
      simp only [mem_Ioi, mem_union, mem_Ioc]
      constructor
      · intro hx
        rcases lt_or_ge 1 x with hx1 | hx1
        · exact Or.inr hx1
        · exact Or.inl ⟨hx, hx1⟩
      · rintro (⟨h1, _⟩ | h1)
        · exact h1
        · linarith
    have hIoc : IntegrableOn gammaTransportKernel (Ioc L 1) := by
      have hfin : IsFiniteMeasure (volume.restrict (Ioc L 1)) := by
        constructor
        simp
      have hdom : IntegrableOn (fun _ : ℝ => 1 / L) (Ioc L 1) := integrable_const _
      refine MeasureTheory.Integrable.mono' hdom
        measurable_gammaTransportKernel.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hxpos : (0 : ℝ) < x := lt_trans hL hx.1
      rw [Real.norm_eq_abs, abs_of_pos (gammaTransportKernel_pos hxpos)]
      exact (gammaTransportKernel_le_inv hxpos).trans (one_div_le_one_div_of_le hL hx.1.le)
    rw [hsplit]
    exact hIoc.union integrableOn_gammaTransportKernel_Ioi_one

/-- **The exact tail integral.**  `∫_L^∞ k(s) ds = −log(1 − e^{−L})`. -/
theorem integral_Ioi_gammaTransportKernel {L : ℝ} (hL : 0 < L) :
    (∫ s in Ioi L, gammaTransportKernel s) = -Real.log (1 - Real.exp (-L)) := by
  have hcont : ContinuousWithinAt (fun t => Real.log (1 - Real.exp (-t))) (Ici L) L := by
    have hne : 1 - Real.exp (-L) ≠ 0 := by
      have hlt : Real.exp (-L) < 1 := by
        have h : Real.exp (-L) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
        rwa [Real.exp_zero] at h
      linarith
    have hinnerc : ContinuousAt (fun t : ℝ => 1 - Real.exp (-t)) L := by fun_prop
    exact (hinnerc.log hne).continuousWithinAt
  have hderiv : ∀ x ∈ Ioi L, HasDerivAt (fun t => Real.log (1 - Real.exp (-t)))
      (gammaTransportKernel x) x := fun x hx =>
    hasDerivAt_log_one_sub_exp_neg (lt_trans hL hx)
  have hint : IntegrableOn gammaTransportKernel (Ioi L) := integrableOn_gammaTransportKernel_Ioi hL
  have hlim : Filter.Tendsto (fun t => Real.log (1 - Real.exp (-t))) Filter.atTop (nhds 0) := by
    have hexp : Filter.Tendsto (fun t : ℝ => 1 - Real.exp (-t)) Filter.atTop (nhds 1) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero
      simpa using (tendsto_const_nhds.sub h)
    have h2 := hexp.log (by norm_num : (1 : ℝ) ≠ 0)
    rwa [Real.log_one] at h2
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [hmain]
  ring

/-- The Gamma transport operator. -/
noncomputable def gammaTransport (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), secondDifference F L s * gammaTransportKernel s

/-! ## The boundary correction is the missing half-line

Extending a half-line profile by zero and running the *translation-invariant* operator over the
whole line produces, beyond `s = L`, a term in which the reflected argument has already left the
support.  There the second difference contributes `F(L)` alone, and integrating the kernel over
`(L, ∞)` returns exactly `q(L) = −log(1 − e^{−L})`.

So the boundary term `q·F` of the half-line operator is not a correction added by hand: it is the
part of the whole-line operator that sees the zero extension.
-/

/-- The extension of a half-line profile by zero. -/
noncomputable def zeroExtend (F : ℝ → ℝ) (x : ℝ) : ℝ := if 0 ≤ x then F x else 0

/-- Past the reflection point the zero extension has already vanished. -/
theorem zeroExtend_reflect_eq_zero {F : ℝ → ℝ} {L s : ℝ} (hs : L < s) :
    zeroExtend F (L - s) = 0 := by
  unfold zeroExtend
  rw [if_neg]
  linarith

/-- **The boundary term is the tail of the kernel.**  Beyond `s = L` the reflected argument has
left the support, so the integrand is `k(s) F(L)` and its integral is `q(L) F(L)`. -/
theorem integral_Ioi_gammaTransportKernel_reflect {F : ℝ → ℝ} {L : ℝ} (hL : 0 < L) :
    (∫ s in Ioi L, gammaTransportKernel s * (F L - zeroExtend F (L - s)))
      = -Real.log (1 - Real.exp (-L)) * F L := by
  have hcongr : (∫ s in Ioi L, gammaTransportKernel s * (F L - zeroExtend F (L - s)))
      = ∫ s in Ioi L, gammaTransportKernel s * F L := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [zeroExtend_reflect_eq_zero (mem_Ioi.mp hs), sub_zero]
  rw [hcongr, MeasureTheory.integral_mul_const, integral_Ioi_gammaTransportKernel hL]

/-! ## The transport term at a penalized maximizer

At a maximizer of a penalized profile the one-sided inequalities bound the second difference from
below by `−2 c s`, linear in the shift.  Against the transport kernel this is integrable on the
whole positive ray, because the kernel has a finite first moment: the simple pole is exactly
cancelled by the linear vanishing.  So the transport term is bounded below by a quantity
proportional to the penalty slope, which is what drives the slope to zero.
-/

/-- **One-sided inequalities bound the second difference.**  If a profile exceeds its value at `X`
by at most `c s` in both directions, its symmetric second difference is at least `−2 c s`. -/
theorem neg_le_secondDifference_of_one_sided {F : ℝ → ℝ} {X c s : ℝ}
    (hp : F (X + s) ≤ F X + c * s) (hm : F (X - s) ≤ F X + c * s) :
    -(2 * c * s) ≤ secondDifference F X s := by
  unfold secondDifference
  linarith

/-- The same bound against the kernel, which is positive on the ray. -/
theorem neg_le_transport_integrand_of_one_sided {F : ℝ → ℝ} {X c s : ℝ} (hs : 0 < s)
    (hp : F (X + s) ≤ F X + c * s) (hm : F (X - s) ≤ F X + c * s) :
    -(2 * c * (s * gammaTransportKernel s))
      ≤ secondDifference F X s * gammaTransportKernel s := by
  have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
  have h := neg_le_secondDifference_of_one_sided hp hm
  nlinarith [h, hk]

/-- **The lower bound is integrable.**  Linear vanishing against a kernel of finite first moment
integrates on the whole positive ray — the simple pole is exactly absorbed. -/
theorem integrable_transport_lower_bound (c : ℝ) :
    IntegrableOn (fun s => -(2 * c * (s * gammaTransportKernel s))) (Ioi 0) :=
  (integrableOn_id_mul_gammaTransportKernel_Ioi_zero.const_mul (2 * c)).neg

/-! ## The far tail of the transport integral

Beyond any fixed radius the second difference is merely bounded, and the kernel's tail mass is
`q(R) = −log(1 − e^{−R})` exactly.  So the far part of the transport integral is bounded by
`4M q(R)`, which tends to zero as the radius grows — the estimate that lets the near part be
handled separately by a pointwise inequality valid only for small shifts.
-/

/-- **The far tail is controlled by the kernel's tail mass.**  For a bounded profile the transport
integral beyond radius `R` is at most `4M q(R)` with `q(R) = −log(1 − e^{−R})`. -/
theorem abs_integral_transport_far_le {F : ℝ → ℝ} {M R : ℝ} (X : ℝ) (hR : 0 < R)
    (hF : ∀ x, |F x| ≤ M) (hmeas : Measurable F) :
    |∫ s in Ioi R, secondDifference F X s * gammaTransportKernel s|
      ≤ 4 * M * (-Real.log (1 - Real.exp (-R))) := by
  have hk := integrableOn_gammaTransportKernel_Ioi hR
  have hdom : IntegrableOn (fun s => 4 * M * gammaTransportKernel s) (Ioi R) := hk.const_mul _
  have hsd : Measurable fun s => secondDifference F X s := by
    unfold secondDifference; fun_prop
  have hptw : ∀ s ∈ Ioi R, ‖secondDifference F X s * gammaTransportKernel s‖
      ≤ 4 * M * gammaTransportKernel s := by
    intro s hs
    have hpos : 0 < s := lt_trans hR hs
    have hkpos := gammaTransportKernel_pos hpos
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hkpos]
    exact mul_le_mul_of_nonneg_right (abs_secondDifference_le_of_bounded hF X s) hkpos.le
  have hint : IntegrableOn (fun s => secondDifference F X s * gammaTransportKernel s) (Ioi R) := by
    refine Integrable.mono' hdom (hsd.mul measurable_gammaTransportKernel).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hptw s hs
  calc |∫ s in Ioi R, secondDifference F X s * gammaTransportKernel s|
      ≤ ∫ s in Ioi R, ‖secondDifference F X s * gammaTransportKernel s‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioi R, 4 * M * gammaTransportKernel s := by
        refine setIntegral_mono_on hint.norm hdom measurableSet_Ioi fun s hs => hptw s hs
    _ = 4 * M * ∫ s in Ioi R, gammaTransportKernel s := integral_const_mul _ _
    _ = 4 * M * (-Real.log (1 - Real.exp (-R))) := by
        rw [integral_Ioi_gammaTransportKernel hR]

/-! ## The near shifts at a penalized maximizer

Combining the two weight-removal directions, the second difference of the *unweighted* profile at a
penalized maximizer is bounded below by two terms, each carrying a factor `s`.  That linear
vanishing is what the kernel's finite first moment absorbs.
-/

/-- **The near-shift bound.**  At a penalized maximizer of the weighted profile, the unweighted
second difference is at least `−2δs/√X − 2(s/X)(f X + δs/√X)` for `0 ≤ s ≤ X/2`.  Both terms are
`O(s)`, so they integrate against the kernel. -/
theorem neg_le_secondDifference_of_weighted {f : ℝ → ℝ} {X s δ : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hsX : s ≤ X / 2) (hδ : 0 ≤ δ) (hf : 0 ≤ f X)
    (hp : Real.sqrt (X + s) * f (X + s) ≤ Real.sqrt X * f X + δ * s)
    (hm : Real.sqrt (X - s) * f (X - s) ≤ Real.sqrt X * f X + δ * s) :
    -(2 * (δ * s / Real.sqrt X) + 2 * (s / X) * (f X + δ * s / Real.sqrt X))
      ≤ secondDifference f X s := by
  have hfwd := le_of_weighted_le_forward hX hs hδ hf hp
  have hbwd := le_of_weighted_le_backward hX hs hsX hδ hf hm
  unfold secondDifference
  have hA : f X + δ * s / Real.sqrt X - f X = δ * s / Real.sqrt X := by ring
  nlinarith [hfwd, hbwd, hA]

/-- **The near-shift bound, linearised.**  On `0 ≤ s ≤ X/2` the two terms collapse to a single
multiple of `s`, with constant `2δ/√X + 2(f X + δ√X/2)/X`.  Only the kernel's *first* moment is
then needed — no second moment enters. -/
theorem neg_mul_le_secondDifference_of_weighted {f : ℝ → ℝ} {X s δ : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hsX : s ≤ X / 2) (hδ : 0 ≤ δ) (hf : 0 ≤ f X)
    (hp : Real.sqrt (X + s) * f (X + s) ≤ Real.sqrt X * f X + δ * s)
    (hm : Real.sqrt (X - s) * f (X - s) ≤ Real.sqrt X * f X + δ * s) :
    -((2 * δ / Real.sqrt X + 2 * (f X + δ * Real.sqrt X / 2) / X) * s)
      ≤ secondDifference f X s := by
  have hsq : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX.le
  have hbase := neg_le_secondDifference_of_weighted hX hs hsX hδ hf hp hm
  have hkey : δ * s / Real.sqrt X ≤ δ * Real.sqrt X / 2 := by
    rw [div_le_div_iff₀ hsq (by norm_num : (0:ℝ) < 2)]
    nlinarith [hsqsq, hsq, hδ, hsX, hs]
  have hstep : 2 * (s / X) * (f X + δ * s / Real.sqrt X)
      ≤ 2 * (f X + δ * Real.sqrt X / 2) / X * s := by
    have h1 : f X + δ * s / Real.sqrt X ≤ f X + δ * Real.sqrt X / 2 := by linarith [hkey]
    have h2 : (0:ℝ) ≤ 2 * (s / X) := by positivity
    have h3 : 2 * (s / X) * (f X + δ * s / Real.sqrt X)
        ≤ 2 * (s / X) * (f X + δ * Real.sqrt X / 2) := by nlinarith [h1, h2]
    have h4 : 2 * (s / X) * (f X + δ * Real.sqrt X / 2)
        = 2 * (f X + δ * Real.sqrt X / 2) / X * s := by field_simp
    linarith [h3, h4.le, h4.ge]
  have hfirst : 2 * (δ * s / Real.sqrt X) = 2 * δ / Real.sqrt X * s := by
    field_simp
  have hexp : (2 * δ / Real.sqrt X + 2 * (f X + δ * Real.sqrt X / 2) / X) * s
      = 2 * δ / Real.sqrt X * s + 2 * (f X + δ * Real.sqrt X / 2) / X * s := by ring
  rw [hexp]
  linarith [hbase, hstep, hfirst.le, hfirst.ge]

/-! ## The near part of the transport integral

Integrating the linearised bound against the kernel over the near window gives a lower bound
proportional to the kernel's first moment there.  The integrability of the transport integrand is
*hypothesis*, not conclusion: the maximizer's inequalities are one-sided and cannot bound the second
difference from above, so existence of the transport integral comes from the equation being solved.
-/

/-- **The near part is bounded below by the first moment.**  On the window `(0, X/2]` the transport
integrand is at least `−C s k(s)` with `C = 2δ/√X + 2(f X + δ√X/2)/X`, so its integral is at least
`−C` times the kernel's first moment over that window. -/
theorem neg_le_integral_transport_near {f : ℝ → ℝ} {X δ : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ)
    (hf : 0 ≤ f X)
    (hint : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hp : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt (X + s) * f (X + s) ≤ Real.sqrt X * f X + δ * s)
    (hm : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt (X - s) * f (X - s) ≤ Real.sqrt X * f X + δ * s) :
    -((2 * δ / Real.sqrt X + 2 * (f X + δ * Real.sqrt X / 2) / X)
        * ∫ s in Ioc 0 (X / 2), s * gammaTransportKernel s)
      ≤ ∫ s in Ioc 0 (X / 2), secondDifference f X s * gammaTransportKernel s := by
  set C : ℝ := 2 * δ / Real.sqrt X + 2 * (f X + δ * Real.sqrt X / 2) / X with hC
  have hmom : IntegrableOn (fun s => s * gammaTransportKernel s) (Ioc 0 (X / 2)) :=
    integrableOn_id_mul_gammaTransportKernel_Ioi_zero.mono_set fun x hx => hx.1
  have hdom : IntegrableOn (fun s => -(C * (s * gammaTransportKernel s))) (Ioc 0 (X / 2)) :=
    (hmom.const_mul C).neg
  have hptw : ∀ s ∈ Ioc (0:ℝ) (X / 2),
      -(C * (s * gammaTransportKernel s))
        ≤ secondDifference f X s * gammaTransportKernel s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs.1
    have hlin := neg_mul_le_secondDifference_of_weighted hX hs0 hs.2 hδ hf
      (hp s hs0 hs.2) (hm s hs0 hs.2)
    nlinarith [hlin, hk]
  have hmono := setIntegral_mono_on hdom hint measurableSet_Ioc hptw
  have hval : (∫ s in Ioc (0:ℝ) (X / 2), -(C * (s * gammaTransportKernel s)))
      = -(C * ∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s) := by
    rw [integral_neg, integral_const_mul]
  rwa [hval] at hmono

/-- **The transport integral splits at any radius.**  The near and far windows partition the
positive ray, so the operator is the sum of the two pieces bounded separately above. -/
theorem gammaTransport_split {f : ℝ → ℝ} {X : ℝ} (hX : 0 < X)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hfar : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioi (X / 2))) :
    gammaTransport f X
      = (∫ s in Ioc (0:ℝ) (X / 2), secondDifference f X s * gammaTransportKernel s)
        + ∫ s in Ioi (X / 2), secondDifference f X s * gammaTransportKernel s := by
  have hsplit : Ioi (0:ℝ) = Ioc 0 (X / 2) ∪ Ioi (X / 2) := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      rcases le_or_gt x (X / 2) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h1)
      · exact h1
      · linarith
  have hdisj : Disjoint (Ioc (0:ℝ) (X / 2)) (Ioi (X / 2)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.mpr hx')
  unfold gammaTransport
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hnear hfar]

/-! ## The transport operator at a penalized maximizer

Assembling the two windows: at a maximizer of the weighted profile the transport operator is
bounded below by a quantity built from the penalty slope and the far-tail mass, both of which
vanish as the maximizer runs to infinity with the slope going to zero.
-/

/-- **The transport operator is bounded below at a penalized maximizer.**  The near window
contributes `−C` times the kernel's first moment there, the far window at most `4M q(X/2)`.  Only
the near integrability is assumed — the far one is derived from boundedness. -/
theorem neg_le_gammaTransport_of_maximizer {f : ℝ → ℝ} {X δ M : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ)
    (hf : 0 ≤ f X) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hp : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt (X + s) * f (X + s) ≤ Real.sqrt X * f X + δ * s)
    (hm : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt (X - s) * f (X - s) ≤ Real.sqrt X * f X + δ * s) :
    -((2 * δ / Real.sqrt X + 2 * (f X + δ * Real.sqrt X / 2) / X)
        * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
      + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))) ≤ gammaTransport f X := by
  have hX2 : (0:ℝ) < X / 2 := by linarith
  have hsd : Measurable fun s => secondDifference f X s := by
    unfold secondDifference; fun_prop
  have hfar : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioi (X / 2)) := by
    have hdom : IntegrableOn (fun s => 4 * M * gammaTransportKernel s) (Ioi (X / 2)) :=
      (integrableOn_gammaTransportKernel_Ioi hX2).const_mul _
    refine Integrable.mono' hdom (hsd.mul measurable_gammaTransportKernel).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hpos : 0 < s := lt_trans hX2 hs
    have hk := gammaTransportKernel_pos hpos
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_right (abs_secondDifference_le_of_bounded hFb X s) hk.le
  have hsplit := gammaTransport_split hX hnear hfar
  have hnearbd := neg_le_integral_transport_near hX hδ hf hnear hp hm
  have hfarbd := abs_integral_transport_far_le (F := f) X hX2 hFb hmeas
  have hfarlow : -(4 * M * (-Real.log (1 - Real.exp (-(X / 2)))))
      ≤ ∫ s in Ioi (X / 2), secondDifference f X s * gammaTransportKernel s :=
    neg_le_of_abs_le hfarbd
  rw [hsplit]
  linarith [hnearbd, hfarlow]

/-! ## The mirrored near-shift bound

At a penalized *minimizer* the same construction bounds the second difference from **above**.  The
two weight-removal directions enter with their roles swapped relative to the maximizer case, and
both resulting terms again carry a factor `s`.
-/

/-- **The mirrored near-shift bound.**  At a penalized minimizer of the weighted profile, the
unweighted second difference is at most `2δs/√X + (f X − δs/√X)·s/(2X)` for `0 ≤ s ≤ X/2`. -/
theorem secondDifference_le_of_weighted {f : ℝ → ℝ} {X s δ : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hsX : s ≤ X / 2) (hnum : 0 ≤ f X - δ * s / Real.sqrt X)
    (hp : Real.sqrt X * f X - δ * s ≤ Real.sqrt (X + s) * f (X + s))
    (hm : Real.sqrt X * f X - δ * s ≤ Real.sqrt (X - s) * f (X - s)) :
    secondDifference f X s
      ≤ 2 * (δ * s / Real.sqrt X) + (f X - δ * s / Real.sqrt X) * (s / (2 * X)) := by
  have hfwd := le_of_weighted_ge_forward hX hs hnum hp
  have hbwd := le_of_weighted_ge_backward hX hs hsX hnum hm
  unfold secondDifference
  nlinarith [hfwd, hbwd]

/-- **The mirrored near part.**  At a penalized minimizer the near window contributes at most
`(2δ/√X + f X/(2X))` times the kernel's first moment there.  As in the maximizer case the
integrability of the transport integrand is hypothesis, supplied by the equation. -/
theorem integral_transport_near_le {f : ℝ → ℝ} {X δ : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ)
    (hint : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hnum : ∀ s, 0 ≤ s → s ≤ X / 2 → 0 ≤ f X - δ * s / Real.sqrt X)
    (hp : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt X * f X - δ * s ≤ Real.sqrt (X + s) * f (X + s))
    (hm : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt X * f X - δ * s ≤ Real.sqrt (X - s) * f (X - s)) :
    (∫ s in Ioc (0:ℝ) (X / 2), secondDifference f X s * gammaTransportKernel s)
      ≤ (2 * δ / Real.sqrt X + f X / (2 * X))
        * ∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s := by
  set C : ℝ := 2 * δ / Real.sqrt X + f X / (2 * X) with hC
  have hsq : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hmom : IntegrableOn (fun s => s * gammaTransportKernel s) (Ioc 0 (X / 2)) :=
    integrableOn_id_mul_gammaTransportKernel_Ioi_zero.mono_set fun x hx => hx.1
  have hdom : IntegrableOn (fun s => C * (s * gammaTransportKernel s)) (Ioc 0 (X / 2)) :=
    hmom.const_mul C
  have hptw : ∀ s ∈ Ioc (0:ℝ) (X / 2),
      secondDifference f X s * gammaTransportKernel s ≤ C * (s * gammaTransportKernel s) := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs.1
    have hbd := secondDifference_le_of_weighted hX hs0 hs.2 (hnum s hs0 hs.2)
      (hp s hs0 hs.2) (hm s hs0 hs.2)
    have hlin : 2 * (δ * s / Real.sqrt X) + (f X - δ * s / Real.sqrt X) * (s / (2 * X))
        ≤ C * s := by
      have hdiv : 0 ≤ δ * s / Real.sqrt X := by positivity
      have hpos : (0:ℝ) < 2 * X := by linarith
      have hsX : 0 ≤ s / (2 * X) := by positivity
      have h1 : (f X - δ * s / Real.sqrt X) * (s / (2 * X)) ≤ f X * (s / (2 * X)) := by
        nlinarith [hdiv, hsX]
      have h2 : 2 * (δ * s / Real.sqrt X) = 2 * δ / Real.sqrt X * s := by field_simp
      have h3 : f X * (s / (2 * X)) = f X / (2 * X) * s := by ring
      rw [hC]
      nlinarith [h1, h2.le, h2.ge, h3.le, h3.ge]
    nlinarith [hbd, hlin, hk]
  have hmono := setIntegral_mono_on hint hdom measurableSet_Ioc hptw
  rwa [integral_const_mul] at hmono

/-- **The transport operator is bounded above at a penalized minimizer.**  The mirror of
`neg_le_gammaTransport_of_maximizer`, reusing the same split and the same two-sided far tail. -/
theorem gammaTransport_le_of_minimizer {f : ℝ → ℝ} {X δ M : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ)
    (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hnum : ∀ s, 0 ≤ s → s ≤ X / 2 → 0 ≤ f X - δ * s / Real.sqrt X)
    (hp : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt X * f X - δ * s ≤ Real.sqrt (X + s) * f (X + s))
    (hm : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt X * f X - δ * s ≤ Real.sqrt (X - s) * f (X - s)) :
    gammaTransport f X
      ≤ (2 * δ / Real.sqrt X + f X / (2 * X))
          * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
        + 4 * M * (-Real.log (1 - Real.exp (-(X / 2)))) := by
  have hX2 : (0:ℝ) < X / 2 := by linarith
  have hsd : Measurable fun s => secondDifference f X s := by
    unfold secondDifference; fun_prop
  have hfar : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioi (X / 2)) := by
    have hdom : IntegrableOn (fun s => 4 * M * gammaTransportKernel s) (Ioi (X / 2)) :=
      (integrableOn_gammaTransportKernel_Ioi hX2).const_mul _
    refine Integrable.mono' hdom (hsd.mul measurable_gammaTransportKernel).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hpos : 0 < s := lt_trans hX2 hs
    have hk := gammaTransportKernel_pos hpos
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_right (abs_secondDifference_le_of_bounded hFb X s) hk.le
  have hsplit := gammaTransport_split hX hnear hfar
  have hnearbd := integral_transport_near_le hX hδ hnear hnum hp hm
  have hfarbd := abs_integral_transport_far_le (F := f) X hX2 hFb hmeas
  have hfarup : (∫ s in Ioi (X / 2), secondDifference f X s * gammaTransportKernel s)
      ≤ 4 * M * (-Real.log (1 - Real.exp (-(X / 2)))) := le_of_abs_le hfarbd
  rw [hsplit]
  linarith [hnearbd, hfarup]

/-! ## The transport bound directly from the maximizer

The bound above takes the two one-sided inequalities as inputs.  They are not assumptions: they are
`le_of_isMaxOn_penalized_shift` applied at the maximizer.  The version below chains them, so the
only hypotheses left are that `X` maximizes the penalized weighted profile and that the window
`[X − X/2, X + X/2]` stays inside the ray.
-/

/-- **The transport lower bound from the maximizer itself.**  No one-sided inequality is assumed —
both are derived from `IsMaxOn`. -/
theorem neg_le_gammaTransport_of_isMaxOn {f : ℝ → ℝ} {X δ M L₀ a : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hf : 0 ≤ f X) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hmax : IsMaxOn (penalized (fun L => Real.sqrt L * f L) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2) :
    -((2 * δ / Real.sqrt X + 2 * (f X + δ * Real.sqrt X / 2) / X)
        * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
      + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))) ≤ gammaTransport f X := by
  refine neg_le_gammaTransport_of_maximizer hX hδ hf hFb hmeas hnear ?_ ?_
  · intro s hs0 hsX
    have hp : X + s ∈ Ici a := by simp only [mem_Ici]; linarith
    have hm : X - s ∈ Ici a := by simp only [mem_Ici]; linarith
    exact (le_of_isMaxOn_penalized_shift hmax hδ hs0 hp hm).1
  · intro s hs0 hsX
    have hp : X + s ∈ Ici a := by simp only [mem_Ici]; linarith
    have hm : X - s ∈ Ici a := by simp only [mem_Ici]; linarith
    exact (le_of_isMaxOn_penalized_shift hmax hδ hs0 hp hm).2

/-- **The transport upper bound from the minimizer itself.**  The mirror of
`neg_le_gammaTransport_of_isMaxOn`: both one-sided inequalities are derived from `IsMaxOn` applied
to the negated weighted profile, not assumed. -/
theorem gammaTransport_le_of_isMaxOn_neg {f : ℝ → ℝ} {X δ M L₀ a : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hnum : ∀ s, 0 ≤ s → s ≤ X / 2 → 0 ≤ f X - δ * s / Real.sqrt X)
    (hmax : IsMaxOn (penalized (fun L => -(Real.sqrt L * f L)) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2) :
    gammaTransport f X
      ≤ (2 * δ / Real.sqrt X + f X / (2 * X))
          * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
        + 4 * M * (-Real.log (1 - Real.exp (-(X / 2)))) := by
  refine gammaTransport_le_of_minimizer hX hδ hFb hmeas hnear hnum ?_ ?_
  · intro s hs0 hsX
    have hp : X + s ∈ Ici a := by simp only [mem_Ici]; linarith
    have hm : X - s ∈ Ici a := by simp only [mem_Ici]; linarith
    exact (le_of_isMaxOn_penalized_neg_shift hmax hδ hs0 hp hm).1
  · intro s hs0 hsX
    have hp : X + s ∈ Ici a := by simp only [mem_Ici]; linarith
    have hm : X - s ∈ Ici a := by simp only [mem_Ici]; linarith
    exact (le_of_isMaxOn_penalized_neg_shift hmax hδ hs0 hp hm).2

/-! ## The tail mass vanishes

The far-window bound is proportional to the kernel's tail mass `q(R) = −log(1 − e^{−R})`, which
tends to zero as the radius grows.  With the radius taken to be `X/2`, the far contribution
therefore vanishes along any family of critical points running to infinity.
-/

open Filter in
/-- **The kernel's tail mass vanishes at infinity.** -/
theorem tendsto_kernelTailMass_atTop :
    Tendsto (fun R : ℝ => -Real.log (1 - Real.exp (-R))) atTop (nhds 0) := by
  have hexp : Tendsto (fun R : ℝ => 1 - Real.exp (-R)) atTop (nhds 1) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using (tendsto_const_nhds.sub h)
  have hlog := hexp.log (by norm_num : (1:ℝ) ≠ 0)
  rw [Real.log_one] at hlog
  simpa using hlog.neg

open Filter in
/-- The same at half the radius, the form the near/far split produces. -/
theorem tendsto_kernelTailMass_half_atTop :
    Tendsto (fun X : ℝ => -Real.log (1 - Real.exp (-(X / 2)))) atTop (nhds 0) :=
  tendsto_kernelTailMass_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2))

end GaloisForLFunctions.HTGeometry
