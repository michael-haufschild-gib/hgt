import GaloisForLFunctions.HTGeometry.MellinReflectionKernel
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import GaloisForLFunctions.HTGeometry.SineVerticalDecay

/-!
# Mellin convergence of the Cauchy kernel

The Cauchy kernel `u ↦ u / (1 + u)` is bounded at infinity and vanishes linearly at the origin, so
its Mellin integral converges exactly on the strip `-1 < Re s < 0`.  There its value is the negative
reflection kernel.

This is the analytic hypothesis of the Mellin inversion that represents `x / (n^s + x)` as a
vertical integral.
-/

open Set MeasureTheory Complex Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry

/-- The Cauchy kernel, as a complex-valued function of a positive real. -/
noncomputable def cauchyKernel (u : ℝ) : ℂ := (u : ℂ) / (1 + (u : ℂ))

theorem cauchyKernel_ofReal (u : ℝ) : cauchyKernel u = ((u / (1 + u) : ℝ) : ℂ) := by
  rw [cauchyKernel]
  push_cast
  ring

theorem norm_cauchyKernel {u : ℝ} (hu : 0 < u) : ‖cauchyKernel u‖ = u / (1 + u) := by
  rw [cauchyKernel_ofReal, Complex.norm_real, Real.norm_eq_abs]
  refine abs_of_nonneg ?_
  positivity

theorem norm_cauchyKernel_le_one {u : ℝ} (hu : 0 < u) : ‖cauchyKernel u‖ ≤ 1 := by
  rw [norm_cauchyKernel hu, div_le_one (by linarith)]
  linarith

theorem norm_cauchyKernel_le_self {u : ℝ} (hu : 0 < u) : ‖cauchyKernel u‖ ≤ u := by
  rw [norm_cauchyKernel hu, div_le_iff₀ (by linarith)]
  nlinarith

theorem continuousOn_cauchyKernel : ContinuousOn cauchyKernel (Ioi (0 : ℝ)) := by
  intro u hu
  have hupos : (0 : ℝ) < u := hu
  have hden : (1 : ℂ) + (u : ℂ) ≠ 0 := by
    intro h
    have : ((1 + u : ℝ) : ℂ) = 0 := by push_cast; exact h
    have hzero : (1 : ℝ) + u = 0 := Complex.ofReal_eq_zero.mp this
    linarith
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.div ?_ ?_ hden
  · exact Complex.continuous_ofReal.continuousAt
  · exact continuousAt_const.add Complex.continuous_ofReal.continuousAt

theorem locallyIntegrableOn_cauchyKernel :
    LocallyIntegrableOn cauchyKernel (Ioi (0 : ℝ)) :=
  continuousOn_cauchyKernel.locallyIntegrableOn measurableSet_Ioi

theorem isBigO_cauchyKernel_atTop :
    cauchyKernel =O[atTop] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_cauchyKernel_le_one hu

theorem isBigO_cauchyKernel_zero :
    cauchyKernel =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-(-1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hupos : (0 : ℝ) < u := hu
  rw [neg_neg, Real.rpow_one, Real.norm_eq_abs, abs_of_pos hupos, one_mul]
  exact norm_cauchyKernel_le_self hupos

/-- **The Mellin integral of the Cauchy kernel converges on the strip.** -/
theorem mellinConvergent_cauchyKernel {s : ℂ} (h1 : -1 < s.re) (h2 : s.re < 0) :
    MellinConvergent cauchyKernel s :=
  mellinConvergent_of_isBigO_rpow locallyIntegrableOn_cauchyKernel
    isBigO_cauchyKernel_atTop h2 isBigO_cauchyKernel_zero h1

/-- **The Mellin transform of the Cauchy kernel is the negative reflection kernel.** -/
theorem mellin_cauchyKernel_eq {s : ℂ} (h1 : -1 < s.re) (h2 : s.re < 0) :
    mellin cauchyKernel s = -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) := by
  rw [mellin]
  have hshape : (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) • cauchyKernel u)
      = ∫ u in Ioi (0 : ℝ), ((u : ℂ) ^ (s - 1) * ((u : ℂ) / (1 + (u : ℂ)))) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [smul_eq_mul, cauchyKernel]
  rw [hshape]
  exact mellin_cauchyKernel h1 h2

/-! ### Vertical integrability of the reflection kernel -/

theorem sin_pi_vertical_ne_zero {σ : ℝ} (hσ : Real.sin (Real.pi * σ) ≠ 0) (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
  intro h
  have hbd := abs_sin_re_le_norm_sin ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))
  rw [re_pi_mul_vertical, h, norm_zero] at hbd
  exact hσ (abs_eq_zero.mp (le_antisymm hbd (abs_nonneg _)))

theorem continuous_reflectionKernel_vertical {σ : ℝ} (hσ : Real.sin (Real.pi * σ) ≠ 0) :
    Continuous fun t : ℝ =>
      -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  refine Continuous.neg (Continuous.div continuous_const ?_ (sin_pi_vertical_ne_zero hσ))
  refine Complex.continuous_sin.comp ?_
  exact continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

/-- **The reflection kernel is integrable on every vertical line off the integers.** -/
theorem verticalIntegrable_reflectionKernel {σ : ℝ} (hσ : Real.sin (Real.pi * σ) ≠ 0) :
    Complex.VerticalIntegrable
      (fun s : ℂ => -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s))) σ := by
  rw [Complex.VerticalIntegrable]
  set C : ℝ := max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32 with hC
  have hCnn : (0 : ℝ) ≤ C := le_trans (by norm_num) (le_max_right _ _)
  refine MeasureTheory.Integrable.mono'
    (g := fun t : ℝ => (Real.pi * C) * (1 + t ^ 2)⁻¹) ?_ ?_ ?_
  · exact (integrable_inv_one_add_sq).const_mul _
  · exact (continuous_reflectionKernel_vertical hσ).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    have hnorm : ‖-((Real.pi : ℂ)
        / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)))‖
        = Real.pi * ‖(Complex.sin ((Real.pi : ℂ)
            * ((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖ := by
      rw [norm_neg, div_eq_mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [hnorm]
    have hbd := norm_inv_sin_vertical_le hσ t
    calc Real.pi * ‖(Complex.sin ((Real.pi : ℂ)
          * ((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖
        ≤ Real.pi * (C * (1 + t ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hbd (le_of_lt Real.pi_pos)
      _ = (Real.pi * C) * (1 + t ^ 2)⁻¹ := by ring

/-! ### The Mellin representation of the Cauchy kernel -/

theorem sin_pi_ne_zero_of_mem_strip {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0) :
    Real.sin (Real.pi * σ) ≠ 0 := by
  have hlt : Real.pi * σ < 0 := mul_neg_of_pos_of_neg Real.pi_pos h2
  have hgt : -Real.pi < Real.pi * σ := by
    nlinarith [Real.pi_pos]
  exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hlt hgt)

theorem verticalIntegrable_mellin_cauchyKernel {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0) :
    Complex.VerticalIntegrable (mellin cauchyKernel) σ := by
  have hsin := sin_pi_ne_zero_of_mem_strip h1 h2
  refine (verticalIntegrable_reflectionKernel hsin).congr ?_
  refine Filter.Eventually.of_forall fun t => ?_
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  symm
  refine mellin_cauchyKernel_eq ?_ ?_
  · rw [hre]; exact h1
  · rw [hre]; exact h2

/-- **The Mellin representation of the Cauchy kernel.**  On the strip the inverse Mellin transform
of its Mellin transform returns it. -/
theorem mellinInv_mellin_cauchyKernel {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin cauchyKernel) x = cauchyKernel x := by
  refine mellinInv_mellin_eq σ cauchyKernel hx ?_ (verticalIntegrable_mellin_cauchyKernel h1 h2) ?_
  · refine mellinConvergent_cauchyKernel ?_ ?_
    · simpa using h1
    · simpa using h2
  · have hopen : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
    exact (continuousOn_cauchyKernel.continuousAt (hopen.mem_nhds hx))

/-! ### The scaled kernel: one term of the Euler logarithmic derivative -/

/-- The Cauchy kernel at `x / a` is the term `x / (a + x)`. -/
theorem cauchyKernel_scaled {a x : ℝ} (ha : 0 < a) :
    cauchyKernel (x / a) = (x : ℂ) / ((a : ℂ) + (x : ℂ)) := by
  have hane : (a : ℝ) ≠ 0 := ne_of_gt ha
  have hreal : x / a / (1 + x / a) = x / (a + x) := by
    by_cases hsum : (a : ℝ) + x = 0
    · rw [hsum]
      rw [show (1 : ℝ) + x / a = (a + x) / a by field_simp, hsum]
      simp
    · field_simp
  rw [cauchyKernel_ofReal, hreal]
  push_cast
  ring

/-- **The Mellin representation of one term of the Euler logarithmic derivative.** -/
theorem mellinInv_mellin_cauchyKernel_scaled {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0)
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    mellinInv σ (mellin cauchyKernel) (x / a) = (x : ℂ) / ((a : ℂ) + (x : ℂ)) := by
  rw [mellinInv_mellin_cauchyKernel h1 h2 (div_pos hx ha)]
  exact cauchyKernel_scaled ha

/-! ### The envelope of the inverse-Mellin integrand -/

/-- **A uniform envelope for the inverse-Mellin integrand.**  On the vertical line the integrand of
the inverse Mellin transform of the reflection kernel is dominated by a fixed multiple of the Cauchy
density, with the scaling entering only through the constant `r ^ (-σ)`. -/
theorem norm_mellinInv_integrand_le {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0)
    {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ‖((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
        * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32)) * (1 + y ^ 2)⁻¹ := by
  have hsin := sin_pi_ne_zero_of_mem_strip h1 h2
  have hre : ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ := by simp
  have hpow : ‖((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))‖ = r ^ (-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    congr 1
    rw [Complex.neg_re, hre]
  have hmel : mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I)
      = -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))) := by
    refine mellin_cauchyKernel_eq ?_ ?_
    · rw [hre]; exact h1
    · rw [hre]; exact h2
  have hker : ‖-((Real.pi : ℂ)
      / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)))‖
      ≤ Real.pi * (max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32 * (1 + y ^ 2)⁻¹) := by
    have hnorm : ‖-((Real.pi : ℂ)
        / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)))‖
        = Real.pi * ‖(Complex.sin ((Real.pi : ℂ)
            * ((σ : ℂ) + (y : ℂ) * Complex.I)))⁻¹‖ := by
      rw [norm_neg, div_eq_mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (norm_inv_sin_vertical_le hsin y) (le_of_lt Real.pi_pos)
  rw [norm_mul, hpow, hmel]
  have hrnn : (0 : ℝ) ≤ r ^ (-σ) := le_of_lt (Real.rpow_pos_of_pos hr _)
  calc r ^ (-σ) * ‖-((Real.pi : ℂ)
        / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)))‖
      ≤ r ^ (-σ) * (Real.pi * (max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32 * (1 + y ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left hker hrnn
    _ = (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32)) * (1 + y ^ 2)⁻¹ := by
        ring

/-! ### Summability of the scaled envelope -/

/-- The scaling constant of the `n`-th term, in closed form. -/
theorem rpow_scaled_eq {s σ x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    (x / (n : ℝ) ^ s) ^ (-σ) = x ^ (-σ) * (n : ℝ) ^ (s * σ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnspos : (0 : ℝ) < (n : ℝ) ^ s := Real.rpow_pos_of_pos hnpos s
  rw [Real.div_rpow (le_of_lt hx) (le_of_lt hnspos), ← Real.rpow_mul (le_of_lt hnpos),
    show s * -σ = -(s * σ) by ring, Real.rpow_neg (le_of_lt hnpos),
    div_eq_mul_inv, inv_inv]

/-- **The envelope of the summed representation is summable exactly on the strip.** -/
theorem summable_scaledEnvelope {s σ : ℝ} (hsσ : s * σ < -1) (c : ℝ) :
    Summable (fun n : ℕ => c * (n : ℝ) ^ (s * σ)) :=
  (Real.summable_nat_rpow.mpr hsσ).mul_left c

/-! ### Integrability of each scaled inverse-Mellin integrand -/

theorem continuous_mellinInv_integrand {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0) {r : ℝ} (hr : 0 < r) :
    Continuous fun y : ℝ => ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
      * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I) := by
  have hsin := sin_pi_ne_zero_of_mem_strip h1 h2
  have hline : Continuous fun y : ℝ => ((σ : ℂ) + (y : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcpow : Continuous fun y : ℝ => ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I)) := by
    refine Continuous.const_cpow hline.neg (Or.inl ?_)
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hmel : (fun y : ℝ => mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I))
      = fun y : ℝ =>
        -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))) := by
    funext y
    have hre : ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ := by simp
    refine mellin_cauchyKernel_eq ?_ ?_
    · rw [hre]; exact h1
    · rw [hre]; exact h2
  rw [show (fun y : ℝ => ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
      * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I))
      = fun y : ℝ => ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
        * (-((Real.pi : ℂ)
          / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)))) by
    funext y
    rw [congrFun hmel y]]
  exact hcpow.mul (continuous_reflectionKernel_vertical hsin)

/-- **Each scaled inverse-Mellin integrand is integrable on the vertical line.** -/
theorem integrable_mellinInv_integrand {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0) {r : ℝ} (hr : 0 < r) :
    MeasureTheory.Integrable fun y : ℝ => ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
      * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I) := by
  refine MeasureTheory.Integrable.mono'
    (g := fun y : ℝ =>
      (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32)) * (1 + y ^ 2)⁻¹) ?_ ?_ ?_
  · exact (integrable_inv_one_add_sq).const_mul _
  · exact (continuous_mellinInv_integrand h1 h2 hr).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => norm_mellinInv_integrand_le h1 h2 hr y

/-! ### The second hypothesis of the interchange -/

/-- The integral of the norm of a scaled integrand is bounded by the envelope's integral. -/
theorem integral_norm_mellinInv_integrand_le {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0)
    {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ, ‖((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
        * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I)‖)
      ≤ (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32))
        * ∫ y : ℝ, (1 + y ^ 2)⁻¹ := by
  have hint := (integrable_mellinInv_integrand h1 h2 hr).norm
  have henv : MeasureTheory.Integrable
      fun y : ℝ => (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32))
        * (1 + y ^ 2)⁻¹ := (integrable_inv_one_add_sq).const_mul _
  have hmono := MeasureTheory.integral_mono hint henv
    (fun y => norm_mellinInv_integrand_le h1 h2 hr y)
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

/-- **The second hypothesis of the interchange.**  The integrals of the norms of the scaled
integrands are summable exactly on the strip `-1 < σ < -1/s`. -/
theorem summable_integral_norm_mellinInv_integrand {s σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0)
    (hsσ : s * σ < -1) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      ∫ y : ℝ, ‖((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
        * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I)‖ := by
  set K : ℝ := (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32)
    * ∫ y : ℝ, (1 + y ^ 2)⁻¹ with hK
  have hpos : ∀ n : ℕ, (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_pos hx (Real.rpow_pos_of_pos hnpos s)
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    simpa using h
  have hshift : Summable fun n : ℕ => (x ^ (-σ) * K) * ((n : ℝ) + 1) ^ (s * σ) := by
    have hbase := (summable_scaledEnvelope (s := s) (σ := σ) hsσ (x ^ (-σ) * K)).comp_injective hinj
    refine hbase.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    ring_nf
  have hmaj : Summable fun n : ℕ => (x / ((n : ℝ) + 1) ^ s) ^ (-σ) * K := by
    refine hshift.congr fun n => ?_
    have hnpos : (0 : ℕ) < n + 1 := Nat.succ_pos n
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, rpow_scaled_eq hx hnpos]
    ring
  refine Summable.of_nonneg_of_le
    (fun n => MeasureTheory.integral_nonneg fun y => norm_nonneg _) (fun n => ?_) hmaj
  refine le_trans (integral_norm_mellinInv_integrand_le h1 h2 (hpos n)) (le_of_eq ?_)
  rw [hK]
  ring

/-! ### The interchange -/

/-- **The sum over `n` may be taken inside the vertical integral.**  Both hypotheses of the
dominated interchange are available on the strip `-1 < σ < -1/s`. -/
theorem hasSum_integral_mellinInv_scaled {s σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0)
    (hsσ : s * σ < -1) {x : ℝ} (hx : 0 < x) :
    HasSum
      (fun n : ℕ => ∫ y : ℝ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ))
          ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
        * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I))
      (∫ y : ℝ, ∑' n : ℕ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ))
          ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
        * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_pos hx (Real.rpow_pos_of_pos hnpos s)
  exact MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun n => integrable_mellinInv_integrand h1 h2 (hpos n))
    (summable_integral_norm_mellinInv_integrand h1 h2 hsσ hx)

/-- The vertical integral of a scaled integrand is `2π` times the kernel value. -/
theorem integral_mellinInv_integrand_eq {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0)
    {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ, ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
        * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I))
      = (2 * Real.pi : ℝ) • cauchyKernel r := by
  have h := mellinInv_mellin_cauchyKernel h1 h2 hr
  rw [mellinInv] at h
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hsmul := congrArg (fun z : ℂ => (2 * Real.pi : ℝ) • z) h
  simp only [smul_smul] at hsmul
  rw [show (2 * Real.pi : ℝ) * (1 / (2 * Real.pi)) = 1 by field_simp, one_smul] at hsmul
  rw [← hsmul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul]

/-- **The summed Mellin representation of the Euler logarithmic derivative.**  Each term of
`H_s(x) = ∑_{n ≥ 1} x / (n^s + x)` is a vertical integral, and the sum passes inside. -/
theorem hasSum_eulerLogDerivTerms_mellin {s σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0)
    (hsσ : s * σ < -1) {x : ℝ} (hx : 0 < x) :
    HasSum
      (fun n : ℕ => (2 * Real.pi : ℝ) •
        ((x : ℂ) / (((((n : ℝ) + 1) ^ s : ℝ) : ℂ) + (x : ℂ))))
      (∫ y : ℝ, ∑' n : ℕ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ))
          ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
        * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1) ^ s := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact Real.rpow_pos_of_pos hnpos s
  have hterm : ∀ n : ℕ,
      (∫ y : ℝ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ))
          ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
        * mellin cauchyKernel ((σ : ℂ) + (y : ℂ) * Complex.I))
      = (2 * Real.pi : ℝ) • ((x : ℂ) / (((((n : ℝ) + 1) ^ s : ℝ) : ℂ) + (x : ℂ))) := by
    intro n
    rw [integral_mellinInv_integrand_eq h1 h2 (div_pos hx (hpos n)),
      cauchyKernel_scaled (hpos n)]
  have hsum := hasSum_integral_mellinInv_scaled h1 h2 hsσ hx
  simpa only [hterm] using hsum

/-! ### Splitting the scaled power -/

/-- On the positive reals the scaled power splits, with the scaling appearing as a positive
power. -/
theorem cpow_scaled_split {a x : ℝ} (hx : 0 < x) (ha : 0 < a) (w : ℂ) :
    (((x / a : ℝ)) : ℂ) ^ (-w) = ((x : ℝ) : ℂ) ^ (-w) * ((a : ℝ) : ℂ) ^ w := by
  have harg : ((a : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt ha)]
    exact ne_of_lt Real.pi_pos
  have hdiv : (x / a : ℝ) = x * a⁻¹ := div_eq_mul_inv x a
  rw [hdiv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (le_of_lt hx) (by positivity : (0 : ℝ) ≤ a⁻¹)]
  congr 1
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, neg_neg]

/-! ### The inner sum is a zeta value -/

theorem ofReal_rpow_cpow {a : ℝ} (ha : 0 < a) (s : ℝ) (w : ℂ) :
    (((a ^ s : ℝ)) : ℂ) ^ w = ((a : ℝ) : ℂ) ^ ((s : ℂ) * w) := by
  have him : (Complex.log ((a : ℝ) : ℂ) * (s : ℂ)).im = 0 := by
    simp [Complex.mul_im, Complex.log_im, Complex.arg_ofReal_of_nonneg (le_of_lt ha)]
  rw [Complex.ofReal_cpow (le_of_lt ha) s]
  refine (Complex.cpow_mul _ ?_ ?_).symm
  · rw [him]
    exact neg_lt_zero.mpr Real.pi_pos
  · rw [him]
    exact le_of_lt Real.pi_pos

/-- **The inner sum of the representation is a zeta value.** -/
theorem tsum_scaled_eq_zeta {s : ℝ} {x : ℝ} (hx : 0 < x) {w : ℂ}
    (hw : 1 < (-(s : ℂ) * w).re) :
    (∑' n : ℕ, (((x / ((n : ℝ) + 1) ^ s : ℝ)) : ℂ) ^ (-w))
      = ((x : ℝ) : ℂ) ^ (-w) * riemannZeta (-(s : ℂ) * w) := by
  have hterm : ∀ n : ℕ, (((x / ((n : ℝ) + 1) ^ s : ℝ)) : ℂ) ^ (-w)
      = ((x : ℝ) : ℂ) ^ (-w) * (1 / ((n : ℂ) + 1) ^ (-(s : ℂ) * w)) := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [cpow_scaled_split hx (Real.rpow_pos_of_pos hnpos s) w,
      ofReal_rpow_cpow hnpos s w]
    congr 1
    rw [one_div, ← Complex.cpow_neg]
    congr 1
    · push_cast
      ring
    · ring
  rw [tsum_congr hterm, tsum_mul_left, ← zeta_eq_tsum_one_div_nat_add_one_cpow hw]

end GaloisForLFunctions.HTGeometry
