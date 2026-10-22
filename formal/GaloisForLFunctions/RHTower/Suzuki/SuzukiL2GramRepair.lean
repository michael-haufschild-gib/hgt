import GaloisForLFunctions.RHTower.Suzuki.SuzukiGramDominationRepair
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Suzuki's oriented-primitive repair on the actual `L²(-a,a)` source class

Suzuki (2022), Theorem 4.2, applies to arbitrary `L²(-a,a)` sources.  Finite point sources are
not dense in that space, so the finite Gram factorization alone does not repair the printed
entrywise-kernel comparison.  This file constructs the exact Bochner integral

`P φ x = ∫ t in [-a,a], φ(t) e_t(x) dt`

for a genuine `L²` representative and proves its support and integrability directly on the product
measure.  Subsequent theorems identify Suzuki's divided-exponential transform with the angular
Fourier transform of `P φ` and derive the two form-level estimates needed in Theorem 4.2.
-/

open MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- Joint measurability of Suzuki's directed-interval feature. -/
theorem measurable_suzukiOrientedSegment_uncurry :
    Measurable (Function.uncurry suzukiOrientedSegment) := by
  have hrepr : Function.uncurry suzukiOrientedSegment = fun p : ℝ × ℝ =>
      if 0 ≤ p.1 then
        if 0 < p.2 ∧ p.2 ≤ p.1 then (1 : ℂ) else 0
      else if p.1 < p.2 ∧ p.2 ≤ 0 then (-1 : ℂ) else 0 := by
    funext p
    rcases p with ⟨t, x⟩
    simp only [Function.uncurry_apply_pair]
    by_cases ht : 0 ≤ t
    · simp [suzukiOrientedSegment, ht, Set.indicator, Set.mem_Ioc]
    · simp [suzukiOrientedSegment, ht, Set.indicator, Set.mem_Ioc]
      split_ifs <;> simp_all
  rw [hrepr]
  apply Measurable.ite
  · exact measurableSet_le measurable_const measurable_fst
  · apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    · exact measurable_const
    · exact measurable_const
  · apply Measurable.ite
    · exact (measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    · exact measurable_const
    · exact measurable_const

/-- Actual oriented primitive attached to a source on `[-a,a]`. -/
def suzukiOrientedPrimitive (a : ℝ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Icc (-a) a, φ t * suzukiOrientedSegment t x

theorem norm_suzukiOrientedSegment_le_indicator_Icc {a t x : ℝ}
    (ha : 0 ≤ a) (ht : t ∈ Icc (-a) a) :
    ‖suzukiOrientedSegment t x‖ ≤
      (Icc (-a) a).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ Icc (-a) a
  · rw [Set.indicator_of_mem hx]
    by_cases ht0 : 0 ≤ t
    · simp [suzukiOrientedSegment, ht0, Set.indicator]
      split_ifs <;> norm_num
    · simp [suzukiOrientedSegment, ht0, Set.indicator]
      split_ifs <;> norm_num
  · rw [suzukiOrientedSegment_eq_zero_of_not_mem_Icc ha ht hx, norm_zero]
    simp [Set.indicator, hx]

/-- Product-measure integrability behind all Fubini interchanges for the actual source map. -/
theorem integrable_suzukiOrientedPrimitive_joint {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : Integrable φ (volume.restrict (Icc (-a) a))) :
    Integrable (Function.uncurry (fun t x => φ t * suzukiOrientedSegment t x))
      ((volume.restrict (Icc (-a) a)).prod volume) := by
  let χ : ℝ → ℝ := (Icc (-a) a).indicator (fun _ => (1 : ℝ))
  have hχ : Integrable χ := by
    exact (MeasureTheory.integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)).integrable_indicator
        measurableSet_Icc
  have hmajor : Integrable (fun p : ℝ × ℝ => ‖φ p.1‖ * χ p.2)
      ((volume.restrict (Icc (-a) a)).prod volume) := hφ.norm.mul_prod hχ
  have hmeasφ : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1)
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    hφ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (fun t x => φ t * suzukiOrientedSegment t x))
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    hmeasφ.mul measurable_suzukiOrientedSegment_uncurry.aestronglyMeasurable
  apply hmajor.mono' hmeas
  have ht : ∀ᵐ t ∂volume.restrict (Icc (-a) a), t ∈ Icc (-a) a :=
    ae_restrict_mem measurableSet_Icc
  have htp := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ).restrict (Icc (-a) a))
    (ν := (volume : Measure ℝ))).ae ht
  filter_upwards [htp] with p hp
  rcases p with ⟨t, x⟩
  simp only [Function.uncurry_apply_pair, norm_mul, χ]
  exact mul_le_mul_of_nonneg_left
    (norm_suzukiOrientedSegment_le_indicator_Icc ha hp) (norm_nonneg (φ t))

/-- An `L²(-a,a)` source is integrable on its finite interval. -/
theorem integrableOn_Icc_of_memLp_two {a : ℝ} {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    Integrable φ (volume.restrict (Icc (-a) a)) := by
  let μ : Measure ℝ := volume.restrict (Icc (-a) a)
  have hμ : μ Set.univ < ⊤ := by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk hμ
  exact hφ.integrable (by norm_num)

/-- The actual oriented primitive is `L¹` on the physical line. -/
theorem integrable_suzukiOrientedPrimitive {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    Integrable (suzukiOrientedPrimitive a φ) := by
  have hjoint := integrable_suzukiOrientedPrimitive_joint ha
    (integrableOn_Icc_of_memLp_two hφ)
  exact hjoint.integral_prod_right

/-- The actual oriented primitive is supported in `[-a,a]`. -/
theorem suzukiOrientedPrimitive_eq_zero_of_not_mem_Icc {a x : ℝ} (ha : 0 ≤ a)
    (φ : ℝ → ℂ) (hx : x ∉ Icc (-a) a) :
    suzukiOrientedPrimitive a φ x = 0 := by
  unfold suzukiOrientedPrimitive
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [suzukiOrientedSegment_eq_zero_of_not_mem_Icc ha ht hx, mul_zero]
  rfl

/-- Pointwise `L¹` control of the actual primitive. -/
theorem norm_suzukiOrientedPrimitive_le_l1 {a x : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    ‖suzukiOrientedPrimitive a φ x‖ ≤ ∫ t in Icc (-a) a, ‖φ t‖ := by
  have hφ1 := integrableOn_Icc_of_memLp_two hφ
  have hseg : AEStronglyMeasurable (fun t : ℝ => suzukiOrientedSegment t x)
      (volume.restrict (Icc (-a) a)) :=
    (measurable_suzukiOrientedSegment_uncurry.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hint : Integrable (fun t => φ t * suzukiOrientedSegment t x)
      (volume.restrict (Icc (-a) a)) := by
    apply hφ1.norm.mono' (hφ.aestronglyMeasurable.mul hseg)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change ‖φ t * suzukiOrientedSegment t x‖ ≤ ‖φ t‖
    rw [norm_mul]
    have hs := norm_suzukiOrientedSegment_le_indicator_Icc (x := x) ha ht
    by_cases hx : x ∈ Icc (-a) a
    · rw [Set.indicator_of_mem hx] at hs
      exact mul_le_of_le_one_right (norm_nonneg _) hs
    · rw [Set.indicator, if_neg hx] at hs
      have hz : ‖suzukiOrientedSegment t x‖ = 0 := le_antisymm hs (norm_nonneg _)
      simp [hz]
  unfold suzukiOrientedPrimitive
  calc
    ‖∫ t in Icc (-a) a, φ t * suzukiOrientedSegment t x‖ ≤
        ∫ t in Icc (-a) a, ‖φ t * suzukiOrientedSegment t x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Icc (-a) a, ‖φ t‖ := by
      apply integral_mono_ae hint.norm hφ1.norm
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [norm_mul]
      have hs := norm_suzukiOrientedSegment_le_indicator_Icc (x := x) ha ht
      by_cases hx : x ∈ Icc (-a) a
      · rw [Set.indicator_of_mem hx] at hs
        exact mul_le_of_le_one_right (norm_nonneg _) hs
      · rw [Set.indicator, if_neg hx] at hs
        have hz : ‖suzukiOrientedSegment t x‖ = 0 := le_antisymm hs (norm_nonneg _)
        simp [hz]

/-- The actual primitive of every `L²(-a,a)` source has finite physical energy. -/
theorem integrable_norm_sq_suzukiOrientedPrimitive {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    Integrable (fun x => ‖suzukiOrientedPrimitive a φ x‖ ^ 2) := by
  let L : ℝ := ∫ t in Icc (-a) a, ‖φ t‖
  let χ : ℝ → ℝ := (Icc (-a) a).indicator (fun _ => L ^ 2)
  have hχ : Integrable χ := by
    exact (MeasureTheory.integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)).integrable_indicator
        measurableSet_Icc
  have hP := integrable_suzukiOrientedPrimitive ha hφ
  apply hχ.mono' (hP.aestronglyMeasurable.norm.pow 2)
  filter_upwards with x
  change ‖‖suzukiOrientedPrimitive a φ x‖ ^ 2‖ ≤ χ x
  by_cases hx : x ∈ Icc (-a) a
  · rw [show χ x = L ^ 2 by simp [χ, hx]]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (by simpa only [L] using norm_suzukiOrientedPrimitive_le_l1 (x := x) ha hφ) 2
  · rw [suzukiOrientedPrimitive_eq_zero_of_not_mem_Icc ha φ hx, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    simp [χ, hx]

/-- **Actual-`L²` contour-shift repair.**  This is the first disputed comparison in Suzuki's
proof of Theorem 4.2, now stated for every source in the paper's source space. -/
theorem suzukiL2ContourShiftForm_le {a q : ℝ} (ha : 0 ≤ a) {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (∫ x in Icc (-a) a,
        ‖((Real.exp (-q * x) : ℝ) : ℂ) * suzukiOrientedPrimitive a φ x‖ ^ 2) ≤
      Real.exp (2 * |q| * a) *
        ∫ x in Icc (-a) a, ‖suzukiOrientedPrimitive a φ x‖ ^ 2 := by
  apply integral_Icc_norm_sq_exp_mul_le ha
  · exact (integrable_suzukiOrientedPrimitive ha hφ).aestronglyMeasurable.restrict
  · exact (integrable_norm_sq_suzukiOrientedPrimitive ha hφ).restrict

/-- **Actual-`L²` low-band repair in mathlib Fourier normalization.**  This is the second disputed
comparison in Suzuki's proof of Theorem 4.2, proved at quadratic-form level rather than inferred
from pointwise kernel ordering. -/
theorem suzukiL2FourierLowBandEnergy_le {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (∫ w in Icc (-T) T, ‖𝓕 (suzukiOrientedPrimitive a φ) w‖ ^ 2) ≤
      4 * a * T * ∫ x in Icc (-a) a, ‖suzukiOrientedPrimitive a φ x‖ ^ 2 := by
  let P := suzukiOrientedPrimitive a φ
  have hP : Integrable P := integrable_suzukiOrientedPrimitive ha hφ
  have hP2 : Integrable (fun x => ‖P x‖ ^ 2) :=
    integrable_norm_sq_suzukiOrientedPrimitive ha hφ
  have hsupport : ∀ x, x ∉ Icc (-a) a → P x = 0 := fun x hx =>
    suzukiOrientedPrimitive_eq_zero_of_not_mem_Icc ha φ hx
  have hmass : (∫ x, ‖P x‖) = ∫ x in Icc (-a) a, ‖P x‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hsupport x hx, norm_zero]).symm
  have hFcont : Continuous (𝓕 P) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hP
  apply integral_Icc_norm_sq_le_four_mul_of_le_l1 ha hT
  · exact hP.aestronglyMeasurable.restrict
  · exact hP2.restrict
  · exact hFcont.aestronglyMeasurable.restrict
  · intro w
    rw [← hmass]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- Actual-source low-band estimate in Suzuki's angular-frequency normalization. -/
theorem suzukiL2AngularLowBandEnergy_le {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (∫ z in Icc (-T) T,
        ‖suzukiAngularFourierTransform (suzukiOrientedPrimitive a φ) z‖ ^ 2) ≤
      4 * a * T * ∫ x in Icc (-a) a, ‖suzukiOrientedPrimitive a φ x‖ ^ 2 := by
  let P := suzukiOrientedPrimitive a φ
  let G : ℝ → ℝ := fun w => ‖𝓕 P w‖ ^ 2
  let U : ℝ := T / (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hU : 0 ≤ U := div_nonneg hT hpi.le
  have hLow := suzukiL2FourierLowBandEnergy_le ha hU hφ
  have hLowInterval : (∫ w in -U..U, G w) ≤
      4 * a * U * ∫ x in Icc (-a) a, ‖P x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    rw [setIntegral_congr_set Ioc_ae_eq_Icc]
    exact hLow
  have hleft : (∫ z in Icc (-T) T,
        ‖suzukiAngularFourierTransform P z‖ ^ 2) =
      (2 * Real.pi) * ∫ w in -U..U, G w := by
    rw [show (∫ z in Icc (-T) T, ‖suzukiAngularFourierTransform P z‖ ^ 2) =
        ∫ z in -T..T, ‖suzukiAngularFourierTransform P z‖ ^ 2 by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm]
    rw [show (fun z => ‖suzukiAngularFourierTransform P z‖ ^ 2) =
        fun z => G (-z / (2 * Real.pi)) by
      funext z
      rw [suzukiAngularFourierTransform_eq_fourier]]
    simpa only [U] using intervalIntegral_comp_neg_div_two_pi G T
  rw [show suzukiOrientedPrimitive a φ = P by rfl]
  rw [hleft]
  calc
    (2 * Real.pi) * ∫ w in -U..U, G w ≤
        (2 * Real.pi) *
          (4 * a * U * ∫ x in Icc (-a) a, ‖P x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hLowInterval hpi.le
    _ = 4 * a * T * ∫ x in Icc (-a) a, ‖P x‖ ^ 2 := by
      dsimp only [U]
      field_simp

/-! ## Exact `L²` transform identity -/

/-- Suzuki's literal transform `Phi_1` from Eq. (4.2), on an actual source representative. -/
def suzukiL2DividedExponentialFeature (a : ℝ) (φ : ℝ → ℂ) (z : ℝ) : ℂ :=
  ∫ t in Icc (-a) a, φ t *
    ((Complex.exp (Complex.I * (z : ℂ) * (t : ℂ)) - 1) / (z : ℂ))

theorem integrable_suzukiOrientedPrimitive_joint_mul_cexp {a z : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    Integrable (Function.uncurry (fun t x =>
      φ t * suzukiOrientedSegment t x *
        Complex.exp (Complex.I * (z : ℂ) * (x : ℂ))))
      ((volume.restrict (Icc (-a) a)).prod volume) := by
  have hbase := integrable_suzukiOrientedPrimitive_joint ha
    (integrableOn_Icc_of_memLp_two hφ)
  have hexp : StronglyMeasurable (fun p : ℝ × ℝ =>
      Complex.exp (Complex.I * (z : ℂ) * (p.2 : ℂ))) := by
    fun_prop
  apply hbase.norm.mono' (hbase.aestronglyMeasurable.mul hexp.aestronglyMeasurable)
  filter_upwards with p
  rcases p with ⟨t, x⟩
  change ‖(φ t * suzukiOrientedSegment t x) *
      Complex.exp (Complex.I * (z : ℂ) * (x : ℂ))‖ ≤
    ‖φ t * suzukiOrientedSegment t x‖
  rw [norm_mul, Complex.norm_exp]
  simp

/-- Fubini identity relating the angular transform of the actual primitive to directed-segment
Fourier features. -/
theorem suzukiAngularFourierTransform_orientedPrimitive_eq {a z : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) (hz : z ≠ 0) :
    suzukiAngularFourierTransform (suzukiOrientedPrimitive a φ) z =
      ∫ t in Icc (-a) a, φ t *
        ((Complex.exp (Complex.I * (z : ℂ) * (t : ℂ)) - 1) /
          (Complex.I * (z : ℂ))) := by
  have hjoint := integrable_suzukiOrientedPrimitive_joint_mul_cexp ha hφ (z := z)
  have hswap := integral_integral_swap hjoint
  unfold suzukiAngularFourierTransform suzukiOrientedPrimitive
  calc
    (∫ x, (∫ t in Icc (-a) a, φ t * suzukiOrientedSegment t x) *
        Complex.exp (Complex.I * (z : ℂ) * (x : ℂ))) =
      ∫ x, ∫ t in Icc (-a) a,
        φ t * suzukiOrientedSegment t x *
          Complex.exp (Complex.I * (z : ℂ) * (x : ℂ)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [integral_mul_const]
    _ = ∫ t in Icc (-a) a, ∫ x,
        φ t * suzukiOrientedSegment t x *
          Complex.exp (Complex.I * (z : ℂ) * (x : ℂ)) := hswap.symm
    _ = ∫ t in Icc (-a) a, φ t *
        ((Complex.exp (Complex.I * (z : ℂ) * (t : ℂ)) - 1) /
          (Complex.I * (z : ℂ))) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [show (fun x => φ t * suzukiOrientedSegment t x *
          Complex.exp (Complex.I * (z : ℂ) * (x : ℂ))) = fun x =>
            φ t * (suzukiOrientedSegment t x *
              Complex.exp (Complex.I * (z : ℂ) * (x : ℂ))) by
        funext x
        ring]
      rw [integral_const_mul, integral_suzukiOrientedSegment_mul_cexp t z hz]

/-- **Exact Suzuki Eq. (4.2) factorization on `L²(-a,a)`.**  The literal divided-exponential
transform is `i` times the angular Fourier transform of the oriented primitive. -/
theorem suzukiL2DividedExponentialFeature_eq_I_mul_angularFourier {a z : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) (hz : z ≠ 0) :
    suzukiL2DividedExponentialFeature a φ z =
      Complex.I * suzukiAngularFourierTransform (suzukiOrientedPrimitive a φ) z := by
  rw [suzukiAngularFourierTransform_orientedPrimitive_eq ha hφ hz]
  unfold suzukiL2DividedExponentialFeature
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hzC : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
  field_simp

/-- `Phi_1` and the angular Fourier transform have equal pointwise norm away from the removable
frequency `0`. -/
theorem norm_suzukiL2DividedExponentialFeature_eq_angularFourier {a z : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) (hz : z ≠ 0) :
    ‖suzukiL2DividedExponentialFeature a φ z‖ =
      ‖suzukiAngularFourierTransform (suzukiOrientedPrimitive a φ) z‖ := by
  rw [suzukiL2DividedExponentialFeature_eq_I_mul_angularFourier ha hφ hz, norm_mul,
    Complex.norm_I, one_mul]

/-- Low-band energies of Suzuki's literal transform and the oriented primitive agree exactly. -/
theorem integral_Icc_norm_sq_suzukiL2DividedExponentialFeature_eq {a T : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (∫ z in Icc (-T) T, ‖suzukiL2DividedExponentialFeature a φ z‖ ^ 2) =
      ∫ z in Icc (-T) T,
        ‖suzukiAngularFourierTransform (suzukiOrientedPrimitive a φ) z‖ ^ 2 := by
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards [volume.ae_ne 0] with z hz hmem
  rw [norm_suzukiL2DividedExponentialFeature_eq_angularFourier ha hφ hz]

/-- **Second disputed comparison in Suzuki's literal notation, on every actual `L²` source.** -/
theorem suzukiL2DividedExponentialLowBandEnergy_le {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (∫ z in Icc (-T) T, ‖suzukiL2DividedExponentialFeature a φ z‖ ^ 2) ≤
      4 * a * T * ∫ x in Icc (-a) a, ‖suzukiOrientedPrimitive a φ x‖ ^ 2 := by
  rw [integral_Icc_norm_sq_suzukiL2DividedExponentialFeature_eq ha hφ]
  exact suzukiL2AngularLowBandEnergy_le ha hT hφ

/-! ## Exact free-kernel quadratic form on `L²(-a,a)` -/

/-- Suzuki's free screw-kernel quadratic form on an actual source representative. -/
def suzukiL2FreeKernelQuadraticForm (a : ℝ) (φ : ℝ → ℂ) : ℂ :=
  ∫ t in Icc (-a) a, ∫ u in Icc (-a) a,
    star (φ t) * (suzukiFreeScrewKernel t u : ℂ) * φ u

private theorem integrable_suzuki_star_sourceSegment_mul_primitive_joint {a : ℝ}
    (ha : 0 ≤ a) {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    Integrable (Function.uncurry (fun t x =>
      star (φ t * suzukiOrientedSegment t x) * suzukiOrientedPrimitive a φ x))
      ((volume.restrict (Icc (-a) a)).prod volume) := by
  have hφ1 := integrableOn_Icc_of_memLp_two hφ
  have hP := integrable_suzukiOrientedPrimitive ha hφ
  have hmajor : Integrable (fun p : ℝ × ℝ => ‖φ p.1‖ * ‖suzukiOrientedPrimitive a φ p.2‖)
      ((volume.restrict (Icc (-a) a)).prod volume) := hφ1.norm.mul_prod hP.norm
  have hφfst : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1)
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    hφ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hPsnd : AEStronglyMeasurable (fun p : ℝ × ℝ => suzukiOrientedPrimitive a φ p.2)
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    hP.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (fun t x =>
        star (φ t * suzukiOrientedSegment t x) * suzukiOrientedPrimitive a φ x))
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    (hφfst.mul measurable_suzukiOrientedSegment_uncurry.aestronglyMeasurable).star.mul hPsnd
  apply hmajor.mono' hmeas
  have ht : ∀ᵐ t ∂volume.restrict (Icc (-a) a), t ∈ Icc (-a) a :=
    ae_restrict_mem measurableSet_Icc
  have htp := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ).restrict (Icc (-a) a))
    (ν := (volume : Measure ℝ))).ae ht
  filter_upwards [htp] with p hp
  rcases p with ⟨t, x⟩
  change ‖star (φ t * suzukiOrientedSegment t x) * suzukiOrientedPrimitive a φ x‖ ≤
    ‖φ t‖ * ‖suzukiOrientedPrimitive a φ x‖
  rw [norm_mul, norm_star, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hs := norm_suzukiOrientedSegment_le_indicator_Icc (x := x) ha hp
  by_cases hx : x ∈ Icc (-a) a
  · rw [Set.indicator_of_mem hx] at hs
    exact mul_le_of_le_one_right (norm_nonneg _) hs
  · rw [Set.indicator, if_neg hx] at hs
    have hz : ‖suzukiOrientedSegment t x‖ = 0 := le_antisymm hs (norm_nonneg _)
    simp [hz]

private theorem integrable_suzuki_two_sourceSegments_joint {a t : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Icc (-a) a) {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    Integrable (Function.uncurry (fun u x =>
      star (φ t * suzukiOrientedSegment t x) *
        (φ u * suzukiOrientedSegment u x)))
      ((volume.restrict (Icc (-a) a)).prod volume) := by
  let χ : ℝ → ℝ := (Icc (-a) a).indicator (fun _ => (1 : ℝ))
  have hφ1 := integrableOn_Icc_of_memLp_two hφ
  have hχ : Integrable χ := by
    exact (MeasureTheory.integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)).integrable_indicator
        measurableSet_Icc
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      ‖φ t‖ * (‖φ p.1‖ * χ p.2))
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    (hφ1.norm.mul_prod hχ).const_mul ‖φ t‖
  have hφfst : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1)
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    hφ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hsegfixed : StronglyMeasurable (fun p : ℝ × ℝ => suzukiOrientedSegment t p.2) :=
    (stronglyMeasurable_suzukiOrientedSegment t).comp_measurable measurable_snd
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (fun u x => star (φ t * suzukiOrientedSegment t x) *
        (φ u * suzukiOrientedSegment u x)))
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    (aestronglyMeasurable_const.mul hsegfixed.aestronglyMeasurable).star.mul
      (hφfst.mul measurable_suzukiOrientedSegment_uncurry.aestronglyMeasurable)
  apply hmajor.mono' hmeas
  have hu : ∀ᵐ u ∂volume.restrict (Icc (-a) a), u ∈ Icc (-a) a :=
    ae_restrict_mem measurableSet_Icc
  have hup := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ).restrict (Icc (-a) a))
    (ν := (volume : Measure ℝ))).ae hu
  filter_upwards [hup] with p hp
  rcases p with ⟨u, x⟩
  change ‖star (φ t * suzukiOrientedSegment t x) *
      (φ u * suzukiOrientedSegment u x)‖ ≤ ‖φ t‖ * (‖φ u‖ * χ x)
  by_cases hx : x ∈ Icc (-a) a
  · rw [show χ x = 1 by simp [χ, hx]]
    rw [norm_mul, norm_star, norm_mul, norm_mul]
    have hst := norm_suzukiOrientedSegment_le_indicator_Icc (x := x) ha ht
    have hsu := norm_suzukiOrientedSegment_le_indicator_Icc (x := x) ha hp
    rw [Set.indicator_of_mem hx] at hst hsu
    have hleft : ‖φ t‖ * ‖suzukiOrientedSegment t x‖ ≤ ‖φ t‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hst
    have hright : ‖φ u‖ * ‖suzukiOrientedSegment u x‖ ≤ ‖φ u‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hsu
    calc
      ‖φ t‖ * ‖suzukiOrientedSegment t x‖ *
          (‖φ u‖ * ‖suzukiOrientedSegment u x‖) ≤ ‖φ t‖ * ‖φ u‖ :=
        mul_le_mul hleft hright (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖φ t‖ * (‖φ u‖ * 1) := by ring
  · rw [suzukiOrientedSegment_eq_zero_of_not_mem_Icc ha ht hx,
      suzukiOrientedSegment_eq_zero_of_not_mem_Icc ha hp hx]
    simp [χ, hx]

private theorem integral_star_sourceSegment_mul_primitive {a t : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Icc (-a) a) {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (∫ x, star (φ t * suzukiOrientedSegment t x) * suzukiOrientedPrimitive a φ x) =
      ∫ u in Icc (-a) a,
        star (φ t) * (suzukiFreeScrewKernel t u : ℂ) * φ u := by
  have hjoint := integrable_suzuki_two_sourceSegments_joint ha ht hφ
  have hswap := integral_integral_swap hjoint
  unfold suzukiOrientedPrimitive
  calc
    (∫ x, star (φ t * suzukiOrientedSegment t x) *
        (∫ u in Icc (-a) a, φ u * suzukiOrientedSegment u x)) =
      ∫ x, ∫ u in Icc (-a) a,
        star (φ t * suzukiOrientedSegment t x) *
          (φ u * suzukiOrientedSegment u x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [integral_const_mul]
    _ = ∫ u in Icc (-a) a, ∫ x,
        star (φ t * suzukiOrientedSegment t x) *
          (φ u * suzukiOrientedSegment u x) := hswap.symm
    _ = ∫ u in Icc (-a) a,
        star (φ t) * (suzukiFreeScrewKernel t u : ℂ) * φ u := by
      apply integral_congr_ae
      filter_upwards with u
      rw [show (fun x => star (φ t * suzukiOrientedSegment t x) *
          (φ u * suzukiOrientedSegment u x)) = fun x =>
            star (φ t) *
              (star (suzukiOrientedSegment t x) * suzukiOrientedSegment u x) * φ u by
        funext x
        rw [star_mul]
        ring]
      rw [integral_mul_const, integral_const_mul,
        integral_star_suzukiOrientedSegment_mul]

/-- **Exact free-kernel Gram factorization on the actual `L²(-a,a)` source class.** -/
theorem suzukiL2FreeKernelQuadraticForm_eq_integral {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    suzukiL2FreeKernelQuadraticForm a φ =
      ∫ x, star (suzukiOrientedPrimitive a φ x) * suzukiOrientedPrimitive a φ x := by
  have hjoint := integrable_suzuki_star_sourceSegment_mul_primitive_joint ha hφ
  have hswap := integral_integral_swap hjoint
  unfold suzukiL2FreeKernelQuadraticForm
  rw [show (∫ x, star (suzukiOrientedPrimitive a φ x) *
      suzukiOrientedPrimitive a φ x) =
      ∫ x, ∫ t in Icc (-a) a,
        star (φ t * suzukiOrientedSegment t x) * suzukiOrientedPrimitive a φ x by
    apply integral_congr_ae
    filter_upwards with x
    unfold suzukiOrientedPrimitive
    change (starRingEnd ℂ) (∫ t in Icc (-a) a, φ t * suzukiOrientedSegment t x) *
        (∫ t in Icc (-a) a, φ t * suzukiOrientedSegment t x) =
      ∫ t in Icc (-a) a, (starRingEnd ℂ) (φ t * suzukiOrientedSegment t x) *
        (∫ t in Icc (-a) a, φ t * suzukiOrientedSegment t x)
    rw [← integral_conj, integral_mul_const]]
  rw [← hswap]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (integral_star_sourceSegment_mul_primitive ha ht hφ).symm

/-- Real free-kernel energy is exactly the physical `L²` energy of the oriented primitive. -/
theorem suzukiL2FreeKernelQuadraticForm_re_eq_energy {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (suzukiL2FreeKernelQuadraticForm a φ).re =
      ∫ x in Icc (-a) a, ‖suzukiOrientedPrimitive a φ x‖ ^ 2 := by
  rw [suzukiL2FreeKernelQuadraticForm_eq_integral ha hφ]
  have henergy : Integrable (fun x => star (suzukiOrientedPrimitive a φ x) *
      suzukiOrientedPrimitive a φ x) := by
    have h := (integrable_norm_sq_suzukiOrientedPrimitive ha hφ)
    apply h.mono'
    · exact ((integrable_suzukiOrientedPrimitive ha hφ).aestronglyMeasurable.star.mul
          (integrable_suzukiOrientedPrimitive ha hφ).aestronglyMeasurable)
    · filter_upwards with x
      rw [norm_mul, norm_star, ← pow_two]
  change RCLike.re (∫ x, star (suzukiOrientedPrimitive a φ x) *
    suzukiOrientedPrimitive a φ x) = _
  rw [← integral_re henergy]
  change (∫ x, (star (suzukiOrientedPrimitive a φ x) *
    suzukiOrientedPrimitive a φ x).re) = _
  rw [show (∫ x, (star (suzukiOrientedPrimitive a φ x) *
      suzukiOrientedPrimitive a φ x).re) =
      ∫ x, ‖suzukiOrientedPrimitive a φ x‖ ^ 2 by
    apply integral_congr_ae
    filter_upwards with x
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_re _]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [suzukiOrientedPrimitive_eq_zero_of_not_mem_Icc ha φ hx, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]).symm

/-! ## Exact Parseval identity, Suzuki Eq. (4.9) -/

theorem integral_comp_neg_div_two_pi (G : ℝ → ℝ) :
    (∫ z : ℝ, G (-z / (2 * Real.pi))) =
      (2 * Real.pi) * ∫ w : ℝ, G w := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)
  have hscale := Measure.integral_comp_mul_left G (-(1 / (2 * Real.pi)))
  rw [show (fun z : ℝ => G (-(1 / (2 * Real.pi)) * z)) =
      fun z => G (-z / (2 * Real.pi)) by
    funext z
    congr 1
    ring] at hscale
  rw [show (-(1 / (2 * Real.pi)) : ℝ)⁻¹ = -(2 * Real.pi) by field_simp] at hscale
  rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos Real.pi_pos] at hscale
  simpa [smul_eq_mul] using hscale

/-- Angular-frequency Parseval identity for the actual oriented primitive. -/
theorem integral_norm_sq_suzukiAngularFourier_orientedPrimitive_eq {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (∫ z : ℝ, ‖suzukiAngularFourierTransform (suzukiOrientedPrimitive a φ) z‖ ^ 2) =
      (2 * Real.pi) * ∫ x in Icc (-a) a, ‖suzukiOrientedPrimitive a φ x‖ ^ 2 := by
  let P := suzukiOrientedPrimitive a φ
  let G : ℝ → ℝ := fun w => ‖𝓕 P w‖ ^ 2
  have hP1 : Integrable P := integrable_suzukiOrientedPrimitive ha hφ
  have hP2int : Integrable (fun x => ‖P x‖ ^ 2) :=
    integrable_norm_sq_suzukiOrientedPrimitive ha hφ
  have hP2 : MemLp P 2 (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hP1.aestronglyMeasurable).2 hP2int
  have hplan := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hP1 hP2
  rw [show (fun z => ‖suzukiAngularFourierTransform P z‖ ^ 2) =
      fun z => G (-z / (2 * Real.pi)) by
    funext z
    rw [suzukiAngularFourierTransform_eq_fourier]]
  rw [integral_comp_neg_div_two_pi G, hplan]
  congr 1
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    change ‖suzukiOrientedPrimitive a φ x‖ ^ 2 = 0
    rw [suzukiOrientedPrimitive_eq_zero_of_not_mem_Icc ha φ hx, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]).symm

/-- Full-line energies of Suzuki's literal `Phi_1` and the angular transform agree. -/
theorem integral_norm_sq_suzukiL2DividedExponentialFeature_eq {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (∫ z : ℝ, ‖suzukiL2DividedExponentialFeature a φ z‖ ^ 2) =
      ∫ z : ℝ, ‖suzukiAngularFourierTransform (suzukiOrientedPrimitive a φ) z‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [volume.ae_ne 0] with z hz
  rw [norm_suzukiL2DividedExponentialFeature_eq_angularFourier ha hφ hz]

/-- **Exact Suzuki Eq. (4.9) on every actual `L²(-a,a)` source.** -/
theorem suzuki_equation_four_nine {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    (1 / (2 * Real.pi)) *
        ∫ z : ℝ, ‖suzukiL2DividedExponentialFeature a φ z‖ ^ 2 =
      (suzukiL2FreeKernelQuadraticForm a φ).re := by
  rw [integral_norm_sq_suzukiL2DividedExponentialFeature_eq ha hφ,
    integral_norm_sq_suzukiAngularFourier_orientedPrimitive_eq ha hφ,
    suzukiL2FreeKernelQuadraticForm_re_eq_energy ha hφ]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)
  field_simp

end RHTower

end
