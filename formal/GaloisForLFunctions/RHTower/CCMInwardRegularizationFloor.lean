import GaloisForLFunctions.RHTower.CCMRestrictedWeilFloorAbscissaTransfer
import GaloisForLFunctions.RHTower.CCMRectangularTwoSidedOscillation
import GaloisForLFunctions.RHTower.TentMellinFactor

/-!
# Inward regularization of the sharp two-edge Weil profile

This module certifies the analytic input consumed by
`CCMRestrictedWeilFloorAbscissaTransfer`: inward trapezoidal smoothing converges in the actual
multiplicity-exact Xi--Weil polarization, its bilateral squared mass tends to `2 * L`, and the
variational lower bound therefore survives with no mass loss.  The last theorems turn this
certificate into the sampled restricted-floor envelope and its transverse amplification law.
-/

open Complex Filter Function Set
open scoped Topology

namespace RHTower

noncomputable section

/-- The Laplace multiplier of the normalized inward averaging kernel. -/
def inwardEdgeRegularizationFactor (epsilon : ℝ) (w : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, Complex.exp (-w * ((epsilon * t : ℝ) : ℂ))

@[simp] theorem inwardEdgeRegularizationFactor_zero (w : ℂ) :
    inwardEdgeRegularizationFactor 0 w = 1 := by
  simp [inwardEdgeRegularizationFactor, intervalIntegral.integral_const]

theorem continuous_inwardEdgeRegularizationFactor (w : ℂ) :
    Continuous (fun epsilon : ℝ => inwardEdgeRegularizationFactor epsilon w) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

theorem tendsto_inwardEdgeRegularizationFactor_zero (w : ℂ) :
    Tendsto (fun epsilon : ℝ => inwardEdgeRegularizationFactor epsilon w)
      (𝓝 0) (𝓝 1) := by
  have h : Tendsto (fun epsilon : ℝ => inwardEdgeRegularizationFactor epsilon w)
      (𝓝 0) (𝓝 (inwardEdgeRegularizationFactor 0 w)) :=
    (continuous_inwardEdgeRegularizationFactor w).continuousAt
  rw [inwardEdgeRegularizationFactor_zero] at h
  exact h

/-- The kernel multiplier is exactly the normalized box amplitude `A_epsilon / epsilon`. -/
theorem inwardEdgeRegularizationFactor_eq_boxLaplace_div
    {epsilon : ℝ} (hepsilon : epsilon ≠ 0) (w : ℂ) :
    inwardEdgeRegularizationFactor epsilon w = boxLaplace epsilon w / epsilon := by
  by_cases hw : w = 0
  · subst w
    rw [inwardEdgeRegularizationFactor, boxLaplace_zero]
    simp [intervalIntegral.integral_const, hepsilon]
  · have hc : -w * (epsilon : ℂ) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hw) (ofReal_ne_zero.mpr hepsilon)
    rw [inwardEdgeRegularizationFactor]
    simp_rw [Complex.ofReal_mul, ← mul_assoc]
    rw [integral_exp_mul_complex hc, boxLaplace_eq epsilon w hw]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_one, mul_one]
    field_simp
    ring_nf

/-- Uniform strip bound used for dominated convergence over the Xi divisor. -/
theorem norm_inwardEdgeRegularizationFactor_le
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    ‖inwardEdgeRegularizationFactor epsilon w‖ ≤ Real.exp (1 / 2) := by
  rw [inwardEdgeRegularizationFactor]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp (1 / 2)) ?_).trans_eq ?_
  · intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have ht0 : 0 ≤ t := ht.1.le
    have ht1 : t ≤ 1 := ht.2
    have hre : (-w * ((epsilon * t : ℝ) : ℂ)).re = -w.re * (epsilon * t) := by
      simp [Complex.mul_re]
    rw [hre]
    have hwneg : -w.re ≤ |w.re| := neg_le_abs _
    have het0 : 0 ≤ epsilon * t := mul_nonneg hepsilon0 ht0
    have het1 : epsilon * t ≤ 1 := by
      calc
        epsilon * t ≤ 1 * t := mul_le_mul_of_nonneg_right hepsilon1 ht0
        _ ≤ 1 := by simpa using ht1
    calc
      -w.re * (epsilon * t) ≤ |w.re| * (epsilon * t) :=
        mul_le_mul_of_nonneg_right hwneg het0
      _ ≤ (1 / 2) * 1 := mul_le_mul hw het1 het0 (by positivity)
      _ = 1 / 2 := by ring
  · norm_num

/-- One inward-smoothed edge in canonical coordinates.  The three nonzero pieces are an incoming
ramp, a plateau, and an outgoing ramp. -/
def inwardTrapezoid (L epsilon x : ℝ) : ℝ :=
  if x < 0 then 0
  else if x ≤ epsilon then x / epsilon
  else if x ≤ L then 1
  else if x ≤ L + epsilon then (L + epsilon - x) / epsilon
  else 0

theorem inwardTrapezoid_eq_leftRamp
    {L epsilon x : ℝ} (hx0 : 0 ≤ x) (hxe : x ≤ epsilon) :
    inwardTrapezoid L epsilon x = x / epsilon := by
  simp [inwardTrapezoid, not_lt.mpr hx0, hxe]

theorem inwardTrapezoid_eq_plateau
    {L epsilon x : ℝ} (hepsilon : 0 < epsilon)
    (hex : epsilon ≤ x) (hxL : x ≤ L) :
    inwardTrapezoid L epsilon x = 1 := by
  by_cases hxe : x ≤ epsilon
  · have hx : x = epsilon := le_antisymm hxe hex
    subst x
    simp [inwardTrapezoid, hepsilon.ne', hepsilon.le]
  · simp [inwardTrapezoid, not_lt.mpr (hepsilon.le.trans hex), hxe, hxL]

theorem inwardTrapezoid_eq_rightRamp
    {L epsilon x : ℝ} (hepsilon : 0 < epsilon) (heL : epsilon ≤ L)
    (hLx : L ≤ x) (hx : x ≤ L + epsilon) :
    inwardTrapezoid L epsilon x = (L + epsilon - x) / epsilon := by
  by_cases hxe : x ≤ epsilon
  · have hLe : L = epsilon := le_antisymm (hLx.trans hxe) heL
    have hxeq : x = epsilon := le_antisymm hxe (hLe ▸ hLx)
    subst L
    subst x
    simp [inwardTrapezoid, hepsilon.ne', hepsilon.le]
  · by_cases hxL : x ≤ L
    · have hxeq : x = L := le_antisymm hxL hLx
      subst x
      have hL0 : 0 ≤ L := hepsilon.le.trans heL
      simp [inwardTrapezoid, not_lt.mpr hL0, hxe, hepsilon.ne']
    · have hL0 : 0 ≤ L := hepsilon.le.trans heL
      simp [inwardTrapezoid, not_lt.mpr (hL0.trans hLx), hxe, hxL, hx]

/-- The squared mass of one edge, split along its exact ramp/plateau/ramp partition. -/
def inwardTrapezoidSquaredMass (L epsilon : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..epsilon, inwardTrapezoid L epsilon x ^ 2) +
    (∫ x in epsilon..L, inwardTrapezoid L epsilon x ^ 2) +
      ∫ x in L..(L + epsilon), inwardTrapezoid L epsilon x ^ 2

theorem inwardTrapezoidSquaredMass_eq
    {L epsilon : ℝ} (hepsilon : 0 < epsilon) (heL : epsilon ≤ L) :
    inwardTrapezoidSquaredMass L epsilon = L - epsilon / 3 := by
  have hramp : (∫ x in (0 : ℝ)..epsilon, (x / epsilon) ^ 2) = epsilon / 3 := by
    calc
      (∫ x in (0 : ℝ)..epsilon, (x / epsilon) ^ 2) =
          (epsilon⁻¹) ^ 2 * (∫ x in (0 : ℝ)..epsilon, x ^ 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        field_simp
      _ = epsilon / 3 := by
        rw [integral_pow]
        norm_num
        field_simp
  have hleft :
      (∫ x in (0 : ℝ)..epsilon, inwardTrapezoid L epsilon x ^ 2) = epsilon / 3 := by
    calc
      _ = ∫ x in (0 : ℝ)..epsilon, (x / epsilon) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hepsilon.le] at hx
        change inwardTrapezoid L epsilon x ^ 2 = (x / epsilon) ^ 2
        rw [inwardTrapezoid_eq_leftRamp hx.1 hx.2]
      _ = epsilon / 3 := hramp
  have hmiddle :
      (∫ x in epsilon..L, inwardTrapezoid L epsilon x ^ 2) = L - epsilon := by
    calc
      _ = ∫ _x in epsilon..L, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le heL] at hx
        change inwardTrapezoid L epsilon x ^ 2 = (1 : ℝ)
        rw [inwardTrapezoid_eq_plateau hepsilon hx.1 hx.2]
        norm_num
      _ = L - epsilon := by simp [intervalIntegral.integral_const]
  have hright :
      (∫ x in L..(L + epsilon), inwardTrapezoid L epsilon x ^ 2) = epsilon / 3 := by
    calc
      _ = ∫ x in L..(L + epsilon), ((L + epsilon - x) / epsilon) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by linarith)] at hx
        change inwardTrapezoid L epsilon x ^ 2 = ((L + epsilon - x) / epsilon) ^ 2
        rw [inwardTrapezoid_eq_rightRamp hepsilon heL hx.1 hx.2]
      _ = ∫ x in (0 : ℝ)..epsilon, (x / epsilon) ^ 2 := by
        simpa [sub_self, add_sub_cancel_left] using
          (intervalIntegral.integral_comp_sub_left
            (f := fun y : ℝ => (y / epsilon) ^ 2)
            (a := L) (b := L + epsilon) (L + epsilon))
      _ = epsilon / 3 := hramp
  rw [inwardTrapezoidSquaredMass, hleft, hmiddle, hright]
  ring

/-- The bilateral squared mass of the two disjoint inward-smoothed edges. -/
def inwardRegularizedTwoEdgeSquaredMass (L epsilon : ℝ) : ℝ :=
  2 * inwardTrapezoidSquaredMass L epsilon

theorem inwardRegularizedTwoEdgeSquaredMass_eq
    {L epsilon : ℝ} (hepsilon : 0 < epsilon) (heL : epsilon ≤ L) :
    inwardRegularizedTwoEdgeSquaredMass L epsilon = 2 * (L - epsilon / 3) := by
  rw [inwardRegularizedTwoEdgeSquaredMass, inwardTrapezoidSquaredMass_eq hepsilon heL]

theorem tendsto_inwardRegularizedTwoEdgeSquaredMass_zero
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun epsilon : ℝ => inwardRegularizedTwoEdgeSquaredMass L epsilon)
      (𝓝[>] 0) (𝓝 (2 * L)) := by
  have hevent : ∀ᶠ epsilon : ℝ in 𝓝[>] 0, 0 < epsilon ∧ epsilon ≤ L := by
    have hupper : ∀ᶠ epsilon : ℝ in 𝓝[>] 0, epsilon ≤ L :=
      Filter.Eventually.filter_mono inf_le_left
        (show ∀ᶠ epsilon : ℝ in 𝓝 0, epsilon ≤ L from Iic_mem_nhds hL)
    filter_upwards [self_mem_nhdsWithin, hupper] with epsilon he0 heL
    exact ⟨he0, heL⟩
  have hformula : Tendsto (fun epsilon : ℝ => 2 * (L - epsilon / 3))
      (𝓝[>] 0) (𝓝 (2 * L)) := by
    have hcontinuous : Continuous (fun epsilon : ℝ => 2 * (L - epsilon / 3)) := by
      fun_prop
    have ht : Tendsto (fun epsilon : ℝ => 2 * (L - epsilon / 3))
        (𝓝 (0 : ℝ)) (𝓝 (2 * (L - 0 / 3))) := hcontinuous.continuousAt
    simpa using ht.mono_left inf_le_left
  exact hformula.congr' (hevent.mono fun epsilon he =>
    (inwardRegularizedTwoEdgeSquaredMass_eq he.1 he.2).symm)

/-- Transform of the two inward-smoothed edges. -/
def inwardRegularizedTwoEdgeTransform (L a epsilon : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w *
      inwardEdgeRegularizationFactor epsilon w +
    Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w) *
      inwardEdgeRegularizationFactor epsilon (-w)

theorem tendsto_inwardRegularizedTwoEdgeTransform_zero (L a : ℝ) (w : ℂ) :
    Tendsto (fun epsilon : ℝ => inwardRegularizedTwoEdgeTransform L a epsilon w)
      (𝓝 0) (𝓝 (rectangularTwoEdgeTransform L a w)) := by
  have hw := tendsto_inwardEdgeRegularizationFactor_zero w
  have hn := tendsto_inwardEdgeRegularizationFactor_zero (-w)
  simpa [inwardRegularizedTwoEdgeTransform, rectangularTwoEdgeTransform] using
    ((tendsto_const_nhds.mul tendsto_const_nhds).mul hw).add
      ((tendsto_const_nhds.mul tendsto_const_nhds).mul hn)

private theorem real_mul_re_le_abs_half {c : ℝ} {w : ℂ}
    (hw : |w.re| ≤ (1 / 2 : ℝ)) :
    ((c : ℂ) * w).re ≤ |c| / 2 := by
  rw [Complex.mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  calc
    c * w.re ≤ |c * w.re| := le_abs_self _
    _ = |c| * |w.re| := abs_mul c w.re
    _ ≤ |c| * (1 / 2) := mul_le_mul_of_nonneg_left hw (abs_nonneg c)
    _ = |c| / 2 := by ring

/-- A uniform reciprocal-height bound for every smoothing scale `0 ≤ epsilon ≤ 1`. -/
theorem norm_inwardRegularizedTwoEdgeTransform_le
    (L a : ℝ) {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    {w : ℂ} (hw0 : w ≠ 0) (hw : |w.re| ≤ 1 / 2) :
    ‖inwardRegularizedTwoEdgeTransform L a epsilon w‖ ≤
      (2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)) / ‖w‖ := by
  have hA := norm_rectangularWindowAmplitude_le L hw0 hw
  have hAnRaw := norm_rectangularWindowAmplitude_le L (neg_ne_zero.mpr hw0) (by simpa using hw)
  have hAn : ‖rectangularWindowAmplitude L (-w)‖ ≤
      (1 + Real.exp (|L| / 2)) / ‖w‖ := by
    simpa only [norm_neg] using hAnRaw
  have hm := norm_inwardEdgeRegularizationFactor_le hepsilon0 hepsilon1 hw
  have hmn := norm_inwardEdgeRegularizationFactor_le (w := -w)
    hepsilon0 hepsilon1 (by simpa using hw)
  have he : ‖Complex.exp ((a : ℂ) * w)‖ ≤ Real.exp (|a| / 2) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (real_mul_re_le_abs_half hw)
  have hen : ‖Complex.exp (-(a : ℂ) * w)‖ ≤ Real.exp (|a| / 2) := by
    rw [Complex.norm_exp]
    have h := real_mul_re_le_abs_half (c := -a) hw
    simpa only [ofReal_neg, neg_mul, abs_neg] using Real.exp_le_exp.mpr h
  rw [inwardRegularizedTwoEdgeTransform]
  calc
    ‖Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w *
          inwardEdgeRegularizationFactor epsilon w +
        Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w) *
          inwardEdgeRegularizationFactor epsilon (-w)‖ ≤
        ‖Complex.exp ((a : ℂ) * w)‖ * ‖rectangularWindowAmplitude L w‖ *
            ‖inwardEdgeRegularizationFactor epsilon w‖ +
          ‖Complex.exp (-(a : ℂ) * w)‖ * ‖rectangularWindowAmplitude L (-w)‖ *
            ‖inwardEdgeRegularizationFactor epsilon (-w)‖ := by
      simpa only [norm_mul] using norm_add_le
        (Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w *
          inwardEdgeRegularizationFactor epsilon w)
        (Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w) *
          inwardEdgeRegularizationFactor epsilon (-w))
    _ ≤ Real.exp (|a| / 2) * ((1 + Real.exp (|L| / 2)) / ‖w‖) * Real.exp (1 / 2) +
        Real.exp (|a| / 2) * ((1 + Real.exp (|L| / 2)) / ‖w‖) * Real.exp (1 / 2) := by
      gcongr
    _ = _ := by ring

def inwardRegularizedXiTwoEdgeTransform (L a epsilon : ℝ) (z : ℂ) : ℂ :=
  inwardRegularizedTwoEdgeTransform L a epsilon (I * z)

theorem tendsto_inwardRegularizedXiTwoEdgeTransform_zero (L a : ℝ) (z : ℂ) :
    Tendsto (fun epsilon : ℝ => inwardRegularizedXiTwoEdgeTransform L a epsilon z)
      (𝓝 0) (𝓝 (xiRectangularTwoEdgeTransform L a z)) := by
  exact tendsto_inwardRegularizedTwoEdgeTransform_zero L a (I * z)

theorem norm_inwardRegularizedXiTwoEdgeTransform_le
    (L a : ℝ) {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (q : XiZeroCopy) :
    ‖inwardRegularizedXiTwoEdgeTransform L a epsilon (xiSpectralPoint q)‖ ≤
      (2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)) /
        ‖xiSpectralPoint q‖ := by
  have hz : I * xiSpectralPoint q ≠ 0 :=
    mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
  simpa only [inwardRegularizedXiTwoEdgeTransform, norm_mul, norm_I, one_mul] using
    norm_inwardRegularizedTwoEdgeTransform_le L a hepsilon0 hepsilon1 hz
      (le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q))

theorem norm_inwardRegularizedXiTwoEdgePolarizationTerm_le
    (L a : ℝ) {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (q : XiZeroCopy) :
    ‖inwardRegularizedXiTwoEdgeTransform L a epsilon (xiSpectralPoint q) *
        xiWeilSharp (inwardRegularizedXiTwoEdgeTransform L a epsilon)
          (xiSpectralPoint q)‖ ≤
      (2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)) ^ 2 *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let C : ℝ := 2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)
  have hq := norm_inwardRegularizedXiTwoEdgeTransform_le L a hepsilon0 hepsilon1 q
  have hqc := norm_inwardRegularizedXiTwoEdgeTransform_le L a hepsilon0 hepsilon1
    (xiZeroCopyLineConjEquiv q)
  have hsharp :
      ‖xiWeilSharp (inwardRegularizedXiTwoEdgeTransform L a epsilon)
          (xiSpectralPoint q)‖ ≤ C / ‖xiSpectralPoint q‖ := by
    rw [xiWeilSharp, norm_conj, ← xiSpectralPoint_lineConj]
    simpa only [C, xiSpectralPoint_lineConj, norm_conj] using hqc
  change ‖_ * _‖ ≤ C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)
  rw [norm_mul]
  calc
    _ ≤ (C / ‖xiSpectralPoint q‖) * (C / ‖xiSpectralPoint q‖) :=
      mul_le_mul hq hsharp (norm_nonneg _) (by positivity)
    _ = C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

/-- Dominated convergence on the actual multiplicity-exact Xi divisor. -/
theorem tendsto_xiWeilPolarization_inwardRegularized_zero (L a : ℝ) :
    Tendsto
      (fun epsilon : ℝ => xiWeilPolarization
        (inwardRegularizedXiTwoEdgeTransform L a epsilon)
        (inwardRegularizedXiTwoEdgeTransform L a epsilon))
      (𝓝[>] 0)
      (𝓝 (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a))) := by
  let C : ℝ := 2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)
  have hsum : Summable (fun q : XiZeroCopy => C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left (C ^ 2)
  have hpoint (q : XiZeroCopy) : Tendsto
      (fun epsilon : ℝ =>
        inwardRegularizedXiTwoEdgeTransform L a epsilon (xiSpectralPoint q) *
          xiWeilSharp (inwardRegularizedXiTwoEdgeTransform L a epsilon)
            (xiSpectralPoint q))
      (𝓝[>] 0)
      (𝓝 (xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) *
        xiWeilSharp (xiRectangularTwoEdgeTransform L a) (xiSpectralPoint q))) := by
    have hleft : Tendsto
        (fun epsilon : ℝ => inwardRegularizedXiTwoEdgeTransform L a epsilon (xiSpectralPoint q))
        (𝓝[>] 0) (𝓝 (xiRectangularTwoEdgeTransform L a (xiSpectralPoint q))) :=
      (tendsto_inwardRegularizedXiTwoEdgeTransform_zero
        L a (xiSpectralPoint q)).mono_left inf_le_left
    have hright0 : Tendsto
        (fun epsilon : ℝ => inwardRegularizedXiTwoEdgeTransform L a epsilon
          ((starRingEnd ℂ) (xiSpectralPoint q)))
        (𝓝[>] 0) (𝓝 (xiRectangularTwoEdgeTransform L a
          ((starRingEnd ℂ) (xiSpectralPoint q)))) :=
      (tendsto_inwardRegularizedXiTwoEdgeTransform_zero
        L a ((starRingEnd ℂ) (xiSpectralPoint q))).mono_left inf_le_left
    have hright := Complex.continuous_conj.continuousAt.tendsto.comp hright0
    simpa only [xiWeilSharp] using hleft.mul hright
  have hbound : ∀ᶠ epsilon : ℝ in 𝓝[>] 0, ∀ q : XiZeroCopy,
      ‖inwardRegularizedXiTwoEdgeTransform L a epsilon (xiSpectralPoint q) *
          xiWeilSharp (inwardRegularizedXiTwoEdgeTransform L a epsilon)
            (xiSpectralPoint q)‖ ≤
        C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    have hupper : ∀ᶠ epsilon : ℝ in 𝓝[>] 0, epsilon < 1 :=
      Filter.Eventually.filter_mono inf_le_left
        (show ∀ᶠ epsilon : ℝ in 𝓝 0, epsilon < 1 from
          Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [self_mem_nhdsWithin, hupper] with epsilon he0 he1
    intro q
    exact norm_inwardRegularizedXiTwoEdgePolarizationTerm_le L a he0.le he1.le q
  simpa only [xiWeilPolarization] using
    tendsto_tsum_of_dominated_convergence hsum hpoint hbound

/-- Lossless variational passage from every inward-smoothed trial to the sharp two-edge value. -/
theorem sharp_xiWeilPolarization_ge_two_mul_length_mul_floor
    {L : ℝ} (hL : 0 < L) (a lambda : ℝ)
    (hvariational : ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      lambda * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiTwoEdgeTransform L a epsilon)
          (inwardRegularizedXiTwoEdgeTransform L a epsilon)).re) :
    2 * L * lambda ≤
      (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a)).re := by
  have hleft : Tendsto
      (fun epsilon : ℝ => lambda * inwardRegularizedTwoEdgeSquaredMass L epsilon)
      (𝓝[>] 0) (𝓝 (2 * L * lambda)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      tendsto_const_nhds.mul (tendsto_inwardRegularizedTwoEdgeSquaredMass_zero hL)
  have hright := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_xiWeilPolarization_inwardRegularized_zero L a)
  exact le_of_tendsto_of_tendsto hleft hright hvariational

def inwardRestrictedWeilNegativeFloor (lambda : ℕ → ℝ) (n : ℕ) : ℝ :=
  (lambda n)⁻

/-- The inward-regularization certificate constructs the exact sampled floor envelope consumed by
the already-formalized prime--polar transfer. -/
theorem xiRestrictedWeilNegativeFloorEnvelope_of_inwardRegularization
    {L : ℝ} (hL : 0 < L) (N : ℕ) (lambda : ℕ → ℝ)
    (hvariational : ∀ n : ℕ, ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      lambda n * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)).re) :
    XiRestrictedWeilNegativeFloorEnvelope L N
      (inwardRestrictedWeilNegativeFloor lambda) := by
  constructor
  · intro n
    exact negPart_nonneg _
  · intro n
    by_cases hn : N ≤ n
    · have hsharp := sharp_xiWeilPolarization_ge_two_mul_length_mul_floor
        hL (Real.log n / 2) (lambda n) (hvariational n)
      rw [xiRectangularWeilTailNegativePart, xiRectangularWeilTailCoefficient, if_pos hn,
        xiRectangularWeilLogCoefficient]
      rw [inwardRestrictedWeilNegativeFloor, negPart_def]
      apply max_le
      · calc
          -(xiWeilPolarization
              (xiRectangularTwoEdgeTransform L (Real.log n / 2))
              (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re ≤
              -(2 * L * lambda n) := neg_le_neg hsharp
          _ = 2 * L * (-lambda n) := by ring
          _ ≤ 2 * L * max (-lambda n) 0 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      · exact mul_nonneg (by positivity) (le_max_right _ _)
    · rw [xiRectangularWeilTailNegativePart, xiRectangularWeilTailCoefficient, if_neg hn]
      simp only [Complex.zero_re, negPart_zero]
      exact mul_nonneg (by positivity) (negPart_nonneg _)

/-- False RH forces the sampled negative restricted floor above every subcritical transverse power
at arbitrarily late logarithmic apertures. -/
theorem not_riemannHypothesis_implies_inwardRestrictedWeilFloor_cofinally_exceeds_power
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup)
    {N : ℕ} {eta : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N eta) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧ C * (n : ℝ) ^ alpha < eta n := by
  intro C hC N0
  obtain ⟨n, hn0, hLa, hq⟩ :=
    not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below_power
      hL halpha0 hRH halpha (2 * L * C) (by positivity) (max N0 N)
  have hnN : N ≤ n := (le_max_right N0 N).trans hn0
  have hnN0 : N0 ≤ n := (le_max_left N0 N).trans hn0
  have henvn := henv.2 n
  rw [xiRectangularWeilTailNegativePart, xiRectangularWeilTailCoefficient, if_pos hnN] at henvn
  have hneg : 2 * L * C * (n : ℝ) ^ alpha <
      ((xiRectangularWeilLogCoefficient L n).re)⁻ := by
    rw [negPart_def]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨n, hnN0, hLa, ?_⟩
  have hpow0 : 0 ≤ (n : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg n) alpha
  nlinarith

/-- Critical floor-abscissa criterion with the inward regularization hypothesis expanded rather
than hidden inside an envelope assumption. -/
theorem riemannHypothesis_iff_inwardRestrictedWeilFloor_negativeAbscissa_le_one
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {lambda : ℕ → ℝ}
    (hvariational : ∀ n : ℕ, ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      lambda n * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)).re)
    (hpositive : RiemannHypothesis → ∀ n, 0 ≤ lambda n) :
    RiemannHypothesis ↔
      LSeries.abscissaOfAbsConv
        (fun n => ((inwardRestrictedWeilNegativeFloor lambda n : ℝ) : ℂ)) ≤
          ((1 : ℝ) : EReal) := by
  apply riemannHypothesis_iff_restrictedWeilFloor_negativeAbscissa_le_one
    hL hN (xiRestrictedWeilNegativeFloorEnvelope_of_inwardRegularization
      hL N lambda hvariational)
  intro hRH n
  rw [inwardRestrictedWeilNegativeFloor, negPart_def,
    max_eq_right (neg_nonpos.mpr (hpositive hRH n))]

end

end RHTower
