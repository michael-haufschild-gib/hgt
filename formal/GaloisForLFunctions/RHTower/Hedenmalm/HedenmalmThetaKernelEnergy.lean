import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination

/-!
# The kernel energy of the Riemann source is finite

The Hilbert--Schmidt energy of the source inverse in quantile coordinates is the theta-tail
integral

`M ∫_ℝ p(x)(1 - p(x)) / k(x) dx`.

Its convergence is a doubly exponential estimate: the theta source is squeezed between two
constant multiples of

`E(x) = e^{9x/2} e^{-π e^{2x}}`

on the positive half-line, and `E` decays so fast that its own tail integral past `x` is at most
`E(x)/(π e^{2x})`.  Dividing the two bounds gives `(1 - p(x))/k(x) = O(e^{-2x})`, and the
reflection law transports the estimate to the negative half-line.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt

/-! ### The doubly exponential envelope -/

/-- The doubly exponential envelope of the theta source. -/
def thetaEnvelope (x : ℝ) : ℝ := Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))

theorem thetaEnvelope_pos (x : ℝ) : 0 < thetaEnvelope x := by
  unfold thetaEnvelope
  positivity

theorem exp_sq (x : ℝ) : Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem exp_four (x : ℝ) : Real.exp x ^ (4 : ℕ) = Real.exp (4 * x) := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem exp_half_add_four (x : ℝ) :
    Real.exp (x / 2) * Real.exp (4 * x) = Real.exp (9 * x / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The first theta atom in envelope coordinates. -/
theorem thetaCuspSourceTerm_one_eq (x : ℝ) :
    thetaCuspSourceTerm x 1
      = 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
  rw [thetaCuspSourceTerm, thetaCuspSeed]
  push_cast
  rw [one_mul, exp_sq, exp_four]
  ring

theorem thetaCuspSourceTerm_one_le (x : ℝ) :
    thetaCuspSourceTerm x 1 ≤ 4 * Real.pi ^ (2 : ℕ) * thetaEnvelope x := by
  have hpos : (0 : ℝ) ≤ Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)) := by positivity
  have hmul : 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x))
      ≤ 4 * Real.pi ^ (2 : ℕ) * Real.exp (4 * x) := by
    nlinarith [Real.pi_pos, Real.exp_pos (2 * x)]
  rw [thetaCuspSourceTerm_one_eq, thetaEnvelope]
  calc 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)))
      ≤ (4 * Real.pi ^ (2 : ℕ) * Real.exp (4 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) :=
        mul_le_mul_of_nonneg_right hmul hpos
    _ = 4 * Real.pi ^ (2 : ℕ) * (Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
        rw [← exp_half_add_four]
        ring

theorem thetaCuspSourceTerm_one_ge {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.pi * (2 * Real.pi - 3) * thetaEnvelope x ≤ thetaCuspSourceTerm x 1 := by
  have hpos : (0 : ℝ) ≤ Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)) := by positivity
  have hexp : Real.exp (2 * x) ≤ Real.exp (4 * x) := Real.exp_le_exp.mpr (by linarith)
  have hmul : 2 * Real.pi * (2 * Real.pi - 3) * Real.exp (4 * x)
      ≤ 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x)) := by
    nlinarith [Real.pi_pos]
  rw [thetaCuspSourceTerm_one_eq, thetaEnvelope]
  calc 2 * Real.pi * (2 * Real.pi - 3)
        * (Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)))
      = (2 * Real.pi * (2 * Real.pi - 3) * Real.exp (4 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
        rw [← exp_half_add_four]
        ring
    _ ≤ 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) :=
        mul_le_mul_of_nonneg_right hmul hpos

/-- The upper envelope constant. -/
def thetaEnvelopeUpper : ℝ := (1 + thetaCuspHigherAtomDominationWeight) * (4 * Real.pi ^ (2 : ℕ))

/-- The lower envelope constant. -/
def thetaEnvelopeLower : ℝ := 2 * Real.pi * (2 * Real.pi - 3)

theorem thetaEnvelopeLower_pos : 0 < thetaEnvelopeLower := by
  unfold thetaEnvelopeLower
  nlinarith [Real.pi_gt_three, Real.pi_pos]

theorem thetaEnvelopeUpper_pos : 0 < thetaEnvelopeUpper := by
  unfold thetaEnvelopeUpper
  have := thetaCuspHigherAtomDominationWeight_nonneg
  nlinarith [Real.pi_pos]

/-- **The theta source is dominated by the envelope** on the positive half-line. -/
theorem thetaCuspFullSource_le_envelope {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x ≤ thetaEnvelopeUpper * thetaEnvelope x := by
  have hW := thetaCuspHigherAtomDominationWeight_nonneg
  have h := thetaCuspFullSource_sub_first_le hx
  have h1 := thetaCuspSourceTerm_one_le x
  have h3 : thetaCuspFullSource x
      ≤ (1 + thetaCuspHigherAtomDominationWeight) * thetaCuspSourceTerm x 1 := by
    have e : (1 + thetaCuspHigherAtomDominationWeight) * thetaCuspSourceTerm x 1
        = thetaCuspSourceTerm x 1
          + thetaCuspHigherAtomDominationWeight * thetaCuspSourceTerm x 1 := by ring
    rw [e]
    linarith
  have h2 : (1 + thetaCuspHigherAtomDominationWeight) * thetaCuspSourceTerm x 1
      ≤ (1 + thetaCuspHigherAtomDominationWeight) * (4 * Real.pi ^ (2 : ℕ) * thetaEnvelope x) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  calc thetaCuspFullSource x
      ≤ (1 + thetaCuspHigherAtomDominationWeight) * thetaCuspSourceTerm x 1 := h3
    _ ≤ (1 + thetaCuspHigherAtomDominationWeight) * (4 * Real.pi ^ (2 : ℕ) * thetaEnvelope x) := h2
    _ = thetaEnvelopeUpper * thetaEnvelope x := by
        rw [thetaEnvelopeUpper]
        ring

/-- **The theta source dominates the envelope** on the open positive half-line. -/
theorem thetaCuspFullSource_ge_envelope {x : ℝ} (hx : 0 < x) :
    thetaEnvelopeLower * thetaEnvelope x ≤ thetaCuspFullSource x := by
  have hterm : thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x := by
    rw [thetaCuspFullSource]
    exact (summable_thetaCuspSourceTerm x).le_tsum 1
      (fun j _ => thetaCuspSourceTerm_nonneg_of_pos hx j)
  have := thetaCuspSourceTerm_one_ge hx.le
  rw [thetaEnvelopeLower]
  linarith

/-! ### The tail of the envelope -/

theorem thetaEnvelope_le_shift {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    thetaEnvelope y ≤ thetaEnvelope x * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := by
  have hd : (0 : ℝ) ≤ y - x := by linarith
  have hbig : Real.exp (2 * x) * (1 + 2 * (y - x)) ≤ Real.exp (2 * y) := by
    have h := Real.add_one_le_exp (2 * (y - x))
    have hpos : (0 : ℝ) < Real.exp (2 * x) := Real.exp_pos _
    have hmul : Real.exp (2 * x) * (2 * (y - x) + 1)
        ≤ Real.exp (2 * x) * Real.exp (2 * (y - x)) := mul_le_mul_of_nonneg_left h hpos.le
    rwa [← Real.exp_add, show 2 * x + 2 * (y - x) = 2 * y by ring,
      show 2 * (y - x) + 1 = 1 + 2 * (y - x) by ring] at hmul
  have hpi : 9 / 2 ≤ Real.pi * Real.exp (2 * x) := by
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    have h2 : Real.exp 2 ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.pi_gt_three]
  have hE : Real.exp (9 * y / 2) = Real.exp (9 * x / 2) * Real.exp (9 * (y - x) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hD : Real.exp (-Real.pi * Real.exp (2 * y))
      ≤ Real.exp (-Real.pi * Real.exp (2 * x))
        * Real.exp (-(2 * Real.pi * Real.exp (2 * x)) * (y - x)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [Real.pi_pos, hbig]
  rw [thetaEnvelope, thetaEnvelope]
  calc Real.exp (9 * y / 2) * Real.exp (-Real.pi * Real.exp (2 * y))
      ≤ (Real.exp (9 * x / 2) * Real.exp (9 * (y - x) / 2))
        * (Real.exp (-Real.pi * Real.exp (2 * x))
          * Real.exp (-(2 * Real.pi * Real.exp (2 * x)) * (y - x))) := by
        rw [hE]
        exact mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)))
        * (Real.exp (9 * (y - x) / 2)
          * Real.exp (-(2 * Real.pi * Real.exp (2 * x)) * (y - x))) := by ring
    _ ≤ (Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)))
        * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hpi, hd]

/-- **The theta source decays exponentially past any point of the positive half-line**, with a
rate that grows doubly exponentially. -/
theorem thetaCuspFullSource_le_shift {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    thetaCuspFullSource y
      ≤ (thetaEnvelopeUpper * thetaEnvelope x)
        * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := by
  have h1 := thetaCuspFullSource_le_envelope (le_trans (by linarith) hxy)
  have h2 := thetaEnvelope_le_shift hx hxy
  have hU := thetaEnvelopeUpper_pos
  calc thetaCuspFullSource y ≤ thetaEnvelopeUpper * thetaEnvelope y := h1
    _ ≤ thetaEnvelopeUpper
        * (thetaEnvelope x * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x))) :=
        mul_le_mul_of_nonneg_left h2 hU.le
    _ = (thetaEnvelopeUpper * thetaEnvelope x)
        * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := by ring


/-! ### The tail integral of the source -/

theorem integrableOn_exp_neg_shift {a x : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => Real.exp (-a * (y - x))) (Ioi x) volume := by
  have h : IntegrableOn (fun y : ℝ => Real.exp (a * x) * Real.exp (-a * y)) (Ioi x) volume :=
    (exp_neg_integrableOn_Ioi x ha).const_mul (Real.exp (a * x))
  refine MeasureTheory.IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_Ioi
  rw [← Real.exp_add]
  congr 1
  ring

theorem integral_Ioi_exp_neg_shift {a x : ℝ} (ha : 0 < a) :
    ∫ y in Ioi x, Real.exp (-a * (y - x)) = 1 / a := by
  set F : ℝ → ℝ := fun t => -(1 / a) * Real.exp (-a * (t - x)) with hF
  have hderiv : ∀ y ∈ Ioi x, HasDerivAt F (Real.exp (-a * (y - x))) y := by
    intro y _
    have h1 : HasDerivAt (fun t : ℝ => -a * (t - x)) (-a) y := by
      simpa using ((hasDerivAt_id y).sub_const x).const_mul (-a)
    have h2 := h1.exp.const_mul (-(1 / a))
    refine h2.congr_deriv ?_
    field_simp
  have hcont : ContinuousWithinAt F (Ici x) x := by
    refine Continuous.continuousWithinAt ?_
    rw [hF]
    fun_prop
  have hshift : Tendsto (fun t : ℝ => t - x) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-x) (tendsto_id (α := ℝ))
    refine h.congr fun t => ?_
    simp [sub_eq_add_neg]
  have hlin : Tendsto (fun t : ℝ => a * (t - x)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha hshift
  have htend : Tendsto F atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-a * (t - x))) atTop (𝓝 0) := by
      have h0 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
      refine h0.congr fun t => ?_
      simp [neg_mul]
    simpa [hF] using hexp.const_mul (-(1 / a))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_exp_neg_shift ha) htend
  rw [h, hF]
  simp

/-- **The tail mass of the theta source past a point of the positive half-line.** -/
theorem integral_Ioi_thetaCuspFullSource_le {x : ℝ} (hx : 1 ≤ x) :
    ∫ y in Ioi x, thetaCuspFullSource y
      ≤ thetaEnvelopeUpper * thetaEnvelope x / (Real.pi * Real.exp (2 * x)) := by
  have ha : (0 : ℝ) < Real.pi * Real.exp (2 * x) := by positivity
  have hk : IntegrableOn thetaCuspFullSource (Ioi x) volume :=
    thetaSource.integrable_k.integrableOn
  have hb : IntegrableOn (fun y : ℝ => (thetaEnvelopeUpper * thetaEnvelope x) *
      Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x))) (Ioi x) volume :=
    (integrableOn_exp_neg_shift ha).const_mul _
  have hmono := setIntegral_mono_on hk hb measurableSet_Ioi
    (fun y hy => thetaCuspFullSource_le_shift hx (le_of_lt hy))
  rw [MeasureTheory.integral_const_mul, integral_Ioi_exp_neg_shift ha] at hmono
  calc ∫ y in Ioi x, thetaCuspFullSource y
      ≤ thetaEnvelopeUpper * thetaEnvelope x * (1 / (Real.pi * Real.exp (2 * x))) := hmono
    _ = thetaEnvelopeUpper * thetaEnvelope x / (Real.pi * Real.exp (2 * x)) := by
        rw [mul_one_div]

/-! ### The reciprocal tail density -/

theorem one_sub_cdfFun (S : PositiveDensitySource) (x : ℝ) :
    1 - S.cdfFun x = (∫ y in Ioi x, S.k y) / S.mass := by
  have hsplit : (∫ y in Iic x, S.k y) + ∫ y in Ioi x, S.k y = S.mass := by
    rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      S.integrable_k.integrableOn S.integrable_k.integrableOn, Iic_union_Ioi, setIntegral_univ]
    rfl
  have hM : S.mass ≠ 0 := S.mass_ne_zero
  rw [PositiveDensitySource.cdfFun]
  field_simp
  linarith

theorem tailEnergyDensity_nonneg (S : PositiveDensitySource) (x : ℝ) :
    0 ≤ tailEnergyDensity S x := by
  have h := S.cdfFun_mem_Ioo x
  exact div_nonneg (mul_nonneg h.1.le (by linarith [h.2])) (S.pos_k x).le

theorem continuous_tailEnergyDensity (S : PositiveDensitySource) :
    Continuous (tailEnergyDensity S) :=
  (S.continuous_cdfFun.mul (continuous_const.sub S.continuous_cdfFun)).div S.continuous_k
    (fun x => (S.pos_k x).ne')

/-- The constant of the reciprocal tail estimate. -/
def thetaTailConstant : ℝ :=
  thetaEnvelopeUpper / (thetaSource.mass * thetaEnvelopeLower * Real.pi)

theorem thetaTailConstant_pos : 0 < thetaTailConstant := by
  rw [thetaTailConstant]
  have := thetaEnvelopeUpper_pos
  have := thetaEnvelopeLower_pos
  have := thetaSource.mass_pos
  positivity

/-- **The reciprocal tail density decays exponentially** on the positive half-line. -/
theorem tailEnergyDensity_le {x : ℝ} (hx : 1 ≤ x) :
    tailEnergyDensity thetaSource x ≤ thetaTailConstant * Real.exp (-(2 * x)) := by
  have hcdf := thetaSource.cdfFun_mem_Ioo x
  have hkpos : 0 < thetaSource.k x := thetaSource.pos_k x
  have hM : 0 < thetaSource.mass := thetaSource.mass_pos
  have henv : 0 < thetaEnvelope x := thetaEnvelope_pos x
  have hL := thetaEnvelopeLower_pos
  have hU := thetaEnvelopeUpper_pos
  have hklow : thetaEnvelopeLower * thetaEnvelope x ≤ thetaCuspFullSource x :=
    thetaCuspFullSource_ge_envelope (by linarith)
  have hT := integral_Ioi_thetaCuspFullSource_le hx
  have hTnn : 0 ≤ ∫ y in Ioi x, thetaCuspFullSource y := by
    refine setIntegral_nonneg measurableSet_Ioi fun y _ => (thetaCuspFullSource_pos y).le
  have hstep1 : tailEnergyDensity thetaSource x
      ≤ (1 - thetaSource.cdfFun x) / thetaSource.k x := by
    have hnum : thetaSource.cdfFun x * (1 - thetaSource.cdfFun x) ≤ 1 - thetaSource.cdfFun x := by
      nlinarith [hcdf.1, hcdf.2]
    exact div_le_div_of_nonneg_right hnum hkpos.le
  have hstep2 : (1 - thetaSource.cdfFun x) / thetaSource.k x
      = (∫ y in Ioi x, thetaCuspFullSource y) / (thetaSource.mass * thetaSource.k x) := by
    rw [one_sub_cdfFun thetaSource x]
    field_simp
    rfl
  have hden : 0 < thetaSource.mass * (thetaEnvelopeLower * thetaEnvelope x) := by positivity
  have hden_le : thetaSource.mass * (thetaEnvelopeLower * thetaEnvelope x)
      ≤ thetaSource.mass * thetaSource.k x :=
    mul_le_mul_of_nonneg_left hklow hM.le
  have hnum_nn : 0 ≤ thetaEnvelopeUpper * thetaEnvelope x / (Real.pi * Real.exp (2 * x)) := by
    positivity
  have hstep3 : (∫ y in Ioi x, thetaCuspFullSource y) / (thetaSource.mass * thetaSource.k x)
      ≤ (thetaEnvelopeUpper * thetaEnvelope x / (Real.pi * Real.exp (2 * x)))
        / (thetaSource.mass * (thetaEnvelopeLower * thetaEnvelope x)) :=
    div_le_div₀ hnum_nn hT hden hden_le
  have hfinal : (thetaEnvelopeUpper * thetaEnvelope x / (Real.pi * Real.exp (2 * x)))
      / (thetaSource.mass * (thetaEnvelopeLower * thetaEnvelope x))
      = thetaTailConstant * Real.exp (-(2 * x)) := by
    rw [thetaTailConstant, Real.exp_neg]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hexp : Real.exp (2 * x) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  calc tailEnergyDensity thetaSource x
      ≤ (1 - thetaSource.cdfFun x) / thetaSource.k x := hstep1
    _ = (∫ y in Ioi x, thetaCuspFullSource y) / (thetaSource.mass * thetaSource.k x) := hstep2
    _ ≤ _ := hstep3
    _ = thetaTailConstant * Real.exp (-(2 * x)) := hfinal

/-- The reciprocal tail density of the theta source is even. -/
theorem tailEnergyDensity_neg (x : ℝ) :
    tailEnergyDensity thetaSource (-x) = tailEnergyDensity thetaSource x := by
  have hc := HedenmalmIntervalAnomaly.cdfFun_neg thetaSource thetaSource_even x
  have hk : thetaSource.k (-x) = thetaSource.k x := thetaSource_even x
  show thetaSource.cdfFun (-x) * (1 - thetaSource.cdfFun (-x)) / thetaSource.k (-x) = _
  rw [hc, hk]
  show (1 - thetaSource.cdfFun x) * (1 - (1 - thetaSource.cdfFun x)) / thetaSource.k x = _
  show _ = thetaSource.cdfFun x * (1 - thetaSource.cdfFun x) / thetaSource.k x
  ring_nf

/-- **The reciprocal tail density decays exponentially at both ends.** -/
theorem tailEnergyDensity_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    tailEnergyDensity thetaSource x ≤ thetaTailConstant * Real.exp (-(2 * |x|)) := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    exact tailEnergyDensity_le (by rwa [abs_of_nonneg h] at hx)
  · rw [abs_of_neg h]
    rw [← tailEnergyDensity_neg x]
    exact tailEnergyDensity_le (by rwa [abs_of_neg h] at hx)

/-! ### Integrability of the kernel energy -/

theorem integrableOn_tailEnergyDensity_tail {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : ∀ x ∈ s, 1 ≤ |x|) :
    IntegrableOn (tailEnergyDensity thetaSource) s volume := by
  refine Integrable.mono'
    (((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (by norm_num : (0:ℝ) < 2)).const_mul
      thetaTailConstant).integrableOn) ?_ ?_
  · exact (continuous_tailEnergyDensity thetaSource).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (tailEnergyDensity_nonneg thetaSource x)]
    exact tailEnergyDensity_le_abs (hsub x hx)

/-- **The theta-tail energy of the Riemann source is finite.** -/
theorem integrable_tailEnergyDensity_thetaSource :
    Integrable (tailEnergyDensity thetaSource) volume := by
  have hmid : IntegrableOn (tailEnergyDensity thetaSource) (Ioc (-1 : ℝ) 1) volume :=
    ((continuous_tailEnergyDensity thetaSource).integrableOn_Icc (a := (-1 : ℝ))
      (b := 1)).mono_set Ioc_subset_Icc_self
  have hleft : IntegrableOn (tailEnergyDensity thetaSource) (Iic (-1 : ℝ)) volume :=
    integrableOn_tailEnergyDensity_tail measurableSet_Iic fun x hx => by
      simp only [mem_Iic] at hx
      rw [abs_of_nonpos (by linarith : x ≤ 0)]
      linarith
  have hright : IntegrableOn (tailEnergyDensity thetaSource) (Ioi (1 : ℝ)) volume :=
    integrableOn_tailEnergyDensity_tail measurableSet_Ioi fun x hx => by
      simp only [mem_Ioi] at hx
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hunion : (Iic (-1 : ℝ)) ∪ (Ioc (-1 : ℝ) 1 ∪ Ioi 1) = univ := by
    rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (-1 : ℝ) ≤ 1), Iic_union_Ioi]
  rw [← integrableOn_univ, ← hunion]
  exact hleft.union (hmid.union hright)

/-- **The kernel field of the Riemann source is square integrable.** -/
theorem hasFiniteKernelEnergy_thetaSource : HasFiniteKernelEnergy thetaSource := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (thetaSource.mass / thetaSource.k x) ^ (2 : ℕ)
        * (thetaSource.cdfFun x * (1 - thetaSource.cdfFun x))) (volume : Measure ℝ) := by
    refine (((continuous_const.div thetaSource.continuous_k
      fun x => (thetaSource.pos_k x).ne').pow 2).mul ?_).aestronglyMeasurable
    exact thetaSource.continuous_cdfFun.mul (continuous_const.sub thetaSource.continuous_cdfFun)
  have hiff := thetaSource.integrableOn_comp_quantileFun_iff (g := fun x : ℝ =>
      (thetaSource.mass / thetaSource.k x) ^ (2 : ℕ)
        * (thetaSource.cdfFun x * (1 - thetaSource.cdfFun x))) hmeas
  have hright : Integrable (fun x : ℝ => thetaSource.normalized x •
      ((thetaSource.mass / thetaSource.k x) ^ (2 : ℕ)
        * (thetaSource.cdfFun x * (1 - thetaSource.cdfFun x)))) (volume : Measure ℝ) := by
    refine (integrable_tailEnergyDensity_thetaSource.const_mul thetaSource.mass).congr ?_
    filter_upwards with x
    have hk : thetaSource.k x ≠ 0 := (thetaSource.pos_k x).ne'
    have hM : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
    show thetaSource.mass * tailEnergyDensity thetaSource x
      = thetaSource.normalized x •
        ((thetaSource.mass / thetaSource.k x) ^ (2 : ℕ)
          * (thetaSource.cdfFun x * (1 - thetaSource.cdfFun x)))
    show thetaSource.mass
        * (thetaSource.cdfFun x * (1 - thetaSource.cdfFun x) / thetaSource.k x)
      = (thetaSource.k x / thetaSource.mass) *
        ((thetaSource.mass / thetaSource.k x) ^ (2 : ℕ)
          * (thetaSource.cdfFun x * (1 - thetaSource.cdfFun x)))
    field_simp
  have hleft := hiff.mpr hright
  have hcongr : IntegrableOn
      (fun t : ℝ => quantileSpeed thetaSource t ^ (2 : ℕ) * (t * (1 - t))) (Ioo (0 : ℝ) 1) volume := by
    refine MeasureTheory.IntegrableOn.congr_fun hleft (fun t ht => ?_) measurableSet_Ioo
    show (thetaSource.mass / thetaSource.k (thetaSource.quantileFun t)) ^ (2 : ℕ)
        * (thetaSource.cdfFun (thetaSource.quantileFun t)
          * (1 - thetaSource.cdfFun (thetaSource.quantileFun t)))
      = quantileSpeed thetaSource t ^ (2 : ℕ) * (t * (1 - t))
    rw [thetaSource.cdfFun_quantile ht, quantileSpeed]
  have hres : unitIntervalMeasure = (volume : Measure ℝ).restrict (Ioo 0 1) := by
    rw [unitIntervalMeasure, restrict_Ioo_eq_restrict_Icc]
  show Integrable _ unitIntervalMeasure
  rw [hres]
  exact hcongr

/-- **The source inverse of the Riemann source is Hilbert--Schmidt** — unconditionally. -/
theorem isHilbertSchmidt_thetaKernelOperator :
    ContinuousLinearMap.IsHilbertSchmidt
      (kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
        (pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)) :=
  isHilbertSchmidt_pinnedKernelOperator thetaSource hasFiniteKernelEnergy_thetaSource

/-- **The source inverse of the Riemann source is compact** — unconditionally. -/
theorem isCompactOperator_thetaKernelOperator :
    IsCompactOperator
      (kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
        (pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)) :=
  isCompactOperator_pinnedKernelOperator thetaSource hasFiniteKernelEnergy_thetaSource

end HedenmalmThetaSource

end

end RHTower
