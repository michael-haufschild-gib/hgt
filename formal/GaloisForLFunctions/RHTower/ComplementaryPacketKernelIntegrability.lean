import GaloisForLFunctions.RHTower.ComplementaryPacketCofinalIsometry
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Function.Floor

/-!
# The boundary packet kernel is uniformly integrable and square integrable

The exponential envelope of `ComplementaryPacketPowerSumEnvelope` turns into uniform `L¹` and `L²`
bounds on the half line:

```text
∫_0^∞ |k_ω| ≤ 2^ω ,        ∫_0^∞ k_ω^(2 : ℕ) ≤ 4^ω .
```

Both constants are bounded on `0 ≤ ω ≤ ω₀`, so the general cofinal law of
`ComplementaryPacketCofinalIsometry` applies to the whole boundary family at once, with a defect
constant that does not degenerate as `ω ↓ 0`.

The kernel also has a closed step form,

```text
k_ω(t) = e^(-(1+ω)t) ∑_{m ≤ e^t} m^ω − 1/(1+ω) ,
```

which makes its measurability immediate: the only non-continuous ingredient is `Nat.floor`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Closed step form of the boundary packet kernel: the subtracted power integral cancels the
exponential weight exactly and leaves the incoming constant. -/
theorem complementaryPacketKernel_eq (ω : ℝ) (hω : 0 ≤ ω) (t : ℝ) :
    complementaryPacketKernel ω t
      = Real.exp (-(1 + ω) * t) * (∑ i ∈ Finset.range (⌊Real.exp t⌋₊ + 1), (i : ℝ) ^ ω)
        - 1 / (1 + ω) := by
  have hne : (1 : ℝ) + ω ≠ 0 := by linarith
  have hpow : (Real.exp t) ^ (1 + ω) = Real.exp (t * (1 + ω)) := (Real.exp_mul t (1 + ω)).symm
  rw [complementaryPacketKernel, powerSumRemainder, hpow, mul_sub]
  congr 1
  rw [mul_div_assoc', ← Real.exp_add]
  rw [show -(1 + ω) * t + t * (1 + ω) = 0 by ring, Real.exp_zero]

theorem measurable_complementaryPacketKernel (ω : ℝ) (hω : 0 ≤ ω) :
    Measurable (complementaryPacketKernel ω) := by
  have hfloor : Measurable fun t : ℝ => ⌊Real.exp t⌋₊ :=
    Nat.measurable_floor.comp Real.measurable_exp
  have hstep : Measurable fun t : ℝ =>
      (∑ i ∈ Finset.range (⌊Real.exp t⌋₊ + 1), (i : ℝ) ^ ω) :=
    (Measurable.of_discrete
      (f := fun n : ℕ => ∑ i ∈ Finset.range (n + 1), (i : ℝ) ^ ω)).comp hfloor
  have h : Measurable fun t : ℝ =>
      Real.exp (-(1 + ω) * t) * (∑ i ∈ Finset.range (⌊Real.exp t⌋₊ + 1), (i : ℝ) ^ ω)
        - 1 / (1 + ω) :=
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hstep).sub
      measurable_const
  have hfun : complementaryPacketKernel ω = fun t : ℝ =>
      Real.exp (-(1 + ω) * t) * (∑ i ∈ Finset.range (⌊Real.exp t⌋₊ + 1), (i : ℝ) ^ ω)
        - 1 / (1 + ω) := funext (complementaryPacketKernel_eq ω hω)
  rw [hfun]
  exact h

/-! ### The dominating exponential -/

private theorem integrableOn_exp_neg : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
  have h := exp_neg_integrableOn_Ioi (0 : ℝ) (b := 1) one_pos
  simpa using h

private theorem setIntegral_exp_neg : (∫ t in Ioi (0 : ℝ), Real.exp (-t)) = 1 :=
  integral_exp_neg_Ioi_zero

/-! ### Uniform `L¹` and `L²` bounds -/

theorem integrableOn_complementaryPacketKernel (ω : ℝ) (hω : 0 ≤ ω) :
    IntegrableOn (complementaryPacketKernel ω) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg.const_mul (2 ^ ω))
    (measurable_complementaryPacketKernel ω hω).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact abs_complementaryPacketKernel_le ω hω (le_of_lt ht)

theorem integrableOn_complementaryPacketKernel_sq (ω : ℝ) (hω : 0 ≤ ω) :
    IntegrableOn (fun t => complementaryPacketKernel ω t ^ 2) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg.const_mul (4 ^ ω))
    (((measurable_complementaryPacketKernel ω hω).pow_const 2)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  have henv := abs_complementaryPacketKernel_le ω hω ht0
  have habs : (0 : ℝ) ≤ |complementaryPacketKernel ω t| := abs_nonneg _
  have hpos : (0 : ℝ) ≤ 2 ^ ω * Real.exp (-t) := by positivity
  have hsq : complementaryPacketKernel ω t ^ 2 ≤ (2 ^ ω * Real.exp (-t)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ habs henv 2
  have hexp : (2 ^ ω * Real.exp (-t)) ^ 2 = 4 ^ ω * (Real.exp (-t) * Real.exp (-t)) := by
    rw [mul_pow, ← Real.rpow_natCast (2 ^ ω) 2, ← Real.rpow_mul (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
    rw [← Real.rpow_mul (by norm_num)]
    ring_nf
  have hmono : Real.exp (-t) * Real.exp (-t) ≤ Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ ω := Real.rpow_nonneg (by norm_num) ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc complementaryPacketKernel ω t ^ 2 ≤ (2 ^ ω * Real.exp (-t)) ^ 2 := hsq
    _ = 4 ^ ω * (Real.exp (-t) * Real.exp (-t)) := hexp
    _ ≤ 4 ^ ω * Real.exp (-t) := mul_le_mul_of_nonneg_left hmono h4

/-- **Uniform `L¹` bound.** -/
theorem setIntegral_abs_complementaryPacketKernel_le (ω : ℝ) (hω : 0 ≤ ω) :
    (∫ t in Ioi (0 : ℝ), |complementaryPacketKernel ω t|) ≤ 2 ^ ω := by
  have hbound : (∫ t in Ioi (0 : ℝ), |complementaryPacketKernel ω t|)
      ≤ ∫ t in Ioi (0 : ℝ), 2 ^ ω * Real.exp (-t) := by
    refine setIntegral_mono_on (integrableOn_complementaryPacketKernel ω hω).abs
      (integrableOn_exp_neg.const_mul (2 ^ ω)) measurableSet_Ioi fun t ht => ?_
    exact abs_complementaryPacketKernel_le ω hω (le_of_lt ht)
  rw [integral_const_mul, setIntegral_exp_neg, mul_one] at hbound
  exact hbound

/-- **Uniform `L²` bound.** -/
theorem setIntegral_complementaryPacketKernel_sq_le (ω : ℝ) (hω : 0 ≤ ω) :
    (∫ t in Ioi (0 : ℝ), complementaryPacketKernel ω t ^ 2) ≤ 4 ^ ω := by
  have hbound : (∫ t in Ioi (0 : ℝ), complementaryPacketKernel ω t ^ 2)
      ≤ ∫ t in Ioi (0 : ℝ), 4 ^ ω * Real.exp (-t) := by
    refine setIntegral_mono_on (integrableOn_complementaryPacketKernel_sq ω hω)
      (integrableOn_exp_neg.const_mul (4 ^ ω)) measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have henv := abs_complementaryPacketKernel_le ω hω ht0
    have habs : (0 : ℝ) ≤ |complementaryPacketKernel ω t| := abs_nonneg _
    have hsq : complementaryPacketKernel ω t ^ 2 ≤ (2 ^ ω * Real.exp (-t)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ habs henv 2
    have hexp : (2 ^ ω * Real.exp (-t)) ^ 2 = 4 ^ ω * (Real.exp (-t) * Real.exp (-t)) := by
      rw [mul_pow, ← Real.rpow_natCast (2 ^ ω) 2, ← Real.rpow_mul (by norm_num)]
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
      rw [← Real.rpow_mul (by norm_num)]
      ring_nf
    have hmono : Real.exp (-t) * Real.exp (-t) ≤ Real.exp (-t) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ ω := Real.rpow_nonneg (by norm_num) ω
    calc complementaryPacketKernel ω t ^ 2 ≤ (2 ^ ω * Real.exp (-t)) ^ 2 := hsq
      _ = 4 ^ ω * (Real.exp (-t) * Real.exp (-t)) := hexp
      _ ≤ 4 ^ ω * Real.exp (-t) := mul_le_mul_of_nonneg_left hmono h4
  rw [integral_const_mul, setIntegral_exp_neg, mul_one] at hbound
  exact hbound

/-! ### The boundary packet is a cofinal affine isometry -/

/-- The incoming constant of the boundary packet. -/
def complementaryPacketConstant (ω : ℝ) : ℝ := 1 / (1 + ω)

/-- **Cofinal affine isometry of the boundary packet.**  For every shift `ω ≥ 0` the two-point
modulus of the complementary packet differs from `c_ω^(2 : ℕ) a` by at most `5·4^ω + 2 c_ω 2^ω`,
uniformly in the separation. -/
theorem abs_complementaryPacketModulus_sub_le (ω : ℝ) (hω : 0 ≤ ω) {a : ℝ} (ha : 0 ≤ a) :
    |packetTranslationModulus (complementaryPacketKernel ω) (complementaryPacketConstant ω) a
        - complementaryPacketConstant ω ^ 2 * a|
      ≤ 5 * 4 ^ ω + 2 * |complementaryPacketConstant ω| * 2 ^ ω :=
  abs_packetTranslationModulus_sub_le (measurable_complementaryPacketKernel ω hω)
    (integrableOn_complementaryPacketKernel ω hω)
    (integrableOn_complementaryPacketKernel_sq ω hω)
    (setIntegral_abs_complementaryPacketKernel_le ω hω)
    (setIntegral_complementaryPacketKernel_sq_le ω hω) ha

/-- **Cofinal slope of the boundary packet.**  Its two-point modulus has affine slope
`c_ω^(2 : ℕ) = 1/(1+ω)^(2 : ℕ)` at infinity, so the packet path is an asymptotic affine isometry. -/
theorem tendsto_complementaryPacketModulus_div (ω : ℝ) (hω : 0 ≤ ω) :
    Filter.Tendsto (fun a : ℝ =>
        packetTranslationModulus (complementaryPacketKernel ω)
          (complementaryPacketConstant ω) a / a)
      Filter.atTop (nhds (complementaryPacketConstant ω ^ 2)) :=
  tendsto_packetTranslationModulus_div (measurable_complementaryPacketKernel ω hω)
    (integrableOn_complementaryPacketKernel ω hω)
    (integrableOn_complementaryPacketKernel_sq ω hω)
    (setIntegral_abs_complementaryPacketKernel_le ω hω)
    (setIntegral_complementaryPacketKernel_sq_le ω hω)

end

end RHTower
