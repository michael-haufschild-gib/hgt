import GaloisForLFunctions.RHTower.EulerMascheroniExponentialIntegral
import GaloisForLFunctions.RHTower.SquarefreeCriticalNormalCone

/-!
# The exact half-normal scale

`prime-valuation-dyadic-fermion-normal-cone-law`, equation `(13o)`.

The half-normal renormalization has an exact scale.  Writing `Ein` for the exponential integral,

`2 Φ(-V) = ∫₀¹ (e^{-Vt} - 1)² dt/t = 2 Ein(V) - Ein(2V)`,

because `(e^{-x} - 1)² = 2(1 - e^{-x}) - (1 - e^{-2x})`.  Since `Ein(a) - log a → γ`, this gives
`2 Φ(-V) - log V → γ - log 2`, that is

`e^{Φ(-V)} ∼ √(e^γ V / 2)`.
-/

open MeasureTheory Filter Topology Set

namespace RHTower

noncomputable section

/-- The `V`-scaled `Ein` integrand `(1 - e^{-Vt})/t`. -/
def scaledEinProfile (V t : ℝ) : ℝ := if t = 0 then 0 else (1 - Real.exp (-(V * t))) / t

theorem scaledEinProfile_eq (V : ℝ) : scaledEinProfile V = fun t => V * einProfile (V * t) := by
  funext t
  rw [scaledEinProfile, einProfile]
  by_cases ht : t = 0
  · simp [ht]
  · by_cases hV : V = 0
    · simp [hV, ht]
    · rw [if_neg ht, if_neg (by exact mul_ne_zero hV ht)]
      field_simp

theorem integral_scaledEinProfile {V : ℝ} (hV : 0 < V) :
    (∫ t in (0 : ℝ)..1, scaledEinProfile V t) = ein V := by
  rw [scaledEinProfile_eq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left einProfile (ne_of_gt hV)]
  rw [mul_zero, mul_one, ein, smul_eq_mul]
  field_simp

theorem scaledEinProfile_nonneg {V t : ℝ} (hV : 0 ≤ V) (ht : 0 ≤ t) :
    0 ≤ scaledEinProfile V t := by
  rw [scaledEinProfile]
  split_ifs with h
  · exact le_rfl
  · have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    have : Real.exp (-(V * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    positivity

theorem scaledEinProfile_le {V t : ℝ} (hV : 0 ≤ V) (ht : 0 ≤ t) : scaledEinProfile V t ≤ V := by
  rw [scaledEinProfile]
  split_ifs with h
  · exact hV
  · have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    rw [div_le_iff₀ ht0]
    have := Real.add_one_le_exp (-(V * t))
    nlinarith

theorem intervalIntegrable_scaledEinProfile {V : ℝ} (hV : 0 ≤ V) :
    IntervalIntegrable (scaledEinProfile V) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  have hcont : ContinuousOn (scaledEinProfile V) (Set.Ioc (0 : ℝ) 1) := by
    have hquot : ContinuousOn (fun t : ℝ => (1 - Real.exp (-(V * t))) / t) (Set.Ioc (0 : ℝ) 1) :=
      (continuousOn_const.sub ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg).continuousOn)).div continuousOn_id
        (fun t ht => ne_of_gt ht.1)
    refine hquot.congr fun t ht => ?_
    rw [scaledEinProfile, if_neg (ne_of_gt ht.1)]
  exact ⟨hcont.aestronglyMeasurable measurableSet_Ioc,
    MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := V) measure_Ioc_lt_top
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (scaledEinProfile_nonneg hV ht.1.le)]
        exact scaledEinProfile_le hV ht.1.le)⟩

/-- **The half-normal exponent in terms of the exponential integral.** -/
theorem coherentExponent_neg_eq {V : ℝ} (hV : 0 < V) :
    2 * coherentExponent (-V) 0 = 2 * ein V - ein (2 * V) := by
  have hpoint : ∀ t : ℝ, divProfile (coherentProfile (-V) 0) t
      = 2 * scaledEinProfile V t - scaledEinProfile (2 * V) t := by
    intro t
    rw [divProfile, coherentProfile, scaledEinProfile, scaledEinProfile]
    by_cases ht : t = 0
    · simp [ht]
    · rw [if_neg ht, if_neg ht, if_neg ht]
      rw [show (0 : ℝ) * t = 0 by ring, Real.exp_zero]
      have hexp : Real.exp (-(2 * V * t)) = Real.exp (-V * t) * Real.exp (-V * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hneg : Real.exp (-(V * t)) = Real.exp (-V * t) := by
        congr 1
        ring
      rw [hexp, hneg]
      field_simp
      ring
  have hint1 := intervalIntegrable_scaledEinProfile (V := V) hV.le
  have hint2 := intervalIntegrable_scaledEinProfile (V := 2 * V) (by linarith)
  rw [coherentExponent]
  have hsplit : (∫ t in (0 : ℝ)..1, divProfile (coherentProfile (-V) 0) t)
      = 2 * (∫ t in (0 : ℝ)..1, scaledEinProfile V t)
        - ∫ t in (0 : ℝ)..1, scaledEinProfile (2 * V) t := by
    rw [intervalIntegral.integral_congr (g := fun t => 2 * scaledEinProfile V t
      - scaledEinProfile (2 * V) t) (fun t _ => hpoint t)]
    rw [intervalIntegral.integral_sub (hint1.const_mul 2) hint2,
      intervalIntegral.integral_const_mul]
  rw [hsplit, integral_scaledEinProfile hV, integral_scaledEinProfile (by linarith : (0:ℝ) < 2 * V)]
  ring

/-! ## `(13o)`: the exact scale -/

theorem sqrt_eq_exp_half_log_halfNormalExactScale {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = Real.exp (Real.log x / 2) := by
  have h : Real.sqrt (Real.exp (Real.log x)) = Real.exp (Real.log x / 2) := sqrt_exp _
  rwa [Real.exp_log hx] at h

theorem tendsto_coherentExponent_neg_sub_log :
    Tendsto (fun V : ℝ => 2 * coherentExponent (-V) 0 - Real.log V) atTop
      (nhds (Real.eulerMascheroniConstant - Real.log 2)) := by
  have hdouble : Tendsto (fun V : ℝ => ein (2 * V) - Real.log (2 * V)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    have hmul : Tendsto (fun V : ℝ => 2 * V) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_id
    exact tendsto_ein_sub_log.comp hmul
  have hcomb := ((tendsto_ein_sub_log.const_mul 2).sub hdouble).sub
    (tendsto_const_nhds (x := Real.log 2) (f := atTop (α := ℝ)))
  have hval : 2 * Real.eulerMascheroniConstant - Real.eulerMascheroniConstant - Real.log 2
      = Real.eulerMascheroniConstant - Real.log 2 := by ring
  rw [hval] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
  have hlog : Real.log (2 * V) = Real.log 2 + Real.log V :=
    Real.log_mul (by norm_num) (ne_of_gt hV)
  rw [coherentExponent_neg_eq hV, hlog]
  ring

/-- **`(13o)`: the exact half-normal scale.**  `e^{Φ(-V)} ∼ √(e^γ V / 2)`. -/
theorem tendsto_halfNormalExactScale :
    Tendsto (fun V : ℝ => Real.exp (coherentExponent (-V) 0)
        / Real.sqrt (Real.exp Real.eulerMascheroniConstant * V / 2)) atTop (nhds 1) := by
  set D : ℝ → ℝ := fun V => 2 * coherentExponent (-V) 0 - Real.log V with hD
  have hDlim : Tendsto D atTop (nhds (Real.eulerMascheroniConstant - Real.log 2)) :=
    tendsto_coherentExponent_neg_sub_log
  have hshift : Tendsto (fun V : ℝ =>
      (D V - Real.eulerMascheroniConstant + Real.log 2) / 2) atTop (nhds 0) := by
    have h := ((hDlim.sub_const Real.eulerMascheroniConstant).add_const
      (Real.log 2)).div_const 2
    have hval : (Real.eulerMascheroniConstant - Real.log 2 - Real.eulerMascheroniConstant
        + Real.log 2) / 2 = 0 := by ring
    rwa [hval] at h
  have hexp := (Real.continuous_exp.tendsto 0).comp hshift
  rw [Real.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
  have hpos : (0 : ℝ) < Real.exp Real.eulerMascheroniConstant * V / 2 := by positivity
  have hlogval : Real.log (Real.exp Real.eulerMascheroniConstant * V / 2)
      = Real.eulerMascheroniConstant + Real.log V - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) (ne_of_gt hV),
      Real.log_exp]
  rw [Function.comp_apply, sqrt_eq_exp_half_log_halfNormalExactScale hpos, hlogval, ← Real.exp_sub]
  congr 1
  rw [hD]
  simp only []
  ring

end

end RHTower
