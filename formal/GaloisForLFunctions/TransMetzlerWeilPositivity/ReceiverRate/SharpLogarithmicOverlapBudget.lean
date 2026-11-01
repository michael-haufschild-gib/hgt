import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheLogarithmicFourierFloorHasAPowerLogBudget
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Sharp conversion from a logarithmic spectral budget to overlap

Splitting at `c² = L` and `c = L` removes the factor four from the critical
multiple: the budget `exp(Bc/log²c) ≤ (log N)^α` holds uniformly up to
`(α/B) L(log L)²`, where `L = loglog N`.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

/-- The intermediate range costs only `4B/log²L`; the large range keeps the exact coefficient. -/
theorem logarithmicExponent_le_of_sharp_overlap_bound {B α L c : ℝ}
    (hB : 0 < B) (hα : 0 < α) (hL : Real.exp 1 ≤ L)
    (hBL : B ^ 2 ≤ α ^ 2 * L) (hlogL : 4 * B ≤ α * Real.log L ^ 2)
    (hc : Real.exp 1 ≤ c) (hcup : c ≤ (α / B) * L * Real.log L ^ 2) :
    B * c / Real.log c ^ 2 ≤ α * L := by
  have hL0 := (Real.exp_pos 1).trans_le hL
  have hc0 := (Real.exp_pos 1).trans_le hc
  have hlc : 1 ≤ Real.log c := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hc
  have hlL : 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hL
  have hden : 0 < Real.log c ^ 2 := sq_pos_of_pos (zero_lt_one.trans_le hlc)
  by_cases hsmall : c ^ 2 ≤ L
  · have hαc := mul_le_mul_of_nonneg_left hsmall (sq_nonneg α)
    have hscaled : α * (B * c) ≤ α * (α * L) := by
      nlinarith only [sq_nonneg (B - α * c), hBL, hαc]
    have hBc : B * c ≤ α * L := (mul_le_mul_iff_right₀ hα).mp hscaled
    exact (div_le_self (mul_nonneg hB.le hc0.le) (one_le_pow₀ hlc)).trans hBc
  · by_cases hmid : c ≤ L
    · have hlog : Real.log L ≤ 2 * Real.log c := by
        have hh := Real.log_le_log hL0 (le_of_lt (lt_of_not_ge hsmall))
        simpa only [Real.log_pow, Nat.cast_ofNat] using hh
      have hsq : Real.log L ^ 2 ≤ 4 * Real.log c ^ 2 := by
        calc
          Real.log L ^ 2 ≤ (2 * Real.log c) ^ 2 :=
            pow_le_pow_left₀ (zero_lt_one.trans_le hlL).le hlog 2
          _ = 4 * Real.log c ^ 2 := by ring
      have hBden : B ≤ α * Real.log c ^ 2 := by
        have hh := mul_le_mul_of_nonneg_left hsq hα.le
        nlinarith only [hlogL, hh]
      rw [div_le_iff₀ hden]
      exact (mul_le_mul_of_nonneg_left hmid hB.le).trans
        (by nlinarith only [mul_le_mul_of_nonneg_right hBden hL0.le])
    · have hlog := Real.log_le_log hL0 (le_of_lt (lt_of_not_ge hmid))
      have hsq := pow_le_pow_left₀ (zero_lt_one.trans_le hlL).le hlog 2
      have hbound := mul_le_mul_of_nonneg_left hsq
        (show 0 ≤ (α / B) * L by positivity)
      rw [div_le_iff₀ hden]
      calc
        B * c ≤ B * ((α / B) * L * Real.log c ^ 2) :=
          mul_le_mul_of_nonneg_left (hcup.trans hbound) hB.le
        _ = α * L * Real.log c ^ 2 := by field_simp [hB.ne']

/-- The full coefficient `α/B` is admissible, uniformly over all smaller overlaps. -/
theorem eventually_logarithmicSpectralControl_le_log_rpow_sharp {B α : ℝ}
    (hB : 0 < B) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, Real.exp 1 ≤ c →
      c ≤ (α / B) * dcScale N →
        logarithmicSpectralControl B c ≤ Real.log (N : ℝ) ^ α := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL := Real.tendsto_log_atTop.comp hlog
  have hLLL := Real.tendsto_log_atTop.comp hLL
  filter_upwards [hLL.eventually_ge_atTop (Real.exp 1),
    hLL.eventually_ge_atTop (B ^ 2 / α ^ 2),
    hLLL.eventually_ge_atTop (max 1 (4 * B / α)), hlog.eventually_gt_atTop 0]
    with N hL hBL hlogL hlogN
  intro c hc hcup
  have hBL' : B ^ 2 ≤ α ^ 2 * Real.log (Real.log (N : ℝ)) := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hα)).mp hBL
    simpa only [mul_comm] using hh
  have hlogL' : 4 * B ≤ α * Real.log (Real.log (Real.log (N : ℝ))) ^ 2 := by
    have h1 := (le_max_left _ _).trans hlogL
    have h2 := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hlogL)
    nlinarith only [h2, mul_le_mul_of_nonneg_left
      (show Real.log (Real.log (Real.log (N : ℝ))) ≤
        Real.log (Real.log (Real.log (N : ℝ))) ^ 2 by nlinarith only [h1]) hα.le]
  have he := logarithmicExponent_le_of_sharp_overlap_bound hB hα hL hBL' hlogL' hc
    (by simpa only [dcScale, mul_assoc] using hcup)
  unfold logarithmicSpectralControl
  rw [Real.rpow_def_of_pos hlogN]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using he

private theorem tendsto_log_critical_schedule_ratio {K : ℝ} (hK : 0 < K) :
    Tendsto (fun L : ℝ => Real.log (K * L * Real.log L ^ 2) / Real.log L)
      atTop (𝓝 1) := by
  have hsmall : Tendsto (fun L : ℝ => Real.log (Real.log L) / Real.log L)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (1 : ℝ) zero_lt_one).tendsto_div_nhds_zero.comp
        Real.tendsto_log_atTop)
  have hconst := Real.tendsto_log_atTop.const_div_atTop (Real.log K)
  have hlim : Tendsto (fun L : ℝ => Real.log K / Real.log L + 1 +
      2 * (Real.log (Real.log L) / Real.log L)) atTop (𝓝 1) := by
    simpa only [zero_add, mul_zero, add_zero] using
      (hconst.add tendsto_const_nhds).add (hsmall.const_mul 2)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  have hL0 := zero_lt_one.trans hL
  have hl0 := Real.log_pos hL
  rw [Real.log_mul (mul_pos hK hL0).ne' (pow_pos hl0 2).ne',
    Real.log_mul hK.ne' hL0.ne', Real.log_pow]
  push_cast
  field_simp [hl0.ne']

/-- At a fixed multiple, the logarithmic spectral exponent has exact leading coefficient `BK`. -/
theorem tendsto_logarithmicExponent_critical_ratio (B : ℝ) {K : ℝ} (hK : 0 < K) :
    Tendsto (fun N : ℕ =>
      (B * (K * dcScale N) / Real.log (K * dcScale N) ^ 2) /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 (B * K)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL := Real.tendsto_log_atTop.comp hlog
  have hr := (tendsto_log_critical_schedule_ratio hK).comp hLL
  have hlim : Tendsto (fun N : ℕ => (B * K) /
      (Real.log (K * Real.log (Real.log (N : ℝ)) *
        Real.log (Real.log (Real.log (N : ℝ))) ^ 2) /
          Real.log (Real.log (Real.log (N : ℝ)))) ^ 2) atTop (𝓝 (B * K)) := by
    simpa only [one_pow, div_one, Function.comp_def] using
      tendsto_const_nhds.div (hr.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  apply hlim.congr'
  filter_upwards [hLL.eventually_gt_atTop (1 : ℝ)] with N hL
  have hL0 := zero_lt_one.trans hL
  have hl0 := Real.log_pos hL
  dsimp only [dcScale]
  rw [div_pow, div_div]
  field_simp [hL0.ne', hl0.ne']
  <;> ring

/-- A larger coefficient fails the same absolute spectral budget eventually. -/
theorem eventually_log_rpow_lt_logarithmicSpectralControl {B α K : ℝ}
    (hB : 0 < B) (hK : 0 < K) (hlarge : α / B < K) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ α < logarithmicSpectralControl B (K * dcScale N) := by
  have hαBK : α < B * K := by
    have hh := (div_lt_iff₀ hB).mp hlarge
    simpa only [mul_comm] using hh
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [(tendsto_logarithmicExponent_critical_ratio B hK).eventually_const_lt hαBK,
    (Real.tendsto_log_atTop.comp hlog).eventually_gt_atTop 0,
    hlog.eventually_gt_atTop 0] with N hratio hLL hL
  have hh := (lt_div_iff₀ hLL).mp hratio
  unfold logarithmicSpectralControl
  rw [Real.rpow_def_of_pos hL]
  apply Real.exp_lt_exp.mpr
  simpa only [mul_comm] using hh

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.logarithmicExponent_le_of_sharp_overlap_bound
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_logarithmicSpectralControl_le_log_rpow_sharp
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.tendsto_logarithmicExponent_critical_ratio
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_log_rpow_lt_logarithmicSpectralControl
