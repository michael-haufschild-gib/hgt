import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheZeroFreeLogarithmicProfileKeepsAQuantitativeReserve

/-!
# The inverse logarithmic Fourier floor below critical overlap

The exponential control `exp(Bc/log²c)` is a small power of `log N` when
`c ≤ ε·loglog N·(logloglog N)²`. An elementary split at `c² = loglog N`
gives the explicit choice `ε = α/(4B)` for exponent `α`.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

/-- Exponential control for the reciprocal logarithmic Fourier floors. -/
def logarithmicSpectralControl (B c : ℝ) : ℝ :=
  Real.exp (B * c / Real.log c ^ 2)

/-- Below the critical overlap, the logarithmic exponent is at most `αL`.
The two cases `c² ≤ L` and `L ≤ c²` avoid differentiating the logarithmic ratio. -/
theorem logarithmicExponent_le_of_overlap_bound {B α L c : ℝ}
    (hB : 0 < B) (hα : 0 < α) (hL : Real.exp 1 ≤ L)
    (hBL : B ^ 2 ≤ α ^ 2 * L) (hc : Real.exp 1 ≤ c)
    (hcup : c ≤ (α / (4 * B)) * L * Real.log L ^ 2) :
    B * c / Real.log c ^ 2 ≤ α * L := by
  have hL0 := (Real.exp_pos 1).trans_le hL
  have hc0 := (Real.exp_pos 1).trans_le hc
  have hlc : 1 ≤ Real.log c := by
    have h := Real.log_le_log (Real.exp_pos 1) hc
    simpa only [Real.log_exp] using h
  have hlL : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using h
  have hden : 0 < Real.log c ^ 2 := by positivity
  rcases le_total (c ^ 2) L with hsmall | hlarge
  · have hαc := mul_le_mul_of_nonneg_left hsmall (sq_nonneg α)
    have hscaled : α * (B * c) ≤ α * (α * L) := by
      nlinarith only [sq_nonneg (B - α * c), hBL, hαc]
    have hBc : B * c ≤ α * L := (mul_le_mul_iff_right₀ hα).mp hscaled
    exact (div_le_self (mul_nonneg hB.le hc0.le) (one_le_pow₀ hlc)).trans hBc
  · have hlog : Real.log L ≤ 2 * Real.log c := by
      have h := Real.log_le_log hL0 hlarge
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hsquare : Real.log L ^ 2 ≤ 4 * Real.log c ^ 2 := by
      nlinarith only [hlog, hlc, hlL]
    have hscale := mul_le_mul_of_nonneg_left hsquare
      (show 0 ≤ (α / (4 * B)) * L by positivity)
    have hcb : c ≤ (α / (4 * B)) * L * (4 * Real.log c ^ 2) := hcup.trans hscale
    rw [div_le_iff₀ hden]
    calc
      B * c ≤ B * ((α / (4 * B)) * L * (4 * Real.log c ^ 2)) :=
        mul_le_mul_of_nonneg_left hcb hB.le
      _ = α * L * Real.log c ^ 2 := by field_simp [hB.ne']

/-- Every fixed positive power budget is available at a sufficiently small critical multiple. -/
theorem eventually_logarithmicSpectralControl_le_log_rpow {B α : ℝ}
    (hB : 0 < B) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, Real.exp 1 ≤ c →
      c ≤ (α / (4 * B)) * dcScale N →
        logarithmicSpectralControl B c ≤ Real.log (N : ℝ) ^ α := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [hloglog.eventually_ge_atTop (Real.exp 1),
    hloglog.eventually_ge_atTop (B ^ 2 / α ^ 2), hlog.eventually_gt_atTop 0]
    with N hL hBL hlogN
  intro c hc hcup
  have hBL' : B ^ 2 ≤ α ^ 2 * Real.log (Real.log (N : ℝ)) := by
    have h := (div_le_iff₀ (sq_pos_of_pos hα)).mp hBL
    simpa only [mul_comm (Real.log (Real.log (N : ℝ)))] using h
  have hcup' : c ≤ (α / (4 * B)) * Real.log (Real.log (N : ℝ)) *
      Real.log (Real.log (Real.log (N : ℝ))) ^ 2 := by
    simpa only [dcScale, mul_assoc] using hcup
  have he := Real.exp_le_exp.mpr
    (logarithmicExponent_le_of_overlap_bound hB hα hL hBL' hc hcup')
  change logarithmicSpectralControl B c ≤ _ at he
  rw [Real.rpow_def_of_pos hlogN]
  exact he.trans_eq (by congr 1; ring)

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.logarithmicExponent_le_of_overlap_bound
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_logarithmicSpectralControl_le_log_rpow
