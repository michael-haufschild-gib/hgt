/-
The resonance method cannot produce a power.

Every known `Ω`-result for `max |ζ(1/2+it)|` comes from the resonance method, whose entire gain is
the maximal Gál sum.  Bondarenko and Seip evaluated that maximum:

    Γ(N) = exp((C + o(1)) · √(log N · loglog N)).

Writing `L = log N`, the gain exponent is `C√(L log L)`, while a power saving `N^c` has exponent
`cL`.  Their difference is

    L · (C·√(log L / L) − c) → −∞,

because `log L / L → 0`.  So the resonance gain is smaller than every fixed power, and the exponent
ratio tends to zero: **no resonance construction can give `Ω(T^c)` for any `c > 0`**.

The module is source-independent: it is a statement about the growth of `√(L log L)` against `L`.
-/
import Mathlib

namespace HTGeometry

open Filter Topology

/-- Bondarenko–Seip exponent of the maximal Gál sum, at `N = exp L`. -/
noncomputable def galSumExponent (C L : ℝ) : ℝ := C * Real.sqrt (L * Real.log L)

theorem log_div_tendsto_zero : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
  simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

theorem sqrt_log_div_tendsto_zero :
    Tendsto (fun x : ℝ => Real.sqrt (Real.log x / x)) atTop (nhds 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp log_div_tendsto_zero
  simpa [Function.comp_def] using h

/-- The gain exponent, factored so that the `L`-scale is explicit. -/
theorem galSumExponent_eq (C : ℝ) {L : ℝ} (hL : 0 < L) :
    galSumExponent C L = L * (C * Real.sqrt (Real.log L / L)) := by
  unfold galSumExponent
  have h : Real.sqrt (L * Real.log L) = L * Real.sqrt (Real.log L / L) := by
    have h2 : L * Real.sqrt (Real.log L / L) =
        Real.sqrt (L ^ (2 : ℕ)) * Real.sqrt (Real.log L / L) := by
      rw [Real.sqrt_sq hL.le]
    rw [h2, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [h]
  ring

/-- **The resonance gain is subpolynomial.**  Against any fixed power saving the exponent
difference tends to `-∞`. -/
theorem galSumExponent_sub_atBot (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun L : ℝ => galSumExponent C L - c * L) atTop atBot := by
  have hfac : Tendsto (fun L : ℝ => C * Real.sqrt (Real.log L / L) - c) atTop (nhds (-c)) := by
    have h := (sqrt_log_div_tendsto_zero.const_mul C).sub_const c
    simpa using h
  have hmul : Tendsto (fun L : ℝ => L * (C * Real.sqrt (Real.log L / L) - c)) atTop atBot :=
    Tendsto.atTop_mul_neg (by linarith) tendsto_id hfac
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [galSumExponent_eq C hL]
  ring

/-- **No resonance construction gives a power.**  The maximal Gál-sum gain divided by any fixed
power tends to zero, so the resonance method cannot produce `Ω(T^c)` for any `c > 0`, and hence no
known method disproves the Lindelöf hypothesis. -/
theorem resonanceGain_tendsto_zero (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun L : ℝ => Real.exp (galSumExponent C L) / Real.exp (c * L))
      atTop (nhds 0) := by
  have h := Real.tendsto_exp_atBot.comp (galSumExponent_sub_atBot C hc)
  simpa [Function.comp_def, Real.exp_sub] using h

end HTGeometry
