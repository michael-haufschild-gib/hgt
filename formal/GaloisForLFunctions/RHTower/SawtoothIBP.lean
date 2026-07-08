/-
Per-interval Euler–Maclaurin integration by parts for the sawtooth.

On a unit interval `[m, m+1]` the local second Bernoulli half `Q(x) = ((x−m)² − (x−m))/2` vanishes at
both integer endpoints, so integrating the centred sawtooth `x−m−½ = Q'(x)` against a smooth `x^(−s−1)`
by parts leaves **no boundary term**:

  `∫_m^{m+1} (x−m−½)·x^(−s−1) dx = −∫_m^{m+1} Q(x)·(−s−1)x^(−s−2) dx`.

Summed over `m`, this lifts the conditionally-convergent sawtooth (`B₁`) to the continuous, absolutely
Fourier-summable `B₂` — the step that makes the reflected-block mode expansion legitimate.  The helper
`hasDerivAt_ofReal_cpow_const` supplies the derivative of `x ↦ (↑x)^c`.
-/
import Mathlib

open Complex intervalIntegral MeasureTheory

noncomputable section

namespace RHTower

private theorem hasDerivAt_ofReal_cpow_const {c : ℂ} {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ c) (c * (x : ℂ) ^ (c - 1)) x := by
  have hb : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have hmem : (x : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hx)
  have hout : HasDerivAt (fun z : ℂ => z ^ c) (c * (x : ℂ) ^ (c - 1) * 1) (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).cpow_const hmem
  simpa using hout.comp x hb

/-- Per-interval sawtooth integration by parts: the local `B₂/2` vanishes at both integer endpoints,
so the boundary term is zero and `∫_m^{m+1} (x−m−½)·x^{−s−1} = −∫_m^{m+1} Q(x)·(−s−1)x^{−s−2}` with
`Q = ((x−m)²−(x−m))/2`. -/
theorem sawtooth_ibp_unit {m : ℕ} (hm : 1 ≤ m) (s : ℂ) :
    (∫ x in (m : ℝ)..(m + 1), (((x - m - 1 / 2 : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1))
      = -∫ x in (m : ℝ)..(m + 1),
          ((((x - m) ^ 2 - (x - m)) / 2 : ℝ) : ℂ) * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) := by
  set U : ℝ → ℂ := fun y => (((y - m) ^ 2 - (y - m)) / 2 : ℝ) with hU
  set U' : ℝ → ℂ := fun y => ((y - m - 1 / 2 : ℝ)) with hU'
  set V : ℝ → ℂ := fun y => (y : ℂ) ^ (-s - 1) with hV
  set V' : ℝ → ℂ := fun y => (-s - 1) * (y : ℂ) ^ (-s - 1 - 1) with hV'
  have hmb : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hpos : ∀ y ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1), 0 < y := by
    intro y hy; rw [Set.uIcc_of_le hmb] at hy
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith [hy.1]
  have hUderiv : ∀ y ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1), HasDerivAt U (U' y) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => z - (m : ℝ)) 1 y := (hasDerivAt_id y).sub_const _
    have h2 := ((h1.pow 2).sub h1).div_const 2
    have h3 := h2.ofReal_comp
    rw [hU, hU']
    convert h3 using 1
    push_cast; ring
  have hVderiv : ∀ y ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1), HasDerivAt V (V' y) y := by
    intro y hy
    rw [hV, hV']
    exact hasDerivAt_ofReal_cpow_const (hpos y hy)
  have hUcont : ContinuousOn U (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    rw [hU]; fun_prop
  have hVcont : ContinuousOn V (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    apply ContinuousOn.cpow_const (by fun_prop) ?_ |>.congr (fun y _ => rfl)
    intro y hy; exact Or.inl (by simpa using hpos y hy)
  have hU'cont : ContinuousOn U' (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by rw [hU']; fun_prop
  have hV'cont : ContinuousOn V' (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    apply continuousOn_const.mul
    apply ContinuousOn.cpow_const (by fun_prop) ?_ |>.congr (fun y _ => rfl)
    intro y hy; exact Or.inl (by simpa using hpos y hy)
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hUderiv hVderiv
    hU'cont.intervalIntegrable hV'cont.intervalIntegrable
  have hUa : U (m : ℝ) = 0 := by rw [hU]; push_cast; ring
  have hUb : U ((m : ℝ) + 1) = 0 := by rw [hU]; push_cast; ring
  rw [hUb, hUa, zero_mul, zero_mul, sub_zero] at hibp
  have hsplit : (∫ x in (m:ℝ)..(m+1), U' x * V x + U x * V' x)
      = (∫ x in (m:ℝ)..(m+1), U' x * V x) + ∫ x in (m:ℝ)..(m+1), U x * V' x :=
    intervalIntegral.integral_add (hU'cont.intervalIntegrable.mul_continuousOn hVcont)
      (hUcont.intervalIntegrable.mul_continuousOn hV'cont)
  rw [hsplit] at hibp
  show (∫ x in (m:ℝ)..((m:ℝ)+1), U' x * V x) = -∫ x in (m:ℝ)..((m:ℝ)+1), U x * V' x
  linear_combination hibp

end RHTower
