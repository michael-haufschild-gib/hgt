/-
# WeldEnvelope — the creation/survival weld (docs 50–52; census weld of doc 52 §10)

Formalizes the ALGEBRAIC STRUCTURE of the census weld: ONE modulus `M θ = |cos θ|`
carries BOTH the creation depth envelope and the survival dip-phase envelope, as
functions of the shared slip `slip p = 2π p²`, differing ONLY by the offset `π/8`:

    creation p = M (slip p),   survival p = M (slip p − π/8).

Scope, stated exactly. What is PROVED here is the algebra of the two defined
envelopes:

* `weld` — both are the one modulus of the shared slip, shifted by `π/8`.
* `creation_zero = 1`, `survival_quarter = 1` — the peaks are at different `p`
  (creation at 0, survival at ¼ where slip = π/8): the census discriminator.
* `creation_quarter = survival_zero = cos(π/8)` — each is only `cos(π/8)` at the
  other's peak.
* `creation_half = 0` vs `survival_half = sin(π/8)` — creation vanishes at the
  half-integer; survival stays finite.
* `survival_suppression : survival 0 / survival ½ = 1 + √2` — the one non-trivial
  evaluation: the census's measured "2.4×" is EXACTLY `cot(π/8) = 1 + √2` (rational
  form `3 + 2√2`).

What is NOT proved here (and must not be read into this): that `slip = 2π p²` and
the offset `π/8` ARE the census's creation/survival constants — that identification
is the labelled conjecture of doc 52 §10, an analytic/empirical claim, not a Lean
theorem. This file only computes the defined functions; it does not derive the
constants from the RS/theta geometry.
-/
import Mathlib

namespace RHTower.Weld

open Real

/-- Shared second-order phase (the "slip", doc 51 §9a): `slip p = 2π p²`. -/
noncomputable def slip (p : ℝ) : ℝ := 2 * Real.pi * p ^ 2

/-- The single weld modulus `M θ = |cos θ|` carried by both envelopes. -/
noncomputable def M (θ : ℝ) : ℝ := |Real.cos θ|

/-- Creation depth envelope: the bare frozen-max modulus (offset 0). -/
noncomputable def creation (p : ℝ) : ℝ := M (slip p)

/-- Survival dip-phase envelope: the modulus shifted by the offset `π/8`. -/
noncomputable def survival (p : ℝ) : ℝ := M (slip p - Real.pi / 8)

/-- **The weld.** Both envelopes are the SAME modulus of the shared slip, differing
by exactly the offset `π/8`. -/
theorem weld (p : ℝ) :
    creation p = M (slip p) ∧ survival p = M (slip p - Real.pi / 8) := ⟨rfl, rfl⟩

theorem slip_zero : slip 0 = 0 := by simp [slip]
theorem slip_quarter : slip (1/4) = Real.pi / 8 := by unfold slip; ring
theorem slip_half : slip (1/2) = Real.pi / 2 := by unfold slip; ring

/-- `cos(π/8) ≥ 0` (reused at the peaks and in the suppression constant). -/
theorem cos_pi_div_eight_nonneg : 0 ≤ Real.cos (Real.pi / 8) := by
  apply Real.cos_nonneg_of_mem_Icc; constructor <;> nlinarith [Real.pi_pos]

/-- `sin(π/8) > 0` (the finite survival value at the half-integer). -/
theorem sin_pi_div_eight_pos : 0 < Real.sin (Real.pi / 8) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> [positivity; (nlinarith [Real.pi_pos])]

/-- Creation peaks (= 1) at `p = 0`. -/
theorem creation_zero : creation 0 = 1 := by
  unfold creation M; rw [slip_zero, Real.cos_zero, abs_one]

/-- Survival peaks (= 1) at `p = 1/4` (where slip = π/8): the peak is displaced from
creation's by exactly the offset. -/
theorem survival_quarter : survival (1/4) = 1 := by
  unfold survival M; rw [slip_quarter, sub_self, Real.cos_zero, abs_one]

/-- At creation's peak, survival is only `cos(π/8) < 1`. -/
theorem survival_zero : survival 0 = Real.cos (Real.pi / 8) := by
  unfold survival M; rw [slip_zero, zero_sub, Real.cos_neg]
  exact abs_of_nonneg cos_pi_div_eight_nonneg

/-- At survival's peak, creation is only `cos(π/8) < 1`. -/
theorem creation_quarter : creation (1/4) = Real.cos (Real.pi / 8) := by
  unfold creation M; rw [slip_quarter]
  exact abs_of_nonneg cos_pi_div_eight_nonneg

/-- Creation VANISHES at `p = 1/2` (total suppression at the half-integer). -/
theorem creation_half : creation (1/2) = 0 := by
  unfold creation M; rw [slip_half, Real.cos_pi_div_two, abs_zero]

/-- Survival at `p = 1/2` is `sin(π/8)` (finite, unlike creation). -/
theorem survival_half : survival (1/2) = Real.sin (Real.pi / 8) := by
  unfold survival M; rw [slip_half, Real.cos_pi_div_two_sub]
  exact abs_of_nonneg (le_of_lt sin_pi_div_eight_pos)

/-- `cos²(π/8) = (2 + √2)/4` (half-angle). -/
theorem cos_sq_pi_div_eight : Real.cos (Real.pi / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  have h := Real.cos_two_mul (Real.pi / 8)
  rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four] at h
  linarith

/-- `sin²(π/8) = (2 − √2)/4` (half-angle). -/
theorem sin_sq_pi_div_eight : Real.sin (Real.pi / 8) ^ 2 = (2 - Real.sqrt 2) / 4 := by
  have hp := Real.sin_sq_add_cos_sq (Real.pi / 8)
  rw [cos_sq_pi_div_eight] at hp; linarith

/-- **The exact suppression (rational form).** `(survival 0 / survival ½)² = 3 + 2√2`. -/
theorem survival_suppression_sq :
    (survival 0 / survival (1/2)) ^ 2 = 3 + 2 * Real.sqrt 2 := by
  rw [survival_zero, survival_half, div_pow, cos_sq_pi_div_eight, sin_sq_pi_div_eight]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlt : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2, h2]
  have hne : (2 - Real.sqrt 2) / 4 ≠ 0 := by
    have : (0:ℝ) < (2 - Real.sqrt 2) / 4 := by linarith
    exact ne_of_gt this
  rw [div_eq_iff hne]; nlinarith [h2]

/-- **The exact suppression.** `survival 0 / survival ½ = 1 + √2 = cot(π/8)` — the
census's measured "2.4×" is exactly `1 + √2`. -/
theorem survival_suppression :
    survival 0 / survival (1/2) = 1 + Real.sqrt 2 := by
  have hsq := survival_suppression_sq
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrhs : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by nlinarith [h2]
  have hx : 0 ≤ survival 0 / survival (1/2) := by
    rw [survival_zero, survival_half]
    exact div_nonneg cos_pi_div_eight_nonneg (le_of_lt sin_pi_div_eight_pos)
  have hy : (0:ℝ) ≤ 1 + Real.sqrt 2 := by positivity
  rw [← Real.sqrt_sq hx, hsq, ← hrhs, Real.sqrt_sq hy]

/-!
### The offset is half the Gaussian/Fresnel phase (built, not posited)

`e^{iπ/4}` is not an arbitrary constant: it is the phase of the oscillatory
Gaussian (Fresnel) integral `∫ e^{ix²}dx`. That integrand is NOT Lebesgue/Bochner
integrable (`|e^{ix²}| = 1`), so we build the value as the regularized limit
`∫ e^{-(ε-i)x²}dx` as `ε→0⁺` — each `ε>0` integral is a genuine Gaussian (Mathlib's
`integral_gaussian_complex`, `Re b > 0`), and the limit is `√π·e^{iπ/4}`. Hence the
survival offset `π/8` equals `½·arg` of the ACTUAL Fresnel/Gaussian integral value —
the metaplectic half-turn, tied to a real analytic object.

NOT proved here (do not read it in): that this phase is the constant of the census
survival envelope. That link is the Riemann–Siegel-remainder / metaplectic derivation
plus the empirical census fit — the labelled conjecture of doc 52 §10, outside Lean.
-/
section Fresnel
open Complex MeasureTheory Filter Topology

/-- The regularized Fresnel / oscillatory-Gaussian value `(π/(-i))^{1/2}`. -/
noncomputable def fresnelValue : ℂ := ((Real.pi : ℂ) / (-Complex.I)) ^ (1/2 : ℂ)

/-- `fresnelValue = √π · e^{iπ/4}`: the phase of the Gaussian/Fresnel integral is
exactly `e^{iπ/4}`. -/
theorem fresnelValue_eq :
    fresnelValue = (Real.sqrt Real.pi : ℂ) * Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) := by
  unfold fresnelValue
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hstep : (Real.pi : ℂ) / (-Complex.I) = (Real.pi : ℂ) * Complex.I := by
    rw [div_eq_mul_inv, inv_neg, Complex.inv_I, neg_neg]
  rw [hstep]
  have hne : (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero hpi Complex.I_ne_zero
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log ((Real.pi : ℂ) * Complex.I)
      = (Real.log Real.pi : ℂ) + (Real.pi / 2 : ℂ) * Complex.I := by
    rw [Complex.log_ofReal_mul Real.pi_pos Complex.I_ne_zero, Complex.log_I]
  rw [hlog,
    show ((Real.log Real.pi : ℂ) + (Real.pi / 2 : ℂ) * Complex.I) * (1/2 : ℂ)
        = ((Real.log Real.pi / 2 : ℝ) : ℂ) + ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos]; ring_nf

/-- Hence `arg` of the Fresnel/Gaussian value is `π/4`. -/
theorem fresnelValue_arg : Complex.arg fresnelValue = Real.pi / 4 := by
  rw [fresnelValue_eq, Complex.arg_real_mul _ (Real.sqrt_pos.mpr Real.pi_pos),
    Complex.arg_exp_mul_I, toIocMod_eq_self]
  constructor <;> nlinarith [Real.pi_pos]

/-- **The Fresnel integral, built by regularization.** The oscillatory Gaussian
`∫ e^{-(ε-i)x²}dx` (Bochner-integrable for `ε>0`) converges as `ε→0⁺` to
`fresnelValue = √π·e^{iπ/4}` — the direct construction of the Fresnel integral from
Mathlib's `Re b > 0` Gaussian. -/
theorem fresnel_integral_tendsto :
    Filter.Tendsto (fun ε : ℝ => ∫ x : ℝ, Complex.exp (-((ε : ℂ) - Complex.I) * (x : ℂ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 fresnelValue) := by
  have heq : (fun ε : ℝ => ∫ x : ℝ, Complex.exp (-((ε : ℂ) - Complex.I) * (x : ℂ) ^ 2))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1/2 : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hb : 0 < ((ε : ℂ) - Complex.I).re := by
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero]; exact hε
    exact integral_gaussian_complex hb
  rw [tendsto_congr' heq]
  have hinner : ContinuousAt (fun b : ℂ => (Real.pi : ℂ) / b) (-Complex.I) :=
    continuousAt_const.div continuousAt_id (neg_ne_zero.mpr Complex.I_ne_zero)
  have houter : ContinuousAt (fun z : ℂ => z ^ (1/2 : ℂ)) ((Real.pi : ℂ) / (-Complex.I)) := by
    apply continuousAt_cpow_const; right
    have hstep : (Real.pi : ℂ) / (-Complex.I) = (Real.pi : ℂ) * Complex.I := by
      rw [div_eq_mul_inv, inv_neg, Complex.inv_I, neg_neg]
    rw [hstep]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    exact Real.pi_ne_zero
  have hcont : ContinuousAt (fun b : ℂ => ((Real.pi : ℂ) / b) ^ (1/2 : ℂ)) (-Complex.I) :=
    houter.comp hinner
  have hmap : Filter.Tendsto (fun ε : ℝ => (ε : ℂ) - Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 (-Complex.I)) := by
    have h0 : Filter.Tendsto (fun ε : ℝ => (ε : ℂ) - Complex.I) (𝓝 (0 : ℝ)) (𝓝 (-Complex.I)) := by
      have hc : Continuous (fun ε : ℝ => (ε : ℂ) - Complex.I) := by fun_prop
      have := hc.tendsto 0; simpa using this
    exact h0.mono_left nhdsWithin_le_nhds
  have := hcont.tendsto.comp hmap
  simpa [fresnelValue, Function.comp] using this

/-- **The offset, tied to the Gaussian phase.** The survival envelope's offset is
`½·arg(fresnelValue)` — half the argument of the ACTUAL Fresnel/Gaussian integral,
the metaplectic half-turn of the 2-cover (`½·(π/4) = π/8`). -/
theorem survival_eq_half_arg_fresnelValue (p : ℝ) :
    survival p = M (slip p - (1/2) * Complex.arg fresnelValue) := by
  unfold survival; rw [fresnelValue_arg]; congr 1; ring

end Fresnel

/-!
### The theta functional equation carries the same Gaussian phase (bridge, exact scope)

Mathlib's Jacobi theta functional equation
`jacobiTheta (S•τ) = (-i·τ)^{1/2}·jacobiTheta τ` (`jacobiTheta_S_smul`) has factor
`(-i·τ)^{1/2}`. For `τ ∈ ℍ`, `-i·τ = Im τ − i·Re τ` has `Re > 0`, so the factor's
argument is `½·arg(-iτ) ∈ (-π/4, π/4)`, reaching `±π/4` only at the real cusps
`τ → ±1` — the Gauss-sum / Landsberg–Schaar limit. At the cusp `τ = 1` the factor is
`(-i)^{1/2} = e^{-iπ/4}`, argument `-π/4 = -arg(fresnelValue)`: the SAME Gaussian
phase `π/4` as the Fresnel integral. So the modular theta functional equation and the
Fresnel integral are one object — Gaussian self-duality, the source of the RS `e^{iπ/4}`.

Honest boundary (this does NOT reach the RS constant). The RS remainder `−1/16 ⟺ π/8`
is HALF the shared `π/4` — the ℤ₂-Kummer 2-cover square-root — and formalizing that
halving is just `π/8 = ½·π/4` (no content; doc 52 §12). The exact `−1/16` needs the
quadratic Gauss sum at the half-integer (Landsberg–Schaar reciprocity), the classical
residual, NOT done here; the census identification stays the labelled conjecture
(doc 52 §10). What IS banked: theta factor and Fresnel integral share the phase `π/4`.
-/
section ThetaBridge
open Complex

/-- Mathlib's Jacobi theta functional equation, re-exposed: the S-transformation
factor is `(-i·τ)^{1/2}`. -/
theorem theta_functional_equation (τ : UpperHalfPlane) :
    jacobiTheta ↑(ModularGroup.S • τ) = (-Complex.I * ↑τ) ^ (1/2 : ℂ) * jacobiTheta ↑τ :=
  jacobiTheta_S_smul τ

/-- The theta S-factor `(-i·τ)^{1/2}` at the real cusp `τ = 1` is `e^{-iπ/4}`. -/
theorem thetaSFactor_cusp :
    (-Complex.I) ^ (1/2 : ℂ) = Complex.exp ((↑(-(Real.pi / 4)) : ℂ) * Complex.I) := by
  have harg : Complex.I.arg ≠ Real.pi := by rw [Complex.arg_I]; nlinarith [Real.pi_pos]
  rw [Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)]
  have hlog : Complex.log (-Complex.I) = -((Real.pi : ℂ) / 2 * Complex.I) := by
    rw [show (-Complex.I) = Complex.I⁻¹ from Complex.inv_I.symm,
      Complex.log_inv Complex.I harg, Complex.log_I]
  rw [hlog, show -((Real.pi : ℂ) / 2 * Complex.I) * (1/2) = (↑(-(Real.pi / 4)) : ℂ) * Complex.I by
    push_cast; ring]

/-- Its argument is `-π/4` — the Gauss-sum / Fresnel phase. -/
theorem thetaSFactor_cusp_arg : Complex.arg ((-Complex.I) ^ (1/2 : ℂ)) = -(Real.pi / 4) := by
  rw [thetaSFactor_cusp, Complex.arg_exp_mul_I, toIocMod_eq_self]
  constructor <;> nlinarith [Real.pi_pos]

/-- **The bridge.** The theta functional-equation factor at the cusp and the Fresnel
integral carry the SAME Gaussian phase: `arg(theta S-factor) = -arg(fresnelValue)`
(both `π/4` in magnitude). This is the shared Gaussian self-duality behind the RS
`e^{iπ/4}`. It does NOT reach `−1/16 = π/8` (the 2-cover halving + Gauss-sum
reciprocity; see the note above). -/
theorem thetaSFactor_arg_eq_neg_fresnel :
    Complex.arg ((-Complex.I) ^ (1/2 : ℂ)) = -Complex.arg fresnelValue := by
  rw [thetaSFactor_cusp_arg, fresnelValue_arg]

end ThetaBridge

end RHTower.Weld
