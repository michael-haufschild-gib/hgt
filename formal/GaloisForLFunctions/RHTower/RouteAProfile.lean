/-
Route A spine (doc 55 §§6–7): the matched covariance profile and the Langevin
intensity — the computable half, machine-checked.

Route A closes (CR-density) through the GAF σ-profile: the matched partial
sum's covariance profile has the limit shape K∞(u) = (1 − e^{−2u})/(2u) in the
rescaled coordinate u = (σ − ½)·log N, the near-line zero intensity is
4π·ρ(u) = (log K∞)″(u), and the integrated rate is the Langevin function
ε(c) = (coth c − 1/c)/4π.  This module proves the exact identities:

* `coth_sub_one` — coth u − 1 = 2e^{−2u}/(1 − e^{−2u}): the Bose/Todd kernel
  form (doc 55 §7's common-ancestor mechanism).
* `log_matchedProfile_hasDerivAt` — (log K∞)′(u) = langevin u − 1: the
  doc 55 §7.1 closed form φ(u) = coth u − 1/u − 1, machine-checked.
* `langevin_hasDerivAt` + `langevin_deriv_eq_intensity` — L′(u) =
  1/u² − 1/sinh²u = 4π·matchedIntensity u: the intensity is the second
  log-derivative of the profile.
* `matchedIntensity_nonneg` — ρ ≥ 0 (sinh u ≥ u): the intensity is a genuine
  point-process intensity.

The open core (doc 55 §6.4, Steinhaus-vs-Gaussian local universality) is
typed as the explicit interface `RouteAUniversality` — the same discipline as
the rest of MID-central: prove the computable half, interface-type the open
half.
-/
import Mathlib

namespace RHTower

open Real

/-- Hyperbolic cotangent. -/
noncomputable def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

/-- The matched covariance limit profile `K∞(u) = (1 − e^{−2u})/(2u)`
(doc 55 §7: `K(½ + u/log N)/log N → K∞(u)` for the matched truncation). -/
noncomputable def matchedProfile (u : ℝ) : ℝ := (1 - Real.exp (-2 * u)) / (2 * u)

/-- The Langevin function `L(c) = coth c − 1/c`; Route A's rate is
`ε(c) = L(c)/4π`. -/
noncomputable def langevin (c : ℝ) : ℝ := coth c - 1 / c

/-- The rescaled near-line GAF zero intensity
`ρ(u) = (1/u² − 1/sinh²u)/(4π) = (log K∞)″(u)/(4π)`. -/
noncomputable def matchedIntensity (u : ℝ) : ℝ :=
  (1 / u ^ 2 - 1 / Real.sinh u ^ 2) / (4 * Real.pi)

theorem exp_neg_two_mul_lt_one {u : ℝ} (hu : 0 < u) : Real.exp (-2 * u) < 1 := by
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem matchedProfile_pos {u : ℝ} (hu : 0 < u) : 0 < matchedProfile u := by
  unfold matchedProfile
  have h1 : Real.exp (-2 * u) < 1 := exp_neg_two_mul_lt_one hu
  positivity

/-- **The Bose/Todd kernel form of coth**: `coth u − 1 = 2e^{−2u}/(1 − e^{−2u})`. -/
theorem coth_sub_one {u : ℝ} (hu : 0 < u) :
    coth u - 1 = 2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) := by
  have hs : (0 : ℝ) < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have h1 : (0 : ℝ) < 1 - Real.exp (-2 * u) := by
    have := exp_neg_two_mul_lt_one hu
    linarith
  have hstep : coth u - 1 = Real.exp (-u) / Real.sinh u := by
    unfold coth
    rw [eq_div_iff hs.ne', sub_mul, div_mul_cancel₀ _ hs.ne', one_mul,
      ← Real.cosh_sub_sinh]
  rw [hstep, div_eq_div_iff hs.ne' h1.ne', Real.sinh_eq]
  have e2 : Real.exp (-2 * u) * Real.exp u = Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination -e2

/-- **The doc 55 §7.1 closed form, machine-checked:**
`(log K∞)′(u) = coth u − 1/u − 1 = langevin u − 1`. -/
theorem log_matchedProfile_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => Real.log (matchedProfile v)) (langevin u - 1) u := by
  have hfne : (1 : ℝ) - Real.exp (-2 * u) ≠ 0 := by
    have := exp_neg_two_mul_lt_one hu
    linarith
  have hf : HasDerivAt (fun v : ℝ => 1 - Real.exp (-2 * v))
      (0 - Real.exp (-2 * u) * (-2 * 1)) u :=
    (hasDerivAt_const u (1 : ℝ)).sub (((hasDerivAt_id u).const_mul (-2 : ℝ)).exp)
  have hlogf := hf.log hfne
  have hg : HasDerivAt (fun v : ℝ => 2 * v) ((2 : ℝ) * 1) u :=
    (hasDerivAt_id u).const_mul 2
  have hlogg := hg.log (by positivity : (2 : ℝ) * u ≠ 0)
  have hsub := hlogf.sub hlogg
  have heq : (fun v => Real.log (matchedProfile v))
      =ᶠ[nhds u] fun v => Real.log (1 - Real.exp (-2 * v)) - Real.log (2 * v) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    have hv0 : (0 : ℝ) < v := hv
    have h1 : Real.exp (-2 * v) < 1 := exp_neg_two_mul_lt_one hv0
    unfold matchedProfile
    rw [Real.log_div (by linarith) (by positivity)]
  have hK := hsub.congr_of_eventuallyEq heq
  have hval : (0 - Real.exp (-2 * u) * (-2 * 1)) / (1 - Real.exp (-2 * u))
      - (2 : ℝ) * 1 / (2 * u) = langevin u - 1 := by
    have hcoth := coth_sub_one hu
    unfold langevin
    rw [show (0 - Real.exp (-2 * u) * (-2 * 1)) / (1 - Real.exp (-2 * u))
        = 2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) by ring_nf]
    rw [← hcoth]
    field_simp
    ring
  rw [hval] at hK
  exact hK

/-- Derivative of coth: `coth′ = −1/sinh²`. -/
theorem coth_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt coth (-(1 / Real.sinh u ^ 2)) u := by
  have hs : Real.sinh u ≠ 0 := (Real.sinh_pos_iff.mpr hu).ne'
  have h := (Real.hasDerivAt_cosh u).div (Real.hasDerivAt_sinh u) hs
  have hval : (Real.sinh u * Real.sinh u - Real.cosh u * Real.cosh u)
      / Real.sinh u ^ 2 = -(1 / Real.sinh u ^ 2) := by
    have hc := Real.cosh_sq u
    field_simp
    nlinarith [hc]
  rw [hval] at h
  exact h

/-- **The Langevin derivative is the intensity:**
`L′(u) = 1/u² − 1/sinh²u`. -/
theorem langevin_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt langevin (1 / u ^ 2 - 1 / Real.sinh u ^ 2) u := by
  have h1 : HasDerivAt (fun c : ℝ => 1 / c) (-(1 / u ^ 2)) u := by
    have := hasDerivAt_inv hu.ne'
    simpa [one_div] using this
  have h := (coth_hasDerivAt hu).sub h1
  have hval : -(1 / Real.sinh u ^ 2) - -(1 / u ^ 2)
      = 1 / u ^ 2 - 1 / Real.sinh u ^ 2 := by ring
  rw [hval] at h
  exact h

/-- The Langevin derivative in intensity normalization:
`L′(u) = 4π·ρ(u)`. -/
theorem langevin_deriv_eq_intensity {u : ℝ} :
    1 / u ^ 2 - 1 / Real.sinh u ^ 2 = 4 * Real.pi * matchedIntensity u := by
  unfold matchedIntensity
  field_simp

/-- **The intensity is nonnegative** (`sinh u ≥ u` for `u > 0`): ρ is a
genuine point-process intensity. -/
theorem matchedIntensity_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ matchedIntensity u := by
  unfold matchedIntensity
  have hs : u < Real.sinh u := Real.self_lt_sinh_iff.mpr hu
  have h1 : u ^ 2 ≤ Real.sinh u ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < u ^ 2 := by positivity
  have h3 : 1 / Real.sinh u ^ 2 ≤ 1 / u ^ 2 :=
    one_div_le_one_div_of_le h2 h1
  have h5 : (0 : ℝ) ≤ 1 / u ^ 2 - 1 / Real.sinh u ^ 2 := by linarith
  exact div_nonneg h5 (by positivity)

/-- **Route A's open core, typed (doc 55 §6.4).**  Steinhaus-vs-Gaussian
local universality: the near-line zero count `count N c` (zeros with
`β − ½ ≥ c/log N` in a window of length `U N`) obeys the GAF intensity law
with the Langevin rate.  This is the single analytic input Route A owes;
everything downstream of it is computable and machine-checked above. -/
def RouteAUniversality (count : ℕ → ℝ → ℝ) (U : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ c > 0, ∀ᶠ N in Filter.atTop,
    count N c ≤ (langevin c / (4 * Real.pi) + ε) * U N * Real.log N

end RHTower
