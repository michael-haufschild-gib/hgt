import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Fuchs rate calculus and the prolate-to-Hermite scaling identity

Fuchs' fixed-index asymptotic for the time–band concentration problem states that the `n`-th
prolate leakage `d_n(λ) = 1 − χ_n(λ)²` decays like `A_n · λ^(2n+1) · exp(−4πλ²)` with a positive
constant `A_n`.  Two unconditional layers of that law are formalized here.

* **Rate calculus.**  The model rate `fuchsRate A n λ = A·λ^(2n+1)·e^(−4πλ²)` has an
  index-independent exponential factor, so every fixed-`λ` ratio of two rates is an exact pure
  power of `λ` (`fuchsRate_ratio`; the radial index step `4` gives the `λ^8` scale separation
  `fuchsRate_radial_ratio`).  Successive rates separate rigidly in the limit
  (`fuchsRate_div_tendsto_atTop`, `fuchsRate_div_tendsto_zero`), and each rate — even after a
  square root — beats every power of `λ` (`pow_mul_fuchsRate_tendsto_zero`,
  `pow_mul_sqrt_fuchsRate_tendsto_zero`).  In logarithmic form the rate is exactly
  `log A + (2n+1)·log λ − 4πλ²` (`fuchsRate_log`).

* **Scaling bridge.**  The prolate Sturm–Liouville action `(1−x²)ψ'' − 2xψ' − c²x²ψ` composed
  with the Hermite rescaling `x = ξ/√c`, `ψ ↦ ψ(√c·)` decomposes exactly as
  `c·(ψ''(ξ) − ξ²ψ(ξ)) − ξ²ψ''(ξ) − 2ξψ'(ξ)` (`prolateSLAction_sqrtScale`) — an identity, valid
  with no differentiability hypothesis because both sides read the same junk values.  Hence the
  `1/c`-normalized prolate action converges pointwise to the Hermite action
  (`prolateSLAction_sqrtScale_tendsto`), and a prolate eigenrelation at the scaled point forces
  the Hermite defect to equal `(ξ²ψ''(ξ) + 2ξψ'(ξ))/c` exactly
  (`prolate_eigen_hermite_defect`).

The asymptotic identification of the true leakage eigenvalues with `fuchsRate` (Fuchs' theorem
proper) is not claimed here.
-/

open Filter Real

namespace RHTower

/-- Powers lose to a Gaussian: `x^k · e^(−b·x²) → 0` as `x → ∞` for every `b > 0`. -/
theorem tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-(b * x ^ 2))) atTop (nhds 0) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop two_ne_zero
  have hcomp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) / 2) b hb).comp hsq
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) ≤ x := zero_le_one.trans hx
  have hpow : ((x ^ 2 : ℝ)) ^ ((k : ℝ) / 2) = x ^ k := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx0,
      show ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) by push_cast; ring]
    exact Real.rpow_natCast x k
  simp only [Function.comp_apply]
  rw [neg_mul, hpow]

/-- The Fuchs model rate `A · λ^(2n+1) · e^(−4πλ²)` for the `n`-th prolate leakage. -/
noncomputable def fuchsRate (A : ℝ) (n : ℕ) (lam : ℝ) : ℝ :=
  A * lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2))

theorem fuchsRate_pos {A : ℝ} (hA : 0 < A) (n : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    0 < fuchsRate A n lam :=
  mul_pos (mul_pos hA (pow_pos hlam _)) (Real.exp_pos _)

/-- The exponential factor of the Fuchs rate is index-independent, so the ratio of two rates at
the same `λ` is an exact pure power of `λ`: the rigid scale separation of the Fuchs ladder. -/
theorem fuchsRate_ratio (A A' : ℝ) (hA' : A' ≠ 0) {lam : ℝ} (hlam : lam ≠ 0) (n k : ℕ) :
    fuchsRate A (n + k) lam / fuchsRate A' n lam = A / A' * lam ^ (2 * k) := by
  unfold fuchsRate
  have hexp : Real.exp (-(4 * Real.pi * lam ^ 2)) ≠ 0 := Real.exp_ne_zero _
  have hpow : lam ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hlam
  rw [show 2 * (n + k) + 1 = (2 * n + 1) + 2 * k by ring, pow_add]
  field_simp

/-- Radial instance: one step `j → j+1` of the radial prolate family advances the Fuchs index by
`4`, so successive radial leakages are separated by the exact factor `(A/A')·λ^8`. -/
theorem fuchsRate_radial_ratio (A A' : ℝ) (hA' : A' ≠ 0) {lam : ℝ} (hlam : lam ≠ 0) (j : ℕ) :
    fuchsRate A (4 * (j + 1)) lam / fuchsRate A' (4 * j) lam = A / A' * lam ^ 8 := by
  rw [show 4 * (j + 1) = 4 * j + 4 by ring, fuchsRate_ratio A A' hA' hlam (4 * j) 4]

theorem fuchsRate_tendsto_zero (A : ℝ) (n : ℕ) :
    Tendsto (fun lam : ℝ => fuchsRate A n lam) atTop (nhds 0) := by
  have h := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero (2 * n + 1)
    (b := 4 * Real.pi) (by positivity)
  have h2 := h.const_mul A
  rw [mul_zero] at h2
  refine h2.congr fun x => ?_
  simp only [fuchsRate]; ring

/-- The Fuchs rate beats every power of `λ`. -/
theorem pow_mul_fuchsRate_tendsto_zero (A : ℝ) (n k : ℕ) :
    Tendsto (fun lam : ℝ => lam ^ k * fuchsRate A n lam) atTop (nhds 0) := by
  have h := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero (k + (2 * n + 1))
    (b := 4 * Real.pi) (by positivity)
  have h2 := h.const_mul A
  rw [mul_zero] at h2
  refine h2.congr fun x => ?_
  simp only [fuchsRate]
  rw [pow_add]; ring

/-- Even the square root of the Fuchs rate beats every power of `λ`: the form consumed by the
exterior-Weil leading law, where `√(d₁(λ))` must absorb polynomially growing prime sums. -/
theorem pow_mul_sqrt_fuchsRate_tendsto_zero (A : ℝ) (n k : ℕ) :
    Tendsto (fun lam : ℝ => lam ^ k * Real.sqrt (fuchsRate A n lam)) atTop (nhds 0) := by
  have h := pow_mul_fuchsRate_tendsto_zero A n (2 * k)
  have hsqrt : Tendsto Real.sqrt (nhds 0) (nhds 0) := by
    simpa using Real.continuous_sqrt.tendsto 0
  have hcomp := hsqrt.comp h
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
  have hx2k : (0 : ℝ) ≤ x ^ (2 * k) := by
    rw [show 2 * k = k * 2 by ring, pow_mul]; exact sq_nonneg _
  simp only [Function.comp_apply]
  rw [Real.sqrt_mul hx2k, show 2 * k = k * 2 by ring, pow_mul,
    Real.sqrt_sq (pow_nonneg hx k)]

/-- Logarithmic form of the Fuchs rate: the Gaussian clock `−4πλ²` plus the index read
`(2n+1)·log λ`. -/
theorem fuchsRate_log {A : ℝ} (hA : 0 < A) (n : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    Real.log (fuchsRate A n lam)
      = Real.log A + ((2 * n + 1 : ℕ) : ℝ) * Real.log lam - 4 * Real.pi * lam ^ 2 := by
  unfold fuchsRate
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul hA.ne' (by positivity), Real.log_pow, Real.log_exp]
  ring

/-- Rigid scale separation, limit form: a strictly higher Fuchs index dominates, with ratio
`(A/A')·λ^(2k) → ∞`. -/
theorem fuchsRate_div_tendsto_atTop {A A' : ℝ} (hA : 0 < A) (hA' : 0 < A') (n : ℕ)
    {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun lam : ℝ => fuchsRate A (n + k) lam / fuchsRate A' n lam) atTop atTop := by
  have hpow : Tendsto (fun lam : ℝ => lam ^ (2 * k)) atTop atTop :=
    Filter.tendsto_pow_atTop (by omega)
  have hmul := Filter.Tendsto.const_mul_atTop (div_pos hA hA') hpow
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  exact (fuchsRate_ratio A A' hA'.ne' hlam.ne' n k).symm

/-- Rigid scale separation, reciprocal form: a strictly lower Fuchs index is negligible against
a higher one. -/
theorem fuchsRate_div_tendsto_zero {A A' : ℝ} (hA : 0 < A) (hA' : 0 < A') (n : ℕ)
    {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun lam : ℝ => fuchsRate A' n lam / fuchsRate A (n + k) lam) atTop (nhds 0) := by
  have h := (fuchsRate_div_tendsto_atTop hA hA' n hk).inv_tendsto_atTop
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  simp only [Pi.inv_apply, inv_div]

/-- The prolate Sturm–Liouville action `(1−x²)ψ'' − 2xψ' − c²x²ψ` (the differential operator
commuting with time–band limiting at bandwidth parameter `c`). -/
noncomputable def prolateSLAction (c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * deriv (deriv ψ) x - 2 * x * deriv ψ x - c ^ 2 * x ^ 2 * ψ x

/-- The Hermite (quantum harmonic oscillator) action `ψ'' − x²ψ`. -/
noncomputable def hermiteSLAction (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv ψ) x - x ^ 2 * ψ x

/-- First derivative of the Hermite rescaling `ψ(√c·)`, with no differentiability hypothesis. -/
theorem deriv_sqrtScale (c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => ψ (Real.sqrt c * y)) x = Real.sqrt c * deriv ψ (Real.sqrt c * x) := by
  simpa [smul_eq_mul] using deriv_comp_mul_left (Real.sqrt c) ψ x

/-- Second derivative of the Hermite rescaling `ψ(√c·)`: the two chain-rule factors `√c`
combine to the exact bandwidth `c`. -/
theorem deriv2_sqrtScale {c : ℝ} (hc : 0 ≤ c) (ψ : ℝ → ℝ) (x : ℝ) :
    deriv (deriv (fun y => ψ (Real.sqrt c * y))) x
      = c * deriv (deriv ψ) (Real.sqrt c * x) := by
  have h1 : deriv (fun y => ψ (Real.sqrt c * y))
      = fun y => Real.sqrt c * deriv ψ (Real.sqrt c * y) :=
    funext fun y => deriv_sqrtScale c ψ y
  rw [h1, deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul, ← mul_assoc,
    Real.mul_self_sqrt hc]

/-- **Exact prolate→Hermite scaling identity.**  At the Hermite scale `x = ξ/√c` the prolate
action on `ψ(√c·)` splits exactly into `c` times the Hermite action plus a `c`-independent
remainder:
`L_c[ψ(√c·)](ξ/√c) = c·(ψ''(ξ) − ξ²ψ(ξ)) − ξ²ψ''(ξ) − 2ξψ'(ξ)`.
This is the mechanism of prolate-to-Hermite convergence: dividing by `c` leaves the Hermite
action plus an explicit `O(1/c)` defect. -/
theorem prolateSLAction_sqrtScale {c : ℝ} (hc : 0 < c) (ψ : ℝ → ℝ) (ξ : ℝ) :
    prolateSLAction c (fun y => ψ (Real.sqrt c * y)) (ξ / Real.sqrt c)
      = c * hermiteSLAction ψ ξ - ξ ^ 2 * deriv (deriv ψ) ξ - 2 * ξ * deriv ψ ξ := by
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hpoint : Real.sqrt c * (ξ / Real.sqrt c) = ξ := mul_div_cancel₀ ξ hs
  simp only [prolateSLAction, hermiteSLAction]
  rw [deriv2_sqrtScale hc.le, deriv_sqrtScale, hpoint]
  have hsq : (ξ / Real.sqrt c) ^ 2 = ξ ^ 2 / c := by
    rw [div_pow, Real.sq_sqrt hc.le]
  rw [hsq]
  field_simp
  ring

/-- The `1/c`-normalized scaled prolate action converges pointwise to the Hermite action as the
bandwidth `c → ∞`. -/
theorem prolateSLAction_sqrtScale_tendsto (ψ : ℝ → ℝ) (ξ : ℝ) :
    Tendsto
      (fun c : ℝ => c⁻¹ * prolateSLAction c (fun y => ψ (Real.sqrt c * y)) (ξ / Real.sqrt c))
      atTop (nhds (hermiteSLAction ψ ξ)) := by
  have h0 : Tendsto
      (fun c : ℝ => c⁻¹ * (ξ ^ 2 * deriv (deriv ψ) ξ + 2 * ξ * deriv ψ ξ))
      atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.mul_const (ξ ^ 2 * deriv (deriv ψ) ξ + 2 * ξ * deriv ψ ξ)
    rwa [zero_mul] at h
  have hR := (tendsto_const_nhds (x := hermiteSLAction ψ ξ) (f := atTop)).sub h0
  rw [sub_zero] at hR
  refine hR.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with c hc
  rw [prolateSLAction_sqrtScale hc ψ ξ]
  field_simp
  ring

/-- A prolate eigenrelation `L_c[ψ(√c·)](ξ/√c) = χ·ψ(ξ)` forces the Hermite defect of `ψ` at
eigenvalue `χ/c` to be exactly `(ξ²ψ''(ξ) + 2ξψ'(ξ))/c`: prolate eigenfunctions at bandwidth `c`
are Hermite quasi-eigenfunctions with explicit `O(1/c)` defect. -/
theorem prolate_eigen_hermite_defect {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ} {χ ξ : ℝ}
    (heig : prolateSLAction c (fun y => ψ (Real.sqrt c * y)) (ξ / Real.sqrt c) = χ * ψ ξ) :
    hermiteSLAction ψ ξ - χ / c * ψ ξ
      = (ξ ^ 2 * deriv (deriv ψ) ξ + 2 * ξ * deriv ψ ξ) / c := by
  have h := prolateSLAction_sqrtScale hc ψ ξ
  rw [heig] at h
  field_simp
  linarith

end RHTower
