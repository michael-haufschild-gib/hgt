import GaloisForLFunctions.RHTower.CHMDStage6PolarDoubleZeroAndContinuumLogMomentCollapse
import GaloisForLFunctions.RHTower.EvenSectorPoleFreeTwoSidedGrowth
import GaloisForLFunctions.RHTower.EvenSectorNegPartAbelRigidity

/-!
# CHMD Stage 7: Universal Hyperbolic Moment Factorizations, Analytic/Cusp Gauss Mode Decomposition, and Unconditional Pole-Free Negative-Part Abel Rigidity

This module establishes the **Stage 7** synthesis of the Causal Hyperbolic–Modular Duality (CHMD)
route:

1. **Universal Hyperbolic `cosh(α u)` and `sinh(α u)` Moment Factorizations for `crossCorr`
   (`integral_cosh_mul_crossCorr_eq`, `integral_sinh_mul_crossCorr_eq`,
   `integral_sinh_mul_crossCorr_self_eq_zero`, `integral_cosh_mul_crossCorr_self_eq`,
   `integral_cosh_mul_crossCorr_self_eq_of_even`, `integral_cosh_mul_crossCorr_self_nonneg_of_even`,
   `integral_cosh_mul_crossCorr_self_eq_of_odd`, `integral_cosh_mul_crossCorr_self_nonpos_of_odd`)**:
   Using `integral_exp_mul_crossCorr_eq` from Stage 6, we prove that for every continuous compactly
   supported `f : ℝ → ℝ` and every `α : ℝ`:
   - `∫ u : ℝ, Real.sinh (α * u) * crossCorr f f u = 0` unconditionally (for arbitrary parity);
   - `∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u = (∫ t, f t * Real.exp (α * t)) * (∫ v, f v * Real.exp (-α * v))`;
   - When `f` is **even** (`f (-t) = f t`),
     `∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u = (∫ t : ℝ, f t * Real.cosh (α * t)) ^ 2 ≥ 0`;
   - When `f` is **odd** (`f (-t) = -f t`),
     `∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u = -(∫ t : ℝ, f t * Real.sinh (α * t)) ^ 2 ≤ 0`.

2. **Exact Analytic/Cusp Decomposition of Decaying Exponential Modes `e^{-α|u|}` on Even, Odd, and Polar Tests
   (`exp_neg_abs_eq_cosh_sub_sinh_abs`, `integral_exp_neg_abs_crossCorr_self_eq`,
   `integral_exp_neg_abs_crossCorr_self_eq_of_even`,
   `integral_exp_neg_abs_crossCorr_self_eq_of_odd`,
   `integral_exp_neg_abs_half_crossCorr_self_eq_of_polar`)**:
   Since `Real.cosh (α * |u|) = Real.cosh (α * u)`, every decaying exponential kernel splits into
   a globally analytic rank-one hyperbolic moment and a UV cusp term:
   `Real.exp (-(α * |u|)) = Real.cosh (α * u) - Real.sinh (α * |u|)`.
   On even tests `f`,
   `∫ u : ℝ, Real.exp (-(α * |u|)) * crossCorr f f u = (∫ t, f t * Real.cosh (α * t)) ^ 2 - ∫ u, Real.sinh (α * |u|) * crossCorr f f u`.
   At `α = 1/2`, on any polar test `f` (`∫ t, f t * Real.exp (t / 2) = 0` or `∫ t, f t * Real.exp (-t / 2) = 0`),
   the smooth `cosh(u/2)` part vanishes identically and the `k = 0` Gauss mode reduces purely to the
   negative cusp integral `-∫ u : ℝ, Real.sinh (|u| / 2) * crossCorr f f u`.

3. **Unconditional Strip Positivity, Resonator Positivity, Positive-Part Summability, and
   Negative-Part Abel Rigidity on `WeilPositiveEvenPolar`
   (`archPoleEnergy_sub_atomPairing_nonneg_of_weilPositiveEvenPolar`,
   `evenWeilDensity_specSq_nonneg_of_weilPositiveEvenPolar_uncond`,
   `re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenPolar_uncond`,
   `even_log_density_le_of_weilPositiveEvenPolar`,
   `even_sum_sq_div_le_of_primitive_of_weilPositiveEvenPolar`,
   `summable_posPart_div_rpow_of_weilPositiveEvenPolar`,
   `riemannHypothesis_of_weilPositiveEvenPolar_of_negPart`,
   `riemannHypothesis_of_weilPositiveEvenPolar_of_sum_negPart_Ioc_le`)**:
   Combining `exists_abs_le_of_weilPositiveEvenPolar` (`EvenSectorPoleFreeTwoSidedGrowth`) with
   `EvenSectorPolarStripCeiling` and `EvenSectorNegPartAbelRigidity`, we remove all external growth
   and pole-weight hypotheses from the even resonator and Toeplitz machinery: every weight system
   `lam` satisfying `WeilPositiveEvenPolar lam` automatically has a positive part `max (lam n) 0`
   that is `ℓ²`-bounded on primitive sets, `O(N log N)` on dyadic blocks, and Dirichlet-summable on
   `Re s > 1`. Consequently, negative-part Abel rigidity holds directly on the pole-free even cone
   `WeilPositiveEvenPolar lam` without assuming positivity on non-polar tests or any pole weight `β`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.CHMDStage7

open EvenSector OddSector WeilOneSided WeilPoleWeight WeilSpectral WeilMeanSquare ResonatorProfile
open CHMDStage6

/-! ## Section 1: Universal Hyperbolic `cosh(α u)` and `sinh(α u)` Moment Factorizations for `crossCorr` -/

theorem cosh_mul_crossCorr_eq (X Y : ℝ → ℝ) (α u : ℝ) :
    Real.cosh (α * u) * crossCorr X Y u =
      (1 / 2) * (Real.exp (α * u) * crossCorr X Y u) +
        (1 / 2) * (Real.exp (-α * u) * crossCorr X Y u) := by
  rw [Real.cosh_eq, show -(α * u) = -α * u by ring]
  ring

theorem sinh_mul_crossCorr_eq (X Y : ℝ → ℝ) (α u : ℝ) :
    Real.sinh (α * u) * crossCorr X Y u =
      (1 / 2) * (Real.exp (α * u) * crossCorr X Y u) -
        (1 / 2) * (Real.exp (-α * u) * crossCorr X Y u) := by
  rw [Real.sinh_eq, show -(α * u) = -α * u by ring]
  ring

theorem integrable_exp_mul_crossCorr {X Y : ℝ → ℝ}
    (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (hYc : HasCompactSupport Y) (c : ℝ) :
    Integrable (fun u => Real.exp (c * u) * crossCorr X Y u) := by
  simp_rw [exp_mul_crossCorr_eq X Y c]
  exact integrable_crossCorr_of_hasCompactSupport
    (by fun_prop) (hasCompactSupport_mul_exp hXc c)
    (by fun_prop) (hasCompactSupport_mul_exp hYc (-c))

/-- **Hyperbolic Cosine Moment Factorization for `crossCorr`**:
`∫ u : ℝ, Real.cosh (α * u) * crossCorr X Y u` splits into the average of the `±α` exponential
moment products. -/
theorem integral_cosh_mul_crossCorr_eq {X Y : ℝ → ℝ}
    (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (hYc : HasCompactSupport Y) (α : ℝ) :
    ∫ u : ℝ, Real.cosh (α * u) * crossCorr X Y u =
      (1 / 2) * ((∫ t : ℝ, X t * Real.exp (α * t)) * (∫ v : ℝ, Y v * Real.exp (-α * v))) +
        (1 / 2) * ((∫ t : ℝ, X t * Real.exp (-α * t)) * (∫ v : ℝ, Y v * Real.exp (α * v))) := by
  simp_rw [cosh_mul_crossCorr_eq X Y α]
  have h1 := integrable_exp_mul_crossCorr hX hXc hY hYc α
  have h2 := integrable_exp_mul_crossCorr hX hXc hY hYc (-α)
  rw [integral_add (h1.const_mul (1 / 2)) (h2.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul,
    integral_exp_mul_crossCorr_eq hX hXc hY hYc α,
    integral_exp_mul_crossCorr_eq hX hXc hY hYc (-α)]
  simp only [neg_neg]

/-- **Hyperbolic Sine Moment Factorization for `crossCorr`**:
`∫ u : ℝ, Real.sinh (α * u) * crossCorr X Y u` splits into the half-difference of the `±α`
exponential moment products. -/
theorem integral_sinh_mul_crossCorr_eq {X Y : ℝ → ℝ}
    (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (hYc : HasCompactSupport Y) (α : ℝ) :
    ∫ u : ℝ, Real.sinh (α * u) * crossCorr X Y u =
      (1 / 2) * ((∫ t : ℝ, X t * Real.exp (α * t)) * (∫ v : ℝ, Y v * Real.exp (-α * v))) -
        (1 / 2) * ((∫ t : ℝ, X t * Real.exp (-α * t)) * (∫ v : ℝ, Y v * Real.exp (α * v))) := by
  simp_rw [sinh_mul_crossCorr_eq X Y α]
  have h1 := integrable_exp_mul_crossCorr hX hXc hY hYc α
  have h2 := integrable_exp_mul_crossCorr hX hXc hY hYc (-α)
  rw [integral_sub (h1.const_mul (1 / 2)) (h2.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul,
    integral_exp_mul_crossCorr_eq hX hXc hY hYc α,
    integral_exp_mul_crossCorr_eq hX hXc hY hYc (-α)]
  simp only [neg_neg]

/-- **Universal Vanishing of `sinh(α u)` Moments on Autocorrelations**:
for every continuous compactly supported `f : ℝ → ℝ` (regardless of parity) and every `α : ℝ`,
`∫ u : ℝ, Real.sinh (α * u) * crossCorr f f u = 0`. -/
theorem integral_sinh_mul_crossCorr_self_eq_zero {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α : ℝ) :
    ∫ u : ℝ, Real.sinh (α * u) * crossCorr f f u = 0 := by
  rw [integral_sinh_mul_crossCorr_eq hf hfc hf hfc α]
  ring

/-- **Universal `cosh(α u)` Moment Factorization on Autocorrelations**:
for every continuous compactly supported `f : ℝ → ℝ` and every `α : ℝ`,
`∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u = (∫ t : ℝ, f t * Real.exp (α * t)) * (∫ v : ℝ, f v * Real.exp (-α * v))`. -/
theorem integral_cosh_mul_crossCorr_self_eq {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α : ℝ) :
    ∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u =
      (∫ t : ℝ, f t * Real.exp (α * t)) * (∫ v : ℝ, f v * Real.exp (-α * v)) := by
  rw [integral_cosh_mul_crossCorr_eq hf hfc hf hfc α]
  ring

/-- On an **even** function `f`, `∫ t, f t * Real.exp (-α * t) = ∫ t, f t * Real.exp (α * t)`. -/
theorem integral_mul_exp_neg_eq_of_even {f : ℝ → ℝ} (heven : ∀ t, f (-t) = f t) (α : ℝ) :
    ∫ t : ℝ, f t * Real.exp (-α * t) = ∫ t : ℝ, f t * Real.exp (α * t) := by
  rw [← integral_neg_eq_self (fun t => f t * Real.exp (-α * t))]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [heven t, show -α * -t = α * t by ring]

/-- On an **even** continuous compactly supported function `f`,
`∫ t, f t * Real.cosh (α * t) = ∫ t, f t * Real.exp (α * t)`. -/
theorem integral_mul_cosh_eq_of_even {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (heven : ∀ t, f (-t) = f t) (α : ℝ) :
    ∫ t : ℝ, f t * Real.cosh (α * t) = ∫ t : ℝ, f t * Real.exp (α * t) := by
  have heq : (fun t => f t * Real.cosh (α * t)) =
      fun t => (1 / 2) * (f t * Real.exp (α * t)) + (1 / 2) * (f t * Real.exp (-α * t)) := by
    funext t
    rw [Real.cosh_eq, show -(α * t) = -α * t by ring]
    ring
  have h1 : Integrable (fun t => f t * Real.exp (α * t)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_mul_exp hfc α)
  have h2 : Integrable (fun t => f t * Real.exp (-α * t)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_mul_exp hfc (-α))
  rw [heq, integral_add (h1.const_mul (1 / 2)) (h2.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul, integral_mul_exp_neg_eq_of_even heven α]
  ring

/-- **Even Hyperbolic Cosine Factorization**:
for every even continuous compactly supported `f : ℝ → ℝ` and every `α : ℝ`,
`∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u = (∫ t : ℝ, f t * Real.cosh (α * t)) ^ 2`. -/
theorem integral_cosh_mul_crossCorr_self_eq_of_even {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (heven : ∀ t, f (-t) = f t) (α : ℝ) :
    ∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u =
      (∫ t : ℝ, f t * Real.cosh (α * t)) ^ 2 := by
  rw [integral_cosh_mul_crossCorr_self_eq hf hfc α,
    integral_mul_exp_neg_eq_of_even heven α,
    ← integral_mul_cosh_eq_of_even hf hfc heven α]
  ring

/-- **Even Hyperbolic Cosine Positivity**:
for every even continuous compactly supported `f : ℝ → ℝ` and every `α : ℝ`,
`0 ≤ ∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u`. -/
theorem integral_cosh_mul_crossCorr_self_nonneg_of_even {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (heven : ∀ t, f (-t) = f t) (α : ℝ) :
    0 ≤ ∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u := by
  rw [integral_cosh_mul_crossCorr_self_eq_of_even hf hfc heven α]
  exact sq_nonneg _

/-- On an **odd** function `f`, `∫ t, f t * Real.exp (-α * t) = -∫ t, f t * Real.exp (α * t)`. -/
theorem integral_mul_exp_neg_eq_of_odd {f : ℝ → ℝ} (hodd : ∀ t, f (-t) = -f t) (α : ℝ) :
    ∫ t : ℝ, f t * Real.exp (-α * t) = -(∫ t : ℝ, f t * Real.exp (α * t)) := by
  rw [← integral_neg_eq_self (fun t => f t * Real.exp (-α * t)), ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [hodd t, show -α * -t = α * t by ring]
  ring

/-- On an **odd** continuous compactly supported function `f`,
`∫ t, f t * Real.sinh (α * t) = ∫ t, f t * Real.exp (α * t)`. -/
theorem integral_mul_sinh_eq_of_odd {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hodd : ∀ t, f (-t) = -f t) (α : ℝ) :
    ∫ t : ℝ, f t * Real.sinh (α * t) = ∫ t : ℝ, f t * Real.exp (α * t) := by
  have heq : (fun t => f t * Real.sinh (α * t)) =
      fun t => (1 / 2) * (f t * Real.exp (α * t)) - (1 / 2) * (f t * Real.exp (-α * t)) := by
    funext t
    rw [Real.sinh_eq, show -(α * t) = -α * t by ring]
    ring
  have h1 : Integrable (fun t => f t * Real.exp (α * t)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_mul_exp hfc α)
  have h2 : Integrable (fun t => f t * Real.exp (-α * t)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_mul_exp hfc (-α))
  rw [heq, integral_sub (h1.const_mul (1 / 2)) (h2.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul, integral_mul_exp_neg_eq_of_odd hodd α]
  ring

/-- **Odd Hyperbolic Cosine Factorization**:
for every odd continuous compactly supported `f : ℝ → ℝ` and every `α : ℝ`,
`∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u = -(∫ t : ℝ, f t * Real.sinh (α * t)) ^ 2`. -/
theorem integral_cosh_mul_crossCorr_self_eq_of_odd {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hodd : ∀ t, f (-t) = -f t) (α : ℝ) :
    ∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u =
      -(∫ t : ℝ, f t * Real.sinh (α * t)) ^ 2 := by
  rw [integral_cosh_mul_crossCorr_self_eq hf hfc α,
    integral_mul_exp_neg_eq_of_odd hodd α,
    ← integral_mul_sinh_eq_of_odd hf hfc hodd α]
  ring

/-- **Odd Hyperbolic Cosine Nonpositivity**:
for every odd continuous compactly supported `f : ℝ → ℝ` and every `α : ℝ`,
`∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u ≤ 0`. -/
theorem integral_cosh_mul_crossCorr_self_nonpos_of_odd {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hodd : ∀ t, f (-t) = -f t) (α : ℝ) :
    ∫ u : ℝ, Real.cosh (α * u) * crossCorr f f u ≤ 0 := by
  rw [integral_cosh_mul_crossCorr_self_eq_of_odd hf hfc hodd α]
  linarith [sq_nonneg (∫ t : ℝ, f t * Real.sinh (α * t))]

/-! ## Section 2: Exact Analytic/Cusp Decomposition of Decaying Exponential Modes `e^{-α|u|}` -/

/-- Because `Real.cosh` is even, `Real.cosh (α * |u|) = Real.cosh (α * u)` for all `α, u : ℝ`. -/
theorem cosh_mul_abs_eq (α u : ℝ) :
    Real.cosh (α * |u|) = Real.cosh (α * u) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu, show α * -u = -(α * u) by ring, Real.cosh_neg]

/-- **Pointwise Analytic/Cusp Decomposition of `e^{-α|u|}`**:
`Real.exp (-(α * |u|)) = Real.cosh (α * u) - Real.sinh (α * |u|)` for all `α, u : ℝ`. -/
theorem exp_neg_abs_eq_cosh_sub_sinh_abs (α u : ℝ) :
    Real.exp (-(α * |u|)) = Real.cosh (α * u) - Real.sinh (α * |u|) := by
  rw [← cosh_mul_abs_eq α u, Real.cosh_sub_sinh]

/-- **Integrated Analytic/Cusp Decomposition of `e^{-α|u|}` on Autocorrelations**:
for every continuous compactly supported `f : ℝ → ℝ` and every `α : ℝ`,
`∫ u : ℝ, Real.exp (-(α * |u|)) * crossCorr f f u` decomposes into the smooth rank-one product
`(∫ t, f t * Real.exp (α * t)) * (∫ v, f v * Real.exp (-α * v))` minus the UV cusp integral
`∫ u : ℝ, Real.sinh (α * |u|) * crossCorr f f u`. -/
theorem integral_exp_neg_abs_crossCorr_self_eq {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α : ℝ) :
    ∫ u : ℝ, Real.exp (-(α * |u|)) * crossCorr f f u =
      (∫ t : ℝ, f t * Real.exp (α * t)) * (∫ v : ℝ, f v * Real.exp (-α * v)) -
        ∫ u : ℝ, Real.sinh (α * |u|) * crossCorr f f u := by
  have heq : (fun u => Real.exp (-(α * |u|)) * crossCorr f f u) =
      fun u => Real.cosh (α * u) * crossCorr f f u - Real.sinh (α * |u|) * crossCorr f f u := by
    funext u
    rw [exp_neg_abs_eq_cosh_sub_sinh_abs α u]
    ring
  have hkc := hasCompactSupport_crossCorr_of_hasCompactSupport hfc hfc
  have hkcont := continuous_crossCorr_of_hasCompactSupport hf hf hfc
  have h1 : Integrable (fun u => Real.cosh (α * u) * crossCorr f f u) :=
    ((by fun_prop : Continuous fun u => Real.cosh (α * u)).mul hkcont).integrable_of_hasCompactSupport
      hkc.mul_left
  have h2 : Integrable (fun u => Real.sinh (α * |u|) * crossCorr f f u) :=
    ((by fun_prop : Continuous fun u => Real.sinh (α * |u|)).mul hkcont).integrable_of_hasCompactSupport
      hkc.mul_left
  rw [heq, integral_sub h1 h2, integral_cosh_mul_crossCorr_self_eq hf hfc α]

/-- **Even Analytic/Cusp Decomposition of `e^{-α|u|}`**:
on every even continuous compactly supported `f : ℝ → ℝ`,
`∫ u : ℝ, Real.exp (-(α * |u|)) * crossCorr f f u = (∫ t, f t * Real.cosh (α * t)) ^ 2 - ∫ u, Real.sinh (α * |u|) * crossCorr f f u`. -/
theorem integral_exp_neg_abs_crossCorr_self_eq_of_even {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (heven : ∀ t, f (-t) = f t) (α : ℝ) :
    ∫ u : ℝ, Real.exp (-(α * |u|)) * crossCorr f f u =
      (∫ t : ℝ, f t * Real.cosh (α * t)) ^ 2 -
        ∫ u : ℝ, Real.sinh (α * |u|) * crossCorr f f u := by
  rw [integral_exp_neg_abs_crossCorr_self_eq hf hfc α,
    integral_mul_exp_neg_eq_of_even heven α,
    ← integral_mul_cosh_eq_of_even hf hfc heven α]
  ring

/-- **Odd Analytic/Cusp Decomposition of `e^{-α|u|}`**:
on every odd continuous compactly supported `f : ℝ → ℝ`,
`∫ u : ℝ, Real.exp (-(α * |u|)) * crossCorr f f u = -(∫ t, f t * Real.sinh (α * t)) ^ 2 - ∫ u, Real.sinh (α * |u|) * crossCorr f f u`. -/
theorem integral_exp_neg_abs_crossCorr_self_eq_of_odd {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hodd : ∀ t, f (-t) = -f t) (α : ℝ) :
    ∫ u : ℝ, Real.exp (-(α * |u|)) * crossCorr f f u =
      -(∫ t : ℝ, f t * Real.sinh (α * t)) ^ 2 -
        ∫ u : ℝ, Real.sinh (α * |u|) * crossCorr f f u := by
  rw [integral_exp_neg_abs_crossCorr_self_eq hf hfc α,
    integral_mul_exp_neg_eq_of_odd hodd α,
    ← integral_mul_sinh_eq_of_odd hf hfc hodd α]
  ring

/-- **Polar Collapse of the `k = 0` Gauss Mode `e^{-|u|/2}`**:
for any continuous compactly supported `f : ℝ → ℝ` with `∫ t, f t * Real.exp (t / 2) = 0` or
`∫ t, f t * Real.exp (-t / 2) = 0`, the smooth `cosh(u/2)` part vanishes and the `k = 0` Gauss
mode equals `-∫ u : ℝ, Real.sinh (|u| / 2) * crossCorr f f u`. -/
theorem integral_exp_neg_abs_half_crossCorr_self_eq_of_polar {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hp : (∫ t : ℝ, f t * Real.exp (t / 2)) = 0 ∨ (∫ t : ℝ, f t * Real.exp (-t / 2)) = 0) :
    ∫ u : ℝ, Real.exp (-|u| / 2) * crossCorr f f u =
      -∫ u : ℝ, Real.sinh (|u| / 2) * crossCorr f f u := by
  have h1 := integral_exp_neg_abs_crossCorr_self_eq hf hfc (1 / 2)
  have e1 : (fun u : ℝ => Real.exp (-(1 / 2 * |u|)) * crossCorr f f u) =
      fun u : ℝ => Real.exp (-|u| / 2) * crossCorr f f u := by
    funext u; congr 2; ring
  have e2 : (fun u : ℝ => Real.sinh (1 / 2 * |u|) * crossCorr f f u) =
      fun u : ℝ => Real.sinh (|u| / 2) * crossCorr f f u := by
    funext u; congr 2; ring
  have e3 : (fun t : ℝ => f t * Real.exp (1 / 2 * t)) =
      fun t : ℝ => f t * Real.exp (t / 2) := by
    funext t; congr 2; ring
  have e4 : (fun v : ℝ => f v * Real.exp (-(1 / 2) * v)) =
      fun v : ℝ => f v * Real.exp (-v / 2) := by
    funext v; congr 2; ring
  rw [e1, e2, e3, e4] at h1
  rcases hp with hp | hm
  · rw [h1, hp, zero_mul, zero_sub]
  · rw [h1, hm, mul_zero, zero_sub]

/-! ## Section 3: Unconditional Strip Positivity, Resonator Positivity, Positive-Part Summability, and Negative-Part Abel Rigidity on `WeilPositiveEvenPolar` -/

/-- **Unconditional Pole-Free Positivity on Decaying Even Tests**:
removes the external growth hypothesis `hg` from `archPoleEnergy_sub_atomPairing_nonneg_of_polar`
using `exists_abs_le_of_weilPositiveEvenPolar`. -/
theorem archPoleEnergy_sub_atomPairing_nonneg_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {F : ℝ → ℝ} (heven : ∀ x, F (-x) = F x) {δ C : ℝ}
    (hδ : 1 / 2 < δ) (hF : DecayBound F δ C) (hP : ∫ u, F u * Real.exp (-u / 2) = 0) :
    0 ≤ archPoleEnergy F - atomPairing lam (crossCorr F F) := by
  obtain ⟨Cg, -, hg⟩ := exists_abs_le_of_weilPositiveEvenPolar hpf
  exact archPoleEnergy_sub_atomPairing_nonneg_of_polar hpf hg heven hδ hF hP

/-- **Unconditional Pole-Free Strip Positivity**:
removes the external growth hypothesis `hg` from
`evenWeilDensity_specSq_nonneg_of_weilPositiveEvenPolar`. -/
theorem evenWeilDensity_specSq_nonneg_of_weilPositiveEvenPolar_uncond {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) (hΦ0 : Φ (I / 2) = 0) :
    0 ≤ evenWeilDensity lam (specSq Φ) := by
  obtain ⟨Cg, -, hg⟩ := exists_abs_le_of_weilPositiveEvenPolar hpf
  exact evenWeilDensity_specSq_nonneg_of_weilPositiveEvenPolar hpf hg hΦ hΦ0

/-- **Unconditional Positivity on Nonnegative Resonators from `WeilPositiveEvenPolar`**:
removes the external growth hypothesis `hgr` from
`re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenPolar`. -/
theorem re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenPolar_uncond {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {ι : Type*} (s : Finset ι) {c : ι → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (x : ι → ℝ) {g : ℝ → ℝ} (hg2 : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hge : ∀ u, g (-u) = g u)
    (hg0 : paperFT (fun u => (g u : ℂ)) (I / 2) = 0) :
    0 ≤ (weilFullFunctional lam
      (EF.weilTest (fun u => ((∑ k ∈ s, c k * g (u - x k) : ℝ) : ℂ))
        (fun u => ((∑ k ∈ s, c k * g (u - x k) : ℝ) : ℂ)))).re := by
  obtain ⟨Cg, -, hgr⟩ := exists_abs_le_of_weilPositiveEvenPolar hpf
  exact re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenPolar hpf hgr s hc x hg2 hgc
    hge hg0

/-- **Unconditional Unit Weil–Toeplitz Bound on `WeilPositiveEvenPolar`**. -/
theorem even_unit_toeplitz_bound_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {N : ℕ} (hN : 1 ≤ N) :
    2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then lam n / (n * m) else 0) ≤
      (Real.log N + (Real.log 2 + 9 / 2 + profileRatio / 2)) *
        ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
  obtain ⟨Cg, -, hgr⟩ := exists_abs_le_of_weilPositiveEvenPolar hpf
  exact even_unit_toeplitz_bound_of_polar hpf hgr hN

/-- **Unconditional Log-Density Ceiling on `WeilPositiveEvenPolar`**. -/
theorem even_log_density_le_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
          (if n * m ≤ N then lam n / (n * m) else 0) ≤ (1 / 2 + ε) * Real.log N ^ 2 := by
  obtain ⟨Cg, -, hgr⟩ := exists_abs_le_of_weilPositiveEvenPolar hpf
  exact even_log_density_le_of_polar hpf hgr hε

/-- **General Nonnegative-Coefficient Resonator Symbol Positivity on `WeilPositiveEvenPolar`**. -/
theorem integral_weilAtomSymbol_evenResonator_nonneg_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) (N : ℕ) (c : ℕ → ℝ) (hc0 : ∀ m, 0 ≤ c m) :
    0 ≤ ∫ τ : ℝ, ‖paperFT (resonator N (fun m => (c m : ℂ)) (1 / ((N : ℝ) + 1))) τ‖ ^ 2 *
      weilAtomSymbol lam ⌊Real.exp (2 * (Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4))⌋₊
        (τ / (2 * π)) := by
  have hw : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨hp1, hp2⟩ := paperFT_resonator_pole (N := N) (c := fun m => (c m : ℂ)) hw
  have ha : 0 ≤ Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4 := by
    have := Real.log_natCast_nonneg N
    positivity
  refine integral_weilAtomSymbol_nonneg_of_polar ha (contDiff_resonator N _ _ 2)
    (tsupport_subset_of_vanish fun u hu => sum_translates_eq_zero
      (fun v hv => gC_eq_zero hw hv) hu) hp1 hp2 ?_
  have hgc : HasCompactSupport (gR (1 / ((N : ℝ) + 1))) :=
    (hasCompactSupport_comp_left (g := Complex.ofReal) fun {_} => Complex.ofReal_eq_zero).mp
      (hasCompactSupport_gC hw)
  rw [resonator_ofRealCoeff]
  exact re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenPolar_uncond hpf
    (Finset.Icc 1 N) (fun m _ => hc0 m) (resPt N) (contDiff_gR _ 2) hgc (gR_neg _)
    (paperFT_gC_pole hw).1

/-- **The Even Weil–Toeplitz Bound for Nonnegative Coefficients on `WeilPositiveEvenPolar`**. -/
theorem even_toeplitz_bound_nonneg_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (hc0 : ∀ m, 0 ≤ c m)
    (hc : ∀ m, N < m → c m = 0) :
    2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m ≤
      (Real.log N + evenToeplitzConst) * ∑ m ∈ Finset.Icc 1 N, c m ^ 2 := by
  have hcC : ∀ m, N < m → (c m : ℂ) = 0 := fun m hm => by rw [hc m hm, Complex.ofReal_zero]
  have hb := weil_multiplicativeToeplitz_bound_of_resonator hN (fun m => (c m : ℂ)) hcC
    (integral_weilAtomSymbol_evenResonator_nonneg_of_weilPositiveEvenPolar hpf N c hc0)
  have hl : ∀ n, (∑ m ∈ Finset.Icc 1 N, (c (n * m) : ℂ) * conj (c m : ℂ)).re =
      ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m := fun n => by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hr : ∑ m ∈ Finset.Icc 1 N, ‖(c m : ℂ)‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, c m ^ 2 :=
    Finset.sum_congr rfl fun m _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hl, hr] at hb
  exact hb

/-- **Mean-Square Bound on Primitive Sets for `WeilPositiveEvenPolar`**:
even pole-free positivity alone bounds the weights in mean square on any primitive set where
they are nonnegative. -/
theorem even_sum_sq_div_le_of_primitive_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ Real.log N + evenToeplitzConst ∧
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S → (∀ n ∈ S, 0 ≤ lam n) →
        ∑ n ∈ S, lam n ^ 2 / n ≤ (Real.log N + evenToeplitzConst) ^ 2 := by
  have key : ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S → (∀ n ∈ S, 0 ≤ lam n) →
      ∀ t : ℝ, 0 ≤ t → 2 * t * ∑ n ∈ S, lam n ^ 2 / n ≤
        (Real.log N + evenToeplitzConst) * (1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n) := by
    intro S hS hprim hpos t ht
    set c : ℕ → ℝ := fun m => if m = 1 then 1 else if m ∈ S then t * lam m / Real.sqrt m else 0
      with hc
    have hc0 : ∀ m, 0 ≤ c m := fun m => by
      simp only [hc]
      split_ifs with h1 h2
      · norm_num
      · exact div_nonneg (mul_nonneg ht (hpos m h2)) (Real.sqrt_nonneg _)
      · exact le_rfl
    have hcN : ∀ m, N < m → c m = 0 := by
      intro m hm
      have h1 : m ≠ 1 := by omega
      have h2 : m ∉ S := fun h' => by have := (Finset.mem_Icc.mp (hS h')).2; omega
      simp [hc, h1, h2]
    have hb := even_toeplitz_bound_nonneg_of_weilPositiveEvenPolar hpf hN c hc0 hcN
    have hinner : ∀ n ∈ Finset.Icc 2 N,
        ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m = if n ∈ S then t * lam n / Real.sqrt n else 0 := by
      intro n hn
      obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hrest : ∑ m ∈ (Finset.Icc 1 N).erase 1, c (n * m) * c m = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        obtain ⟨hm1, hmI⟩ := Finset.mem_erase.mp hm
        by_cases hmS : m ∈ S
        · have hnm1 : n * m ≠ 1 := by
            have := (Finset.mem_Icc.mp hmI).1; nlinarith
          have hnmS : n * m ∉ S := fun h' => hprim _ h' m hmS n hn2 rfl
          simp [hc, hnm1, hnmS]
        · simp [hc, hm1, hmS]
      rw [hrest, add_zero, mul_one]
      have hn1 : n ≠ 1 := by omega
      by_cases hnS : n ∈ S
      · simp [hc, hn1, hnS]
      · simp [hc, hn1, hnS]
    have hmass : ∑ m ∈ Finset.Icc 1 N, c m ^ 2 = 1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hS' : S ⊆ (Finset.Icc 1 N).erase 1 := fun n hn => by
        have := Finset.mem_Icc.mp (hS hn)
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, this.2⟩⟩
      rw [← Finset.sum_subset hS' (fun m hm hmS => by
        have hm1 := (Finset.mem_erase.mp hm).1
        simp [hc, hm1, hmS]), Finset.mul_sum]
      congr 1
      · simp [hc]
      · refine Finset.sum_congr rfl fun n hn => ?_
        have hn2 := (Finset.mem_Icc.mp (hS hn)).1
        have hn1 : n ≠ 1 := by omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        simp only [hc, hn1, hn, if_false, if_true, div_pow, mul_pow, Real.sq_sqrt hn0.le]
        ring
    have hlhs : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m = t * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [Finset.sum_congr rfl fun n hn => by rw [hinner n hn], Finset.mul_sum]
      rw [← Finset.sum_subset hS (fun n _ hnS => by simp [hnS])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 := (Finset.mem_Icc.mp (hS hn)).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      rw [if_pos hn, show lam n / Real.sqrt n * (t * lam n / Real.sqrt n) =
        t * (lam n ^ 2 / (Real.sqrt n * Real.sqrt n)) by ring, hsq]
    rw [hlhs, hmass] at hb
    linarith
  have hB : 0 ≤ Real.log N + evenToeplitzConst := by
    have := key ∅ (Finset.empty_subset _) (fun m hm => absurd hm (Finset.notMem_empty m))
      (fun n hn => absurd hn (Finset.notMem_empty n)) 0 le_rfl
    simpa using this
  refine ⟨hB, fun S hS hprim hpos => ?_⟩
  set Q := ∑ n ∈ S, lam n ^ 2 / n with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
  set B := Real.log N + evenToeplitzConst with hBdef
  rcases hQ0.lt_or_eq with hQpos | hQzero
  · have h1 := key S hS hprim hpos (B / Q) (div_nonneg hB hQ0)
    rw [← hQ] at h1
    have e : 2 * (B / Q) * Q = 2 * B := by field_simp
    have e2 : B * (1 + (B / Q) ^ 2 * Q) = B + B ^ 3 / Q := by field_simp
    rw [e, e2] at h1
    have h3 : B ≤ B ^ 3 / Q := by linarith
    rcases hB.lt_or_eq with hBpos | hBzero
    · rw [le_div_iff₀ hQpos] at h3
      nlinarith
    · have h4 := key S hS hprim hpos 1 zero_le_one
      rw [← hQ, ← hBzero] at h4
      nlinarith
  · rw [← hQzero]; positivity

/-- **Dyadic Mean-Square Bound of the Positive Part on `WeilPositiveEvenPolar`**. -/
theorem even_sum_posPart_sq_Ioc_le_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ Real.log (2 * N : ℕ) + evenToeplitzConst ∧
      ∑ n ∈ Finset.Ioc N (2 * N), max (lam n) 0 ^ 2 ≤
        (2 * N : ℕ) * (Real.log (2 * N : ℕ) + evenToeplitzConst) ^ 2 := by
  obtain ⟨hB, hS⟩ := even_sum_sq_div_le_of_primitive_of_weilPositiveEvenPolar hpf (N := 2 * N)
    (by omega)
  refine ⟨hB, ?_⟩
  set S := (Finset.Ioc N (2 * N)).filter fun n => 0 ≤ lam n with hSdef
  have hsub : S ⊆ Finset.Icc 2 (2 * N) := fun n hn => by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
  have hprim : IsPrimitiveSet S := by
    intro m hm m' hm' k hk heq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm hm'
    have : k * m' ≥ 2 * (N + 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hQ := hS S hsub hprim fun n hn => (Finset.mem_filter.mp hn).2
  have h2N : (0 : ℝ) < (2 * N : ℕ) := by exact_mod_cast (show 0 < 2 * N by omega)
  have hsplit : ∑ n ∈ Finset.Ioc N (2 * N), max (lam n) 0 ^ 2 = ∑ n ∈ S, lam n ^ 2 := by
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hn
    · rw [max_eq_left hn]
    · push Not at hn; rw [max_eq_right hn.le]; ring
  rw [hsplit]
  calc ∑ n ∈ S, lam n ^ 2
      = (2 * N : ℕ) * ∑ n ∈ S, lam n ^ 2 / (2 * N : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by field_simp
    _ ≤ (2 * N : ℕ) * ∑ n ∈ S, lam n ^ 2 / n := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) h2N.le
        rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        exact div_le_div_of_nonneg_left (sq_nonneg _) hn0 (by exact_mod_cast hn.1.2)
    _ ≤ (2 * N : ℕ) * (Real.log (2 * N : ℕ) + evenToeplitzConst) ^ 2 :=
        mul_le_mul_of_nonneg_left hQ h2N.le

/-- **Dyadic `ℓ¹` Bound of the Positive Part on `WeilPositiveEvenPolar`**. -/
theorem even_sum_posPart_Ioc_le_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc N (2 * N), max (lam n) 0 ≤
      3 / 2 * N * (Real.log (2 * N : ℕ) + evenToeplitzConst + 1) := by
  obtain ⟨hB, hsq⟩ := even_sum_posPart_sq_Ioc_le_of_weilPositiveEvenPolar hpf hN
  have h1 := sum_abs_Ioc_le_of_sum_sq (lam := fun n => max (lam n) 0) hB hsq
  have e : ∀ n, |max (lam n) 0| = max (lam n) 0 := fun n => abs_of_nonneg (le_max_right _ _)
  simp only [e] at h1
  exact h1

/-- **Unconditional Positive-Part Dirichlet Summability on `WeilPositiveEvenPolar`**:
the positive part `max (lam n) 0` of any even pole-free positive weight system converges
absolutely on `Re s > 1`. -/
theorem summable_posPart_div_rpow_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => max (lam n) 0 / (n : ℝ) ^ σ := by
  refine summable_div_rpow_of_block (fun n => le_max_right (lam n) 0)
    (B := 3 / 2 * (2 + |evenToeplitzConst|)) (j₀ := 1) hσ fun j _ => ?_
  have hpos := even_sum_posPart_Ioc_le_of_weilPositiveEvenPolar hpf (N := 2 ^ j) Nat.one_le_two_pow
  rw [show 2 * 2 ^ j = 2 ^ (j + 1) by ring] at hpos
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlog : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    nlinarith
  have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
  rw [hcast] at hpos
  have t : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) + evenToeplitzConst + 1 ≤
      (2 + |evenToeplitzConst|) * ((j : ℝ) + 1) := by
    nlinarith [le_abs_self evenToeplitzConst, abs_nonneg evenToeplitzConst]
  have hpos' := hpos.trans (mul_le_mul_of_nonneg_left t (by positivity))
  nlinarith

/-- **Absolute Convergence on `Re s > 1` for `WeilPositiveEvenPolar` Reduces to the Negative Part**. -/
theorem summable_abs_div_rpow_of_weilPositiveEvenPolar_of_negPart {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {σ : ℝ} (hσ : 1 < σ)
    (hneg : Summable fun n : ℕ => max (-lam n) 0 / (n : ℝ) ^ σ) :
    Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  refine ((summable_posPart_div_rpow_of_weilPositiveEvenPolar hpf hσ).add hneg).congr fun n => ?_
  rw [← add_div, abs_eq_max_zero_add_max_neg_zero]

/-- **Negative-Part Abel Rigidity on the Pole-Free Even Cone (`WeilPositiveEvenPolar`)**:
if `lam` is Weil-positive on even pole-free tests (`f̂(i/2) = 0`), and its negative part
`max (-lam n) 0` converges on `Re s > 1` and has no double pole at `s = 0`, then `lam` is
Weil-positive on all even tests at pole weight `1`, so RH holds and `lam = Λ` on `n ≥ 2`. -/
theorem riemannHypothesis_of_weilPositiveEvenPolar_of_negPart {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam)
    (hneg : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => max (-lam n) 0 / (n : ℝ) ^ σ)
    (hdp : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ),
      s * (s * oddDirichlet (fun n => max (-lam n) 0) s) ≤ ε) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ :=
    fun σ hσ => summable_abs_div_rpow_of_weilPositiveEvenPolar_of_negPart hpf hσ (hneg σ hσ)
  have hup := eventually_le_one_add_of_log_density_le hsl fun _ hε =>
    even_log_density_le_of_weilPositiveEvenPolar hpf hε
  have hdp' : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s) := by
    intro ε hε
    filter_upwards [self_mem_nhdsWithin, hdp ε hε] with s hs hds
    have hs' : 0 < s := hs
    have hle := neg_oddDirichlet_negPart_le (hsl (1 + s) (by linarith))
    have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hs'.le) hs'.le
    linarith
  exact weilPositiveEvenAt_one_iff.mp (weilPositiveEvenAt_one_of_real fun _ hg' hgc hge =>
    realWeil_nonneg_of_polar hpf hsl hup hdp' hg' hgc hge)

/-- **Pole-Free Even Rigidity Under Linear Dyadic Negative Part**:
if `lam` is Weil-positive on even pole-free tests (`f̂(i/2) = 0`) and
`∑_{N < n ≤ 2N} max (-lam n) 0 ≤ B N` for all `N ≥ 1`, then RH holds and `lam = Λ` on `n ≥ 2`. -/
theorem riemannHypothesis_of_weilPositiveEvenPolar_of_sum_negPart_Ioc_le {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {B : ℝ} (hB0 : 0 ≤ B)
    (hb : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Ioc N (2 * N), max (-lam n) 0 ≤ B * N) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine riemannHypothesis_of_weilPositiveEvenPolar_of_negPart hpf (fun σ hσ => ?_)
    (eventually_mul_mul_oddDirichlet_le_of_sum_Ioc_le (fun n => le_max_right _ _) hB0 hb)
  refine summable_div_rpow_of_block (fun n => le_max_right _ _) (B := B) (j₀ := 0) hσ fun j _ => ?_
  rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring]
  have h1 := hb (2 ^ j) Nat.one_le_two_pow
  rw [Nat.cast_pow, Nat.cast_ofNat] at h1
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have : (0 : ℝ) ≤ B * (2 : ℝ) ^ j := by positivity
  nlinarith

end RHTower.CHMDStage7

end
