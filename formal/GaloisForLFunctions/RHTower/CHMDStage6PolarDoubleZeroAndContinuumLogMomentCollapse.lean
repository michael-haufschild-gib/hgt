import GaloisForLFunctions.RHTower.CHMDStage5FourModeGaussCoercivityAndPolarCone
import GaloisForLFunctions.RHTower.EvenSectorPoleFreeBlindFarkas

/-!
# CHMD Stage 6: Second-Order Polar Zero, Continuum Double-Pole Collapse, and Quadratic Moment Sign Dichotomy

This module establishes the foundational **Stage 6** identities of the Causal Hyperbolic–Modular
Duality (CHMD) route, resolving the continuum double-pole obstruction and the even/odd quadratic
exponential moment dichotomy on the polar subspace (`∫ f(t) e^{±t/2} dt = 0`):

1. **Master 1D Fubini Factorization for `crossCorr` and Exponential Moments
   (`integral_crossCorr_eq_mul`, `integral_exp_mul_crossCorr_eq`,
   `integral_mul_exp_mul_crossCorr_eq`, `integral_sq_mul_exp_mul_crossCorr_eq`)**:
   Using `EF.paperFT_weilTest` at `z = 0`, we establish the exact 1D Fubini factorization
   `∫ u : ℝ, crossCorr A B u = (∫ t : ℝ, A t) * (∫ v : ℝ, B v)` and combine it with the pointwise
   exponential shift decompositions of `e^{cu} crossCorr X Y u`, `u e^{cu} crossCorr X Y u`, and
   `u^2 e^{cu} crossCorr X Y u` to factorize all zeroth-, first-, and second-order exponential
   moments of `crossCorr X Y`.

2. **Second-Order Zero at `±i/2` and Even/Odd Quadratic Exponential Moment Sign Dichotomy on Polar Tests
   (`integral_mul_exp_half_crossCorr_self_eq_zero`,
   `integral_sq_mul_exp_half_crossCorr_self_eq_of_polar`,
   `integral_sq_mul_exp_half_crossCorr_self_nonneg_of_even_polar`,
   `integral_sq_mul_exp_half_crossCorr_self_nonpos_of_odd_polar`)**:
   On every polar real test `f` (`∫ t, f(t) e^{±t/2} dt = 0`), both first-order exponential moments
   `∫ u, u e^{±u/2} crossCorr f f u = 0` vanish identically (`k̂_f = |f̂|^2` has a **double zero**
   at `±i/2`), and in the second-order exponential moment `∫ u, u^2 e^{u/2} crossCorr f f u` the
   boundary `t^2` terms vanish, leaving
   `-2 * (∫ t, t f(t) e^{t/2} dt) * (∫ v, v f(v) e^{-v/2} dv)`.
   - When `f` is **even polar** (`f(-t) = f(t)`), `t f(t)` is odd, so the two factors have opposite
     signs and `∫ u, u^2 e^{u/2} crossCorr f f u = +2 * (∫ t, t f(t) e^{t/2} dt)^2 ≥ 0` (midpoint
     convexity of `s ↦ ∫ e^{(1/2 + s)|u|} k_f(u) du`).
   - When `f` is **odd polar** (`f(-t) = -f(t)`), `t f(t)` is even, so the two factors have the same
     sign and `∫ u, u^2 e^{u/2} crossCorr f f u = -2 * (∫ t, t f(t) e^{t/2} dt)^2 ≤ 0` (midpoint
     concavity).

3. **The Continuum Double-Pole Collapse Theorem on Polar Tests
   (`abs_mul_exp_abs_half_eq`, `integral_abs_mul_exp_abs_half_crossCorr_self_eq_of_polar`)**:
   From the exact algebraic identity on `ℝ`:
   `|u| e^{|u|/2} = u e^{u/2} - u e^{-u/2} + |u| e^{-|u|/2} = 2 u sinh(u/2) + |u| e^{-|u|/2}`,
   and the vanishing of both `∫ u e^{±u/2} crossCorr f f u = 0` on polar tests, the exponentially
   growing continuum double-pole integral `∫ u : ℝ, |u| e^{|u|/2} crossCorr f f u` collapses
   identically to the **exponentially decaying** moment `∫ u : ℝ, |u| e^{-|u|/2} crossCorr f f u`!

4. **Exact $L^1$ Norm `∫_{ℝ} |u| e^{-|u|/2} du = 8` and Unconditional $L^2$ / 4-Mode Resolvent Bounds
   (`integral_Ioi_zero_mul_exp_neg_half`, `integral_abs_mul_exp_neg_abs_half`,
   `abs_integral_abs_mul_exp_abs_half_crossCorr_self_le_of_polar`,
   `seven_div_780_mul_abs_doublePole_le_markovArchRe_add_fourMode_gauss`)**:
   Evaluating `∫_0^∞ u e^{-u/2} du = 4` and `∫_{ℝ} |u| e^{-|u|/2} du = 8` gives the uniform $L^2$
   bound `|∫ u, |u| e^{|u|/2} crossCorr f f u| ≤ 8 ∫ f^2` on all polar tests, and combining with
   Stage 5's atom-free 4-mode Gauss coercivity (`42 / 585`) yields the unconditional bound
   `(7 / 780) * |∫ u, |u| e^{|u|/2} crossCorr f f u| ≤ markovArchRe k_f + fourModeGaussPairSum f`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate Convolution
open Zeta23

noncomputable section

namespace RHTower.CHMDStage6

open EvenSector OddSector WeilOneSided WeilPoleWeight LebesgueAtomWeil

/-! ## Section 1: Master 1D Fubini Factorization for `crossCorr` and Exponential Moments -/

theorem paperFT_ofReal_zero (f : ℝ → ℝ) :
    paperFT (fun u => (f u : ℂ)) 0 = ((∫ u : ℝ, f u : ℝ) : ℂ) := by
  unfold paperFT
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp

/-- **Master Integral Factorization for `crossCorr`**:
for any continuous compactly supported `A, B : ℝ → ℝ`,
`∫ u : ℝ, crossCorr A B u = (∫ t : ℝ, A t) * (∫ v : ℝ, B v)`. -/
theorem integral_crossCorr_eq_mul {A B : ℝ → ℝ} (hA : Continuous A) (hAc : HasCompactSupport A)
    (hB : Continuous B) (hBc : HasCompactSupport B) :
    ∫ u : ℝ, crossCorr A B u = (∫ t : ℝ, A t) * (∫ v : ℝ, B v) := by
  have hAC : Continuous fun u => (A u : ℂ) := Complex.continuous_ofReal.comp hA
  have hACc : HasCompactSupport fun u => (A u : ℂ) := hAc.comp_left Complex.ofReal_zero
  have hBC : Continuous fun u => (B u : ℂ) := Complex.continuous_ofReal.comp hB
  have hBCc : HasCompactSupport fun u => (B u : ℂ) := hBc.comp_left Complex.ofReal_zero
  have hk : EF.weilTest (fun u => (A u : ℂ)) (fun u => (B u : ℂ)) =
      fun u => (crossCorr A B u : ℂ) := by
    funext u; rw [weilTest_ofReal_ofReal_eq]; rfl
  have h1 := EF.paperFT_weilTest hAC hBC hACc hBCc 0
  rw [hk, map_zero, paperFT_ofReal_zero, paperFT_ofReal_zero, paperFT_ofReal_zero,
    Complex.conj_ofReal] at h1
  exact_mod_cast h1

/-- Expressing `crossCorr A B` as a real convolution `A ⋆ (B ∘ neg)`. -/
theorem crossCorr_eq_convolution_neg (A B : ℝ → ℝ) :
    crossCorr A B = A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun u => B (-u)) := by
  funext y
  unfold crossCorr
  simp only [convolution, ContinuousLinearMap.mul_apply']
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [show -(y - t) = t - y by ring]

/-- Continuity of `crossCorr A B` for continuous compactly supported `A, B`. -/
theorem continuous_crossCorr_of_hasCompactSupport {A B : ℝ → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hBc : HasCompactSupport B) :
    Continuous (crossCorr A B) := by
  rw [crossCorr_eq_convolution_neg]
  have hBn : Continuous fun u => B (-u) := hB.comp continuous_neg
  have hBnc : HasCompactSupport fun u => B (-u) := hBc.comp_homeomorph (Homeomorph.neg ℝ)
  exact hBnc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hA.locallyIntegrable hBn

/-- Compact support of `crossCorr A B` for compactly supported `A, B`. -/
theorem hasCompactSupport_crossCorr_of_hasCompactSupport {A B : ℝ → ℝ}
    (hAc : HasCompactSupport A) (hBc : HasCompactSupport B) :
    HasCompactSupport (crossCorr A B) := by
  rw [crossCorr_eq_convolution_neg]
  exact hAc.convolution (ContinuousLinearMap.mul ℝ ℝ)
    (hBc.comp_homeomorph (Homeomorph.neg ℝ))

/-- Integrability of `crossCorr A B` for continuous compactly supported `A, B`. -/
theorem integrable_crossCorr_of_hasCompactSupport {A B : ℝ → ℝ}
    (hA : Continuous A) (hAc : HasCompactSupport A)
    (hB : Continuous B) (hBc : HasCompactSupport B) :
    Integrable (crossCorr A B) :=
  (continuous_crossCorr_of_hasCompactSupport hA hB hBc).integrable_of_hasCompactSupport
    (hasCompactSupport_crossCorr_of_hasCompactSupport hAc hBc)

theorem hasCompactSupport_mul_exp {X : ℝ → ℝ} (hXc : HasCompactSupport X) (c : ℝ) :
    HasCompactSupport (fun t => X t * Real.exp (c * t)) :=
  hXc.mul_right

theorem hasCompactSupport_weight_mul_exp {X : ℝ → ℝ} (hXc : HasCompactSupport X)
    (w : ℝ → ℝ) (c : ℝ) :
    HasCompactSupport (fun t => w t * X t * Real.exp (c * t)) := by
  have h : (fun t => w t * X t * Real.exp (c * t)) = (w * X) * (fun t => Real.exp (c * t)) := rfl
  rw [h]
  exact (hXc.mul_left).mul_right

/-- **Zeroth-Order Pointwise Exponential Shift Identity for `crossCorr`**:
`Real.exp (c * u) * crossCorr X Y u = crossCorr (fun t => X t * Real.exp (c * t)) (fun v => Y v * Real.exp (-c * v)) u`. -/
theorem exp_mul_crossCorr_eq (X Y : ℝ → ℝ) (c u : ℝ) :
    Real.exp (c * u) * crossCorr X Y u =
      crossCorr (fun t => X t * Real.exp (c * t)) (fun v => Y v * Real.exp (-c * v)) u := by
  unfold crossCorr
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  have he : Real.exp (c * t) * Real.exp (-c * (t - u)) = Real.exp (c * u) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (c * u) * (X t * Y (t - u))
      = X t * Y (t - u) * (Real.exp (c * t) * Real.exp (-c * (t - u))) := by rw [he]; ring
    _ = X t * Real.exp (c * t) * (Y (t - u) * Real.exp (-c * (t - u))) := by ring

/-- **First-Order Pointwise Exponential Shift Identity for `crossCorr`**:
`u * Real.exp (c * u) * crossCorr X Y u = crossCorr (fun t => t * X t * Real.exp (c * t)) (fun v => Y v * Real.exp (-c * v)) u - crossCorr (fun t => X t * Real.exp (c * t)) (fun v => v * Y v * Real.exp (-c * v)) u`. -/
theorem mul_exp_mul_crossCorr_eq {X Y : ℝ → ℝ} (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (c u : ℝ) :
    u * Real.exp (c * u) * crossCorr X Y u =
      crossCorr (fun t => t * X t * Real.exp (c * t)) (fun v => Y v * Real.exp (-c * v)) u -
        crossCorr (fun t => X t * Real.exp (c * t)) (fun v => v * Y v * Real.exp (-c * v)) u := by
  unfold crossCorr
  have h1 : Integrable fun t =>
      (t * X t * Real.exp (c * t)) * (Y (t - u) * Real.exp (-c * (t - u))) :=
    integrable_translate_prod (X := fun t => t * X t * Real.exp (c * t))
      (Y := fun v => Y v * Real.exp (-c * v)) (by fun_prop)
      (hasCompactSupport_weight_mul_exp hXc id c) (by fun_prop) u
  have h2 : Integrable fun t =>
      (X t * Real.exp (c * t)) * ((t - u) * Y (t - u) * Real.exp (-c * (t - u))) :=
    integrable_translate_prod (X := fun t => X t * Real.exp (c * t))
      (Y := fun v => v * Y v * Real.exp (-c * v)) (by fun_prop)
      (hasCompactSupport_mul_exp hXc c) (by fun_prop) u
  rw [← integral_sub h1 h2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  have he : Real.exp (c * t) * Real.exp (-c * (t - u)) = Real.exp (c * u) := by
    rw [← Real.exp_add]; congr 1; ring
  calc u * Real.exp (c * u) * (X t * Y (t - u))
      = (t - (t - u)) * X t * Y (t - u) * (Real.exp (c * t) * Real.exp (-c * (t - u))) := by
        rw [he]; ring
    _ = t * X t * Real.exp (c * t) * (Y (t - u) * Real.exp (-c * (t - u))) -
        X t * Real.exp (c * t) * ((t - u) * Y (t - u) * Real.exp (-c * (t - u))) := by ring

/-- **Second-Order Pointwise Exponential Shift Identity for `crossCorr`**:
`u ^ 2 * Real.exp (c * u) * crossCorr X Y u` decomposes into three shifted `crossCorr` terms. -/
theorem sq_mul_exp_mul_crossCorr_eq {X Y : ℝ → ℝ} (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (c u : ℝ) :
    u ^ 2 * Real.exp (c * u) * crossCorr X Y u =
      crossCorr (fun t => t ^ 2 * X t * Real.exp (c * t)) (fun v => Y v * Real.exp (-c * v)) u -
        2 * crossCorr (fun t => t * X t * Real.exp (c * t))
          (fun v => v * Y v * Real.exp (-c * v)) u +
        crossCorr (fun t => X t * Real.exp (c * t))
          (fun v => v ^ 2 * Y v * Real.exp (-c * v)) u := by
  unfold crossCorr
  dsimp only
  have h1 : Integrable fun t =>
      (t ^ 2 * X t * Real.exp (c * t)) * (Y (t - u) * Real.exp (-c * (t - u))) :=
    integrable_translate_prod (X := fun t => t ^ 2 * X t * Real.exp (c * t))
      (Y := fun v => Y v * Real.exp (-c * v)) (by fun_prop)
      (hasCompactSupport_weight_mul_exp hXc (fun t => t ^ 2) c) (by fun_prop) u
  have h2 : Integrable fun t =>
      (t * X t * Real.exp (c * t)) * ((t - u) * Y (t - u) * Real.exp (-c * (t - u))) :=
    integrable_translate_prod (X := fun t => t * X t * Real.exp (c * t))
      (Y := fun v => v * Y v * Real.exp (-c * v)) (by fun_prop)
      (hasCompactSupport_weight_mul_exp hXc id c) (by fun_prop) u
  have h12 : Integrable fun t =>
      t ^ 2 * X t * Real.exp (c * t) * (Y (t - u) * Real.exp (-c * (t - u))) -
        2 * (t * X t * Real.exp (c * t) * ((t - u) * Y (t - u) * Real.exp (-c * (t - u)))) :=
    h1.sub (h2.const_mul 2)
  have h3 : Integrable fun t =>
      (X t * Real.exp (c * t)) * ((t - u) ^ 2 * Y (t - u) * Real.exp (-c * (t - u))) :=
    integrable_translate_prod (X := fun t => X t * Real.exp (c * t))
      (Y := fun v => v ^ 2 * Y v * Real.exp (-c * v)) (by fun_prop)
      (hasCompactSupport_mul_exp hXc c) (by fun_prop) u
  rw [← integral_const_mul 2, ← integral_sub h1 (h2.const_mul 2),
    ← integral_add h12 h3, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  have he : Real.exp (c * t) * Real.exp (-c * (t - u)) = Real.exp (c * u) := by
    rw [← Real.exp_add]; congr 1; ring
  calc u ^ 2 * Real.exp (c * u) * (X t * Y (t - u))
      = (t - (t - u)) ^ 2 * X t * Y (t - u) * (Real.exp (c * t) * Real.exp (-c * (t - u))) := by
        rw [he]; ring
    _ = t ^ 2 * X t * Real.exp (c * t) * (Y (t - u) * Real.exp (-c * (t - u))) -
        2 * (t * X t * Real.exp (c * t) * ((t - u) * Y (t - u) * Real.exp (-c * (t - u)))) +
        X t * Real.exp (c * t) * ((t - u) ^ 2 * Y (t - u) * Real.exp (-c * (t - u))) := by ring

/-! ## Section 2: Integrated Exponential Moments of `crossCorr` and Double Zero on Polar Tests -/

/-- **Zeroth-Order Exponential Moment Factorization**:
`∫ u : ℝ, Real.exp (c * u) * crossCorr X Y u = (∫ t : ℝ, X t * Real.exp (c * t)) * (∫ v : ℝ, Y v * Real.exp (-c * v))`. -/
theorem integral_exp_mul_crossCorr_eq {X Y : ℝ → ℝ}
    (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (hYc : HasCompactSupport Y) (c : ℝ) :
    ∫ u : ℝ, Real.exp (c * u) * crossCorr X Y u =
      (∫ t : ℝ, X t * Real.exp (c * t)) * (∫ v : ℝ, Y v * Real.exp (-c * v)) := by
  simp_rw [exp_mul_crossCorr_eq X Y c]
  exact integral_crossCorr_eq_mul (A := fun t => X t * Real.exp (c * t))
    (B := fun v => Y v * Real.exp (-c * v))
    (by fun_prop) (hasCompactSupport_mul_exp hXc c)
    (by fun_prop) (hasCompactSupport_mul_exp hYc (-c))

/-- **First-Order Exponential Moment Factorization**:
`∫ u : ℝ, u * Real.exp (c * u) * crossCorr X Y u = (∫ t, t * X t * Real.exp (c * t)) * (∫ v, Y v * Real.exp (-c * v)) - (∫ t, X t * Real.exp (c * t)) * (∫ v, v * Y v * Real.exp (-c * v))`. -/
theorem integral_mul_exp_mul_crossCorr_eq {X Y : ℝ → ℝ}
    (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (hYc : HasCompactSupport Y) (c : ℝ) :
    ∫ u : ℝ, u * Real.exp (c * u) * crossCorr X Y u =
      (∫ t : ℝ, t * X t * Real.exp (c * t)) * (∫ v : ℝ, Y v * Real.exp (-c * v)) -
        (∫ t : ℝ, X t * Real.exp (c * t)) * (∫ v : ℝ, v * Y v * Real.exp (-c * v)) := by
  simp_rw [mul_exp_mul_crossCorr_eq hX hXc hY c]
  have hcX0 := hasCompactSupport_mul_exp hXc c
  have hcX1 := hasCompactSupport_weight_mul_exp hXc id c
  have hcY0 := hasCompactSupport_mul_exp hYc (-c)
  have hcY1 := hasCompactSupport_weight_mul_exp hYc id (-c)
  have hi1 := integrable_crossCorr_of_hasCompactSupport
    (A := fun t => t * X t * Real.exp (c * t)) (B := fun v => Y v * Real.exp (-c * v))
    (by fun_prop) hcX1 (by fun_prop) hcY0
  have hi2 := integrable_crossCorr_of_hasCompactSupport
    (A := fun t => X t * Real.exp (c * t)) (B := fun v => v * Y v * Real.exp (-c * v))
    (by fun_prop) hcX0 (by fun_prop) hcY1
  rw [integral_sub hi1 hi2,
    integral_crossCorr_eq_mul (A := fun t => t * X t * Real.exp (c * t))
      (B := fun v => Y v * Real.exp (-c * v)) (by fun_prop) hcX1 (by fun_prop) hcY0,
    integral_crossCorr_eq_mul (A := fun t => X t * Real.exp (c * t))
      (B := fun v => v * Y v * Real.exp (-c * v)) (by fun_prop) hcX0 (by fun_prop) hcY1]

/-- **Second-Order Exponential Moment Factorization**:
`∫ u : ℝ, u ^ 2 * Real.exp (c * u) * crossCorr X Y u` factors into zeroth, first, and second moments. -/
theorem integral_sq_mul_exp_mul_crossCorr_eq {X Y : ℝ → ℝ}
    (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (hYc : HasCompactSupport Y) (c : ℝ) :
    ∫ u : ℝ, u ^ 2 * Real.exp (c * u) * crossCorr X Y u =
      (∫ t : ℝ, t ^ 2 * X t * Real.exp (c * t)) * (∫ v : ℝ, Y v * Real.exp (-c * v)) -
        2 * ((∫ t : ℝ, t * X t * Real.exp (c * t)) * (∫ v : ℝ, v * Y v * Real.exp (-c * v))) +
        (∫ t : ℝ, X t * Real.exp (c * t)) * (∫ v : ℝ, v ^ 2 * Y v * Real.exp (-c * v)) := by
  simp_rw [sq_mul_exp_mul_crossCorr_eq hX hXc hY c]
  have hcX0 := hasCompactSupport_mul_exp hXc c
  have hcX1 := hasCompactSupport_weight_mul_exp hXc id c
  have hcX2 := hasCompactSupport_weight_mul_exp hXc (fun t => t ^ 2) c
  have hcY0 := hasCompactSupport_mul_exp hYc (-c)
  have hcY1 := hasCompactSupport_weight_mul_exp hYc id (-c)
  have hcY2 := hasCompactSupport_weight_mul_exp hYc (fun v => v ^ 2) (-c)
  have hi1 := integrable_crossCorr_of_hasCompactSupport
    (A := fun t => t ^ 2 * X t * Real.exp (c * t)) (B := fun v => Y v * Real.exp (-c * v))
    (by fun_prop) hcX2 (by fun_prop) hcY0
  have hi2 := integrable_crossCorr_of_hasCompactSupport
    (A := fun t => t * X t * Real.exp (c * t)) (B := fun v => v * Y v * Real.exp (-c * v))
    (by fun_prop) hcX1 (by fun_prop) hcY1
  have hi12 : Integrable fun u =>
      crossCorr (fun t => t ^ 2 * X t * Real.exp (c * t)) (fun v => Y v * Real.exp (-c * v)) u -
        2 * crossCorr (fun t => t * X t * Real.exp (c * t)) (fun v => v * Y v * Real.exp (-c * v)) u :=
    hi1.sub (hi2.const_mul 2)
  have hi3 := integrable_crossCorr_of_hasCompactSupport
    (A := fun t => X t * Real.exp (c * t)) (B := fun v => v ^ 2 * Y v * Real.exp (-c * v))
    (by fun_prop) hcX0 (by fun_prop) hcY2
  rw [integral_add hi12 hi3, integral_sub hi1 (hi2.const_mul 2),
    integral_const_mul,
    integral_crossCorr_eq_mul (A := fun t => t ^ 2 * X t * Real.exp (c * t))
      (B := fun v => Y v * Real.exp (-c * v)) (by fun_prop) hcX2 (by fun_prop) hcY0,
    integral_crossCorr_eq_mul (A := fun t => t * X t * Real.exp (c * t))
      (B := fun v => v * Y v * Real.exp (-c * v)) (by fun_prop) hcX1 (by fun_prop) hcY1,
    integral_crossCorr_eq_mul (A := fun t => X t * Real.exp (c * t))
      (B := fun v => v ^ 2 * Y v * Real.exp (-c * v)) (by fun_prop) hcX0 (by fun_prop) hcY2]

/-- **First-Order Exponential Moment Vanishing on Polar Tests (`c = 1/2` and `c = -1/2`)**:
for any polar real test `f` (`∫ t, f t * exp(t/2) = 0` and `∫ t, f t * exp(-t/2) = 0`),
both first-order exponential moments of `crossCorr f f` at `±1/2` vanish identically! -/
theorem integral_mul_exp_half_crossCorr_self_eq_zero {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hp : ∫ t : ℝ, f t * Real.exp (t / 2) = 0)
    (hm : ∫ t : ℝ, f t * Real.exp (-t / 2) = 0) :
    (∫ u : ℝ, u * Real.exp (u / 2) * crossCorr f f u = 0) ∧
      (∫ u : ℝ, u * Real.exp (-u / 2) * crossCorr f f u = 0) := by
  have h1 := integral_mul_exp_mul_crossCorr_eq hf hfc hf hfc (1 / 2)
  have h2 := integral_mul_exp_mul_crossCorr_eq hf hfc hf hfc (-(1 / 2))
  have e1 : (fun u : ℝ => u * Real.exp ((1 / 2 : ℝ) * u) * crossCorr f f u) =
      fun u => u * Real.exp (u / 2) * crossCorr f f u := by
    funext u; rw [show (1 / 2 : ℝ) * u = u / 2 by ring]
  have e2 : (fun u : ℝ => u * Real.exp (-(1 / 2 : ℝ) * u) * crossCorr f f u) =
      fun u => u * Real.exp (-u / 2) * crossCorr f f u := by
    funext u; rw [show -(1 / 2 : ℝ) * u = -u / 2 by ring]
  have ep : (fun t : ℝ => f t * Real.exp ((1 / 2 : ℝ) * t)) =
      fun t => f t * Real.exp (t / 2) := by
    funext t; rw [show (1 / 2 : ℝ) * t = t / 2 by ring]
  have em : (fun t : ℝ => f t * Real.exp (-(1 / 2 : ℝ) * t)) =
      fun t => f t * Real.exp (-t / 2) := by
    funext t; rw [show -(1 / 2 : ℝ) * t = -t / 2 by ring]
  have em' : (fun t : ℝ => f t * Real.exp (- -(1 / 2 : ℝ) * t)) =
      fun t => f t * Real.exp (t / 2) := by
    funext t; rw [show - -(1 / 2 : ℝ) * t = t / 2 by ring]
  rw [e1, ep, em, hp, hm] at h1
  rw [e2, em, em', hp, hm] at h2
  exact ⟨by linarith, by linarith⟩

/-- **Second-Order Exponential Moment on Polar Tests (`c = 1/2`)**:
for any polar real test `f`, the boundary `t²` terms vanish and only the pure first-moment product
`-2 * (∫ t, t * f t * exp(t/2)) * (∫ v, v * f v * exp(-v/2))` survives. -/
theorem integral_sq_mul_exp_half_crossCorr_self_eq_of_polar {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hp : ∫ t : ℝ, f t * Real.exp (t / 2) = 0)
    (hm : ∫ t : ℝ, f t * Real.exp (-t / 2) = 0) :
    ∫ u : ℝ, u ^ 2 * Real.exp (u / 2) * crossCorr f f u =
      -2 * ((∫ t : ℝ, t * f t * Real.exp (t / 2)) * (∫ v : ℝ, v * f v * Real.exp (-v / 2))) := by
  have h := integral_sq_mul_exp_mul_crossCorr_eq hf hfc hf hfc (1 / 2)
  have eu : (fun u : ℝ => u ^ 2 * Real.exp ((1 / 2 : ℝ) * u) * crossCorr f f u) =
      fun u => u ^ 2 * Real.exp (u / 2) * crossCorr f f u := by
    funext u; rw [show (1 / 2 : ℝ) * u = u / 2 by ring]
  have ep : (fun t : ℝ => f t * Real.exp ((1 / 2 : ℝ) * t)) =
      fun t => f t * Real.exp (t / 2) := by
    funext t; rw [show (1 / 2 : ℝ) * t = t / 2 by ring]
  have em : (fun t : ℝ => f t * Real.exp (-(1 / 2 : ℝ) * t)) =
      fun t => f t * Real.exp (-t / 2) := by
    funext t; rw [show -(1 / 2 : ℝ) * t = -t / 2 by ring]
  have ep1 : (fun t : ℝ => t * f t * Real.exp ((1 / 2 : ℝ) * t)) =
      fun t => t * f t * Real.exp (t / 2) := by
    funext t; rw [show (1 / 2 : ℝ) * t = t / 2 by ring]
  have em1 : (fun v : ℝ => v * f v * Real.exp (-(1 / 2 : ℝ) * v)) =
      fun v => v * f v * Real.exp (-v / 2) := by
    funext v; rw [show -(1 / 2 : ℝ) * v = -v / 2 by ring]
  rw [eu, ep, em, ep1, em1, hp, hm] at h
  linarith

/-- **Quadratic Exponential Moment Sign Dichotomy — Even Polar Case (`≥ 0`)**:
for any even polar real test `f` (`f (-t) = f t`, `∫ t, f t * exp(±t/2) = 0`),
`∫ u : ℝ, u ^ 2 * Real.exp (u / 2) * crossCorr f f u = 2 * (∫ t : ℝ, t * f t * Real.exp (t / 2)) ^ 2 ≥ 0`. -/
theorem integral_sq_mul_exp_half_crossCorr_self_eq_of_even_polar {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (heven : ∀ t : ℝ, f (-t) = f t)
    (hp : ∫ t : ℝ, f t * Real.exp (t / 2) = 0)
    (hm : ∫ t : ℝ, f t * Real.exp (-t / 2) = 0) :
    ∫ u : ℝ, u ^ 2 * Real.exp (u / 2) * crossCorr f f u =
      2 * (∫ t : ℝ, t * f t * Real.exp (t / 2)) ^ 2 := by
  rw [integral_sq_mul_exp_half_crossCorr_self_eq_of_polar hf hfc hp hm]
  have hneg : ∫ v : ℝ, v * f v * Real.exp (-v / 2) =
      -∫ t : ℝ, t * f t * Real.exp (t / 2) := by
    rw [← integral_neg, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [heven t, show - -t / 2 = t / 2 by ring]
    ring
  rw [hneg]
  ring

theorem integral_sq_mul_exp_half_crossCorr_self_nonneg_of_even_polar {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (heven : ∀ t : ℝ, f (-t) = f t)
    (hp : ∫ t : ℝ, f t * Real.exp (t / 2) = 0)
    (hm : ∫ t : ℝ, f t * Real.exp (-t / 2) = 0) :
    0 ≤ ∫ u : ℝ, u ^ 2 * Real.exp (u / 2) * crossCorr f f u := by
  rw [integral_sq_mul_exp_half_crossCorr_self_eq_of_even_polar hf hfc heven hp hm]
  positivity

/-- **Quadratic Exponential Moment Sign Dichotomy — Odd Polar Case (`≤ 0`)**:
for any odd polar real test `f` (`f (-t) = -f t`, `∫ t, f t * exp(±t/2) = 0`),
`∫ u : ℝ, u ^ 2 * Real.exp (u / 2) * crossCorr f f u = -2 * (∫ t : ℝ, t * f t * Real.exp (t / 2)) ^ 2 ≤ 0`. -/
theorem integral_sq_mul_exp_half_crossCorr_self_eq_of_odd_polar {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hodd : ∀ t : ℝ, f (-t) = -f t)
    (hp : ∫ t : ℝ, f t * Real.exp (t / 2) = 0)
    (hm : ∫ t : ℝ, f t * Real.exp (-t / 2) = 0) :
    ∫ u : ℝ, u ^ 2 * Real.exp (u / 2) * crossCorr f f u =
      -2 * (∫ t : ℝ, t * f t * Real.exp (t / 2)) ^ 2 := by
  rw [integral_sq_mul_exp_half_crossCorr_self_eq_of_polar hf hfc hp hm]
  have hneg : ∫ v : ℝ, v * f v * Real.exp (-v / 2) =
      ∫ t : ℝ, t * f t * Real.exp (t / 2) := by
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hodd t, show - -t / 2 = t / 2 by ring]
    ring
  rw [hneg]
  ring

theorem integral_sq_mul_exp_half_crossCorr_self_nonpos_of_odd_polar {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hodd : ∀ t : ℝ, f (-t) = -f t)
    (hp : ∫ t : ℝ, f t * Real.exp (t / 2) = 0)
    (hm : ∫ t : ℝ, f t * Real.exp (-t / 2) = 0) :
    ∫ u : ℝ, u ^ 2 * Real.exp (u / 2) * crossCorr f f u ≤ 0 := by
  rw [integral_sq_mul_exp_half_crossCorr_self_eq_of_odd_polar hf hfc hodd hp hm]
  nlinarith [sq_nonneg (∫ t : ℝ, t * f t * Real.exp (t / 2))]

/-! ## Section 3: Exact Continuum Double-Pole Collapse on Polar Tests -/

/-- **Exact Opposite-Parity Algebraic Identity for the Double-Pole Kernel `|u| * exp(|u| / 2)`**:
for all `u : ℝ`,
`|u| * Real.exp (|u| / 2) = u * Real.exp (u / 2) - u * Real.exp (-u / 2) + |u| * Real.exp (-|u| / 2)`. -/
theorem abs_mul_exp_abs_half_eq (u : ℝ) :
    |u| * Real.exp (|u| / 2) =
      u * Real.exp (u / 2) - u * Real.exp (-u / 2) + |u| * Real.exp (-|u| / 2) := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]; ring
  · rw [abs_of_nonpos hu, show - -u / 2 = u / 2 by ring]; ring

/-- Hyperbolic form of `abs_mul_exp_abs_half_eq`:
`|u| * Real.exp (|u| / 2) = 2 * u * Real.sinh (u / 2) + |u| * Real.exp (-|u| / 2)`. -/
theorem abs_mul_exp_abs_half_eq_two_mul_sinh_add (u : ℝ) :
    |u| * Real.exp (|u| / 2) =
      2 * u * Real.sinh (u / 2) + |u| * Real.exp (-|u| / 2) := by
  rw [abs_mul_exp_abs_half_eq, Real.sinh_eq, show -(u / 2) = -u / 2 by ring]
  ring

/-- **Exact Decomposition of the Growing Double-Pole Integral `∫ |u| e^{|u|/2} k(u) du`**:
for any continuous compactly supported `k : ℝ → ℝ`,
`∫ u : ℝ, |u| * Real.exp (|u| / 2) * k u = (∫ u : ℝ, u * Real.exp (u / 2) * k u) - (∫ u : ℝ, u * Real.exp (-u / 2) * k u) + ∫ u : ℝ, |u| * Real.exp (-|u| / 2) * k u`. -/
theorem integral_abs_mul_exp_abs_half_eq {k : ℝ → ℝ}
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    ∫ u : ℝ, |u| * Real.exp (|u| / 2) * k u =
      (∫ u : ℝ, u * Real.exp (u / 2) * k u) -
        (∫ u : ℝ, u * Real.exp (-u / 2) * k u) +
        ∫ u : ℝ, |u| * Real.exp (-|u| / 2) * k u := by
  have hi : ∀ g : ℝ → ℝ, Continuous g → Integrable fun u => g u * k u := fun g hg =>
    (hg.mul hk).integrable_of_hasCompactSupport hkc.mul_left
  have h1 : Integrable fun u : ℝ => u * Real.exp (u / 2) * k u := hi _ (by fun_prop)
  have h2 : Integrable fun u : ℝ => u * Real.exp (-u / 2) * k u := hi _ (by fun_prop)
  have h3 : Integrable fun u : ℝ => |u| * Real.exp (-|u| / 2) * k u := hi _ (by fun_prop)
  have hcongr : (fun u : ℝ => |u| * Real.exp (|u| / 2) * k u) =
      fun u => (u * Real.exp (u / 2) * k u - u * Real.exp (-u / 2) * k u) +
        |u| * Real.exp (-|u| / 2) * k u := by
    funext u; rw [abs_mul_exp_abs_half_eq]; ring
  rw [hcongr,
    integral_add (f := fun u => u * Real.exp (u / 2) * k u - u * Real.exp (-u / 2) * k u)
      (g := fun u => |u| * Real.exp (-|u| / 2) * k u) (h1.sub h2) h3,
    integral_sub (f := fun u => u * Real.exp (u / 2) * k u)
      (g := fun u => u * Real.exp (-u / 2) * k u) h1 h2]

/-- **The Continuum Double-Pole Collapse Theorem on Polar Tests**:
for every polar real test `f` (`∫ t, f t * exp(t/2) = 0` and `∫ t, f t * exp(-t/2) = 0`),
the growing continuum double-pole integral `∫ u, |u| * exp(|u| / 2) * crossCorr f f u`
collapses identically to the exponentially decaying moment
`∫ u, |u| * exp(-|u| / 2) * crossCorr f f u`! -/
theorem integral_abs_mul_exp_abs_half_crossCorr_self_eq_of_polar {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hp : ∫ t : ℝ, f t * Real.exp (t / 2) = 0)
    (hm : ∫ t : ℝ, f t * Real.exp (-t / 2) = 0) :
    ∫ u : ℝ, |u| * Real.exp (|u| / 2) * crossCorr f f u =
      ∫ u : ℝ, |u| * Real.exp (-|u| / 2) * crossCorr f f u := by
  rw [integral_abs_mul_exp_abs_half_eq (continuous_crossCorr_of_hasCompactSupport hf hf hfc)
    (hasCompactSupport_crossCorr_of_hasCompactSupport hfc hfc)]
  obtain ⟨h1, h2⟩ := integral_mul_exp_half_crossCorr_self_eq_zero hf hfc hp hm
  rw [h1, h2]
  ring

/-! ## Section 4: Exact $L^1$ Norm `∫ |u| e^{-|u|/2} du = 8` and Unconditional $L^2$ / 4-Mode Resolvent Bounds -/

/-- Pointwise exponential bound `|u| * Real.exp (-|u| / 2) ≤ 4 * Real.exp (-|u| / 4)` for all `u : ℝ`. -/
theorem abs_mul_exp_neg_abs_half_le (u : ℝ) :
    |u| * Real.exp (-|u| / 2) ≤ 4 * Real.exp (-|u| / 4) := by
  have h1 := Real.add_one_le_exp (|u| / 4)
  have h2 : |u| / 4 ≤ Real.exp (|u| / 4) := by linarith
  have h3 : Real.exp (|u| / 4) * Real.exp (-|u| / 2) = Real.exp (-|u| / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < Real.exp (-|u| / 2) := Real.exp_pos _
  calc |u| * Real.exp (-|u| / 2)
      = 4 * (|u| / 4) * Real.exp (-|u| / 2) := by ring
    _ ≤ 4 * Real.exp (|u| / 4) * Real.exp (-|u| / 2) := by
      nlinarith [mul_le_mul_of_nonneg_right h2 hpos.le]
    _ = 4 * Real.exp (-|u| / 4) := by rw [mul_assoc, h3]

/-- Integrability of `u * Real.exp (-u / 2)` on `Ioi 0`. -/
theorem integrableOn_mul_exp_neg_half_Ioi :
    IntegrableOn (fun u : ℝ => u * Real.exp (-u / 2)) (Ioi 0) := by
  have hdom : IntegrableOn (fun u : ℝ => 4 * Real.exp (-(1 / 4 : ℝ) * u)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0) 0).const_mul 4
  refine hdom.mono' (by fun_prop)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_))
  have hu0 : (0 : ℝ) < u := hu
  rw [Real.norm_of_nonneg (by positivity)]
  have hle := abs_mul_exp_neg_abs_half_le u
  rwa [abs_of_pos hu0, show -u / 4 = -(1 / 4 : ℝ) * u by ring] at hle

/-- Exact antiderivative of `u * Real.exp (-u / 2)`:
`HasDerivAt (fun u => -(2 * u + 4) * Real.exp (-u / 2)) (u * Real.exp (-u / 2)) u`. -/
theorem hasDerivAt_neg_two_mul_add_four_exp_neg_half (u : ℝ) :
    HasDerivAt (fun x : ℝ => -(2 * x + 4) * Real.exp (-x / 2))
      (u * Real.exp (-u / 2)) u := by
  have ha : HasDerivAt (fun x : ℝ => 2 * x + 4) (2 * 1) u :=
    ((hasDerivAt_id u).const_mul 2).add_const 4
  have hneg : HasDerivAt (fun x : ℝ => -(2 * x + 4)) (-(2 * 1)) u := ha.neg
  have h1 : HasDerivAt (fun x : ℝ => -(2 * x + 4)) (-2) u :=
    hneg.congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x / 2)) (Real.exp (-u / 2) * (-1 / 2)) u := by
    have hd : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) u := by
      simpa [neg_div] using ((hasDerivAt_id u).neg).div_const 2
    exact hd.exp
  exact (h1.mul h2).congr_deriv (by ring)

/-- **Exact Half-Line Moment `∫_{0}^∞ u e^{-u/2} du = 4`**. -/
theorem integral_Ioi_zero_mul_exp_neg_half :
    ∫ u in Ioi (0 : ℝ), u * Real.exp (-u / 2) = 4 := by
  set F : ℝ → ℝ := fun x => -(2 * x + 4) * Real.exp (-x / 2) with hF
  have hcont : ContinuousWithinAt F (Ici 0) 0 := (by fun_prop : Continuous F).continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (x * Real.exp (-x / 2)) x :=
    fun x _ => hasDerivAt_neg_two_mul_add_four_exp_neg_half x
  have htend : Tendsto F atTop (𝓝 0) := by
    have hdom : Tendsto (fun x : ℝ => 12 * Real.exp (-x / 4)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun x : ℝ => x / 4) atTop atTop :=
        tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4)
      have h1 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h0).const_mul 12
      simpa [neg_div] using h1
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hle := abs_mul_exp_neg_abs_half_le x
    rw [abs_of_nonneg hx] at hle
    have h4 : 4 * Real.exp (-x / 2) ≤ 4 * Real.exp (-x / 4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    have heq : ‖F x‖ = 2 * (x * Real.exp (-x / 2)) + 4 * Real.exp (-x / 2) := by
      rw [hF, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * x + 4), abs_of_pos (Real.exp_pos _)]
      ring
    rw [heq]
    linarith
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv integrableOn_mul_exp_neg_half_Ioi htend]
  simp [hF]

/-- Integrability of `|u| * Real.exp (-|u| / 2)` on `ℝ`. -/
theorem integrable_abs_mul_exp_neg_abs_half :
    Integrable fun u : ℝ => |u| * Real.exp (-|u| / 2) := by
  have hpos : IntegrableOn (fun u : ℝ => |u| * Real.exp (-|u| / 2)) (Ioi 0) := by
    refine integrableOn_mul_exp_neg_half_Ioi.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu' : 0 < u := hu
    rw [abs_of_pos hu']
  have hneg : IntegrableOn (fun u : ℝ => |u| * Real.exp (-|u| / 2)) (Iic 0) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi] at hpos
    have hcomp : IntegrableOn (fun u : ℝ => |-u| * Real.exp (-|-u| / 2)) (Iic 0) := by
      have := hpos.comp_neg
      simpa using this
    refine hcomp.congr_fun (fun u _ => by simp) measurableSet_Iic
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hneg.union hpos

/-- **Exact Full-Line Moment `∫_{ℝ} |u| e^{-|u|/2} du = 8`**. -/
theorem integral_abs_mul_exp_neg_abs_half :
    ∫ u : ℝ, |u| * Real.exp (-|u| / 2) = 8 := by
  have hi := integrable_abs_mul_exp_neg_abs_half
  have hneg_eq : ∫ x in Iic (0 : ℝ), |x| * Real.exp (-|x| / 2) =
      ∫ x in Ioi (0 : ℝ), |x| * Real.exp (-|x| / 2) := by
    have h := integral_comp_neg_Ioi (c := (0 : ℝ)) (f := fun x : ℝ => |x| * Real.exp (-|x| / 2))
    simp only [neg_zero, abs_neg] at h
    exact h.symm
  have h2 : ∫ u in Ioi (0 : ℝ), |u| * Real.exp (-|u| / 2) =
      ∫ u in Ioi (0 : ℝ), u * Real.exp (-u / 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : 0 < u := hu
    rw [abs_of_pos hu']
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hi.integrableOn hi.integrableOn,
    hneg_eq, h2, integral_Ioi_zero_mul_exp_neg_half]
  norm_num

/-- Uniform $L^2$ bound `|crossCorr f f u| ≤ ∫ t : ℝ, f t ^ 2` for all `u : ℝ`. -/
theorem abs_crossCorr_self_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (u : ℝ) :
    |crossCorr f f u| ≤ ∫ t : ℝ, f t ^ 2 := by
  unfold crossCorr
  have hcs : HasCompactSupport fun t : ℝ => f t ^ 2 := by
    have heq : (fun t : ℝ => f t ^ 2) = f * f := funext fun t => sq (f t)
    rw [heq]
    exact hfc.mul_right
  have hi1 : Integrable fun t : ℝ => f t ^ 2 :=
    (hf.pow 2).integrable_of_hasCompactSupport hcs
  have hi2 : Integrable fun t : ℝ => f (t - u) ^ 2 := hi1.comp_sub_right u
  have hip : Integrable fun t : ℝ => f t * f (t - u) :=
    integrable_translate_prod hf hfc hf u
  calc |∫ t : ℝ, f t * f (t - u)|
      ≤ ∫ t : ℝ, |f t * f (t - u)| := abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, (f t ^ 2 + f (t - u) ^ 2) / 2 := by
        refine integral_mono hip.abs ((hi1.add hi2).div_const 2) fun t => ?_
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (f t + f (t - u)), sq_nonneg (f t - f (t - u))]
    _ = ∫ t : ℝ, f t ^ 2 := by
        rw [integral_div, integral_add hi1 hi2, integral_sub_right_eq_self (fun t : ℝ => f t ^ 2) u]
        ring

/-- **Unconditional $L^2$ Bound on the Decaying Double-Pole Moment**:
for any continuous compactly supported `f : ℝ → ℝ`,
`|∫ u : ℝ, |u| * Real.exp (-|u| / 2) * crossCorr f f u| ≤ 8 * ∫ t : ℝ, f t ^ 2`. -/
theorem abs_integral_abs_mul_exp_neg_abs_half_crossCorr_self_le {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    |∫ u : ℝ, |u| * Real.exp (-|u| / 2) * crossCorr f f u| ≤
      8 * ∫ t : ℝ, f t ^ 2 := by
  have hi : Integrable fun u : ℝ => |u| * Real.exp (-|u| / 2) * crossCorr f f u :=
    ((by fun_prop : Continuous fun u : ℝ => |u| * Real.exp (-|u| / 2)).mul
      (continuous_crossCorr_of_hasCompactSupport hf hf hfc)).integrable_of_hasCompactSupport
      (hasCompactSupport_crossCorr_of_hasCompactSupport hfc hfc).mul_left
  have hdom : Integrable fun u : ℝ =>
      (|u| * Real.exp (-|u| / 2)) * (∫ t : ℝ, f t ^ 2) :=
    integrable_abs_mul_exp_neg_abs_half.mul_const _
  calc |∫ u : ℝ, |u| * Real.exp (-|u| / 2) * crossCorr f f u|
      ≤ ∫ u : ℝ, |(|u| * Real.exp (-|u| / 2) * crossCorr f f u)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, (|u| * Real.exp (-|u| / 2)) * (∫ t : ℝ, f t ^ 2) := by
        refine integral_mono hi.abs hdom fun u => ?_
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ |u| * Real.exp (-|u| / 2))]
        exact mul_le_mul_of_nonneg_left (abs_crossCorr_self_le hf hfc u) (by positivity)
    _ = 8 * ∫ t : ℝ, f t ^ 2 := by
        rw [integral_mul_const, integral_abs_mul_exp_neg_abs_half]

/-- **Unconditional $L^2$ Bound on the Growing Continuum Double-Pole Integral for Polar Tests**:
for every polar real test `f` (`∫ t, f t * exp(t/2) = 0` and `∫ t, f t * exp(-t/2) = 0`),
`|∫ u : ℝ, |u| * Real.exp (|u| / 2) * crossCorr f f u| ≤ 8 * ∫ t : ℝ, f t ^ 2`. -/
theorem abs_integral_abs_mul_exp_abs_half_crossCorr_self_le_of_polar {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hp : ∫ t : ℝ, f t * Real.exp (t / 2) = 0)
    (hm : ∫ t : ℝ, f t * Real.exp (-t / 2) = 0) :
    |∫ u : ℝ, |u| * Real.exp (|u| / 2) * crossCorr f f u| ≤
      8 * ∫ t : ℝ, f t ^ 2 := by
  rw [integral_abs_mul_exp_abs_half_crossCorr_self_eq_of_polar hf hfc hp hm]
  exact abs_integral_abs_mul_exp_neg_abs_half_crossCorr_self_le hf hfc

/-- **Unconditional 4-Mode Archimedean Bound on the Growing Continuum Double-Pole Integral for Polar Tests**:
combining `abs_integral_abs_mul_exp_abs_half_crossCorr_self_le_of_polar` with the atom-free 4-mode
Gauss coercivity `forty_two_div_585_l2_le_markovArchRe_add_fourMode_gauss` from Stage 5 gives
`(7 / 780) * |∫ u : ℝ, |u| * Real.exp (|u| / 2) * crossCorr f f u| ≤ markovArchRe k_f + fourModeGaussPairSum f`
for every polar test `f ∈ C²_c(ℝ)`. -/
theorem seven_div_780_mul_abs_doublePole_le_markovArchRe_add_fourMode_gauss {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hp : ∫ t : ℝ, f t * Real.exp (t / 2) = 0)
    (hm : ∫ t : ℝ, f t * Real.exp (-t / 2) = 0) :
    (7 / 780) * |∫ u : ℝ, |u| * Real.exp (|u| / 2) * crossCorr f f u| ≤
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) +
        fourModeGaussPairSum f := by
  have h1 := abs_integral_abs_mul_exp_abs_half_crossCorr_self_le_of_polar hf.continuous hfc hp hm
  have h2 := forty_two_div_585_l2_le_markovArchRe_add_fourMode_gauss hf hfc
  linarith

end RHTower.CHMDStage6
