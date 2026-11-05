import GaloisForLFunctions.FiniteFreeProbability.AlmostAllJensenRootsAreReal
import GaloisForLFunctions.FiniteFreeProbability.SymmetrizedEulerHorizon

/-!
# The half-circle formula for the Jensen polynomials of `Ξ`

For every entire `f`, `R_d(f)(x) = ∂_w^d (e^{xw} f(w))|_{w = 0}`. For `f = Ξ`, in the variable `τ = iw` of
`ξ(1/2 + τ) = Ξ(−iτ)`, Cauchy's formula on `|τ| = ρ` gives

`R_d(x) = i^d (d!/2π) ∫_{−π}^{π} e^{−ixτ} ξ(1/2 + τ) τ^{−d} dθ`.

The functional equation `ξ(1/2 − τ) = ξ(1/2 + τ)` folds the left half of the circle onto the right half, and the
reality of `ξ` turns it into the conjugate. So for real `x`,

`R_d(x) = (d!/π) Re[ i^d ∫_{−π/2}^{π/2} e^{−ixτ} ξ(1/2 + τ) τ^{−d} dθ ]`,   `τ = ρ e^{iθ}`,

and the integrand lives in the half-plane `Re s ≥ 1/2`.
-/

open Polynomial Filter Topology Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace FiniteFreeProbability

noncomputable section

/-- `R_d(f)(x) = ∂_w^d (e^{xw} f(w))|_{w=0}`. -/
theorem eval_jensenRev_taylorPS {f : ℂ → ℂ} (hf : Differentiable ℂ f) (d : ℕ) (x : ℂ) :
    (jensenRev d (taylorPS f)).eval x = iteratedDeriv d (fun w => Complex.exp (x * w) * f w) 0 := by
  have hexp : Differentiable ℂ fun w : ℂ => Complex.exp (x * w) := by fun_prop
  have hmul := taylorPS_mul hexp hf
  rw [taylorPS_exp] at hmul
  have htr := jensenRev_expSeries_mul d x (taylorPS f)
  rw [← hmul] at htr
  have h0 := congrArg (eval 0) htr
  rw [eval_comp, eval_add, eval_X, eval_C, zero_add] at h0
  rw [← h0, jensenRev_eq_sum, eval_finsetSum, Finset.sum_eq_single d]
  · have hd : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
    simp only [taylorPS, PowerSeries.coeff_mk, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one,
      eval_C]
    show iteratedDeriv d ((fun w => Complex.exp (x * w)) * f) 0 / (d.factorial : ℂ) * (d.factorial : ℂ) = _
    rw [div_mul_cancel₀ _ hd]
    rfl
  · intro i hi hid
    have hlt : d - i ≠ 0 := by have := Finset.mem_range.1 hi; omega
    simp [hlt]
  · intro h; exact absurd (Finset.self_mem_range_succ d) h

theorem taylorPS_XiC : taylorPS XiC = xiSeries := by
  ext k
  have h := ofReal_realTaylorCoeff (fun w => XiC_conj w) k
  rw [xiSeries, PowerSeries.coeff_mk, taylorPS, PowerSeries.coeff_mk, h, inv_mul_eq_div]

/-- `ξ(1/2 + τ)`. -/
def xiCentered (τ : ℂ) : ℂ := xi (1 / 2 + τ)

theorem differentiable_xiCentered : Differentiable ℂ xiCentered :=
  xi_differentiable.comp (by fun_prop)

theorem XiC_eq_xiCentered (w : ℂ) : XiC w = xiCentered (I * w) := by
  rw [XiC, xiCentered]
  congr 1
  ring

theorem xiCentered_neg (τ : ℂ) : xiCentered (-τ) = xiCentered τ := by
  rw [xiCentered, xiCentered, ← xi_one_sub]
  congr 1
  ring

theorem xiCentered_conj (τ : ℂ) : xiCentered ((starRingEnd ℂ) τ) = (starRingEnd ℂ) (xiCentered τ) := by
  have h := xi_conj (1 / 2 + τ)
  rw [xiCentered, xiCentered, ← h]
  congr 1
  simp only [map_add, map_div₀, map_one, map_ofNat]

/-- The integrand of the Cauchy formula on the circle `|τ| = ρ`. -/
def jensenCircleTerm (d : ℕ) (x ρ θ : ℝ) : ℂ :=
  Complex.exp (-(I * x * circleMap 0 ρ θ)) * xiCentered (circleMap 0 ρ θ) / circleMap 0 ρ θ ^ d

theorem continuous_jensenCircleTerm {d : ℕ} (x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (jensenCircleTerm d x ρ) := by
  unfold jensenCircleTerm
  refine Continuous.div ?_ ?_ fun θ => pow_ne_zero _ (circleMap_ne_center hρ.ne')
  · exact (Complex.continuous_exp.comp (by fun_prop)).mul
      (differentiable_xiCentered.continuous.comp (continuous_circleMap 0 ρ))
  · exact (continuous_circleMap 0 ρ).pow d

theorem jensenCircleTerm_periodic (d : ℕ) (x ρ : ℝ) : Function.Periodic (jensenCircleTerm d x ρ) (2 * π) := by
  intro θ
  have h : circleMap 0 ρ (θ + 2 * π) = circleMap 0 ρ θ := periodic_circleMap 0 ρ θ
  simp only [jensenCircleTerm, h]

/-- Cauchy's formula: the full circle integral is the Jensen value. -/
theorem integral_jensenCircleTerm (d : ℕ) (x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    I ^ d * (d.factorial : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), jensenCircleTerm d x ρ θ =
      (2 * π : ℝ) * (jensenRev d xiSeries).eval (x : ℂ) := by
  set h : ℂ → ℂ := fun τ => Complex.exp (-(I * x * τ)) * xiCentered τ with hh
  have hd : Differentiable ℂ h := by
    simp only [hh]
    exact (Complex.differentiable_exp.comp (by fun_prop)).mul differentiable_xiCentered
  have hc := (hd.differentiableOn (s := Metric.closedBall 0 ρ)).circleIntegral_one_div_sub_center_pow_smul
    hρ d
  have hfact : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  -- the circle integral in the angle variable
  have hint : (∮ z in C(0, ρ), (1 / (z - 0) ^ (d + 1)) • h z) =
      I * ∫ θ in (0 : ℝ)..(2 * π), jensenCircleTerm d x ρ θ := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hz : circleMap 0 ρ θ ≠ 0 := circleMap_ne_center hρ.ne'
    simp only [deriv_circleMap, jensenCircleTerm, sub_zero, smul_eq_mul, hh, pow_succ]
    field_simp
  -- `h` is `w ↦ e^{xw} Ξ(w)` read in the variable `w = −iτ`
  have hcomp : iteratedDeriv d h 0 = (-I) ^ d * (jensenRev d xiSeries).eval (x : ℂ) := by
    rw [← taylorPS_XiC, eval_jensenRev_taylorPS XiC_differentiable]
    have hfun : h = fun τ => (fun w => Complex.exp ((x : ℂ) * w) * XiC w) (-I * τ) := by
      funext τ
      simp only [hh]
      rw [XiC_eq_xiCentered]
      congr 2
      · ring
      · rw [← mul_assoc]
        simp
    have hg : ContDiff ℂ d fun w => Complex.exp ((x : ℂ) * w) * XiC w :=
      (((Complex.differentiable_exp.comp (by fun_prop)).mul XiC_differentiable)).contDiff
    rw [hfun, iteratedDeriv_comp_const_mul hg]
    simp
  have hmain : I * ∫ θ in (0 : ℝ)..(2 * π), jensenCircleTerm d x ρ θ =
      (2 * π * I / (d.factorial : ℂ)) * ((-I) ^ d * (jensenRev d xiSeries).eval (x : ℂ)) := by
    rw [← hint, hc, hcomp, smul_eq_mul]
  have hIneg : I ^ d * (-I) ^ d = 1 := by
    rw [← mul_pow]
    simp
  have hcancel : ∫ θ in (0 : ℝ)..(2 * π), jensenCircleTerm d x ρ θ =
      (2 * π / (d.factorial : ℂ)) * ((-I) ^ d * (jensenRev d xiSeries).eval (x : ℂ)) := by
    apply mul_left_cancel₀ hI
    rw [hmain]
    ring
  rw [hcancel]
  push_cast
  have e : I ^ d * (d.factorial : ℂ) * (2 * π / (d.factorial : ℂ) * ((-I) ^ d * (jensenRev d xiSeries).eval (x : ℂ))) =
      2 * π * (jensenRev d xiSeries).eval (x : ℂ) * (I ^ d * (-I) ^ d) := by
    field_simp
  rw [e, hIneg, mul_one]

theorem jensenCircleTerm_add_pi (d : ℕ) (x ρ θ : ℝ) :
    jensenCircleTerm d x ρ (θ + π) =
      (-1) ^ d * (Complex.exp (I * x * circleMap 0 ρ θ) * xiCentered (circleMap 0 ρ θ) / circleMap 0 ρ θ ^ d) := by
  have hz : circleMap 0 ρ (θ + π) = -circleMap 0 ρ θ := by
    simp only [circleMap, zero_add, ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [jensenCircleTerm, hz, xiCentered_neg, neg_pow]
  have hexp : -(I * (x : ℂ) * -circleMap 0 ρ θ) = I * x * circleMap 0 ρ θ := by ring
  have h2 : ((-1 : ℂ) ^ d) * (-1) ^ d = 1 := by rw [← mul_pow]; simp
  have hp : ((-1 : ℂ) ^ d)⁻¹ = (-1) ^ d := inv_eq_of_mul_eq_one_right h2
  rw [hexp, div_eq_mul_inv, mul_inv, hp, div_eq_mul_inv]
  ring

/-- Reflection in the real axis turns the left half of the circle into the conjugate of the right half. -/
theorem jensenCircleTerm_conj (d : ℕ) (x ρ θ : ℝ) :
    Complex.exp (I * x * circleMap 0 ρ (-θ)) * xiCentered (circleMap 0 ρ (-θ)) / circleMap 0 ρ (-θ) ^ d =
      (starRingEnd ℂ) (jensenCircleTerm d x ρ θ) := by
  have hz : circleMap 0 ρ (-θ) = (starRingEnd ℂ) (circleMap 0 ρ θ) := by
    simp only [circleMap, zero_add, map_mul, conj_ofReal, ← Complex.exp_conj, conj_I, ofReal_neg]
    congr 2
    ring
  rw [hz, jensenCircleTerm, xiCentered_conj, map_div₀, map_mul, map_pow, ← Complex.exp_conj]
  congr 3
  simp only [map_neg, map_mul, conj_I, conj_ofReal]
  ring

/-- **The half-circle formula.** For real `x` and `ρ > 0`,
`R_d(x) = (d!/π) Re[i^d ∫_{−π/2}^{π/2} e^{−ixτ} ξ(1/2 + τ) τ^{−d} dθ]`. -/
theorem eval_jensenRev_xiSeries_eq_half_circle (d : ℕ) (x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (jensenRev d xiSeries).eval (x : ℂ) =
      ((d.factorial / π * (I ^ d * ∫ θ in (-(π / 2))..(π / 2), jensenCircleTerm d x ρ θ).re : ℝ) : ℂ) := by
  set B := ∫ θ in (-(π / 2))..(π / 2), jensenCircleTerm d x ρ θ with hB
  have hcont := continuous_jensenCircleTerm (d := d) x hρ
  have hshift : ∫ θ in (0 : ℝ)..(2 * π), jensenCircleTerm d x ρ θ =
      ∫ θ in (-(π / 2))..(3 * π / 2), jensenCircleTerm d x ρ θ := by
    have h := (jensenCircleTerm_periodic d x ρ).intervalIntegral_add_eq 0 (-(π / 2))
    rw [zero_add] at h
    rw [h]
    congr 1
    ring
  have hsplit : ∫ θ in (-(π / 2))..(3 * π / 2), jensenCircleTerm d x ρ θ =
      B + ∫ θ in (π / 2)..(3 * π / 2), jensenCircleTerm d x ρ θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hsecond : ∫ θ in (π / 2)..(3 * π / 2), jensenCircleTerm d x ρ θ =
      (-1) ^ d * (starRingEnd ℂ) B := by
    have h1 : ∫ θ in (π / 2)..(3 * π / 2), jensenCircleTerm d x ρ θ =
        ∫ θ in (-(π / 2))..(π / 2), jensenCircleTerm d x ρ (θ + π) := by
      rw [intervalIntegral.integral_comp_add_right (jensenCircleTerm d x ρ) π]
      congr 1 <;> ring
    rw [h1, hB, ← intervalIntegral_conj]
    simp only [jensenCircleTerm_add_pi]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hneg := intervalIntegral.integral_comp_neg (a := -(π / 2)) (b := π / 2)
      (fun θ => Complex.exp (I * x * circleMap 0 ρ θ) * xiCentered (circleMap 0 ρ θ) / circleMap 0 ρ θ ^ d)
    rw [neg_neg] at hneg
    rw [← hneg]
    exact intervalIntegral.integral_congr fun θ _ => jensenCircleTerm_conj d x ρ θ
  have hfull := integral_jensenCircleTerm d x hρ
  rw [hshift, hsplit, hsecond] at hfull
  have hconjI : (starRingEnd ℂ) (I ^ d * B) = I ^ d * ((-1) ^ d * (starRingEnd ℂ) B) := by
    rw [map_mul, map_pow, conj_I, neg_pow, mul_comm ((-1 : ℂ) ^ d) (I ^ d)]
    ring
  have hre : I ^ d * (B + (-1) ^ d * (starRingEnd ℂ) B) = ((2 * (I ^ d * B).re : ℝ) : ℂ) := by
    have h := Complex.add_conj (I ^ d * B)
    rw [hconjI] at h
    rw [mul_add]
    push_cast
    rw [h]
    push_cast
    ring
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  apply mul_left_cancel₀ hπ
  rw [← hfull]
  have : I ^ d * (d.factorial : ℂ) * (B + (-1) ^ d * (starRingEnd ℂ) B) =
      (d.factorial : ℂ) * (I ^ d * (B + (-1) ^ d * (starRingEnd ℂ) B)) := by ring
  rw [this, hre]
  push_cast
  have hπ' : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eval_jensenRev_xiSeries_eq_half_circle
