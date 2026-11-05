import GaloisForLFunctions.FiniteFreeProbability.JensenSaddleModel

/-!
# The Jensen approximant is a circle mean

For an entire `f`, the rescaled Jensen polynomial `Φ_d(u) = Σ_{k≤d} f_k (d!/((d−k)! d^k)) u^k` is the exact mean of `f` on the circle of radius `|u|`:

`Φ_d(u) = (d!/(2π d^d)) ∫_0^{2π} e^{d(e^{iφ} − iφ)} f(u e^{iφ}) dφ`,

against a complex weight of total mass `1` and size `≍ √d e^{−d(1 − cos φ)}`. Near `φ = 0`, `u e^{iφ} ≈ u + i u φ` with `φ` of variance `1/d`: this is the vertical Gaussian
average of the de Bruijn–Newman flow, `H_t(z) = ∫ g_t(v) H_0(z − iv) dv`, at the height-dependent time `t = u²/(2d)`. So at height `u` the Jensen polynomials of degree `d` behave like the flow at
time `u²/(2d)`.
-/

open Polynomial Complex Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace FiniteFreeProbability

noncomputable section

/-- **The circle mean formula.** -/
theorem scaledJensen_eq_circle_mean {f : ℂ → ℂ} (hf : Differentiable ℂ f) {d : ℕ} (hd : 0 < d) {u : ℂ} (hu : u ≠ 0) :
    scaledJensen (fun k => iteratedDeriv k f 0 / (k.factorial : ℂ)) d u =
      (d.factorial : ℂ) / (2 * π * (d : ℂ) ^ d) *
        ∫ φ in (0 : ℝ)..(2 * π), saddleWeight d φ * f (u * Complex.exp (φ * I)) := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hfact : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set h : ℂ → ℂ := fun ζ => Complex.exp ((d : ℂ) * ζ) * f (u * ζ) with hh
  have hd' : Differentiable ℂ h := by
    simp only [hh]
    exact (Complex.differentiable_exp.comp (by fun_prop)).mul (hf.comp (by fun_prop))
  have hc := (hd'.differentiableOn (s := Metric.closedBall 0 1)).circleIntegral_one_div_sub_center_pow_smul
    one_pos d
  have hint : (∮ z in C(0, 1), (1 / (z - 0) ^ (d + 1)) • h z) =
      I * ∫ φ in (0 : ℝ)..(2 * π), saddleWeight d φ * f (u * Complex.exp (φ * I)) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    have hz : Complex.exp (φ * I) ≠ 0 := Complex.exp_ne_zero _
    have hw : saddleWeight d φ = Complex.exp ((d : ℂ) * Complex.exp (φ * I)) / Complex.exp (φ * I) ^ d := by
      rw [saddleWeight, Complex.exp_sub, ← Complex.exp_nat_mul]
      congr 2
      ring
    simp only [deriv_circleMap, circleMap, ofReal_one, one_mul, zero_add, sub_zero, smul_eq_mul, pow_succ, hw, hh]
    field_simp
  -- `h` is `w ↦ e^{(d/u) w} f(w)` read in the variable `w = uζ`
  have hcomp : iteratedDeriv d h 0 = u ^ d * (jensenRev d (taylorPS f)).eval ((d : ℂ) / u) := by
    rw [eval_jensenRev_taylorPS hf]
    have hfun : h = fun ζ => (fun w => Complex.exp ((d : ℂ) / u * w) * f w) (u * ζ) := by
      funext ζ
      simp only [hh]
      congr 2
      field_simp
    have hg : ContDiff ℂ d fun w => Complex.exp ((d : ℂ) / u * w) * f w :=
      ((Complex.differentiable_exp.comp (by fun_prop)).mul hf).contDiff
    rw [hfun, iteratedDeriv_comp_const_mul hg]
    simp
  have hmk : taylorPS f = PowerSeries.mk fun k => iteratedDeriv k f 0 / (k.factorial : ℂ) := rfl
  have heval := eval_jensenRev_div (fun k => iteratedDeriv k f 0 / (k.factorial : ℂ)) hd hu
  rw [← hmk] at heval
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hmain : ∫ φ in (0 : ℝ)..(2 * π), saddleWeight d φ * f (u * Complex.exp (φ * I)) =
      (2 * π / (d.factorial : ℂ)) * (d : ℂ) ^ d *
        scaledJensen (fun k => iteratedDeriv k f 0 / (k.factorial : ℂ)) d u := by
    apply mul_left_cancel₀ hI
    rw [← hint, hc, hcomp, heval, smul_eq_mul, div_pow]
    field_simp
  rw [hmain]
  field_simp

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.scaledJensen_eq_circle_mean
