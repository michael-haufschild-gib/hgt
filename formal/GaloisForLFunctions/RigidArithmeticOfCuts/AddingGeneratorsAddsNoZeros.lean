import GaloisForLFunctions.RHTower.IntegerBeurlingAddedGeneratorsFullDimension

/-!
# Adding generators adds no zeros

An integer-supported Beurling system has integer masses `a`, with `|a n| ≤ 1`, and generator von Mangoldt function `Λ − e`.
Suppose it only adds generators, `e ≤ 0`, and that its count is `A x + O(x^θ)`. The added mass has dimension at most `θ`,
so the quotient of the system by `ζ` is `K exp L(c)` on `Re s > θ`, with `c = −e/log`. Therefore

`(s − 1) L(a)(s) = K exp L(c)(s) · (s − 1) ζ(s)`  on `Re s > θ`,

and **the system has exactly the zeros of `ζ` there**, with multiplicity. A new zero to the right of the count exponent can
only be produced by deleting primes. Deletions cost half the dimension, so the asymmetry of the exchange is the
statement that `exp(−P)` may vanish analytically at the abscissa while `exp(P)` cannot.
-/

open Complex Filter Topology Asymptotics
open ArithmeticFunction (vonMangoldt)
open RHTower RHTower.IntegerBeurling

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

variable {a e : ℕ → ℝ}

/-- **The factorization of an additive system on `Re s > θ`.** -/
theorem exists_numerator_eq_mul (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1) (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((vonMangoldt n - e n : ℝ) : ℂ)) (countSeq a) =
      LSeries.logMul (countSeq a))
    (hadd : ∀ n, e n ≤ 0) {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ z : ℂ, θ < z.re →
      numerator a A z = K * Complex.exp (LSeries (fun n => ((logCoeff e n : ℝ) : ℂ)) z) *
        zetaResidueFactor z := by
  obtain ⟨K, hK, hratio⟩ := exists_ratio_eq_mul_exp ha ha1 he hconv
  refine ⟨K, hK, ?_⟩
  set L := LSeries fun n => ((logCoeff e n : ℝ) : ℂ) with hL
  have habs := abscissaOfAbsConv_logCoeff_le ha ha1 he hconv hadd hθ hN
  set U : Set ℂ := {z | θ < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt θ).isPreconnected
  have hLd : DifferentiableOn ℂ L U := fun z hz =>
    (LSeries_differentiableOn _ z (habs.trans_lt (by exact_mod_cast hz))).mono
      (fun w hw => habs.trans_lt (by exact_mod_cast hw))
  have hLHS : AnalyticOnNhd ℂ (numerator a A) U :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_numerator hθ hN hz).differentiableWithinAt) hUopen
  have hRHS : AnalyticOnNhd ℂ (fun z => K * Complex.exp (L z) * zetaResidueFactor z) U :=
    DifferentiableOn.analyticOnNhd
      (((hLd.cexp).const_mul K).mul (differentiable_zetaResidueFactor.differentiableOn)) hUopen
  set σ₀ : ℝ := max θ 1 + 1 with hσ₀
  have hσθ : θ < σ₀ := by
    have := le_max_left θ 1
    rw [hσ₀]
    linarith
  have hmem : ((σ₀ : ℝ) : ℂ) ∈ U := by simpa [hU] using hσθ
  have heq : numerator a A =ᶠ[𝓝 ((σ₀ : ℝ) : ℂ)] fun z => K * Complex.exp (L z) * zetaResidueFactor z := by
    have hnhds : {z : ℂ | max θ 1 < z.re} ∈ 𝓝 ((σ₀ : ℝ) : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      have hlt : max θ 1 < σ₀ := by rw [hσ₀]; linarith
      simpa using hlt
    filter_upwards [hnhds] with z hz
    have hz' : max θ 1 < z.re := hz
    have hzθ : θ < z.re := (le_max_left _ _).trans_lt hz'
    have hz1 : 1 < z.re := (le_max_right _ _).trans_lt hz'
    have hne1 : z ≠ 1 := fun h => by
      rw [h] at hz1
      simp at hz1
    have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz1.le
    rw [numerator_eq ha hθ hN hz1 hzθ, zetaResidueFactor_of_ne hne1]
    have hr := hratio z hz1
    rw [ratio, div_eq_iff hζ] at hr
    rw [hr]
    ring
  exact fun z hz => hLHS.eqOn_of_preconnected_of_eventuallyEq hRHS hUconn hmem heq hz

/-- **Adding generators adds no zeros.** On `Re s > θ` the continued system vanishes exactly where `ζ` does. -/
theorem numerator_eq_zero_iff (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1) (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((vonMangoldt n - e n : ℝ) : ℂ)) (countSeq a) =
      LSeries.logMul (countSeq a))
    (hadd : ∀ n, e n ≤ 0) {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) {z : ℂ} (hz : θ < z.re) :
    numerator a A z = 0 ↔ zetaResidueFactor z = 0 := by
  obtain ⟨K, hK, h⟩ := exists_numerator_eq_mul ha ha1 he hconv hadd hθ hN
  rw [h z hz, mul_eq_zero, mul_eq_zero, or_iff_right (or_iff_right hK |>.not.mpr
    (Complex.exp_ne_zero _))]

end GaloisForLFunctions.RigidArithmeticOfCuts
