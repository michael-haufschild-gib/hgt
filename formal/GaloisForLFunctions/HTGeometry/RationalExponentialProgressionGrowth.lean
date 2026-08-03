import GaloisForLFunctions.U0.PolyAsymptotics

/-!
# Growth of rational-exponential progression representations

Dreyfus's conclusion restricts on a period progression to a finite sum of rational functions
times exponential monomials.  This file proves, without a special-function assumption, that every
such sequence has an eventual polynomial-times-exponential upper bound.
-/

open Filter Polynomial Topology
open scoped BigOperators

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- Sum of coefficient norms used in the polynomial growth bound. -/
def rationalExpPolynomialCoeffNormSum (P : Polynomial ℂ) : ℝ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖

theorem norm_polynomial_eval_natCast_le (P : Polynomial ℂ) (n : ℕ) :
    ‖P.eval (n : ℂ)‖ ≤
      rationalExpPolynomialCoeffNormSum P * ((n : ℝ) + 1) ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum_range, rationalExpPolynomialCoeffNormSum, Finset.sum_mul]
  apply norm_sum_le_of_le
  intro i hi
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hin : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  calc
    (n : ℝ) ^ i ≤ ((n : ℝ) + 1) ^ i := by gcongr
    _ ≤ ((n : ℝ) + 1) ^ P.natDegree := by
      apply pow_le_pow_right₀ (by linarith)
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)

/-- The reciprocal of a nonzero polynomial is eventually bounded on the nonnegative integers. -/
theorem exists_eventually_norm_inv_polynomial_eval_natCast_le
    {Q : Polynomial ℂ} (hQ : Q ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop, ‖(Q.eval (n : ℂ))⁻¹‖ ≤ B := by
  let L : ℝ := ‖Q.leadingCoeff‖
  have hlead : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hL : 0 < L := norm_pos_iff.mpr hlead
  have hlimReal := PolyAsymptotics.tendsto_eval_div_pow_natDegree Q
  have hlimNat : Tendsto
      (fun n : ℕ => ‖Q.eval (n : ℂ) / (n : ℂ) ^ Q.natDegree‖)
      atTop (𝓝 L) := by
    simpa [L, Function.comp_def] using
      (continuous_norm.tendsto Q.leadingCoeff).comp
        (hlimReal.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N, hclose⟩ :=
    (Metric.tendsto_atTop.mp hlimNat) (L / 2) (by positivity)
  refine ⟨2 / L, div_pos (by norm_num) hL, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with n hnN hn1
  have hn := hclose n hnN
  rw [Real.dist_eq] at hn
  have hratio : L / 2 ≤ ‖Q.eval (n : ℂ) / (n : ℂ) ^ Q.natDegree‖ := by
    rw [abs_lt] at hn
    linarith [hn.1]
  have hpow : 1 ≤ ‖(n : ℂ) ^ Q.natDegree‖ := by
    rw [norm_pow, Complex.norm_natCast]
    exact one_le_pow₀ (by exact_mod_cast hn1)
  have hq : L / 2 ≤ ‖Q.eval (n : ℂ)‖ := by
    rw [norm_div] at hratio
    exact hratio.trans (div_le_self (norm_nonneg _) hpow)
  have hqpos : 0 < ‖Q.eval (n : ℂ)‖ := lt_of_lt_of_le (half_pos hL) hq
  rw [norm_inv]
  calc
    ‖Q.eval (n : ℂ)‖⁻¹ ≤ (L / 2)⁻¹ := inv_anti₀ (half_pos hL) hq
    _ = 2 / L := by field_simp

/-- Exact normal form obtained after restricting a Dreyfus periodic-exponential expression to
one period progression. -/
def HasRationalExponentialProgressionRepresentation (u : ℕ → ℂ) : Prop :=
  ∃ (m : ℕ) (num den : Fin m → Polynomial ℂ) (lambda : Fin m → ℂ),
    (∀ j, den j ≠ 0) ∧
      ∀ n, u n = ∑ j : Fin m,
        (num j).eval (n : ℂ) / (den j).eval (n : ℂ) *
          Complex.exp (lambda j * (n : ℂ))

/-- A finite rational-exponential progression representation has eventual
polynomial-times-exponential growth. -/
theorem HasRationalExponentialProgressionRepresentation.eventually_upper
    {u : ℕ → ℂ} (hu : HasRationalExponentialProgressionRepresentation u) :
    ∃ (C A : ℝ) (d : ℕ), 0 < C ∧ 0 < A ∧
      ∀ᶠ n : ℕ in atTop,
        ‖u n‖ ≤ C * ((n : ℝ) + 1) ^ d * A ^ n := by
  classical
  obtain ⟨m, num, den, lambda, hden, hu⟩ := hu
  choose B hBpos hB using fun j =>
    exists_eventually_norm_inv_polynomial_eval_natCast_le (hden j)
  let d : ℕ := ∑ j : Fin m, (num j).natDegree
  let A : ℝ := 1 + ∑ j : Fin m, Real.exp ‖lambda j‖
  let C : ℝ := 1 + ∑ j : Fin m,
    rationalExpPolynomialCoeffNormSum (num j) * B j
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    have hnonneg : 0 ≤ ∑ j : Fin m,
        rationalExpPolynomialCoeffNormSum (num j) * B j := by
      apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hBpos j).le
    linarith
  refine ⟨C, A, d, hC, hA, ?_⟩
  choose N hN using fun j => Filter.eventually_atTop.1 (hB j)
  have hBall : ∀ᶠ n : ℕ in atTop, ∀ j : Fin m,
      ‖((den j).eval (n : ℂ))⁻¹‖ ≤ B j := by
    apply Filter.eventually_atTop.2
    refine ⟨∑ j : Fin m, N j, fun n hn j => hN j n ?_⟩
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hn
  filter_upwards [hBall] with n hBn
  rw [hu n]
  calc
    ‖∑ j : Fin m,
        (num j).eval (n : ℂ) / (den j).eval (n : ℂ) *
          Complex.exp (lambda j * (n : ℂ))‖ ≤
        ∑ j : Fin m, ‖(num j).eval (n : ℂ) /
          (den j).eval (n : ℂ) * Complex.exp (lambda j * (n : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin m,
        (rationalExpPolynomialCoeffNormSum (num j) * B j) *
          ((n : ℝ) + 1) ^ d * A ^ n := by
      apply Finset.sum_le_sum
      intro j _
      have hdeg : (num j).natDegree ≤ d := by
        dsimp [d]
        exact Finset.single_le_sum
          (f := fun k : Fin m => (num k).natDegree)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have hpoly := norm_polynomial_eval_natCast_le (num j) n
      have hpow : ((n : ℝ) + 1) ^ (num j).natDegree ≤
          ((n : ℝ) + 1) ^ d := by
        exact pow_le_pow_right₀ (by linarith) hdeg
      have hexpBase : Real.exp ‖lambda j‖ ≤ A := by
        dsimp [A]
        have hsingle : Real.exp ‖lambda j‖ ≤
            ∑ k : Fin m, Real.exp ‖lambda k‖ :=
          Finset.single_le_sum (fun k _ => (Real.exp_pos ‖lambda k‖).le)
            (Finset.mem_univ j)
        linarith
      have hexp : ‖Complex.exp (lambda j * (n : ℂ))‖ ≤ A ^ n := by
        rw [Complex.norm_exp]
        calc
          Real.exp (lambda j * (n : ℂ)).re ≤
              Real.exp (‖lambda j‖ * n) := by
            apply Real.exp_le_exp.mpr
            calc
              (lambda j * (n : ℂ)).re ≤ ‖lambda j * (n : ℂ)‖ :=
                Complex.re_le_norm _
              _ = ‖lambda j‖ * n := by rw [norm_mul, Complex.norm_natCast]
          _ = (Real.exp ‖lambda j‖) ^ n := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
          _ ≤ A ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hexpBase n
      have hcoeff : 0 ≤ rationalExpPolynomialCoeffNormSum (num j) :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hdeninv : ‖(den j).eval (n : ℂ)‖⁻¹ ≤ B j := by
        simpa only [norm_inv] using hBn j
      have hnumden :
          ‖(num j).eval (n : ℂ)‖ * ‖(den j).eval (n : ℂ)‖⁻¹ ≤
            (rationalExpPolynomialCoeffNormSum (num j) *
              ((n : ℝ) + 1) ^ (num j).natDegree) * B j :=
        mul_le_mul hpoly hdeninv (inv_nonneg.mpr (norm_nonneg _))
          (mul_nonneg hcoeff (pow_nonneg (by positivity) _))
      rw [norm_mul, norm_div, div_eq_mul_inv]
      calc
        ‖(num j).eval (n : ℂ)‖ * ‖(den j).eval (n : ℂ)‖⁻¹ *
            ‖Complex.exp (lambda j * (n : ℂ))‖ ≤
            ((rationalExpPolynomialCoeffNormSum (num j) *
              ((n : ℝ) + 1) ^ (num j).natDegree) * B j) * A ^ n :=
          mul_le_mul hnumden hexp (norm_nonneg _)
            (mul_nonneg
              (mul_nonneg hcoeff (pow_nonneg (by positivity) _)) (hBpos j).le)
        _ = (rationalExpPolynomialCoeffNormSum (num j) * B j) *
              ((n : ℝ) + 1) ^ (num j).natDegree * A ^ n := by ring
        _ ≤ (rationalExpPolynomialCoeffNormSum (num j) * B j) *
              ((n : ℝ) + 1) ^ d * A ^ n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow
              (mul_nonneg hcoeff (hBpos j).le))
            (pow_nonneg hA.le n)
    _ = (∑ j : Fin m,
        rationalExpPolynomialCoeffNormSum (num j) * B j) *
          ((n : ℝ) + 1) ^ d * A ^ n := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ C * ((n : ℝ) + 1) ^ d * A ^ n := by
      gcongr
      dsimp [C]
      linarith

end

end HTGeometry
end GaloisForLFunctions
