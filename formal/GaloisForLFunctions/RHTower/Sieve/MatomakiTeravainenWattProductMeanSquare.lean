import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDIOverHeight
import GaloisForLFunctions.RHTower.Sieve.DirichletPolyAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.DirichletYoung
import GaloisForLFunctions.RHTower.Sieve.TwistedSeriesAsDirichletPoly

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Coefficients of the exact Watt integrand after multiplying its three Dirichlet factors. -/
def mtWattProductAF (a : ℕ → ℂ) (A N N' : ℕ) : ArithmeticFunction ℂ :=
  (mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ) *
      mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ)) *
    mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)

/-- The triple product coefficients have their literal product support. -/
theorem mtWattProductAF_support (a : ℕ → ℂ) (A N N' : ℕ) :
    ∀ n, mtWattProductAF a A N N' n ≠ 0 →
      n ∈ Finset.Icc 1 ((N' * N') * (2 * A)) := by
  let U := mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ)
  let B := mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)
  have hU : ∀ n, U n ≠ 0 → n ∈ Finset.Icc 1 N' := by
    simpa [U] using mtRealIntervalAF_support_nat (fun _ => (1 : ℂ)) (N : ℝ) (N' : ℝ)
  have hB : ∀ n, B n ≠ 0 → n ∈ Finset.Icc 1 (2 * A) := by
    simpa [B] using mtWattCoefficientBlock_support a A
  have hUU : ∀ n, (U * U) n ≠ 0 → n ∈ Finset.Icc 1 (N' * N') := by
    intro n hn
    exact convolution_mem_Icc_of_support_mul hU hU
      (arithmeticFunction_mul_eq_lseriesConvolution U U ▸ hn)
  intro n hn
  exact convolution_mem_Icc_of_support_mul hUU hB
    (arithmeticFunction_mul_eq_lseriesConvolution (U * U) B ▸ hn)

/-- The exact Watt integrand is one Dirichlet polynomial with triple-convolution coefficients. -/
theorem perronPoly_mtWattProductAF
    (a : ℕ → ℂ) (A N N' : ℕ) (t : ℝ) :
    perronPoly (fun n => mtWattProductAF a A N N' n)
        ((N' * N') * (2 * A)) 1 t =
      mtWattUnitBlock N N' t * mtWattUnitBlock N N' t *
        mtWattCoefficientBlock a A t := by
  let U := mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ)
  let B := mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)
  have hU : ∀ n, U n ≠ 0 → n ∈ Finset.Icc 1 N' := by
    simpa [U] using mtRealIntervalAF_support_nat (fun _ => (1 : ℂ)) (N : ℝ) (N' : ℝ)
  have hB : ∀ n, B n ≠ 0 → n ∈ Finset.Icc 1 (2 * A) := by
    simpa [B] using mtWattCoefficientBlock_support a A
  have hUU : ∀ n, (U * U) n ≠ 0 → n ∈ Finset.Icc 1 (N' * N') := by
    intro n hn
    exact convolution_mem_Icc_of_support_mul hU hU
      (arithmeticFunction_mul_eq_lseriesConvolution U U ▸ hn)
  rw [show mtWattProductAF a A N N' = (U * U) * B by rfl,
    perronPoly_arithmeticFunction_mul (U * U) B hUU hB,
    perronPoly_arithmeticFunction_mul U U hU hU]
  rfl

/-- Ordinary affine mean square controls the exact Watt product at every height. -/
theorem integral_mtWatt_le_productAffine
    (a : ℕ → ℂ) (A N N' : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      generalMeanSquareConst (fun n => mtWattProductAF a A N N' n)
          (Finset.Icc 1 ((N' * N') * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtWattProductAF a A N N' n)
          (Finset.Icc 1 ((N' * N') * (2 * A))) 1 * T := by
  let c : ℕ → ℂ := fun n => mtWattProductAF a A N N' n
  let M := (N' * N') * (2 * A)
  let B := generalMeanSquareConst c (Finset.Icc 1 M) 1 +
    generalMeanSquareRate c (Finset.Icc 1 M) 1 * T
  have hsupp : ∀ n, c n ≠ 0 → n ∈ Finset.Icc 1 M := mtWattProductAF_support a A N N'
  have hpoly : ∀ t : ℝ,
      perronPoly c M 1 t = LSeries c (((1 : ℝ) : ℂ) + (t : ℝ) * I) := by
    intro t
    exact perronPoly_eq_LSeries_of_support hsupp 1 t
  have hfullSet := integral_Icc_normSq_LSeries_le_general_affine
    (a := c) (s := Finset.Icc 1 M) (by simp) hsupp 1 hT
  have hfull : (∫ t in (-T)..T, ‖perronPoly c M 1 t‖ ^ 2) ≤ B := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    simpa only [hpoly, B] using hfullSet
  have hcont : Continuous (fun t : ℝ => ‖perronPoly c M 1 t‖ ^ 2) :=
    (continuous_perronPoly c M 1).norm.pow 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => ‖perronPoly c M 1 t‖ ^ 2)
    (μ := volume) (a := -T) (b := T / 2) (c := T)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hleft : 0 ≤ ∫ t in (-T)..(T / 2), ‖perronPoly c M 1 t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hsub : (∫ t in (T / 2)..T, ‖perronPoly c M 1 t‖ ^ 2) ≤ B := by
    linarith [hsplit, hleft, hfull]
  have hpoint : ∀ t : ℝ,
      ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 =
        ‖perronPoly c M 1 t‖ ^ 2 := by
    intro t
    rw [perronPoly_mtWattProductAF]
    simp only [norm_mul]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
  simpa only [B, c, M] using hsub

/-- When the full triple-product support lies below the height, the constant affine mass is
absorbed into the height-linear mass. -/
theorem integral_mtWatt_longHeight_le_rate
    (a : ℕ → ℂ) (A N N' : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hM : (((N' * N') * (2 * A) : ℕ) : ℝ) ≤ T) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      (2 * Real.exp 1 + 1) *
        generalMeanSquareRate (fun n => mtWattProductAF a A N N' n)
          (Finset.Icc 1 ((N' * N') * (2 * A))) 1 * T := by
  let c : ℕ → ℂ := fun n => mtWattProductAF a A N N' n
  let M := (N' * N') * (2 * A)
  let S₀ := ∑ n ∈ Finset.Icc 1 M,
    ‖c n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2
  let S₁ := ∑ n ∈ Finset.Icc 1 M, (n : ℝ) *
    ‖c n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2
  have hsum : S₁ ≤ T * S₀ := by
    dsimp only [S₁, S₀]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn => by
      have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
      have hnT : (n : ℝ) ≤ T := (Nat.cast_le.mpr hnM).trans hM
      exact mul_le_mul_of_nonneg_right hnT (sq_nonneg _)
  have hconst : generalMeanSquareConst c (Finset.Icc 1 M) 1 ≤
      2 * Real.exp 1 * generalMeanSquareRate c (Finset.Icc 1 M) 1 * T := by
    rw [generalMeanSquareConst, generalMeanSquareRate]
    dsimp only [S₁, S₀] at hsum ⊢
    have hfac : 0 ≤ 5 * Real.pi * Real.exp 1 := by positivity
    have hs := mul_le_mul_of_nonneg_left hsum hfac
    nlinarith [Real.exp_pos 1, Real.pi_pos]
  have hbase := integral_mtWatt_le_productAffine a A N N' hT
  calc
    _ ≤ generalMeanSquareConst c (Finset.Icc 1 M) 1 +
        generalMeanSquareRate c (Finset.Icc 1 M) 1 * T := by
      simpa only [c, M] using hbase
    _ ≤ 2 * Real.exp 1 * generalMeanSquareRate c (Finset.Icc 1 M) 1 * T +
        generalMeanSquareRate c (Finset.Icc 1 M) 1 * T :=
      add_le_add hconst le_rfl
    _ = (2 * Real.exp 1 + 1) * generalMeanSquareRate c (Finset.Icc 1 M) 1 * T := by
      ring

end

end RHTower.Sieve
