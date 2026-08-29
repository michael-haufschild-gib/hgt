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

/-- A Perron polynomial is the corresponding finite Dirichlet polynomial with its real-axis
weight absorbed into the coefficients. -/
theorem perronPoly_eq_dirPoly_twistedTruncCoeff
    (f : ℕ → ℂ) (hf0 : f 0 = 0) (M : ℕ) (σ t : ℝ) :
    perronPoly f M σ t = dirPoly M (twistedTruncCoeff f σ M) (-t) := by
  have hpoly := sum_range_twistedSummand_eq_dirPoly hf0 σ t M
  rw [perronPoly]
  have hsub : Finset.Icc 1 M ⊆ Finset.range (M + 1) := by
    intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  calc
    (∑ n ∈ Finset.Icc 1 M,
        f n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I)))) =
        ∑ n ∈ Finset.Icc 1 M,
          twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n := by
      rfl
    _ = ∑ n ∈ Finset.range (M + 1),
          twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n := by
      apply Finset.sum_subset hsub
      intro n hn hnot
      have hn0 : n = 0 := by
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Icc] at hnot
        omega
      subst n
      simp [twistedSummand, hf0]
    _ = dirPoly M (twistedTruncCoeff f σ M) (-t) := hpoly

/-- Perron-line coefficients of the long unit block. -/
def mtWattUnitCoeff (N N' : ℕ) : Fin N' → ℂ :=
  twistedTruncCoeff
    (fun n => mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ) n) 1 N'

/-- Perron-line coefficients of the dyadic data block. -/
def mtWattDataCoeff (a : ℕ → ℂ) (A : ℕ) : Fin (2 * A) → ℂ :=
  twistedTruncCoeff
    (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n) 1 (2 * A)

theorem mtWattUnitBlock_eq_dirPoly (N N' : ℕ) (t : ℝ) :
    mtWattUnitBlock N N' t = dirPoly N' (mtWattUnitCoeff N N') (-t) := by
  apply perronPoly_eq_dirPoly_twistedTruncCoeff
  simp [mtRealIntervalAF]

theorem mtWattCoefficientBlock_eq_dirPoly (a : ℕ → ℂ) (A : ℕ) (t : ℝ) :
    mtWattCoefficientBlock a A t = dirPoly (2 * A) (mtWattDataCoeff a A) (-t) := by
  apply perronPoly_eq_dirPoly_twistedTruncCoeff
  simp [mtRealIntervalAF]

/-- The reciprocal mass of a unit block inside `(N,2N]` is at most one. -/
theorem sum_norm_mtWattUnitCoeff_le_one
    {N N' : ℕ} (hN : 1 ≤ N) (hN' : N' ≤ 2 * N) :
    ∑ j : Fin N', ‖mtWattUnitCoeff N N' j‖ ≤ 1 := by
  let F : ℕ → ℂ := fun n => mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ) n
  have hbridge :
      (∑ j : Fin N', ‖mtWattUnitCoeff N N' j‖) =
        ∑ n ∈ Finset.Icc 1 N',
          ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ := by
    rw [← sum_fin_eq_sum_Icc N'
      (fun n => ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mtWattUnitCoeff, twistedTruncCoeff]
    dsimp only [F]
    push_cast
    rfl
  rw [hbridge]
  have hsub : Finset.Ioc N N' ⊆ Finset.Icc 1 N' := by
    intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    omega
  have hrestrict :
      (∑ n ∈ Finset.Icc 1 N',
          ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖) =
        ∑ n ∈ Finset.Ioc N N',
          ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hnmem
    have hnpos : 0 < n := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [show F n = 0 by
      dsimp only [F]
      rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos]
      apply if_neg
      intro hinside
      apply hnmem
      simp only [Finset.mem_Ioc]
      exact_mod_cast hinside]
    simp
  rw [hrestrict]
  have hterm : ∀ n ∈ Finset.Ioc N N',
      ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ≤ 1 / (N : ℝ) := by
    intro n hn
    have hnNat : N < n ∧ n ≤ N' := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := by omega
    have hinside : (N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (N' : ℝ) := by
      exact_mod_cast hnNat
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hnRpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnNat.1.le
    have hinv : (n : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hNpos hNn
    dsimp only [F]
    rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos, if_pos hinside,
      Real.rpow_neg_one]
    simp only [one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_pos hnRpos, one_div]
    exact hinv
  calc
    (∑ n ∈ Finset.Ioc N N',
        ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖) ≤
        ∑ _n ∈ Finset.Ioc N N', 1 / (N : ℝ) :=
      Finset.sum_le_sum hterm
    _ = ((N' - N : ℕ) : ℝ) * (1 / (N : ℝ)) := by
      simp
    _ ≤ (N : ℝ) * (1 / (N : ℝ)) := by
      have hdiff : N' - N ≤ N := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdiff) (by positivity)
    _ = 1 := by field_simp

/-- The Perron-line data coefficients retain the source energy with the exact `A⁻²` damping. -/
theorem sum_norm_sq_mtWattDataCoeff_le_energy
    (a : ℕ → ℂ) {A : ℕ} (hA : 1 ≤ A) :
    (∑ j : Fin (2 * A), ‖mtWattDataCoeff a A j‖ ^ 2) ≤
      (1 / (A : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 := by
  let F : ℕ → ℂ := fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n
  have hbridge :
      (∑ j : Fin (2 * A), ‖mtWattDataCoeff a A j‖ ^ 2) =
        ∑ n ∈ Finset.Icc 1 (2 * A),
          ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 := by
    rw [← sum_fin_eq_sum_Icc (2 * A)
      (fun n => ‖F n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mtWattDataCoeff, twistedTruncCoeff]
    dsimp only [F]
    push_cast
    rfl
  have h := generalMeanSquareRate_mtWattCoefficientBlock_le_energy a hA
  rw [generalMeanSquareRate] at h
  dsimp only [F] at hbridge
  rw [← hbridge] at h
  have hfac : 0 < 5 * Real.pi / 2 := by positivity
  nlinarith

/-- Convolution coefficients of the squared unit block. -/
def mtWattUnitSquareCoeff (N N' : ℕ) : Fin (N' * N') → ℂ :=
  dirConv N' N' (mtWattUnitCoeff N N') (mtWattUnitCoeff N N')

/-- Complete three-factor coefficients, ordered with the data block first for Young's inequality. -/
def mtWattProductDirCoeff (a : ℕ → ℂ) (A N N' : ℕ) :
    Fin ((2 * A) * (N' * N')) → ℂ :=
  dirConv (2 * A) (N' * N') (mtWattDataCoeff a A) (mtWattUnitSquareCoeff N N')

/-- Multiplicative Young transfers source `ℓ²` energy through both reciprocal unit blocks without a
divisor loss. -/
theorem sum_norm_sq_mtWattProductDirCoeff_le_energy
    (a : ℕ → ℂ) {A N N' : ℕ} (hA : 1 ≤ A)
    (hN : 1 ≤ N) (hN' : N' ≤ 2 * N) :
    (∑ r : Fin ((2 * A) * (N' * N')), ‖mtWattProductDirCoeff a A N N' r‖ ^ 2) ≤
      (1 / (A : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 := by
  let u := mtWattUnitCoeff N N'
  let b := mtWattDataCoeff a A
  let uu := mtWattUnitSquareCoeff N N'
  have hu := sum_norm_mtWattUnitCoeff_le_one hN hN'
  have huu : (∑ r : Fin (N' * N'), ‖uu r‖) ≤ (∑ j : Fin N', ‖u j‖) ^ 2 := by
    have h := sum_norm_dirConv_le N' N' u u
    simpa only [uu, mtWattUnitSquareCoeff, pow_two] using h
  have huu_one : (∑ r : Fin (N' * N'), ‖uu r‖) ≤ 1 := by
    have hu0 : 0 ≤ ∑ j : Fin N', ‖u j‖ := by positivity
    have hu' : (∑ j : Fin N', ‖u j‖) ≤ 1 := by simpa only [u] using hu
    calc
      _ ≤ (∑ j : Fin N', ‖u j‖) ^ 2 := huu
      _ ≤ 1 := by nlinarith
  have hb := sum_norm_sq_mtWattDataCoeff_le_energy a hA
  have hyoung := sum_norm_sq_dirConv_le_l2_l1 (2 * A) (N' * N') b uu
  have henergy0 : 0 ≤ ∑ j : Fin (2 * A), ‖b j‖ ^ 2 := by positivity
  have huu0 : 0 ≤ ∑ r : Fin (N' * N'), ‖uu r‖ := by positivity
  calc
    _ ≤ (∑ j : Fin (2 * A), ‖b j‖ ^ 2) *
        (∑ r : Fin (N' * N'), ‖uu r‖) ^ 2 := by
      simpa only [mtWattProductDirCoeff, b, uu] using hyoung
    _ ≤ ∑ j : Fin (2 * A), ‖b j‖ ^ 2 := by
      have hsquare : (∑ r : Fin (N' * N'), ‖uu r‖) ^ 2 ≤ 1 := by
        nlinarith
      nlinarith
    _ ≤ (1 / (A : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 := by
      simpa only [b] using hb

/-- The exact Watt product is one Dirichlet polynomial with the Young-compatible coefficient
ordering. -/
theorem mtWattProduct_eq_dirPoly
    (a : ℕ → ℂ) (A N N' : ℕ) (t : ℝ) :
    mtWattUnitBlock N N' t * mtWattUnitBlock N N' t *
        mtWattCoefficientBlock a A t =
      dirPoly ((2 * A) * (N' * N')) (mtWattProductDirCoeff a A N N') (-t) := by
  rw [mtWattUnitBlock_eq_dirPoly, mtWattCoefficientBlock_eq_dirPoly]
  calc
    dirPoly N' (mtWattUnitCoeff N N') (-t) *
          dirPoly N' (mtWattUnitCoeff N N') (-t) *
        dirPoly (2 * A) (mtWattDataCoeff a A) (-t) =
        dirPoly (2 * A) (mtWattDataCoeff a A) (-t) *
          (dirPoly N' (mtWattUnitCoeff N N') (-t) *
            dirPoly N' (mtWattUnitCoeff N N') (-t)) := by ring
    _ = dirPoly (2 * A) (mtWattDataCoeff a A) (-t) *
          dirPoly (N' * N') (mtWattUnitSquareCoeff N N') (-t) := by
      rw [dirPoly_mul_eq_dirPoly]
      rfl
    _ = dirPoly ((2 * A) * (N' * N')) (mtWattProductDirCoeff a A N N') (-t) := by
      rw [dirPoly_mul_eq_dirPoly]
      rfl

/-- If the complete three-factor Dirichlet polynomial lies below the height, ordinary affine
mean square and multiplicative Young give the Watt energy bound. -/
theorem integral_mtWatt_longHeight_le_energy
    (a : ℕ → ℂ) {A N N' : ℕ} (hA : 1 ≤ A)
    (hN : 1 ≤ N) (hN' : N' ≤ 2 * N)
    {T : ℝ} (hT : 1 ≤ T)
    (hM : (((N' * N') * (2 * A) : ℕ) : ℝ) ≤ T) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2) *
        (1 / (A : ℝ) ^ 2) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) * T := by
  let M := (2 * A) * (N' * N')
  let c := mtWattProductDirCoeff a A N N'
  let E := ∑ r : Fin M, ‖c r‖ ^ 2
  let S := (1 / (A : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2
  let C := 5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2
  have hMR : (M : ℝ) ≤ T := by
    simpa only [M, Nat.mul_comm] using hM
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hweight :
      (∑ r : Fin M, (((r : ℕ) : ℝ) + 1) * ‖c r‖ ^ 2) ≤ T * E := by
    dsimp only [E]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => by
      have hrM : (r : ℕ) + 1 ≤ M := by omega
      have hrT : (((r : ℕ) : ℝ) + 1) ≤ T := by
        have : ((((r : ℕ) + 1 : ℕ) : ℝ)) ≤ (M : ℝ) := Nat.cast_le.mpr hrM
        push_cast at this
        exact this.trans hMR
      exact mul_le_mul_of_nonneg_right hrT (sq_nonneg _)
  have haff := integral_Icc_normSq_dirPoly_le_affine c hT
  have hfull :
      (∫ t in Set.Icc (-T) T, ‖dirPoly M c t‖ ^ 2) ≤ C * E * T := by
    calc
      _ ≤ 5 * Real.pi * Real.exp 1 *
            (∑ r : Fin M, (((r : ℕ) : ℝ) + 1) * ‖c r‖ ^ 2) +
          (5 * Real.pi / 2) * E * T := by
        simpa only [M, c, E] using haff
      _ ≤ 5 * Real.pi * Real.exp 1 * (T * E) +
          (5 * Real.pi / 2) * E * T := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hweight (by positivity)) le_rfl
      _ = C * E * T := by
        dsimp only [C]
        ring
  have hreflect :
      (∫ t in Set.Icc (-T) T, ‖dirPoly M c (-t)‖ ^ 2) =
        ∫ t in Set.Icc (-T) T, ‖dirPoly M c t‖ ^ 2 := by
    exact GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg
      (fun t : ℝ => dirPoly M c t) hT0
  have hcont : Continuous (fun t : ℝ => ‖dirPoly M c (-t)‖ ^ 2) :=
    ((continuous_dirPoly M c).comp continuous_neg).norm.pow 2
  have hsubset : Set.Ioc (T / 2) T ⊆ Set.Icc (-T) T := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hmono :
      (∫ t in Set.Ioc (T / 2) T, ‖dirPoly M c (-t)‖ ^ 2) ≤
        ∫ t in Set.Icc (-T) T, ‖dirPoly M c (-t)‖ ^ 2 := by
    exact MeasureTheory.setIntegral_mono_set hcont.integrableOn_Icc
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall fun _ ht => hsubset ht)
  have hsource := sum_norm_sq_mtWattProductDirCoeff_le_energy a hA hN hN'
  have hES : E ≤ S := by
    simpa only [E, S, M, c] using hsource
  calc
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) =
        ∫ t in (T / 2)..T, ‖dirPoly M c (-t)‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      change ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 =
        ‖dirPoly M c (-t)‖ ^ 2
      rw [show dirPoly M c (-t) =
          mtWattUnitBlock N N' t * mtWattUnitBlock N N' t *
            mtWattCoefficientBlock a A t by
        simpa only [M, c] using (mtWattProduct_eq_dirPoly a A N N' t).symm]
      simp only [norm_mul]
      ring
    _ = ∫ t in Set.Ioc (T / 2) T, ‖dirPoly M c (-t)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith)]
    _ ≤ ∫ t in Set.Icc (-T) T, ‖dirPoly M c (-t)‖ ^ 2 := hmono
    _ ≤ C * E * T := by rw [hreflect]; exact hfull
    _ = (C * T) * E := by ring
    _ ≤ (C * T) * S :=
      mul_le_mul_of_nonneg_left hES (mul_nonneg hC0 hT0)
    _ = (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2) *
        (1 / (A : ℝ) ^ 2) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) * T := by
      dsimp only [C, S]
      ring

end

end RHTower.Sieve
