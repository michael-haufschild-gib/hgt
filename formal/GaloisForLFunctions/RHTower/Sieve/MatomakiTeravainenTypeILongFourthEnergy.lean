import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierCanonicalScalar
import GaloisForLFunctions.RHTower.Sieve.ProdIdxFibreDivisorBound
import GaloisForLFunctions.RHTower.Sieve.DirichletConvolutionDivisorReindex

/-!
# Energy bound for the Type-I long-factor fourth moment

The long fourth moment is the affine mean square of the Dirichlet-convolution square of one
dyadic coefficient block.  This file identifies that square with the corpus's finite `dirConv`
coefficient and applies the unconditional divisor-fibre `ell^(2 : ℕ)` estimate.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Finite positive-index coefficients attached to an arithmetic function. -/
def arithmeticFunctionFinCoeff (F : ArithmeticFunction ℂ) (N : ℕ) : Fin N → ℂ :=
  fun j => F ((j : ℕ) + 1)

/-- Positive-natural extension recovers an arithmetic function supported on `[1,N]`. -/
theorem finCoeffNat_arithmeticFunctionFinCoeff_eq
    (F : ArithmeticFunction ℂ) (N n : ℕ)
    (hsupport : ∀ {m : ℕ}, F m ≠ 0 → m ∈ Finset.Icc 1 N) :
    finCoeffNat N (arithmeticFunctionFinCoeff F N) n = F n := by
  rw [finCoeffNat]
  split_ifs with hn
  · change F ((n - 1) + 1) = F n
    rw [Nat.sub_add_cancel hn.1]
  · symm
    by_contra hne
    exact hn (by simpa only [Finset.mem_Icc] using hsupport hne)

/-- The long-factor convolution square is exactly the finite product-fibre coefficient. -/
theorem mtTypeILongSquareAF_succ_eq_dirConv
    (a : ℕ → ℂ) (A : ℕ) (r : Fin ((2 * A) * (2 * A))) :
    mtTypeILongSquareAF a A ((r : ℕ) + 1) =
      dirConv (2 * A) (2 * A)
        (arithmeticFunctionFinCoeff
          (mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)) (2 * A))
        (arithmeticFunctionFinCoeff
          (mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)) (2 * A)) r := by
  let F := mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)
  have hsupport : ∀ {n : ℕ}, F n ≠ 0 → n ∈ Finset.Icc 1 (2 * A) := by
    intro n hn
    exact mtWattCoefficientBlock_support a A n (by simpa only [F] using hn)
  calc
    mtTypeILongSquareAF a A ((r : ℕ) + 1) =
        mtCoefficientConvolution (fun n => F n) (fun n => F n) ((r : ℕ) + 1) := by
      exact (congrFun (mtCoefficientConvolution_eq_arithmeticFunction_mul F F)
        ((r : ℕ) + 1)).symm
    _ = dirConv (2 * A) (2 * A)
        (arithmeticFunctionFinCoeff F (2 * A))
        (arithmeticFunctionFinCoeff F (2 * A)) r := by
      rw [dirConv_eq_sum_divisors_finCoeffNat]
      simp_rw [finCoeffNat_arithmeticFunctionFinCoeff_eq F (2 * A) _ hsupport]
      rfl

/-- Complete `ell^(2 : ℕ)` energy of the long-factor convolution square. -/
theorem exists_sum_normSq_mtTypeILongSquareAF_le_rpow
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A : ℕ),
      ∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          ‖mtTypeILongSquareAF a A n‖ ^ 2 ≤
        C * ((((2 * A) * (2 * A) : ℕ) : ℝ)) ^ eta *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) ^ 2 := by
  obtain ⟨C, hC, hconv⟩ := exists_sum_norm_sq_dirConv_le_rpow heta
  refine ⟨C, hC, ?_⟩
  intro a A
  let F := mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)
  let b := arithmeticFunctionFinCoeff F (2 * A)
  have hbound := hconv (2 * A) (2 * A) b b
  have hlong :
      (∑ r : Fin ((2 * A) * (2 * A)),
          ‖dirConv (2 * A) (2 * A) b b r‖ ^ 2) =
        ∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          ‖mtTypeILongSquareAF a A n‖ ^ 2 := by
    rw [← sum_fin_eq_sum_Icc]
    apply Finset.sum_congr rfl
    intro r _
    rw [mtTypeILongSquareAF_succ_eq_dirConv]
  have hsource :
      (∑ j : Fin (2 * A), ‖b j‖ ^ 2) =
        ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 := by
    dsimp only [b, arithmeticFunctionFinCoeff, F]
    calc
      (∑ j : Fin (2 * A),
          ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) ((j : ℕ) + 1)‖ ^ 2) =
          ∑ n ∈ Finset.Icc 1 (2 * A),
            ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 :=
        sum_fin_eq_sum_Icc (2 * A) (fun n =>
          ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2)
      _ = _ := sum_normSq_mtWattCoefficientBlock_eq a A
  rw [hlong, hsource] at hbound
  simpa only [pow_two] using hbound

/-- The long convolution square retains the squared dyadic support interval. -/
theorem mtTypeILongSquareAF_scaleSupported (a : ℕ → ℂ) (A : ℕ) :
    MTRealScaleSupported (mtTypeILongSquareAF a A)
      ((A : ℝ) ^ 2) ((2 * A : ℝ) ^ 2) := by
  have hF : MTRealScaleSupported
      (mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)) (A : ℝ) (2 * A : ℝ) :=
    mtRealIntervalAF_scaleSupported a (A : ℝ) (2 * A : ℝ)
  have hmul : MTRealScaleSupported
      (mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) *
        mtRealIntervalAF a (A : ℝ) (2 * A : ℝ))
      ((A : ℝ) * A) ((2 * A : ℝ) * (2 * A : ℝ)) :=
    MTRealScaleSupported.mul (F := mtRealIntervalAF a (A : ℝ) (2 * A : ℝ))
      (G := mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)) hF hF
      (by positivity) (by positivity)
  intro n hn
  have hs := hmul (by simpa only [mtTypeILongSquareAF] using hn)
  simpa only [pow_two] using hs

/-- On the squared dyadic support, the height-independent Perron weight costs `A⁻²`. -/
theorem mtTypeILongSquareAF_weightedMass_term_le
    (a : ℕ → ℂ) {A n : ℕ} (hA : 1 ≤ A) :
    (n : ℝ) * ‖mtTypeILongSquareAF a A n *
        (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2 ≤
      (1 / (A : ℝ) ^ 2) * ‖mtTypeILongSquareAF a A n‖ ^ 2 := by
  by_cases hzero : mtTypeILongSquareAF a A n = 0
  · simp [hzero]
  · have hs := mtTypeILongSquareAF_scaleSupported a A hzero
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs.1
    have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hA2pos : (0 : ℝ) < (A : ℝ) ^ 2 := sq_pos_of_pos hApos
    have hinv : (n : ℝ)⁻¹ ≤ ((A : ℝ) ^ 2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hA2pos hs.2.1.le
    rw [Real.rpow_neg_one]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hnpos, one_div]
    have hnorm : 0 ≤ ‖mtTypeILongSquareAF a A n‖ ^ 2 := sq_nonneg _
    calc
      (n : ℝ) * (‖mtTypeILongSquareAF a A n‖ * (n : ℝ)⁻¹) ^ 2 =
          (n : ℝ)⁻¹ * ‖mtTypeILongSquareAF a A n‖ ^ 2 := by field_simp
      _ ≤ ((A : ℝ) ^ 2)⁻¹ * ‖mtTypeILongSquareAF a A n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hinv hnorm

/-- On the squared dyadic support, the height-linear Perron weight costs `A⁻⁴`. -/
theorem mtTypeILongSquareAF_plainMass_term_le
    (a : ℕ → ℂ) {A n : ℕ} (hA : 1 ≤ A) :
    ‖mtTypeILongSquareAF a A n *
        (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2 ≤
      (1 / ((A : ℝ) ^ 2) ^ 2) * ‖mtTypeILongSquareAF a A n‖ ^ 2 := by
  by_cases hzero : mtTypeILongSquareAF a A n = 0
  · simp [hzero]
  · have hs := mtTypeILongSquareAF_scaleSupported a A hzero
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs.1
    have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hA2pos : (0 : ℝ) < (A : ℝ) ^ 2 := sq_pos_of_pos hApos
    have hinv : (n : ℝ)⁻¹ ≤ ((A : ℝ) ^ 2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hA2pos hs.2.1.le
    rw [Real.rpow_neg_one]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hnpos, one_div]
    have hinv0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnpos.le
    have hinvSq : (n : ℝ)⁻¹ ^ 2 ≤ ((A : ℝ) ^ 2)⁻¹ ^ 2 :=
      pow_le_pow_left₀ hinv0 hinv 2
    have hnorm : 0 ≤ ‖mtTypeILongSquareAF a A n‖ ^ 2 := sq_nonneg _
    calc
      (‖mtTypeILongSquareAF a A n‖ * (n : ℝ)⁻¹) ^ 2 =
          (n : ℝ)⁻¹ ^ 2 * ‖mtTypeILongSquareAF a A n‖ ^ 2 := by ring
      _ ≤ ((A : ℝ) ^ 2)⁻¹ ^ 2 * ‖mtTypeILongSquareAF a A n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hinvSq hnorm
      _ = (((A : ℝ) ^ 2) ^ 2)⁻¹ * ‖mtTypeILongSquareAF a A n‖ ^ 2 := by
        rw [inv_pow]

/-- Height-independent affine mass of the long convolution square. -/
theorem generalMeanSquareConst_mtTypeILongSquareAF_le_energy
    (a : ℕ → ℂ) {A : ℕ} (hA : 1 ≤ A) :
    generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
        (Finset.Icc 1 ((2 * A) * (2 * A))) 1 ≤
      5 * Real.pi * Real.exp 1 * (1 / (A : ℝ) ^ 2) *
        (∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          ‖mtTypeILongSquareAF a A n‖ ^ 2) := by
  rw [generalMeanSquareConst]
  have hsum :
      (∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          (n : ℝ) * ‖mtTypeILongSquareAF a A n *
            (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          (1 / (A : ℝ) ^ 2) * ‖mtTypeILongSquareAF a A n‖ ^ 2 :=
    Finset.sum_le_sum fun n _ =>
      mtTypeILongSquareAF_weightedMass_term_le a hA (n := n)
  have hfac : 0 ≤ 5 * Real.pi * Real.exp 1 := by positivity
  calc
    5 * Real.pi * Real.exp 1 *
        (∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          (n : ℝ) * ‖mtTypeILongSquareAF a A n *
            (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2) ≤
      5 * Real.pi * Real.exp 1 *
        ((1 / (A : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
            ‖mtTypeILongSquareAF a A n‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hfac
      simpa only [Finset.mul_sum] using hsum
    _ = _ := by ring

/-- Height-linear affine mass of the long convolution square. -/
theorem generalMeanSquareRate_mtTypeILongSquareAF_le_energy
    (a : ℕ → ℂ) {A : ℕ} (hA : 1 ≤ A) :
    generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
        (Finset.Icc 1 ((2 * A) * (2 * A))) 1 ≤
      (5 * Real.pi / 2) * (1 / ((A : ℝ) ^ 2) ^ 2) *
        (∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          ‖mtTypeILongSquareAF a A n‖ ^ 2) := by
  rw [generalMeanSquareRate]
  have hsum :
      (∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          ‖mtTypeILongSquareAF a A n *
            (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          (1 / ((A : ℝ) ^ 2) ^ 2) * ‖mtTypeILongSquareAF a A n‖ ^ 2 :=
    Finset.sum_le_sum fun n _ =>
      mtTypeILongSquareAF_plainMass_term_le a hA (n := n)
  have hfac : 0 ≤ 5 * Real.pi / 2 := by positivity
  calc
    (5 * Real.pi / 2) *
        (∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
          ‖mtTypeILongSquareAF a A n *
            (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2) ≤
      (5 * Real.pi / 2) *
        ((1 / ((A : ℝ) ^ 2) ^ 2) *
          ∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
            ‖mtTypeILongSquareAF a A n‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hfac
      simpa only [Finset.mul_sum] using hsum
    _ = _ := by ring

/-- Complete affine fourth-moment envelope in source coefficient energy. -/
theorem exists_mtTypeILongFourthAffine_le_rpow_energy
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A : ℕ) (T : ℝ),
      1 ≤ A → 0 ≤ T →
      generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T ≤
        C * ((((2 * A) * (2 * A) : ℕ) : ℝ)) ^ eta *
          (5 * Real.pi * Real.exp 1 * (1 / (A : ℝ) ^ 2) +
            (5 * Real.pi / 2) * (1 / ((A : ℝ) ^ 2) ^ 2) * T) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) ^ 2 := by
  obtain ⟨C, hC, hmass⟩ := exists_sum_normSq_mtTypeILongSquareAF_le_rpow heta
  refine ⟨C, hC, ?_⟩
  intro a A T hA hT
  let S := ∑ n ∈ Finset.Icc 1 ((2 * A) * (2 * A)),
    ‖mtTypeILongSquareAF a A n‖ ^ 2
  let E := ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2
  let K0 := 5 * Real.pi * Real.exp 1 * (1 / (A : ℝ) ^ 2)
  let K1 := (5 * Real.pi / 2) * (1 / ((A : ℝ) ^ 2) ^ 2)
  have hconst := generalMeanSquareConst_mtTypeILongSquareAF_le_energy a hA
  have hrate := generalMeanSquareRate_mtTypeILongSquareAF_le_energy a hA
  have hmass' : S ≤ C * ((((2 * A) * (2 * A) : ℕ) : ℝ)) ^ eta * E ^ 2 :=
    hmass a A
  have hK : 0 ≤ K0 + K1 * T := by
    dsimp only [K0, K1]
    positivity
  dsimp only [S, E, K0, K1] at hconst hrate hmass' ⊢
  calc
    _ ≤ (5 * Real.pi * Real.exp 1 * (1 / (A : ℝ) ^ 2)) * S +
        ((5 * Real.pi / 2) * (1 / ((A : ℝ) ^ 2) ^ 2)) * S * T :=
      add_le_add hconst (mul_le_mul_of_nonneg_right hrate hT)
    _ = (K0 + K1 * T) * S := by ring
    _ ≤ (K0 + K1 * T) *
        (C * ((((2 * A) * (2 * A) : ℕ) : ℝ)) ^ eta * E ^ 2) :=
      mul_le_mul_of_nonneg_left hmass' hK
    _ = _ := by ring

end

end RHTower.Sieve
