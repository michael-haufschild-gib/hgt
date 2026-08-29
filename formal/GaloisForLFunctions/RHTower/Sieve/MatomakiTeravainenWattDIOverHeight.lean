import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPerronFactorization
import GaloisForLFunctions.RHTower.Sieve.MaynardKuzminLandauFactor
import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare

/-!
# Over-height branch of the Watt--Deshouillers--Iwaniec moment

Matomäki--Teräväinen Lemma 3.5 splits at the length of its unit-coefficient factor.  When that
length exceeds the ordinate height, Kuzmin--Landau gives a pointwise `T⁻¹` bound for the factor;
the remaining coefficient polynomial is paid by the ordinary affine mean-square theorem.

This file proves that branch with explicit constants for the exact Perron-line polynomials.  No
Watt, Deshouillers--Iwaniec, or spectral premise remains in this regime.  The complementary
sub-height branch is the deep twisted-moment input still needed by the Type-I and Type-I/II cases.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Unit-coefficient Perron block on the exact natural interval `(N,N']`. -/
def mtWattUnitBlock (N N' : ℕ) (t : ℝ) : ℂ :=
  perronPoly (fun n => mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ) n) N' 1 t

/-- Dyadic coefficient block on `(A,2A]`, normalized on the Perron line. -/
def mtWattCoefficientBlock (a : ℕ → ℂ) (A : ℕ) (t : ℝ) : ℂ :=
  perronPoly (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n) (2 * A) 1 t

/-- The Perron representation is the literal Dirichlet block used by Kuzmin--Landau. -/
theorem mtWattUnitBlock_eq_sum_Ico
    {N N' : ℕ} (t : ℝ) :
    mtWattUnitBlock N N' t =
      ∑ n ∈ Finset.Ico (N + 1) (N' + 1),
        (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (t : ℂ)) := by
  classical
  rw [mtWattUnitBlock, perronPoly]
  rw [show Finset.Ico (N + 1) (N' + 1) = Finset.Ioc N N' by ext n; simp]
  have hsub : Finset.Ioc N N' ⊆ Finset.Icc 1 N' := by
    intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    omega
  have hsum :
      (∑ n ∈ Finset.Icc 1 N',
          mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ) n *
            (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * I))) =
        ∑ n ∈ Finset.Ioc N N',
          mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ) n *
            (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * I)) := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hnmem
    have hnpos : 0 < n := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos]
    have hnot : ¬((N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (N' : ℝ)) := by
      have hnotNat : ¬(N < n ∧ n ≤ N') := by
        simpa only [Finset.mem_Ioc] using hnmem
      exact_mod_cast hnotNat
    rw [if_neg hnot, zero_mul]
  calc
    (∑ n ∈ Finset.Icc 1 N',
        mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ) n *
          (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * I))) =
        ∑ n ∈ Finset.Ioc N N',
          mtRealIntervalAF (fun _ => 1) (N : ℝ) (N' : ℝ) n *
            (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * I)) := by simpa using hsum
    _ = ∑ n ∈ Finset.Ioc N N',
        (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (t : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := by
        simp only [Finset.mem_Ioc] at hn
        omega
      rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos]
      have hmem : (N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (N' : ℝ) := by
        simp only [Finset.mem_Ioc] at hn
        exact_mod_cast hn
      rw [if_pos hmem, one_mul]
      congr 1
      ring

/-- Above the ordinate height, the unit block has one full reciprocal-height saving. -/
theorem norm_mtWattUnitBlock_le_over_height
    {N N' : ℕ} (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {T t : ℝ} (hT : 0 < T) (hTt : T / 2 ≤ t) (htT : t ≤ T)
    (hTN : T ≤ (N : ℝ)) :
    ‖mtWattUnitBlock N N' t‖ ≤ 2 * (6 * Real.pi + 1) / T := by
  rw [mtWattUnitBlock_eq_sum_Ico]
  have ht : 0 < t := (by linarith : 0 < T / 2).trans_le hTt
  have hlower : 1 ≤ N + 1 := by omega
  have hrange : N + 1 ≤ N' + 1 := by omega
  have hdyadic : N' + 1 ≤ 2 * (N + 1) := by omega
  have hbase : T / 2 ≤ ((N + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hreg : 3 * t ≤ 4 * Real.pi * ((N + 1 : ℕ) : ℝ) := by
    have hpi := Real.pi_gt_three
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    push_cast
    nlinarith
  have hraw := norm_dirichletBlock_sigma_le_kuzminLandau
    (sigma := (1 : ℝ)) (by norm_num) t ht (N + 1) (N' + 1) hlower hrange hdyadic hreg
  have hpref := kuzminLandau_envelope_le_over_height
    (T := T / 2) (t := t) (N := ((N + 1 : ℕ) : ℝ))
    (by positivity) hTt hbase
  have hbasepos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hweight0 : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_nonneg hbasepos.le _
  have hscaled := mul_le_mul_of_nonneg_right hpref hweight0
  calc
    ‖∑ n ∈ Finset.Ico (N + 1) (N' + 1),
        (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (t : ℂ))‖
        ≤ (6 * Real.pi * ((N + 1 : ℕ) : ℝ) / t + 1) *
            ((N + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) := by simpa using hraw
    _ ≤ ((6 * Real.pi + 1) * ((N + 1 : ℕ) : ℝ) / (T / 2)) *
            ((N + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) := hscaled
    _ = 2 * (6 * Real.pi + 1) / T := by
      rw [Real.rpow_neg_one]
      field_simp

/-- Canonical natural cutoff contains the complete dyadic coefficient block. -/
theorem mtWattCoefficientBlock_support (a : ℕ → ℂ) (A : ℕ) :
    ∀ n, mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n ≠ 0 →
      n ∈ Finset.Icc 1 (2 * A) := by
  intro n hn
  have hs := mtRealIntervalAF_support_nat a (A : ℝ) (2 * A : ℝ) n hn
  have hceil : ⌈(2 * (A : ℝ))⌉₊ = 2 * A := by
    convert Nat.ceil_natCast (R := ℝ) (2 * A) using 1
    norm_num
  simpa only [hceil] using hs

/-- Affine mean square of the exact coefficient block. -/
theorem integral_Icc_normSq_mtWattCoefficientBlock_le_general_affine
    (a : ℕ → ℂ) (A : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      generalMeanSquareConst
          (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
          (Finset.Icc 1 (2 * A)) 1 +
        generalMeanSquareRate
          (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
          (Finset.Icc 1 (2 * A)) 1 * T := by
  let f : ℕ → ℂ := fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n
  have hsupp : ∀ n, f n ≠ 0 → n ∈ Finset.Icc 1 (2 * A) :=
    mtWattCoefficientBlock_support a A
  have hpoly : ∀ t : ℝ,
      mtWattCoefficientBlock a A t = LSeries f (((1 : ℝ) : ℂ) + (t : ℝ) * I) := by
    intro t
    exact perronPoly_eq_LSeries_of_support hsupp 1 t
  simpa only [hpoly, f] using
    integral_Icc_normSq_LSeries_le_general_affine
      (a := f) (s := Finset.Icc 1 (2 * A)) (by simp) hsupp 1 hT

/-- Unconditional over-height branch of both Watt's and Deshouillers--Iwaniec's hybrid moments.
The fourth power of the long unit block contributes `T⁻⁴`; the arbitrary coefficient block is
charged only its explicit affine mean-square masses. -/
theorem integral_mtWatt_overHeight_le_generalAffine
    (a : ℕ → ℂ) {A N N' : ℕ}
    (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {T : ℝ} (hT : 1 ≤ T) (hTN : T ≤ (N : ℝ)) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      (2 * (6 * Real.pi + 1) / T) ^ 4 *
        (generalMeanSquareConst
            (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
            (Finset.Icc 1 (2 * A)) 1 +
          generalMeanSquareRate
            (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
            (Finset.Icc 1 (2 * A)) 1 * T) := by
  let C : ℝ := 2 * (6 * Real.pi + 1) / T
  let B : ℝ := generalMeanSquareConst
      (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
      (Finset.Icc 1 (2 * A)) 1 +
    generalMeanSquareRate
      (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
      (Finset.Icc 1 (2 * A)) 1 * T
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hunit : ∀ t ∈ Set.Icc (T / 2) T, ‖mtWattUnitBlock N N' t‖ ≤ C := by
    intro t ht
    exact norm_mtWattUnitBlock_le_over_height hN hNN' hN' hTpos ht.1 ht.2 hTN
  have hpoint : ∀ t ∈ Set.Icc (T / 2) T,
      ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 ≤
        C ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 := by
    intro t ht
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hunit t ht) 4) (sq_nonneg _)
  have hunitCont : Continuous (mtWattUnitBlock N N') :=
    continuous_perronPoly _ _ _
  have hcoeffCont : Continuous (mtWattCoefficientBlock a A) :=
    continuous_perronPoly _ _ _
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t : ℝ => ‖mtWattUnitBlock N N' t‖ ^ 4 *
      ‖mtWattCoefficientBlock a A t‖ ^ 2)
    (g := fun t : ℝ => C ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2)
    (by linarith : T / 2 ≤ T)
    (((hunitCont.norm.pow 4).mul (hcoeffCont.norm.pow 2)).intervalIntegrable _ _)
    ((continuous_const.mul (hcoeffCont.norm.pow 2)).intervalIntegrable _ _) hpoint
  have hfullSet := integral_Icc_normSq_mtWattCoefficientBlock_le_general_affine a A hT
  have hfull : (∫ t in (-T)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ B := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hfullSet
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => ‖mtWattCoefficientBlock a A t‖ ^ 2)
    (μ := volume) (a := -T) (b := T / 2) (c := T)
    ((hcoeffCont.norm.pow 2).intervalIntegrable _ _)
    ((hcoeffCont.norm.pow 2).intervalIntegrable _ _)
  have hleft : 0 ≤ ∫ t in (-T)..(T / 2), ‖mtWattCoefficientBlock a A t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hsub : (∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ B := by
    linarith [hsplit, hleft, hfull]
  rw [intervalIntegral.integral_const_mul] at hmono
  have hscaled := mul_le_mul_of_nonneg_left hsub (pow_nonneg hC0 4)
  dsimp only [C, B] at hmono hscaled ⊢
  exact hmono.trans hscaled

/-- On `(A,2A]`, the `n`-weighted Perron mass costs at most `A⁻¹` per coefficient. -/
theorem mtWatt_weightedMass_term_le
    (a : ℕ → ℂ) {A n : ℕ} (hA : 1 ≤ A) :
    (n : ℝ) * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n *
        (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2 ≤
      (1 / (A : ℝ)) * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := by
  by_cases hzero : mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n = 0
  · simp [hzero]
  · have hs := mtRealIntervalAF_scaleSupported a (A : ℝ) (2 * A : ℝ) hzero
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs.1
    have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hinv : (n : ℝ)⁻¹ ≤ (A : ℝ)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hApos hs.2.1.le
    rw [Real.rpow_neg_one]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hnpos, one_div]
    have hnorm : 0 ≤ ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := sq_nonneg _
    calc
      (n : ℝ) *
          (‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ * (n : ℝ)⁻¹) ^ 2 =
          (n : ℝ)⁻¹ * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := by
            field_simp
      _ ≤ (A : ℝ)⁻¹ * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hinv hnorm

/-- On `(A,2A]`, the plain Perron mass costs at most `A⁻²` per coefficient. -/
theorem mtWatt_plainMass_term_le
    (a : ℕ → ℂ) {A n : ℕ} (hA : 1 ≤ A) :
    ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n *
        (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2 ≤
      (1 / (A : ℝ) ^ 2) * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := by
  by_cases hzero : mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n = 0
  · simp [hzero]
  · have hs := mtRealIntervalAF_scaleSupported a (A : ℝ) (2 * A : ℝ) hzero
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs.1
    have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hinv : (n : ℝ)⁻¹ ≤ (A : ℝ)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hApos hs.2.1.le
    rw [Real.rpow_neg_one]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hnpos, one_div]
    have hinv0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnpos.le
    have hAinv0 : 0 ≤ (A : ℝ)⁻¹ := inv_nonneg.mpr hApos.le
    have hinvSq : (n : ℝ)⁻¹ ^ 2 ≤ (A : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_left₀ hinv0 hinv 2
    have hnorm : 0 ≤ ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := sq_nonneg _
    calc
      (‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ * (n : ℝ)⁻¹) ^ 2 =
          (n : ℝ)⁻¹ ^ 2 * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := by ring
      _ ≤ (A : ℝ)⁻¹ ^ 2 * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hinvSq hnorm
      _ = ((A : ℝ) ^ 2)⁻¹ * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := by
        rw [inv_pow]

/-- Restricting to `(A,2A]` preserves exactly the source coefficient energy on that interval. -/
theorem sum_normSq_mtWattCoefficientBlock_eq
    (a : ℕ → ℂ) (A : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2 * A),
        ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 =
      ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 := by
  classical
  have hsub : Finset.Ioc A (2 * A) ⊆ Finset.Icc 1 (2 * A) := by
    intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    omega
  have hrestrict :
      (∑ n ∈ Finset.Icc 1 (2 * A),
          ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2) =
        ∑ n ∈ Finset.Ioc A (2 * A),
          ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hnmem
    have hnpos : 0 < n := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos]
    have hnotNat : ¬(A < n ∧ n ≤ 2 * A) := by
      simpa only [Finset.mem_Ioc] using hnmem
    have hnot : ¬((A : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (2 * A : ℝ)) := by
      exact_mod_cast hnotNat
    rw [if_neg hnot, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [hrestrict]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := by
    simp only [Finset.mem_Ioc] at hn
    omega
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos]
  have hmem : (A : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (2 * A : ℝ) := by
    simp only [Finset.mem_Ioc] at hn
    exact_mod_cast hn
  rw [if_pos hmem]

/-- The constant affine mass is bounded by `5πe/A` times the literal coefficient energy. -/
theorem generalMeanSquareConst_mtWattCoefficientBlock_le_energy
    (a : ℕ → ℂ) {A : ℕ} (hA : 1 ≤ A) :
    generalMeanSquareConst
        (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
        (Finset.Icc 1 (2 * A)) 1 ≤
      5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) := by
  rw [generalMeanSquareConst]
  have hsum :
      ∑ n ∈ Finset.Icc 1 (2 * A),
          (n : ℝ) * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n *
            (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2 ≤
        (1 / (A : ℝ)) *
          ∑ n ∈ Finset.Icc 1 (2 * A),
            ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => mtWatt_weightedMass_term_le a hA
  have hfac : 0 ≤ 5 * Real.pi * Real.exp 1 := by positivity
  calc
    5 * Real.pi * Real.exp 1 *
        ∑ n ∈ Finset.Icc 1 (2 * A),
          (n : ℝ) * ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n *
            (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2 ≤
        5 * Real.pi * Real.exp 1 *
          ((1 / (A : ℝ)) *
            ∑ n ∈ Finset.Icc 1 (2 * A),
              ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hfac
    _ = 5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) := by
      rw [sum_normSq_mtWattCoefficientBlock_eq]
      ring

/-- The height-linear affine mass is bounded by `5π/(2A²)` times coefficient energy. -/
theorem generalMeanSquareRate_mtWattCoefficientBlock_le_energy
    (a : ℕ → ℂ) {A : ℕ} (hA : 1 ≤ A) :
    generalMeanSquareRate
        (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
        (Finset.Icc 1 (2 * A)) 1 ≤
      (5 * Real.pi / 2) * (1 / (A : ℝ) ^ 2) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) := by
  rw [generalMeanSquareRate]
  have hsum :
      ∑ n ∈ Finset.Icc 1 (2 * A),
          ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n *
            (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2 ≤
        (1 / (A : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc 1 (2 * A),
            ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => mtWatt_plainMass_term_le a hA
  have hfac : 0 ≤ 5 * Real.pi / 2 := by positivity
  calc
    (5 * Real.pi / 2) *
        ∑ n ∈ Finset.Icc 1 (2 * A),
          ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n *
            (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ ^ 2 ≤
        (5 * Real.pi / 2) *
          ((1 / (A : ℝ) ^ 2) *
            ∑ n ∈ Finset.Icc 1 (2 * A),
              ‖mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hfac
    _ = (5 * Real.pi / 2) * (1 / (A : ℝ) ^ 2) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) := by
      rw [sum_normSq_mtWattCoefficientBlock_eq]
      ring

/-- Energy form of the over-height hybrid moment, matching the residual term in both parts of
Matomäki--Teräväinen Lemma 3.5 up to explicit absolute constants. -/
theorem integral_mtWatt_overHeight_le_energy
    (a : ℕ → ℂ) {A N N' : ℕ} (hA : 1 ≤ A)
    (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {T : ℝ} (hT : 1 ≤ T) (hTN : T ≤ (N : ℝ)) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      (2 * (6 * Real.pi + 1) / T) ^ 4 *
        (5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) +
          (5 * Real.pi / 2) * (1 / (A : ℝ) ^ 2) * T) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) := by
  have hbase := integral_mtWatt_overHeight_le_generalAffine (A := A) a hN hNN' hN' hT hTN
  have hconst := generalMeanSquareConst_mtWattCoefficientBlock_le_energy a hA
  have hrate := generalMeanSquareRate_mtWattCoefficientBlock_le_energy a hA
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hrateT := mul_le_mul_of_nonneg_right hrate hT0
  have hmass :
      generalMeanSquareConst
          (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
          (Finset.Icc 1 (2 * A)) 1 +
        generalMeanSquareRate
          (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
          (Finset.Icc 1 (2 * A)) 1 * T ≤
        (5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) +
          (5 * Real.pi / 2) * (1 / (A : ℝ) ^ 2) * T) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) := by
    calc
      _ ≤ 5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) *
            (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) +
          ((5 * Real.pi / 2) * (1 / (A : ℝ) ^ 2) *
            (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2)) * T := add_le_add hconst hrateT
      _ = _ := by ring
  have hC0 : 0 ≤ (2 * (6 * Real.pi + 1) / T) ^ 4 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmass hC0
  calc
    _ ≤ (2 * (6 * Real.pi + 1) / T) ^ 4 *
        (generalMeanSquareConst
            (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
            (Finset.Icc 1 (2 * A)) 1 +
          generalMeanSquareRate
            (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
            (Finset.Icc 1 (2 * A)) 1 * T) := hbase
    _ ≤ (2 * (6 * Real.pi + 1) / T) ^ 4 *
        ((5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) +
          (5 * Real.pi / 2) * (1 / (A : ℝ) ^ 2) * T) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2)) := hscaled
    _ = _ := by ring


end

end RHTower.Sieve
