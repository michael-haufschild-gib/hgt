import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattProductMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LogPhaseKernelBound
import GaloisForLFunctions.RHTower.Sieve.DirichletMeasureLargeValues
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35OverHeight

/-!
# Large coefficient-length branch of Matomäki--Teräväinen Lemma 3.5

The previously exposed premise `A ≤ T` is discharged by treating its complement directly.
An unconditional second-derivative estimate gives
`|N(1+it)| ≪ sqrt T / N + 1 / sqrt T`; the coefficient block is controlled by its
constructed affine mean square.  Splitting at `N² ≤ A sqrt T` yields the literal
Deshouillers--Iwaniec envelope throughout `N < T ≤ A`, with no spectral hypothesis.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

theorem norm_logPhase_partial_block_le_affine
    {N L : ℕ} (hN : 1 ≤ N) (hL : L ≤ N) {t : ℝ} (ht : 0 < t) :
    ‖∑ j ∈ Finset.range L,
        ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
      214 * Real.sqrt t + 1536 * ((N : ℝ) / Real.sqrt t) := by
  rcases Nat.eq_zero_or_pos L with rfl | hLpos
  · simp
    positivity
  · by_cases hlam : logDyadicLambda N t ≤ 1
    · exact (norm_logPhase_partial_block_le ht hN hLpos hL hlam).trans
        (logDyadicSecondBound_le_affine hN ht)
    · have htri :
          ‖∑ j ∈ Finset.range L,
              ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ (L : ℝ) := by
        calc
          _ ≤ ∑ j ∈ Finset.range L,
                ‖((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ := norm_sum_le _ _
          _ = ∑ _j ∈ Finset.range L, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact norm_cpow_imag_eq_one (by omega) t
          _ = (L : ℝ) := by simp
      exact htri.trans ((by exact_mod_cast hL : (L : ℝ) ≤ (N : ℝ)).trans
        (trivial_le_affine hN ht (lt_of_not_ge hlam)))

theorem norm_mtWattUnitBlock_le_secondDerivativeAffine
    {N N' : ℕ} (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {t : ℝ} (ht : 0 < t) :
    ‖mtWattUnitBlock N N' t‖ ≤
      214 * Real.sqrt t / ((N : ℝ) + 1) + 1536 / Real.sqrt t := by
  rw [mtWattUnitBlock_eq_sum_Ico]
  let P : ℝ := 214 * Real.sqrt t + 1536 * (((N : ℝ) + 1) / Real.sqrt t)
  have hprefix : ∀ m, N + 1 ≤ m → m ≤ N' + 1 →
      ‖∑ n ∈ Finset.Ico (N + 1) m,
          (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ P := by
    intro m hm hm'
    rw [Finset.sum_Ico_eq_sum_range]
    have hL : m - (N + 1) ≤ N + 1 := by omega
    simpa only [P, Nat.cast_add, Nat.cast_one] using
      norm_logPhase_partial_block_le_affine (show 1 ≤ N + 1 by omega) hL ht
  have hbase := dirichlet_block_one_bound t (N + 1) (N' + 1)
    (by omega) (by omega) P hprefix
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  calc
    ‖∑ n ∈ Finset.Ico (N + 1) (N' + 1),
        (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (t : ℂ))‖
        ≤ P * ((N : ℝ) + 1)⁻¹ := by simpa only [Nat.cast_add, Nat.cast_one] using hbase
    _ = 214 * Real.sqrt t / ((N : ℝ) + 1) + 1536 / Real.sqrt t := by
      dsimp only [P]
      field_simp

theorem norm_mtWattUnitBlock_le_one
    {N N' : ℕ} (hN : 1 ≤ N) (hN' : N' ≤ 2 * N) (t : ℝ) :
    ‖mtWattUnitBlock N N' t‖ ≤ 1 := by
  rw [mtWattUnitBlock_eq_dirPoly]
  exact (norm_dirPoly_le_sum_norm N' (mtWattUnitCoeff N N') (-t)).trans
    (sum_norm_mtWattUnitCoeff_le_one hN hN')

theorem norm_mtWattUnitBlock_le_secondDerivativeWindow
    {N N' : ℕ} (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {T t : ℝ} (hT : 0 < T) (hTt : T / 2 ≤ t) (htT : t ≤ T) :
    ‖mtWattUnitBlock N N' t‖ ≤
      3072 * (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) := by
  have ht : 0 < t := (by linarith : 0 < T / 2).trans_le hTt
  have hbase := norm_mtWattUnitBlock_le_secondDerivativeAffine hN hNN' hN' ht
  have hsTpos : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hstpos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hNs : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrt_le : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hsqrt_two : Real.sqrt T ≤ 2 * Real.sqrt t := by
    have hT0 : 0 ≤ T := hT.le
    have ht0 : 0 ≤ t := ht.le
    nlinarith [Real.sq_sqrt hT0, Real.sq_sqrt ht0]
  have hfirst : Real.sqrt t / ((N : ℝ) + 1) ≤ Real.sqrt T / (N : ℝ) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1) hNs]
    nlinarith [Real.sqrt_nonneg T, Real.sqrt_nonneg t]
  have hsecond : 1 / Real.sqrt t ≤ 2 / Real.sqrt T := by
    rw [div_le_div_iff₀ hstpos hsTpos]
    nlinarith
  calc
    ‖mtWattUnitBlock N N' t‖ ≤
        214 * Real.sqrt t / ((N : ℝ) + 1) + 1536 / Real.sqrt t := hbase
    _ ≤ 214 * (Real.sqrt T / (N : ℝ)) + 1536 * (2 / Real.sqrt T) := by
      exact add_le_add
        (calc
          214 * Real.sqrt t / ((N : ℝ) + 1) =
              214 * (Real.sqrt t / ((N : ℝ) + 1)) := by ring
          _ ≤ 214 * (Real.sqrt T / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfirst (by norm_num))
        (calc
          1536 / Real.sqrt t = 1536 * (1 / Real.sqrt t) := by ring
          _ ≤ 1536 * (2 / Real.sqrt T) :=
            mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ ≤ 3072 * (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) := by
      have hx : 0 ≤ Real.sqrt T / (N : ℝ) := by positivity
      have hy : 0 ≤ 1 / Real.sqrt T := by positivity
      calc
        214 * (Real.sqrt T / (N : ℝ)) + 1536 * (2 / Real.sqrt T) =
            214 * (Real.sqrt T / (N : ℝ)) + 3072 * (1 / Real.sqrt T) := by ring
        _ ≤ 3072 * (Real.sqrt T / (N : ℝ)) + 3072 * (1 / Real.sqrt T) := by
          gcongr
          norm_num
        _ = _ := by ring

def mtLemma35CoefficientMeanSquareConst : ℝ :=
  5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2

theorem integral_normSq_mtWattCoefficientBlock_le_largeA
    (a : ℕ → ℂ) {A : ℕ} (hA : 1 ≤ A)
    {T : ℝ} (hT : 1 ≤ T) (hTA : T ≤ (A : ℝ)) :
    (∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) := by
  let E : ℝ := ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2
  have hconst := generalMeanSquareConst_mtWattCoefficientBlock_le_energy a hA
  have hrate := generalMeanSquareRate_mtWattCoefficientBlock_le_energy a hA
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hrateT := mul_le_mul_of_nonneg_right hrate hT0
  have hmass :
      generalMeanSquareConst
          (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
          (Finset.Icc 1 (2 * A)) 1 +
        generalMeanSquareRate
          (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
          (Finset.Icc 1 (2 * A)) 1 * T ≤
        mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) * E := by
    calc
      _ ≤ 5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) * E +
          ((5 * Real.pi / 2) * (1 / (A : ℝ) ^ 2) * E) * T := by
        simpa only [E] using add_le_add hconst hrateT
      _ ≤ 5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) * E +
          (5 * Real.pi / 2) * (1 / (A : ℝ)) * E := by
        have hfac : 0 ≤ (5 * Real.pi / 2) * E := by positivity
        have hdiv : T / (A : ℝ) ^ 2 ≤ 1 / (A : ℝ) := by
          rw [div_le_div_iff₀ (sq_pos_of_pos hApos) hApos]
          nlinarith
        have hscaled := mul_le_mul_of_nonneg_left hdiv hfac
        calc
          _ = 5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) * E +
              ((5 * Real.pi / 2) * E) * (T / (A : ℝ) ^ 2) := by ring
          _ ≤ 5 * Real.pi * Real.exp 1 * (1 / (A : ℝ)) * E +
              ((5 * Real.pi / 2) * E) * (1 / (A : ℝ)) := by
            exact add_le_add le_rfl hscaled
          _ = _ := by ring
      _ = mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) * E := by
        dsimp only [mtLemma35CoefficientMeanSquareConst]
        ring
  have hfullSet := integral_Icc_normSq_mtWattCoefficientBlock_le_general_affine a A hT
  have hfull :
      (∫ t in (-T)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) * E := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hfullSet.trans hmass
  have hcont : Continuous (fun t : ℝ => ‖mtWattCoefficientBlock a A t‖ ^ 2) :=
    (continuous_perronPoly _ _ _).norm.pow 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => ‖mtWattCoefficientBlock a A t‖ ^ 2)
    (μ := volume) (a := -T) (b := T / 2) (c := T)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hleft : 0 ≤ ∫ t in (-T)..(T / 2), ‖mtWattCoefficientBlock a A t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  simpa only [E] using (show
    (∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) * E by linarith)

private theorem mtLemma35_secondDerivative_scalar_le
    {A N : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N)
    {T : ℝ} (hT : 1 ≤ T) (hTA : T ≤ (A : ℝ))
    (hhard : (A : ℝ) * Real.sqrt T ≤ (N : ℝ) ^ 2) :
    (Real.sqrt T / (N : ℝ)) ^ 4 * (1 / (A : ℝ)) ≤
      Real.sqrt T / (N : ℝ) ^ 2 := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hs0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hspos : 0 < Real.sqrt T := Real.sqrt_pos.2 (zero_lt_one.trans_le hT)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsquare : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0
  have hAsq : T ≤ (A : ℝ) ^ 2 := by nlinarith
  have hhardA := mul_le_mul_of_nonneg_left hhard hApos.le
  have hkey : Real.sqrt T ^ 3 ≤ (A : ℝ) * (N : ℝ) ^ 2 := by
    nlinarith [hsquare]
  calc
    (Real.sqrt T / (N : ℝ)) ^ 4 * (1 / (A : ℝ)) =
        Real.sqrt T ^ 4 / ((A : ℝ) * (N : ℝ) ^ 4) := by
      field_simp
    _ ≤ Real.sqrt T / (N : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos hApos (pow_pos hNpos 4)) (pow_pos hNpos 2)]
      have hcross := mul_le_mul_of_nonneg_right hkey
        (mul_nonneg hs0 (sq_nonneg (N : ℝ)))
      nlinarith [hcross]

private theorem integral_mtWatt_le_of_unit_bound_largeA
    (a : ℕ → ℂ) {A N N' : ℕ} (hA : 1 ≤ A)
    {T U : ℝ} (hT : 1 ≤ T) (hTA : T ≤ (A : ℝ)) (hU : 0 ≤ U)
    (hunit : ∀ t ∈ Set.Icc (T / 2) T, ‖mtWattUnitBlock N N' t‖ ≤ U) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 *
          ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      U ^ 4 * mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) := by
  have hpoint : ∀ t ∈ Set.Icc (T / 2) T,
      ‖mtWattUnitBlock N N' t‖ ^ 4 *
          ‖mtWattCoefficientBlock a A t‖ ^ 2 ≤
        U ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 := by
    intro t ht
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hunit t ht) 4) (sq_nonneg _)
  have hunitCont : Continuous (mtWattUnitBlock N N') := continuous_perronPoly _ _ _
  have hcoeffCont : Continuous (mtWattCoefficientBlock a A) := continuous_perronPoly _ _ _
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t : ℝ => ‖mtWattUnitBlock N N' t‖ ^ 4 *
      ‖mtWattCoefficientBlock a A t‖ ^ 2)
    (g := fun t : ℝ => U ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2)
    (by linarith : T / 2 ≤ T)
    (((hunitCont.norm.pow 4).mul (hcoeffCont.norm.pow 2)).intervalIntegrable _ _)
    ((continuous_const.mul (hcoeffCont.norm.pow 2)).intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hcoeff := integral_normSq_mtWattCoefficientBlock_le_largeA a hA hT hTA
  have hU4 : 0 ≤ U ^ 4 := pow_nonneg hU 4
  have hscaled := mul_le_mul_of_nonneg_left hcoeff hU4
  exact hmono.trans (by simpa only [mul_assoc] using hscaled)

def mtLemma35LargeAConst : ℝ := mtLemma35CoefficientMeanSquareConst * (6144 : ℝ) ^ 4

theorem integral_mtDI_lemma35_largeA
    (a : ℕ → ℂ) {A N N' : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N)
    (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {T : ℝ} (hT : 2 ≤ T) (hNT : (N : ℝ) < T) (hTA : T ≤ (A : ℝ)) :
    (∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 *
          ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      mtLemma35LargeAConst * (Real.sqrt T / (N : ℝ) ^ 2) *
        (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) := by
  let E : ℝ := ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2
  have hT1 : 1 ≤ T := one_le_two.trans hT
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hspos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hcoeffPos : 0 < mtLemma35CoefficientMeanSquareConst := by
    dsimp only [mtLemma35CoefficientMeanSquareConst]
    positivity
  by_cases hshort : (N : ℝ) ^ 2 ≤ (A : ℝ) * Real.sqrt T
  · have hbase := integral_mtWatt_le_of_unit_bound_largeA a hA hT1 hTA (show 0 ≤ (1 : ℝ) by norm_num)
      (fun t _ => norm_mtWattUnitBlock_le_one hN hN' t)
    have hinv : 1 / (A : ℝ) ≤ Real.sqrt T / (N : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hApos (pow_pos hNpos 2)]
      simpa [mul_comm] using hshort
    have hfactor : mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) * E ≤
        mtLemma35LargeAConst * (Real.sqrt T / (N : ℝ) ^ 2) * E := by
      have hpow : (1 : ℝ) ≤ (6144 : ℝ) ^ 4 := by norm_num
      dsimp only [mtLemma35LargeAConst]
      calc
        mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) * E ≤
            mtLemma35CoefficientMeanSquareConst * (Real.sqrt T / (N : ℝ) ^ 2) * E := by gcongr
        _ ≤ (mtLemma35CoefficientMeanSquareConst * (6144 : ℝ) ^ 4) *
            (Real.sqrt T / (N : ℝ) ^ 2) * E := by
          gcongr
          nlinarith [mul_le_mul_of_nonneg_left hpow hcoeffPos.le]
    have hbaseE :
        (∫ t in (T / 2)..T,
            ‖mtWattUnitBlock N N' t‖ ^ 4 *
              ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
          mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) * E := by
      simpa only [one_pow, one_mul, E] using hbase
    simpa only [E] using hbaseE.trans hfactor
  · have hhard : (A : ℝ) * Real.sqrt T ≤ (N : ℝ) ^ 2 := (not_le.mp hshort).le
    let U : ℝ := 6144 * (Real.sqrt T / (N : ℝ))
    have hyx : 1 / Real.sqrt T ≤ Real.sqrt T / (N : ℝ) := by
      rw [div_le_div_iff₀ hspos hNpos]
      nlinarith [Real.mul_self_sqrt hTpos.le]
    have hU0 : 0 ≤ U := by dsimp only [U]; positivity
    have hunit : ∀ t ∈ Set.Icc (T / 2) T, ‖mtWattUnitBlock N N' t‖ ≤ U := by
      intro t ht
      have hb := norm_mtWattUnitBlock_le_secondDerivativeWindow hN hNN' hN' hTpos ht.1 ht.2
      dsimp only [U]
      calc
        ‖mtWattUnitBlock N N' t‖ ≤
            3072 * (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) := hb
        _ ≤ 3072 * (Real.sqrt T / (N : ℝ) + Real.sqrt T / (N : ℝ)) := by
          gcongr
        _ = 6144 * (Real.sqrt T / (N : ℝ)) := by ring
    have hbase := integral_mtWatt_le_of_unit_bound_largeA a hA hT1 hTA hU0 hunit
    have hscalar := mtLemma35_secondDerivative_scalar_le hA hN hT1 hTA hhard
    have hfactor : U ^ 4 * mtLemma35CoefficientMeanSquareConst * (1 / (A : ℝ)) * E ≤
        mtLemma35LargeAConst * (Real.sqrt T / (N : ℝ) ^ 2) * E := by
      dsimp only [U, mtLemma35LargeAConst]
      rw [mul_pow]
      have hnonneg : 0 ≤ mtLemma35CoefficientMeanSquareConst * (6144 : ℝ) ^ 4 * E := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hscalar hnonneg]
    simpa only [E] using hbase.trans hfactor

theorem exists_integral_mtDI_lemma35_largeA
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (N : ℝ) < T → T ≤ (A : ℝ) →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (1 / (A : ℝ)) *
            (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2)) := by
  refine ⟨mtLemma35LargeAConst, ?_, ?_⟩
  · dsimp only [mtLemma35LargeAConst, mtLemma35CoefficientMeanSquareConst]
    positivity
  · intro a A N N' hA hN hNN' hN' T hT hNT hTA
    have hbase := integral_mtDI_lemma35_largeA a hA hN hNN' hN' hT hNT hTA
    let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
    have hTpos : 0 < T := zero_lt_two.trans_le hT
    have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hE0 : 0 ≤ E := by dsimp only [E]; positivity
    have hpow : 1 ≤ T ^ ε := Real.one_le_rpow (one_le_two.trans hT) hε.le
    have hcarrier : Real.sqrt T / (N : ℝ) ^ 2 ≤
        ((T + (A : ℝ) ^ 2 * Real.sqrt T +
                (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
              ((N : ℝ) ^ 2 * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
          (1 / (A : ℝ)) := by
      calc
        Real.sqrt T / (N : ℝ) ^ 2 =
            (((A : ℝ) ^ 2 * Real.sqrt T) /
              ((N : ℝ) ^ 2 * (A : ℝ))) * (1 / (A : ℝ)) := by
          field_simp
        _ ≤ ((T + (A : ℝ) ^ 2 * Real.sqrt T +
                (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
              ((N : ℝ) ^ 2 * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
          (1 / (A : ℝ)) := by
            have hden : 0 ≤ (N : ℝ) ^ 2 * (A : ℝ) := by positivity
            have hnum : (A : ℝ) ^ 2 * Real.sqrt T ≤
                T + (A : ℝ) ^ 2 * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
              have hlast : 0 ≤ (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
              nlinarith
            have hdiv := div_le_div_of_nonneg_right hnum hden
            have hres : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
            exact mul_le_mul_of_nonneg_right
              (hdiv.trans (le_add_of_nonneg_right hres)) (by positivity)
    have htarget : mtLemma35LargeAConst * (Real.sqrt T / (N : ℝ) ^ 2) * E ≤
        mtLemma35LargeAConst * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (1 / (A : ℝ)) * E) := by
      have hC0 : 0 ≤ mtLemma35LargeAConst := by
        dsimp only [mtLemma35LargeAConst, mtLemma35CoefficientMeanSquareConst]
        positivity
      calc
        mtLemma35LargeAConst * (Real.sqrt T / (N : ℝ) ^ 2) * E ≤
            mtLemma35LargeAConst *
              (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                      (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                    ((N : ℝ) ^ 2 * (A : ℝ)) +
                  (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
                (1 / (A : ℝ))) * E := by gcongr
        _ ≤ mtLemma35LargeAConst * T ^ ε *
              (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                      (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                    ((N : ℝ) ^ 2 * (A : ℝ)) +
                  (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
                (1 / (A : ℝ)) * E) := by
          have hrest : 0 ≤
              (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                      (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                    ((N : ℝ) ^ 2 * (A : ℝ)) +
                  (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
                (1 / (A : ℝ)) * E) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hpow
            (mul_nonneg hC0 hrest)]
    simpa only [E] using hbase.trans htarget

/-- Watt's coefficient-maximum envelope on `N < T ≤ A`; the same internally constructed
second-derivative estimate supplies its `A²√T` term. -/
theorem exists_integral_mtWatt_lemma35_largeA
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (N : ℝ) < T → T ≤ (A : ℝ) →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (mtWattCoefficientMaxSq a A : ℝ)) := by
  refine ⟨mtLemma35LargeAConst, ?_, ?_⟩
  · dsimp only [mtLemma35LargeAConst, mtLemma35CoefficientMeanSquareConst]
    positivity
  · intro a A N N' hA hN hNN' hN' T hT hNT hTA
    have hbase := integral_mtDI_lemma35_largeA a hA hN hNN' hN' hT hNT hTA
    let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
    let M : ℝ := mtWattCoefficientMaxSq a A
    have hTpos : 0 < T := zero_lt_two.trans_le hT
    have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hM0 : 0 ≤ M := by dsimp only [M]; positivity
    have henergy : E ≤ (A : ℝ) * M := by
      simpa only [E, M] using sum_normSq_mtWattCoefficientBlock_le_max a hA
    have hpow : 1 ≤ T ^ ε := Real.one_le_rpow (one_le_two.trans hT) hε.le
    have hcarrier : (A : ℝ) * Real.sqrt T / (N : ℝ) ^ 2 ≤
        (T + (A : ℝ) ^ 2 * Real.sqrt T) /
              ((N : ℝ) ^ 2 * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by
      calc
        (A : ℝ) * Real.sqrt T / (N : ℝ) ^ 2 =
            ((A : ℝ) ^ 2 * Real.sqrt T) /
              ((N : ℝ) ^ 2 * (A : ℝ)) := by field_simp
        _ ≤ (T + (A : ℝ) ^ 2 * Real.sqrt T) /
              ((N : ℝ) ^ 2 * (A : ℝ)) := by
          gcongr
          linarith
        _ ≤ (T + (A : ℝ) ^ 2 * Real.sqrt T) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by
          exact le_add_of_nonneg_right (by positivity)
    have hC0 : 0 ≤ mtLemma35LargeAConst := by
      dsimp only [mtLemma35LargeAConst, mtLemma35CoefficientMeanSquareConst]
      positivity
    have htarget : mtLemma35LargeAConst *
          (Real.sqrt T / (N : ℝ) ^ 2) * E ≤
        mtLemma35LargeAConst * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) * M) := by
      calc
        mtLemma35LargeAConst * (Real.sqrt T / (N : ℝ) ^ 2) * E ≤
            mtLemma35LargeAConst *
              ((A : ℝ) * Real.sqrt T / (N : ℝ) ^ 2) * M := by
          calc
            mtLemma35LargeAConst * (Real.sqrt T / (N : ℝ) ^ 2) * E ≤
                mtLemma35LargeAConst * (Real.sqrt T / (N : ℝ) ^ 2) *
                  ((A : ℝ) * M) := by
              exact mul_le_mul_of_nonneg_left henergy (by positivity)
            _ = mtLemma35LargeAConst *
                ((A : ℝ) * Real.sqrt T / (N : ℝ) ^ 2) * M := by ring
        _ ≤ mtLemma35LargeAConst *
              (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                    ((N : ℝ) ^ 2 * (A : ℝ)) +
                  (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) * M) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcarrier hM0) hC0
        _ ≤ mtLemma35LargeAConst * T ^ ε *
              (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                    ((N : ℝ) ^ 2 * (A : ℝ)) +
                  (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) * M) := by
          have hrest : 0 ≤ mtLemma35LargeAConst *
              (((T + (A : ℝ) ^ 2 * Real.sqrt T) /
                    ((N : ℝ) ^ 2 * (A : ℝ)) +
                  (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) * M) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hpow hrest]
    simpa only [E, M] using hbase.trans htarget

end

end RHTower.Sieve
