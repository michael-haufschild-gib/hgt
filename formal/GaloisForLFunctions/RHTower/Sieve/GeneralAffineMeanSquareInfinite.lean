import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology Set Finset

/-- Absolute convergence plus the Montgomery--Vaughan weighted square mass
promotes the finite affine estimate to an exact infinite Dirichlet series. -/
theorem integral_Icc_normSq_LSeries_le_general_affine_infinite
    {a : ℕ → ℂ} (ha0 : a 0 = 0) (sigma : ℝ)
    (habs : Summable (fun n : ℕ ↦
      ‖a n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖))
    (hplain : Summable (fun n : ℕ ↦
      ‖a n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖ ^ 2))
    (hweighted : Summable (fun n : ℕ ↦
      (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖ ^ 2))
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in Set.Icc (-T) T,
        ‖LSeries a ((sigma : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ 5 * Real.pi * Real.exp 1 *
          (∑' n : ℕ,
            (n : ℝ) *
              ‖a n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖ ^ 2)
        + (5 * Real.pi / 2) *
          (∑' n : ℕ,
            ‖a n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖ ^ 2) * T := by
  classical
  let u : ℕ → ℝ := fun n ↦
    ‖a n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖
  let P : Finset ℕ → ℝ → ℂ := fun S y ↦
    ∑ n ∈ S, LSeries.term a ((sigma : ℂ) + (y : ℝ) * I) n
  have htermnorm (n : ℕ) (y : ℝ) :
      ‖LSeries.term a ((sigma : ℂ) + (y : ℝ) * I) n‖ = u n := by
    by_cases hn : n = 0
    · subst n
      simp [u, ha0]
    · rw [LSeries.norm_term_eq, if_neg hn]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one,
        zero_sub, add_zero]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hrpow : 0 ≤ (n : ℝ) ^ (-sigma) := Real.rpow_nonneg hn0 _
      dsimp only [u]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hrpow, Real.rpow_neg hn0]
      simp only [neg_zero, add_zero, div_eq_mul_inv]
  have htermcont (n : ℕ) : Continuous (fun y : ℝ ↦
      LSeries.term a ((sigma : ℂ) + (y : ℝ) * I) n) := by
    by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero]
      fun_prop
    · letI : NeZero (n : ℂ) := ⟨by exact_mod_cast hn⟩
      simp_rw [LSeries.term_def₀ ha0]
      exact continuous_const.mul
        ((continuous_const_cpow (n : ℂ)).comp (by fun_prop))
  have hunif : TendstoUniformlyOn P
      (fun y : ℝ ↦ LSeries a ((sigma : ℂ) + (y : ℝ) * I))
      atTop (Set.uIcc (-T) T) := by
    change TendstoUniformlyOn
      (fun S : Finset ℕ ↦ fun y : ℝ ↦
        ∑ n ∈ S, LSeries.term a ((sigma : ℂ) + (y : ℝ) * I) n)
      (fun y : ℝ ↦ ∑' n : ℕ,
        LSeries.term a ((sigma : ℂ) + (y : ℝ) * I) n)
      atTop (Set.uIcc (-T) T)
    exact tendstoUniformlyOn_tsum habs fun n y _ ↦ (htermnorm n y).le
  have hPcont (S : Finset ℕ) : Continuous (P S) := by
    dsimp only [P]
    exact continuous_finsetSum S fun n _ ↦ htermcont n
  let A : ℝ := ∑' n : ℕ, u n
  have hA0 : 0 ≤ A := tsum_nonneg fun n ↦ norm_nonneg _
  have hPnorm (S : Finset ℕ) (y : ℝ) : ‖P S y‖ ≤ A := by
    calc
      ‖P S y‖ ≤ ∑ n ∈ S, ‖LSeries.term a
          ((sigma : ℂ) + (y : ℝ) * I) n‖ := by
            dsimp only [P]
            exact norm_sum_le S _
      _ = ∑ n ∈ S, u n := by
            exact Finset.sum_congr rfl fun n _ ↦ htermnorm n y
      _ ≤ A := habs.sum_le_tsum S (fun _ _ ↦ norm_nonneg _) 
  have htend : Tendsto
      (fun S : Finset ℕ ↦ ∫ y in (-T)..T, ‖P S y‖ ^ 2)
      atTop
      (nhds (∫ y in (-T)..T,
        ‖LSeries a ((sigma : ℂ) + (y : ℝ) * I)‖ ^ 2)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ ↦ A ^ 2)
    · exact Filter.Eventually.of_forall fun S ↦
        (hPcont S).norm.pow 2 |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun S ↦
        Filter.Eventually.of_forall fun y _ ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hPnorm S y) 2
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun y ↦
        fun hy ↦ ((hunif.tendsto_at (Set.uIoc_subset_uIcc hy)).norm.pow 2)
  let B : ℝ := 5 * Real.pi * Real.exp 1 *
          (∑' n : ℕ, (n : ℝ) * u n ^ 2)
        + (5 * Real.pi / 2) * (∑' n : ℕ, u n ^ 2) * T
  have hfinite (S : Finset ℕ) :
      (∫ y in (-T)..T, ‖P S y‖ ^ 2) ≤ B := by
    let s : Finset ℕ := S.erase 0
    let b : ℕ → ℂ := fun n ↦ if n ∈ s then a n else 0
    have hs0 : (0 : ℕ) ∉ s := by simp [s]
    have hbsupp : ∀ n : ℕ, b n ≠ 0 → n ∈ s := by
      intro n hn
      by_contra hns
      simp [b, hns] at hn
    have hpartial (y : ℝ) :
        LSeries b ((sigma : ℂ) + (y : ℝ) * I) = P S y := by
      unfold LSeries
      rw [tsum_eq_sum (s := s)]
      · dsimp only [P]
        calc
          (∑ n ∈ s, LSeries.term b ((sigma : ℂ) + (y : ℝ) * I) n)
              = ∑ n ∈ s, LSeries.term a ((sigma : ℂ) + (y : ℝ) * I) n := by
                  exact Finset.sum_congr rfl fun n hn ↦ by
                    have hn0 : n ≠ 0 := by
                      exact fun h ↦ by subst n; simpa [s] using hn
                    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
                    simp [b, hn]
          _ = ∑ n ∈ S, LSeries.term a ((sigma : ℂ) + (y : ℝ) * I) n := by
                rw [show s = S.erase 0 by rfl,
                  Finset.sum_erase S (LSeries.term_zero a _)]
      · intro n hn
        have hns : n ∉ s := hn
        simp [LSeries.term_def, b, hns]
    have hms := integral_Icc_normSq_LSeries_le_general_affine
      (a := b) (s := s) hs0 hbsupp sigma hT
    have hset :
        (∫ y in Set.Icc (-T) T,
          ‖LSeries b ((sigma : ℂ) + (y : ℝ) * I)‖ ^ 2)
        = ∫ y in (-T)..T, ‖P S y‖ ^ 2 := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact intervalIntegral.integral_congr fun y _ ↦ by rw [hpartial]
    rw [hset] at hms
    refine hms.trans ?_
    rw [generalMeanSquareConst, generalMeanSquareRate]
    have hconst :
        (∑ n ∈ s, (n : ℝ) *
          ‖b n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖ ^ 2)
        ≤ ∑' n : ℕ, (n : ℝ) * u n ^ 2 := by
      calc
        (∑ n ∈ s, (n : ℝ) *
          ‖b n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖ ^ 2)
            = ∑ n ∈ s, (n : ℝ) * u n ^ 2 := by
                exact Finset.sum_congr rfl fun n hn ↦ by simp [b, u, hn]
        _ ≤ ∑' n : ℕ, (n : ℝ) * u n ^ 2 :=
          hweighted.sum_le_tsum s (fun n _ ↦ by positivity)
    have hrate :
        (∑ n ∈ s,
          ‖b n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖ ^ 2)
        ≤ ∑' n : ℕ, u n ^ 2 := by
      calc
        (∑ n ∈ s,
          ‖b n * ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)‖ ^ 2)
            = ∑ n ∈ s, u n ^ 2 := by
                exact Finset.sum_congr rfl fun n hn ↦ by simp [b, u, hn]
        _ ≤ ∑' n : ℕ, u n ^ 2 :=
          hplain.sum_le_tsum s (fun n _ ↦ sq_nonneg _)
    dsimp only [B]
    have hT0 : 0 ≤ T := by linarith
    have hc0 : 0 ≤ 5 * Real.pi * Real.exp 1 := by positivity
    have hr0 : 0 ≤ 5 * Real.pi / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hconst hc0,
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hrate hT0) hr0]
  have hlimit :
      (∫ y in (-T)..T,
        ‖LSeries a ((sigma : ℂ) + (y : ℝ) * I)‖ ^ 2) ≤ B :=
    le_of_tendsto htend (Filter.Eventually.of_forall hfinite)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  simpa [B, u] using hlimit

end RHTower.Sieve
