import GaloisForLFunctions.RHTower.SteinhausSummatoryFirstMoment
import GaloisForLFunctions.RHTower.BourgainPartialSummation

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- Every finite deterministic linear combination of the original characters has integrable magnitude. -/
theorem integrable_norm_steinhausFiniteSum (a : ℕ → ℂ) (S : Finset ℕ) :
    Integrable (fun ω => ‖∑ n ∈ S, a n * X n ω‖) steinhausMeasure := by
  have hm : Measurable (fun ω => ∑ n ∈ S, a n * X n ω) :=
    Finset.measurable_sum _ (fun n _ => measurable_const.mul (measurable_X n))
  refine Integrable.mono' (integrable_const (∑ n ∈ S, ‖a n‖)) hm.norm.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [norm_norm]
  simpa only [norm_mul, norm_X, mul_one] using norm_sum_le S (fun n => a n * X n ω)

private theorem integrable_summatoryNorm (N : ℕ) :
    Integrable (fun ω => ‖∑ n ∈ Finset.Icc 1 N, X n ω‖) steinhausMeasure := by
  simpa only [one_mul] using integrable_norm_steinhausFiniteSum (fun _ => 1) (Finset.Icc 1 N)

/-- The elementary all-cutoff first-mean ceiling, used only for the finite initial segment. -/
theorem integral_norm_steinhausSummatory_le (N : ℕ) :
    (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ ∂steinhausMeasure) ≤ (N : ℝ) := by
  have hpoint (ω : Omega) : ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ ≤ (N : ℝ) := by
    simpa only [norm_X, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.card_Icc, Nat.add_sub_cancel] using norm_sum_le (Finset.Icc 1 N) (fun n => X n ω)
  have h := integral_mono (integrable_summatoryNorm N) (integrable_const (N : ℝ)) hpoint
  simpa using h

/-- Actual first-mean decay gives one global affine square-root envelope at every tolerance. -/
theorem exists_steinhausSummatoryMean_sqrt_envelope {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫ ω, ‖∑ k ∈ Finset.Icc 1 n, X k ω‖ ∂steinhausMeasure) ≤ C + ε * Real.sqrt n := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (tendsto_integral_norm_steinhausSummatory_div_sqrt.eventually (gt_mem_nhds hε))
  refine ⟨(M + 1 : ℕ), Nat.cast_nonneg _, fun n => ?_⟩
  by_cases hn : M + 1 ≤ n
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h := (div_lt_iff₀ (Real.sqrt_pos.2 hnpos)).mp (hM n (by omega))
    have hC : (0 : ℝ) ≤ (M + 1 : ℕ) := Nat.cast_nonneg _
    linarith
  · have h := integral_norm_steinhausSummatory_le n
    have hnM : (n : ℝ) ≤ (M + 1 : ℕ) := by exact_mod_cast (by omega : n ≤ M + 1)
    have hp := mul_nonneg hε.le (Real.sqrt_nonneg (n : ℝ))
    linarith

private theorem Ioc_zero_eq_Icc_one (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- Finite Abel summation bounds the actual weighted mean by the same positive combination of prefix means. -/
theorem integral_norm_steinhausWeightedSummatory_le_abel (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, 1 ≤ n → 0 ≤ w n) (hanti : ∀ n, 1 ≤ n → w (n + 1) ≤ w n) :
    (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, (w n : ℂ) * X n ω‖ ∂steinhausMeasure) ≤
      w (N + 1) * (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ ∂steinhausMeasure) +
        ∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) *
          (∫ ω, ‖∑ k ∈ Finset.Icc 1 n, X k ω‖ ∂steinhausMeasure) := by
  have hpoint (ω : Omega) : ‖∑ n ∈ Finset.Icc 1 N, (w n : ℂ) * X n ω‖ ≤
      w (N + 1) * ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ +
        ∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, X k ω‖ := by
    have h := sum_Ioc_weight_mul_eq (fun n => X n ω) (fun n => (w n : ℂ)) (Nat.zero_le N)
    simp only [Ioc_zero_eq_Icc_one, ← Complex.ofReal_sub] at h
    rw [h]
    calc
      _ ≤ ‖(w (N + 1) : ℂ) * ∑ n ∈ Finset.Icc 1 N, X n ω‖ +
          ∑ n ∈ Finset.Icc 1 N, ‖((w n - w (n + 1) : ℝ) : ℂ) *
            ∑ k ∈ Finset.Icc 1 n, X k ω‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ = _ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _ (by omega))]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr (hanti n (Finset.mem_Icc.mp hn).1))]
  have hhead := (integrable_summatoryNorm N).const_mul (w (N + 1))
  have htail := integrable_finsetSum (Finset.Icc 1 N)
    (fun n _ => (integrable_summatoryNorm n).const_mul (w n - w (n + 1)))
  calc
    _ ≤ ∫ ω, (w (N + 1) * ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ +
        ∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) * ‖∑ k ∈ Finset.Icc 1 n, X k ω‖)
          ∂steinhausMeasure :=
      integral_mono (integrable_norm_steinhausFiniteSum (fun n => (w n : ℂ)) _) (hhead.add htail) hpoint
    _ = _ := by
      rw [integral_add hhead htail, integral_const_mul,
        integral_finsetSum _ (fun n _ => (integrable_summatoryNorm n).const_mul (w n - w (n + 1)))]
      simp_rw [integral_const_mul]

/-- A global prefix-mean envelope transfers to every positive decreasing weight without a smoothing-dependent constant. -/
theorem integral_norm_steinhausWeightedSummatory_le_envelope (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, 1 ≤ n → 0 ≤ w n) (hanti : ∀ n, 1 ≤ n → w (n + 1) ≤ w n)
    {C ε : ℝ} (hmean : ∀ n : ℕ,
      (∫ ω, ‖∑ k ∈ Finset.Icc 1 n, X k ω‖ ∂steinhausMeasure) ≤ C + ε * Real.sqrt n) :
    (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, (w n : ℂ) * X n ω‖ ∂steinhausMeasure) ≤
      C * w 1 + ε * (w (N + 1) * Real.sqrt N +
        ∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) * Real.sqrt n) := by
  have htel : w (N + 1) + ∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) = w 1 := by
    have h := sum_Ioc_sub_succ w (Nat.zero_le N)
    rw [Ioc_zero_eq_Icc_one] at h
    simp only [Nat.zero_add] at h
    linarith
  calc
    _ ≤ w (N + 1) * (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ ∂steinhausMeasure) +
        ∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) *
          (∫ ω, ‖∑ k ∈ Finset.Icc 1 n, X k ω‖ ∂steinhausMeasure) :=
      integral_norm_steinhausWeightedSummatory_le_abel w N hw hanti
    _ ≤ w (N + 1) * (C + ε * Real.sqrt N) +
        ∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) * (C + ε * Real.sqrt n) :=
      add_le_add (mul_le_mul_of_nonneg_left (hmean N) (hw _ (by omega)))
        (Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hmean n)
          (sub_nonneg.mpr (hanti n (Finset.mem_Icc.mp hn).1))))
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have hsum : (∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) * (ε * Real.sqrt n)) =
          ε * ∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1)) * Real.sqrt n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      rw [hsum, ← htel]
      ring

end RHTower
