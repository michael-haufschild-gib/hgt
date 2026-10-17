import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Concentration of finite positive packets

Convergent mass and vanishing second moment give convergence against bounded tests continuous
at the concentration point, including their squared errors. The index types may vary with degree.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [PseudoMetricSpace α]

theorem bounded_continuousAt_sq_modulus
    {g : α → ℝ} {p : α} {M ε : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, |g x| ≤ M)
    (hg : ContinuousAt g p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      (g x - g p) ^ 2 ≤ ε + C * dist x p ^ 2 := by
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hg
    (min ε 1) (lt_min hε zero_lt_one)
  refine ⟨(2 * M) ^ 2 / δ ^ 2, by positivity, ?_⟩
  intro x
  have hC : 0 ≤ (2 * M) ^ 2 / δ ^ 2 := by positivity
  by_cases hx : dist x p < δ
  · have hsmall : |g x - g p| < min ε 1 := by
      simpa only [Real.dist_eq] using hnear hx
    have hsq : (g x - g p) ^ 2 ≤ ε := by
      have h1 := min_le_left ε 1
      have h2 := min_le_right ε 1
      have h3 := abs_nonneg (g x - g p)
      nlinarith [sq_abs (g x - g p)]
    exact hsq.trans (le_add_of_nonneg_right (mul_nonneg hC (sq_nonneg _)))
  · have hfar : δ ≤ dist x p := le_of_not_gt hx
    have habs : |g x - g p| ≤ 2 * M := by
      have h := abs_sub_le (g x) 0 (g p)
      simp only [sub_zero, zero_sub, abs_neg] at h
      linarith [hbound x, hbound p]
    have hsq : (g x - g p) ^ 2 ≤ (2 * M) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs
    have hscale : (2 * M) ^ 2 ≤ (2 * M) ^ 2 / δ ^ 2 * dist x p ^ 2 := by
      calc
        (2 * M) ^ 2 = (2 * M) ^ 2 / δ ^ 2 * δ ^ 2 := by
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ hδ.le dist_nonneg).mpr hfar) hC
    linarith

/-- Concentration of a finite positive packet controls every bounded test continuous at its
centre, even when the test is discontinuous away from the centre. -/
theorem tendsto_finiteWeighted_sq_error_of_secondMoment
    {ι : ℕ → Type*} (s : ∀ n, Finset (ι n))
    (w : ∀ n, ι n → ℝ) (x : ∀ n, ι n → α)
    {p : α} {L M : ℝ} {g : α → ℝ}
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hmass : Tendsto (fun n => ∑ i ∈ s n, w n i) atTop (nhds L))
    (hvar : Tendsto (fun n => ∑ i ∈ s n, w n i * dist (x n i) p ^ 2)
      atTop (nhds 0))
    (hM : 0 ≤ M) (hbound : ∀ y, |g y| ≤ M) (hg : ContinuousAt g p) :
    Tendsto (fun n => ∑ i ∈ s n, w n i * (g (x n i) - g p) ^ 2)
      atTop (nhds 0) := by
  have hnonneg : ∀ n, 0 ≤ ∑ i ∈ s n, w n i * (g (x n i) - g p) ^ 2 :=
    fun n => Finset.sum_nonneg fun i hi => mul_nonneg (hw n i hi) (sq_nonneg _)
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall fun n => ha.trans_le (hnonneg n)
  · intro ε hε
    let A := |L| + 1
    have hA : 0 < A := by dsimp [A]; positivity
    have hLA : L < A := by dsimp [A]; linarith [le_abs_self L]
    obtain ⟨C, hC, hpoint⟩ := bounded_continuousAt_sq_modulus (ε := ε / (2 * A))
      hM hbound hg (div_pos hε (mul_pos (by norm_num) hA))
    have hmass' := hmass.eventually_lt_const hLA
    have hvar' : ∀ᶠ n in atTop,
        C * (∑ i ∈ s n, w n i * dist (x n i) p ^ 2) < ε / 2 := by
      apply Filter.Tendsto.eventually_lt_const (by positivity)
      simpa using hvar.const_mul C
    filter_upwards [hmass', hvar'] with n hn hn'
    calc
      (∑ i ∈ s n, w n i * (g (x n i) - g p) ^ 2)
          ≤ ∑ i ∈ s n, w n i * (ε / (2 * A) + C * dist (x n i) p ^ 2) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (hpoint (x n i)) (hw n i hi)
      _ = ε / (2 * A) * (∑ i ∈ s n, w n i) +
          C * (∑ i ∈ s n, w n i * dist (x n i) p ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ < ε / (2 * A) * A + ε / 2 :=
        add_lt_add (mul_lt_mul_of_pos_left hn (by positivity)) hn'
      _ = ε := by field_simp; ring

/-- The same concentration law gives the weighted test limit. -/
theorem tendsto_finiteWeighted_test_of_secondMoment
    {ι : ℕ → Type*} (s : ∀ n, Finset (ι n))
    (w : ∀ n, ι n → ℝ) (x : ∀ n, ι n → α)
    {p : α} {L M : ℝ} {g : α → ℝ}
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hmass : Tendsto (fun n => ∑ i ∈ s n, w n i) atTop (nhds L))
    (hvar : Tendsto (fun n => ∑ i ∈ s n, w n i * dist (x n i) p ^ 2)
      atTop (nhds 0))
    (hM : 0 ≤ M) (hbound : ∀ y, |g y| ≤ M) (hg : ContinuousAt g p) :
    Tendsto (fun n => ∑ i ∈ s n, w n i * g (x n i)) atTop (nhds (L * g p)) := by
  have herr := tendsto_finiteWeighted_sq_error_of_secondMoment
    s w x hw hmass hvar hM hbound hg
  have hsq : Tendsto (fun n => (∑ i ∈ s n, w n i * (g (x n i) - g p)) ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _)
      (fun n => Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s n)
        (fun i hi => mul_nonneg (hw n i hi) (sq_nonneg (g (x n i) - g p)))
        (fun i hi => hw n i hi) (fun i _ => by nlinarith))
    simpa using herr.mul hmass
  have herr' : Tendsto (fun n => ∑ i ∈ s n, w n i * (g (x n i) - g p))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Function.comp_def, Real.norm_eq_abs, Real.sqrt_sq_eq_abs, Real.sqrt_zero]
      using Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have h := herr'.add (hmass.mul_const (g p))
  simp only [zero_add] at h
  convert h using 1
  ext n
  simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

end GaloisForLFunctions.HTGeometry
