import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMoebiusSigmaSumsDecay
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization

/-!+# A quantitative normalization for the factorial producers

The harmonic Möbius bound `|Σ μ(n)/n| ≤ C/(1 + log N)⁴` gives
`|-Σ μ(n) log n/n − 1| ≤ 3C/(log N)³` for `N ≥ 3`.
Finite Abel summation and the reciprocal-log integral test control the tail uniformly;
the normalization to one identifies its limit.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.HTGeometry
open _root_.RHTower _root_.RHTower.Sieve

noncomputable section
namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

private def normalizationIncrement (n : ℕ) : ℝ :=
  deningerHarmonicPartial n * (Real.log ((n : ℝ) + 1) - Real.log n)

private theorem normalization_abel (N : ℕ) :
    moebiusLogHarmonicPartial N + deningerHarmonicPartial N * Real.log N =
      ∑ i ∈ range N, normalizationIncrement i := by
  have h := deningerAbelSummation
    (fun n : ℕ => ((moebius n : ℤ) : ℝ) / (n : ℝ))
    (fun n : ℕ => -Real.log (n : ℝ)) N
  have hsum : (∑ n ∈ range (N + 1),
      ((moebius n : ℤ) : ℝ) / (n : ℝ) * -Real.log n) =
      moebiusLogHarmonicPartial N := by
    apply sum_congr rfl
    intro n _
    simp only [moebiusLogHarmonicTerm, Real.rpow_neg_one]
    ring
  have hterms : (∑ i ∈ range N,
      deningerPartialSum (fun n : ℕ => ((moebius n : ℤ) : ℝ) / n) i *
        (-Real.log i - -Real.log (i + 1 : ℕ))) =
      ∑ i ∈ range N, normalizationIncrement i := by
    apply sum_congr rfl
    intro i _
    change deningerHarmonicPartial i * _ = _
    simp only [normalizationIncrement, Nat.cast_add, Nat.cast_one]
    ring
  rw [hsum, hterms] at h
  change moebiusLogHarmonicPartial N =
    deningerHarmonicPartial N * -Real.log N + _ at h
  linarith

private theorem normalizationIncrement_bound {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      |deningerHarmonicPartial n| ≤ C / (1 + Real.log n) ^ 4)
    {n : ℕ} (hn : 3 ≤ n) :
    |normalizationIncrement n| ≤ C / ((n : ℝ) * (Real.log n) ^ 4) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hm : |deningerHarmonicPartial n| ≤ C / (Real.log n) ^ 4 :=
    (hbound n (by omega)).trans (div_le_div_of_nonneg_left hC (by positivity)
      (pow_le_pow_left₀ hl.le (by linarith) 4))
  have hdiff0 : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n :=
    sub_nonneg.mpr (Real.log_le_log hn0 (by linarith))
  have hdiff := log_natCast_succ_sub_log_natCast_le_inv n (by omega)
  rw [normalizationIncrement, abs_mul, abs_of_nonneg hdiff0]
  calc |deningerHarmonicPartial n| * (Real.log ((n : ℝ) + 1) - Real.log n)
      ≤ (C / (Real.log n) ^ 4) * (1 / (n : ℝ)) :=
        mul_le_mul hm hdiff hdiff0 (by positivity)
    _ = _ := by ring

/-- Quantitative Abel normalization from the unconditional harmonic Möbius estimate. -/
theorem exists_abs_moebiusLogHarmonicPartial_sub_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      |moebiusLogHarmonicPartial N - 1| ≤ C / (Real.log N) ^ 3 := by
  obtain ⟨C₀, hC₀⟩ := exists_abs_moebiusHarmonicSum_le
  have hC₀0 : 0 ≤ C₀ := by
    have h := hC₀ 1 le_rfl
    norm_num at h
    exact (abs_nonneg _).trans h
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |deningerHarmonicPartial n| ≤ C₀ / (1 + Real.log n) ^ 4 := by
    intro n hn
    simpa only [moebiusHarmonicSum_eq_deningerHarmonicPartial] using hC₀ n hn
  refine ⟨3 * C₀ + 1, by positivity, fun N hN => ?_⟩
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have heN : Real.exp 1 ≤ (N : ℝ) := (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 3).trans hNR
  have hl1 : 1 ≤ Real.log (N : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) heN
  have hl0 : 0 < Real.log (N : ℝ) := by linarith
  have htail : ∀ a : ℕ,
      |∑ i ∈ range a, normalizationIncrement (N + i)| ≤
        C₀ / ((N : ℝ) * (Real.log N) ^ 4) + C₀ / (3 * (Real.log N) ^ 3) := by
    intro a
    rcases a with _ | a
    · simp only [sum_range_zero, abs_zero]
      positivity
    · rw [sum_range_succ']
      have hs : |∑ i ∈ range a, normalizationIncrement (N + (i + 1))| ≤
          C₀ / (3 * (Real.log N) ^ 3) := by
        calc |∑ i ∈ range a, normalizationIncrement (N + (i + 1))|
            ≤ ∑ i ∈ range a, |normalizationIncrement (N + (i + 1))| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ range a,
              C₀ / (((N : ℝ) + ((i : ℝ) + 1)) *
                (Real.log ((N : ℝ) + ((i : ℝ) + 1))) ^ 4) := by
            apply sum_le_sum
            intro i _
            simpa only [Nat.cast_add, Nat.cast_one] using
              normalizationIncrement_bound hC₀0 hbound (n := N + (i + 1)) (by omega)
          _ = C₀ * ∑ i ∈ range a,
              1 / (((N : ℝ) + ((i : ℝ) + 1)) *
                (Real.log ((N : ℝ) + ((i : ℝ) + 1))) ^ 4) := by
            rw [mul_sum]
            exact sum_congr rfl fun _ _ => by ring
          _ ≤ C₀ * (1 / (3 * (Real.log N) ^ 3)) :=
            mul_le_mul_of_nonneg_left (sum_one_div_mul_log_four_le heN a) hC₀0
          _ = _ := by ring
      simpa only [Nat.add_zero] using
        (abs_add_le (∑ i ∈ range a, normalizationIncrement (N + (i + 1)))
          (normalizationIncrement N)).trans
            (by linarith [normalizationIncrement_bound hC₀0 hbound hN])
  let A : ℕ → ℝ := fun n => moebiusLogHarmonicPartial n +
    deningerHarmonicPartial n * Real.log n
  have hA : Tendsto A atTop (𝓝 1) := by
    simpa only [add_zero, mul_comm] using
      tendsto_moebiusLogHarmonicPartial_one.add tendsto_log_mul_deningerHarmonicPartial_zero
  have hdiff : ∀ a : ℕ, A (N + a) - A N =
      ∑ i ∈ range a, normalizationIncrement (N + i) := by
    intro a
    dsimp only [A]
    rw [normalization_abel, normalization_abel, sum_range_add]
    ring
  have hlim : Tendsto (fun a : ℕ => |A (N + a) - A N|) atTop (𝓝 |1 - A N|) := by
    simpa only [Nat.add_comm] using
      ((hA.comp (tendsto_add_atTop_nat N)).sub_const (A N)).abs
  have htail' := le_of_tendsto' hlim (fun a => by rw [hdiff]; exact htail a)
  have hm : |deningerHarmonicPartial N| ≤ C₀ / (Real.log N) ^ 4 :=
    (hbound N (by omega)).trans (div_le_div_of_nonneg_left hC₀0 (by positivity)
      (pow_le_pow_left₀ hl0.le (by linarith) 4))
  have hb : |deningerHarmonicPartial N * Real.log N| ≤ C₀ / (Real.log N) ^ 3 := by
    rw [abs_mul, abs_of_pos hl0]
    calc |deningerHarmonicPartial N| * Real.log N ≤ C₀ / (Real.log N) ^ 4 * Real.log N :=
        mul_le_mul_of_nonneg_right hm hl0.le
      _ = _ := by field_simp
  have hfirst : C₀ / ((N : ℝ) * (Real.log N) ^ 4) ≤ C₀ / (Real.log N) ^ 3 := by
    apply div_le_div_of_nonneg_left hC₀0 (by positivity)
    calc (Real.log N) ^ 3 ≤ (Real.log N) ^ 4 := pow_le_pow_right₀ hl1 (by omega)
      _ ≤ (N : ℝ) * (Real.log N) ^ 4 := le_mul_of_one_le_left (by positivity) (by linarith)
  have htri : |moebiusLogHarmonicPartial N - 1| ≤ |1 - A N| +
      |deningerHarmonicPartial N * Real.log N| := by
    calc |moebiusLogHarmonicPartial N - 1| =
        |-(1 - A N) - deningerHarmonicPartial N * Real.log N| := by dsimp [A]; congr 1; ring
      _ ≤ |-(1 - A N)| + |deningerHarmonicPartial N * Real.log N| := abs_sub _ _
      _ = _ := by rw [abs_neg]
  have hsmall : C₀ / (3 * (Real.log N) ^ 3) ≤ C₀ / (Real.log N) ^ 3 :=
    div_le_div_of_nonneg_left hC₀0 (by positivity) (by nlinarith [pow_pos hl0 3])
  calc |moebiusLogHarmonicPartial N - 1| ≤ 3 * C₀ / (Real.log N) ^ 3 := by
      linarith [htri, htail', hb, hfirst, hsmall]
    _ ≤ (3 * C₀ + 1) / (Real.log N) ^ 3 := by gcongr; linarith

end GaloisForLFunctions.ArithmeticKreinLangerTheory
