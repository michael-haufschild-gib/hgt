import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusOneRate
import GaloisForLFunctions.RHTower.Sieve.LogarithmicHarmonicSampling

/-!+# Uniform harmonic energy of two logarithmic Möbius cutoffs

The modulus-one logarithmic Möbius sum is a step function plus an error with
uniformly bounded squared harmonic samples. Thus its two-cutoff energy is
controlled by the logarithmic distance between the cutoffs, independently of
their absolute sizes.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

/-- The asymptotic log-square error estimate can be made uniform down to one. -/
theorem exists_abs_coprimeLogMoebius_one_sub_one_uniform_rate :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ Y : ℝ, 1 ≤ Y →
      |coprimeLogMoebius 1 Y - 1| ≤ A / (1 + Real.log Y) ^ 2 := by
  obtain ⟨C, hC, hrate⟩ := exists_abs_coprimeLogMoebius_one_sub_one_log_sq_rate
  obtain ⟨R, hR⟩ := eventually_atTop.mp hrate
  let B := max R (Real.exp 1)
  let D := 7 + |Real.eulerMascheroniConstant|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 < B := (Real.exp_pos 1).trans_le (le_max_right _ _)
  have hlogB : 1 ≤ Real.log B := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_max_right R (Real.exp 1))
    simpa [B] using h
  refine ⟨4 * C + D * (1 + Real.log B) ^ 2, by positivity, fun Y hY => ?_⟩
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  apply (le_div_iff₀ (by positivity : 0 < (1 + Real.log Y) ^ 2)).mpr
  by_cases hBY : B ≤ Y
  · have hlogY1 : 1 ≤ Real.log Y := hlogB.trans (Real.log_le_log hB hBY)
    have hmain := (le_div_iff₀ (by positivity : 0 < Real.log Y ^ 2)).mp
      (hR Y ((le_max_left _ _).trans hBY))
    have hfactor : (1 + Real.log Y) ^ 2 ≤ 4 * Real.log Y ^ 2 := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hfactor
      (abs_nonneg (coprimeLogMoebius 1 Y - 1))
    have htail : 0 ≤ D * (1 + Real.log B) ^ 2 := by positivity
    nlinarith
  · have hlogYB : Real.log Y ≤ Real.log B :=
      Real.log_le_log hY0 (le_of_not_ge hBY)
    have herr : |coprimeLogMoebius 1 Y - 1| ≤ D := by
      have h := abs_sub (coprimeLogMoebius 1 Y) 1
      have hb := abs_coprimeLogMoebius_one_le Y
      dsimp [D]
      norm_num at h
      linarith
    have hsquare : (1 + Real.log Y) ^ 2 ≤ (1 + Real.log B) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hmul := mul_le_mul herr hsquare (sq_nonneg _) hD
    nlinarith

/-- Error after subtracting the principal harmonic step at a real cutoff. -/
noncomputable def logMoebiusSampleError (Y : ℝ) (d : ℕ) : ℝ :=
  coprimeLogMoebius 1 (Y / d) - if (d : ℝ) ≤ Y then 1 else 0

theorem logMoebiusSampleError_eq_zero {Y : ℝ} {d : ℕ}
    (hd : 0 < d) (hYd : Y < d) : logMoebiusSampleError Y d = 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [logMoebiusSampleError, if_neg (not_le.mpr hYd),
    coprimeLogMoebius_of_lt_one 1 ((div_lt_one hd0).mpr hYd), sub_zero]

/-- The error part has bounded harmonic energy on every finite positive set. -/
theorem exists_sum_sq_logMoebiusSampleError_div_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ s : Finset ℕ,
      (∀ d ∈ s, 0 < d) → ∑ d ∈ s, logMoebiusSampleError Y d ^ 2 / d ≤ K := by
  obtain ⟨A, hA, hAerr⟩ := exists_abs_coprimeLogMoebius_one_sub_one_uniform_rate
  refine ⟨2 * Real.exp 1 * A ^ 2, by positivity, fun Y hY s hs => ?_⟩
  let t : Finset ℕ := s.filter (fun d : ℕ => (d : ℝ) ≤ Y)
  have ht : ∀ d ∈ t, 0 < d ∧ (d : ℝ) ≤ Y := by
    intro d hd
    exact ⟨hs d (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2⟩
  have hbound : ∀ d ∈ t,
      |coprimeLogMoebius 1 (Y / d) - 1| ≤ A / (1 + Real.log (Y / d)) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (ht d hd).1
    have hratio : 1 ≤ Y / d := (one_le_div hd0).mpr (ht d hd).2
    have hlog : 0 ≤ Real.log (Y / d) := Real.log_nonneg hratio
    refine (hAerr _ hratio).trans ?_
    apply div_le_div_of_nonneg_left hA (by positivity)
    nlinarith
  have hsum := sum_sq_div_le_of_log_decay hY hA ht
    (fun d => coprimeLogMoebius 1 (Y / d) - 1) hbound
  have heq : (∑ d ∈ s, logMoebiusSampleError Y d ^ 2 / d) =
      ∑ d ∈ t, (coprimeLogMoebius 1 (Y / d) - 1) ^ 2 / d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs with hdY
    · simp [logMoebiusSampleError, hdY]
    · rw [logMoebiusSampleError_eq_zero (hs d hd) (lt_of_not_ge hdY)]
      simp
  rwa [heq]

private theorem logMoebius_difference_decomposition {X Y : ℝ} (hXY : X ≤ Y)
    (d : ℕ) :
    coprimeLogMoebius 1 (Y / d) - coprimeLogMoebius 1 (X / d) =
      logMoebiusSampleError Y d - logMoebiusSampleError X d +
        if X < (d : ℝ) ∧ (d : ℝ) ≤ Y then 1 else 0 := by
  unfold logMoebiusSampleError
  by_cases hdX : (d : ℝ) ≤ X
  · have hdY := hdX.trans hXY
    simp [hdX, hdY, not_lt.mpr hdX]
  · by_cases hdY : (d : ℝ) ≤ Y
    · simp only [hdX, hdY, lt_of_not_ge hdX, and_self, if_true, if_false]
      ring
    · simp [hdX, hdY]

/-- Two logarithmic Möbius cutoffs have harmonic energy proportional to their
logarithmic separation, uniformly in the cutoffs and truncation. -/
theorem exists_sum_sq_coprimeLogMoebius_difference_div_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : ℝ, 0 < X → X ≤ Y → ∀ N : ℕ,
      (∑ d ∈ Finset.Icc 1 N,
        (coprimeLogMoebius 1 (Y / d) - coprimeLogMoebius 1 (X / d)) ^ 2 / d) ≤
          C * (1 + Real.log (Y / X)) := by
  obtain ⟨K, hK, herror⟩ := exists_sum_sq_logMoebiusSampleError_div_le
  refine ⟨3 + 6 * K, by positivity, fun X Y hX hXY N => ?_⟩
  let s := Finset.Icc 1 N
  let w : ℕ → ℝ := fun d => if X < (d : ℝ) ∧ (d : ℝ) ≤ Y then 1 else 0
  have hs : ∀ d ∈ s, 0 < d := fun d hd => (Finset.mem_Icc.mp hd).1
  have hY : 0 < Y := hX.trans_le hXY
  have herrorX := herror X hX s hs
  have herrorY := herror Y hY s hs
  have hwindow : ∑ d ∈ s, w d ^ 2 / d ≤ 1 + Real.log (Y / X) := by
    let t : Finset ℕ := s.filter (fun d : ℕ => X < (d : ℝ) ∧ (d : ℝ) ≤ Y)
    have ht : ∀ d ∈ t, 0 < d ∧ X < (d : ℝ) ∧ (d : ℝ) ≤ Y := by
      intro d hd
      exact ⟨hs d (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2⟩
    have heq : (∑ d ∈ s, w d ^ 2 / d) = ∑ d ∈ t, 1 / (d : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      dsimp [w]
      split_ifs <;> simp
    rw [heq]
    exact sum_one_div_log_window_le hX hXY ht
  have hpoint : ∀ d ∈ s,
      (coprimeLogMoebius 1 (Y / d) - coprimeLogMoebius 1 (X / d)) ^ 2 / d ≤
        3 * (logMoebiusSampleError Y d ^ 2 / d) +
        3 * (logMoebiusSampleError X d ^ 2 / d) + 3 * (w d ^ 2 / d) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hs d hd
    rw [logMoebius_difference_decomposition hXY d]
    change (logMoebiusSampleError Y d - logMoebiusSampleError X d + w d) ^ 2 / d ≤ _
    have hsq : (logMoebiusSampleError Y d - logMoebiusSampleError X d + w d) ^ 2 ≤
        3 * logMoebiusSampleError Y d ^ 2 + 3 * logMoebiusSampleError X d ^ 2 +
          3 * w d ^ 2 := by
      nlinarith [sq_nonneg (logMoebiusSampleError Y d + logMoebiusSampleError X d),
        sq_nonneg (logMoebiusSampleError Y d - w d),
        sq_nonneg (logMoebiusSampleError X d + w d)]
    simpa [add_div, mul_div_assoc] using div_le_div_of_nonneg_right hsq hd0.le
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hlog : 0 ≤ Real.log (Y / X) :=
    Real.log_nonneg ((one_le_div hX).mpr hXY)
  change (∑ d ∈ s, _) ≤ _
  nlinarith

end RHTower.Sieve
