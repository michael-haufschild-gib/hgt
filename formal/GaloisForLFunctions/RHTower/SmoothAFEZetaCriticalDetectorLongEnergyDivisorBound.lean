import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorLongRangeSplit
import GaloisForLFunctions.RHTower.Sieve.ProdIdxFibreDivisorBound
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Divisor-fibre upper bound for the critical detector long energy

The exact product range beyond the detector head is dominated by the full finite convolution
energy.  The unconditional divisor bound then supplies an arbitrarily small power loss times the
factor energies.  This is a coarse reusable cap, not the sharp Levinson asymptotic.
-/

noncomputable section

namespace RHTower

open Complex Finset

/-- The nonnegative long range is bounded by the full finite-convolution energy. -/
theorem levinsonCriticalDetectorLongEnergy_le_fullEnergy
    (lam : ℝ) (L M : ℕ) :
    levinsonCriticalDetectorLongEnergy lam L M ≤
      ∑ r : Fin (L * M),
        ‖levinsonCriticalDetectorMollifiedFinCoeff lam L M r‖ ^ 2 := by
  classical
  unfold levinsonCriticalDetectorLongEnergy levinsonCriticalDetectorFiniteEnergyTerm
  rw [show (∑ r ∈ (Finset.univ : Finset (Fin (L * M))).filter
        (fun r : Fin (L * M) => L < (r : ℕ) + 1),
          Complex.normSq (levinsonCriticalDetectorMollifiedFinCoeff lam L M r)) =
      ∑ r ∈ (Finset.univ : Finset (Fin (L * M))).filter
        (fun r : Fin (L * M) => L < (r : ℕ) + 1),
          ‖levinsonCriticalDetectorMollifiedFinCoeff lam L M r‖ ^ 2 by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Complex.sq_norm]]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => sq_nonneg _)

/-- Harmonic upper bound for the literal finite linear mollifier energy. -/
theorem sum_normSq_levinsonLinearMollifierFinCoeff_le
    {M : ℕ} (hM : 1 < M) :
    ∑ m : Fin M, ‖levinsonLinearMollifierFinCoeff M m‖ ^ 2 ≤
      1 + Real.log M := by
  rw [show (∑ m : Fin M, ‖levinsonLinearMollifierFinCoeff M m‖ ^ 2) =
      ∑ k ∈ Finset.Icc 1 M,
        ‖Sieve.levinsonLinearMollifierCoeff M k‖ ^ 2 by
    exact Sieve.sum_fin_eq_sum_Icc M
      (fun k => ‖Sieve.levinsonLinearMollifierCoeff M k‖ ^ 2)]
  refine (Finset.sum_le_sum fun k hk => ?_).trans
    (Sieve.sum_Icc_one_div_le_one_add_log M)
  have hkpos : 0 < k := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  have hnorm := Sieve.norm_levinsonLinearMollifierCoeff_le (M := M) (n := k) hM
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  refine hsquare.trans_eq ?_
  have hsqrt : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  rw [div_pow, one_pow, hsqrt]

/-- Harmonic-logarithmic upper bound for the finite unsmoothed detector-head energy. -/
theorem sum_normSq_levinsonCriticalDetectorHeadCoeff_le
    (lam : ℝ) {L : ℕ} (hL : 1 ≤ L) :
    ∑ n : Fin L,
        ‖Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)‖ ^ 2 ≤
      (1 + |lam| * Real.log L) ^ 2 * (1 + Real.log L) := by
  rw [show (∑ n : Fin L,
        ‖Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)‖ ^ 2) =
      ∑ k ∈ Finset.Icc 1 L,
        ‖Sieve.levinsonCriticalDetectorHeadCoeff lam k‖ ^ 2 by
    exact Sieve.sum_fin_eq_sum_Icc L
      (fun k => ‖Sieve.levinsonCriticalDetectorHeadCoeff lam k‖ ^ 2)]
  let B : ℝ := 1 + |lam| * Real.log L
  have hlogL : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hterm : ∀ k ∈ Finset.Icc 1 L,
      ‖Sieve.levinsonCriticalDetectorHeadCoeff lam k‖ ^ 2 ≤
        (1 / (k : ℝ)) * B ^ 2 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkL : k ≤ L := (Finset.mem_Icc.mp hk).2
    have hkpos : 0 < k := by omega
    have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
    have hlogle : Real.log (k : ℝ) ≤ Real.log (L : ℝ) := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hkL)
    have habs : |1 - lam * Real.log (k : ℝ)| ≤ B := by
      calc
        |1 - lam * Real.log (k : ℝ)| ≤ |(1 : ℝ)| + |lam * Real.log (k : ℝ)| :=
          abs_sub _ _
        _ = 1 + |lam| * Real.log (k : ℝ) := by
          rw [abs_one, abs_mul, abs_of_nonneg hlogk]
        _ ≤ B := by
          dsimp only [B]
          gcongr
    rw [norm_levinsonCriticalDetectorHeadCoeff lam hkpos]
    have hmul :
        (1 / Real.sqrt (k : ℝ)) * |1 - lam * Real.log (k : ℝ)| ≤
          (1 / Real.sqrt (k : ℝ)) * B :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    refine (pow_le_pow_left₀ (by positivity) hmul 2).trans_eq ?_
    have hsqrt : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) :=
      Real.sq_sqrt (by positivity)
    rw [mul_pow, div_pow, one_pow, hsqrt]
  refine (Finset.sum_le_sum hterm).trans ?_
  calc
    (∑ k ∈ Finset.Icc 1 L, (1 / (k : ℝ)) * B ^ 2) =
        B ^ 2 * ∑ k ∈ Finset.Icc 1 L, 1 / (k : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ B ^ 2 * (1 + Real.log L) :=
      mul_le_mul_of_nonneg_left (Sieve.sum_Icc_one_div_le_one_add_log L) (sq_nonneg B)
    _ = (1 + |lam| * Real.log L) ^ 2 * (1 + Real.log L) := by rfl

/-- Unconditional divisor-fibre cap for the exact long energy. -/
theorem exists_levinsonCriticalDetectorLongEnergy_le_rpow_factorEnergy
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : ℝ) (L M : ℕ),
      levinsonCriticalDetectorLongEnergy lam L M ≤
        C * ((L * M : ℕ) : ℝ) ^ ε *
          ((∑ n : Fin L,
              ‖Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)‖ ^ 2) *
            (∑ m : Fin M, ‖levinsonLinearMollifierFinCoeff M m‖ ^ 2)) := by
  obtain ⟨C, hC, hconv⟩ := Sieve.exists_sum_norm_sq_dirConv_le_rpow hε
  refine ⟨C, hC, ?_⟩
  intro lam L M
  refine (levinsonCriticalDetectorLongEnergy_le_fullEnergy lam L M).trans ?_
  simpa only [levinsonCriticalDetectorMollifiedFinCoeff] using
    hconv L M
      (fun n : Fin L => Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1))
      (levinsonLinearMollifierFinCoeff M)

/-- Divisor-fibre cap with the mollifier factor reduced to its harmonic envelope. -/
theorem exists_levinsonCriticalDetectorLongEnergy_le_rpow_headEnergy
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : ℝ) (L : ℕ) {M : ℕ}, 1 < M →
      levinsonCriticalDetectorLongEnergy lam L M ≤
        C * ((L * M : ℕ) : ℝ) ^ ε *
          ((∑ n : Fin L,
              ‖Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)‖ ^ 2) *
            (1 + Real.log M)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_levinsonCriticalDetectorLongEnergy_le_rpow_factorEnergy hε
  refine ⟨C, hC, ?_⟩
  intro lam L M hM
  refine (hbound lam L M).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul_of_nonneg_left
      (sum_normSq_levinsonLinearMollifierFinCoeff_le hM)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · positivity

/-- Fully explicit coarse divisor-fibre cap for the exact long energy. -/
theorem exists_levinsonCriticalDetectorLongEnergy_le_rpow_explicit
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : ℝ) {L M : ℕ}, 1 ≤ L → 1 < M →
      levinsonCriticalDetectorLongEnergy lam L M ≤
        C * ((L * M : ℕ) : ℝ) ^ ε *
          (((1 + |lam| * Real.log L) ^ 2 * (1 + Real.log L)) *
            (1 + Real.log M)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_levinsonCriticalDetectorLongEnergy_le_rpow_headEnergy hε
  refine ⟨C, hC, ?_⟩
  intro lam L M hL hM
  refine (hbound lam L hM).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul_of_nonneg_right
      (sum_normSq_levinsonCriticalDetectorHeadCoeff_le lam hL)
      (by positivity)
  · positivity

end RHTower
