import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteConductorResidualsRetainTheirHorizonDecay
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel

/-!
# Conductor costs of the complete Weil replacements

The horizon-uniform arithmetic budget gives cubic conductor growth for the
prime residual. Periodic Ramanujan mass gives quadratic growth for the
self, center, polar and separated archimedean replacements. Every constant
is chosen before the conductor and overlap.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory HTGeometry
  SuccessorShellArithmetic RenormalizedBiarithmeticGeometry

private theorem normalized_action_sq (N m : ℕ)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) :
    ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
      ‖Matrix.toEuclideanLin A (ramanujanHorizonVector m N)‖ ^ 2 / Real.log N := by
  rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

private theorem normalized_residual_sq (N m : ℕ)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) (e : ℝ) :
    ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
      e • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      ‖Matrix.toEuclideanLin A (ramanujanHorizonVector m N) -
        e • ramanujanHorizonVector m N‖ ^ 2 / Real.log N := by
  simp only [normalizedRamanujanHorizonVector, map_smul]
  rw [smul_comm e (Real.sqrt (Real.log N))⁻¹, ← smul_sub,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

private theorem abs_mode_le_conductor {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |normalizedRamanujanMode m n| ≤ (m : ℝ) :=
  (abs_normalizedRamanujanMode_le hm n).trans (sum_range_abs_normalizedRamanujanMode_le hm)

private theorem normalized_mode_norm_sq_le_conductor {m N : ℕ}
    (hm : 0 < m) (hlog : 1 ≤ Real.log (N : ℝ)) :
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 2 * (m : ℝ) ^ 2 := by
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hraw : ‖ramanujanHorizonVector m N‖ ^ 2 ≤
      (m : ℝ) ^ 2 * (1 + Real.log N) := by
    rw [ramanujanHorizonVector_norm_sq]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, (m : ℝ) ^ 2 * (1 / (n : ℝ)) := by
        apply sum_le_sum
        intro n hn
        rw [ramanujanPoleProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        have hs := mul_self_le_mul_self (abs_nonneg (normalizedRamanujanMode m n))
          (abs_mode_le_conductor hm n)
        rw [← sq, sq_abs, ← sq] at hs
        simpa only [div_eq_mul_inv, one_mul] using
          div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
      _ = (m : ℝ) ^ 2 * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N) (sq_nonneg _)
  calc
    _ = ‖ramanujanHorizonVector m N‖ ^ 2 / Real.log N := by
      rw [normalizedRamanujanHorizonVector, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, inv_pow, Real.sq_sqrt hL.le]
      ring
    _ ≤ (m : ℝ) ^ 2 * (1 + Real.log N) / Real.log N :=
      div_le_div_of_nonneg_right hraw hL.le
    _ ≤ _ := by
      rw [div_le_iff₀ hL]
      nlinarith only [mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hlog)]

/-- The full prime residual has one constant and an explicit cubic conductor cost. -/
theorem exists_primeResidual_uniform_conductor_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ N : ℕ,
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        C * (m : ℝ) ^ 3 / Real.log N := by
  obtain ⟨B, hB, hbound⟩ := SignedArithmeticHodgeTheory.exists_uniform_ramanujanPrimeResidual_family_bound
  refine ⟨25 * B, by positivity, fun m hm N => ?_⟩
  let mpos : ℕ+ := ⟨m, hm⟩
  have hraw := hbound {mpos} (fun _ => 1) N
  simp only [sum_singleton, one_mul, one_pow, mul_one] at hraw
  have hraw' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • ramanujanHorizonVector m N‖ ^ 2 ≤
      B * SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m ^ 2 := by
    rw [ramanujanHorizonVector_residual_norm_sq]
    exact hraw
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have hlog := Real.log_le_sub_one_of_pos hm0
  have hlog0 := Real.log_natCast_nonneg m
  have hfac : (1 + 4 * Real.log (m : ℝ)) ^ 2 ≤ (5 * m) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hlog, hm1]) 2
  have htot : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hcost : SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m ^ 2 ≤
      25 * (m : ℝ) ^ 3 := by
    rw [SignedArithmeticHodgeTheory.ramanujanResidualConductorCost, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg m.totient)]
    exact (mul_le_mul htot hfac (sq_nonneg _) hm0.le).trans_eq (by ring)
  rw [normalized_residual_sq]
  exact div_le_div_of_nonneg_right
    (hraw'.trans ((mul_le_mul_of_nonneg_left hcost hB.le).trans_eq (by ring)))
    (Real.log_natCast_nonneg N)

/-- Logarithmic normalization gives a quadratic conductor bound for the self replacement. -/
theorem exists_selfError_uniform_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ N : ℕ,
      1 ≤ N → 1 ≤ Real.log N → ∀ c : ℝ, 0 < c → c ≤ (N : ℝ) →
        ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          C * (m : ℝ) ^ 2 * c ^ 2 / (N : ℝ) ^ 2 := by
  let B : ℝ := Real.exp (1 / 2) / 2
  refine ⟨2 * B ^ 2, by dsimp only [B]; positivity, fun m hm N hN hlog c hc hcN => ?_⟩
  have hv := normalized_mode_norm_sq_le_conductor hm hlog
  have hs := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc hN hcN
  have hsq := mul_self_le_mul_self (abs_nonneg _) hs
  rw [← sq, sq_abs, ← sq] at hsq
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact (mul_le_mul hsq hv (sq_nonneg _) (sq_nonneg _)).trans_eq (by dsimp only [B]; ring)

/-- The two polar moments retain a quadratic conductor cost uniformly in overlap. -/
theorem exists_poleError_uniform_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 0 < c →
      ∀ N : ℕ, 1 ≤ N → c ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
          C * (m : ℝ) ^ 2 * c ^ 4 / Real.log N := by
  refine ⟨4 * (atomPoleMomentErrorConstant φ) ^ 2, by positivity, ?_⟩
  intro m hm c hc N hN hcN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hraw : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (ramanujanHorizonVector m N)‖ ^ 2 ≤
      4 * (atomPoleMomentErrorConstant φ) ^ 2 * (m : ℝ) ^ 2 * c ^ 4 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hd := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM hc hN hcN
    have hs := mul_self_le_mul_self (abs_nonneg _) hd
    rw [← sq, sq_abs, ← sq] at hs
    calc
      _ = ∑ n ∈ Icc 1 N, (atomPoleErrorCoefficient φ c N * ∑ j ∈ Icc 1 N,
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
            (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 := by
        refine sum_congr rfl fun n _ => ?_
        rw [mul_sum]
        congr 1
        exact sum_congr rfl fun j _ => by simp only [ramanujanPoleProfile]; ring
      _ ≤ 4 * (atomPoleErrorCoefficient φ c N) ^ 2 * (m : ℝ) ^ 2 * (N : ℝ) ^ 4 :=
        sum_sq_twoPoleKernel_poleProfile_le (Nat.cast_nonneg m) N
          (fun j _ => abs_mode_le_conductor hm j) _
      _ ≤ 4 * (atomPoleMomentErrorConstant φ * (c / N) ^ 2) ^ 2 *
          (m : ℝ) ^ 2 * (N : ℝ) ^ 4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = _ := by field_simp [hN0.ne']
  rw [normalized_action_sq]
  exact div_le_div_of_nonneg_right hraw (Real.log_natCast_nonneg N)

/-- The far archimedean replacement has the same uniform quadratic conductor cost. -/
theorem exists_crossError_uniform_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 0 < c →
      ∀ N : ℕ, 1 ≤ N →
        ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
          C * (m : ℝ) ^ 2 * c ^ 4 / Real.log N := by
  let K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  refine ⟨(36 * K₀) ^ 2, sq_nonneg _, ?_⟩
  intro m hm c hc N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hraw : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
      (ramanujanHorizonVector m N)‖ ^ 2 ≤ (36 * K₀) ^ 2 * (m : ℝ) ^ 2 * c ^ 4 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => if 2 * (c / N) < |Real.log j - Real.log n| then
        atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hentry := fun (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ Icc 1 N) =>
      abs_separatedCrossError_le hφ hsupp hM hc hN hn hj
    have hb := sum_sq_kernel_poleProfile_le
      (mul_nonneg hK₀0 (sq_nonneg (c / (N : ℝ)))) hentry (Nat.cast_nonneg m)
      (fun j _ => abs_mode_le_conductor hm j)
    change (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N,
      (if 2 * (c / N) < |Real.log j - Real.log n| then
        atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) *
          (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) ≤ _
    exact hb.trans_eq (by field_simp [hN0.ne'])
  rw [normalized_action_sq]
  exact div_le_div_of_nonneg_right hraw (Real.log_natCast_nonneg N)

#print axioms exists_primeResidual_uniform_conductor_bound
#print axioms exists_selfError_uniform_conductor_bound
#print axioms exists_poleError_uniform_conductor_bound
#print axioms exists_crossError_uniform_conductor_bound

private theorem normalized_mode_one (n : ℕ) : normalizedRamanujanMode 1 n = 1 := by
  simp only [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one,
    Nat.cast_one, Real.sqrt_one, div_one]

private theorem normalized_mode_sum_zero {m : ℕ} (hm : 0 < m) (hm1 : m ≠ 1) :
    ∑ j ∈ range m, normalizedRamanujanMode m j = 0 := by
  have h := periodMean_normalizedRamanujanMode_mul hm zero_lt_one dvd_rfl (one_dvd m) hm
  simp only [normalized_mode_one, mul_one, if_neg hm1, periodMean] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by exact_mod_cast hm.ne')

/-- The complete center residual has quadratic conductor cost, including the polar mode. -/
theorem fullWeilCenter_residual_uniform_conductor_bound {m : ℕ} (hm : 0 < m)
    (α : ℝ) (N : ℕ) :
    ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      87 * α ^ 2 * (m : ℝ) ^ 2 / Real.log N := by
  have hraw : ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (ramanujanHorizonVector m N) -
      (if m = 1 then α else 0) • ramanujanHorizonVector m N‖ ^ 2 ≤
      87 * α ^ 2 * (m : ℝ) ^ 2 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => (α / N) *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n - archimedeanCenterKernel n j)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N) -
      (if m = 1 then α else 0) • horizonProfileVector (ramanujanPoleProfile m) N‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_residual_norm_sq]
    by_cases hm1 : m = 1
    · subst m
      have hb := sum_sq_centerCorrection_pole_residual_le α N
      have he : (6 : ℝ) * α ^ 2 ≤ 87 * α ^ 2 := by
        nlinarith only [sq_nonneg α]
      simpa only [ramanujanPoleProfile, normalized_mode_one, if_pos rfl, ite_true,
        mul_one_div, mul_div_assoc, mul_one, Nat.cast_one, one_pow, mul_assoc,
        ← mul_sum] using hb.trans he
    · have hB : ∀ l k : ℕ, l ≤ k →
          |∑ j ∈ Ico l k, normalizedRamanujanMode m j| ≤ 2 * (m : ℝ) := by
        intro l k hlk
        exact (abs_sum_Ico_le_of_periodic hm (normalizedRamanujanMode_periodic hm)
          (normalized_mode_sum_zero hm hm1) l k hlk).trans
          (mul_le_mul_of_nonneg_left (sum_range_abs_normalizedRamanujanMode_le hm) zero_le_two)
      have hb := sum_sq_centerCorrection_poleProfile_le (Nat.cast_nonneg m)
        (abs_mode_le_conductor hm) hB α N
      have he : α ^ 2 * (4 * (2 * (m : ℝ)) + m) ^ 2 ≤ 87 * α ^ 2 * (m : ℝ) ^ 2 := by
        nlinarith only [sq_nonneg (α * (m : ℝ))]
      simpa only [if_neg hm1, zero_mul, sub_zero, ramanujanPoleProfile,
        mul_assoc, ← mul_sum] using hb.trans he
  rw [normalized_residual_sq]
  exact div_le_div_of_nonneg_right hraw (Real.log_natCast_nonneg N)

/-- Center charge is linear in overlap, with a horizon-independent conductor constant. -/
theorem exists_centerError_uniform_conductor_bound (φ : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, ∀ N : ℕ,
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
        (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) •
          normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        C * (m : ℝ) ^ 2 * c ^ 2 / Real.log N := by
  refine ⟨87 * completeWeilPoleShift φ 1 ^ 2, by positivity, fun m hm c N => ?_⟩
  have hb := fullWeilCenter_residual_uniform_conductor_bound hm (completeWeilPoleShift φ c) N
  have he : completeWeilPoleShift φ c = c * completeWeilPoleShift φ 1 := by
    unfold completeWeilPoleShift
    ring
  rw [he] at hb
  rw [he]
  exact hb.trans_eq (by ring)

/-- The near-center replacement keeps its explicit quadratic conductor factor. -/
theorem exists_nearCenter_uniform_conductor_bound {φ : ℝ → ℝ}
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → 2 * c ≤ (N : ℝ) →
        ‖nearCenterVector φ c N m‖ ^ 2 ≤ C * (m : ℝ) ^ 2 * c ^ 5 / Real.log N := by
  let A := completeWeilPoleShift φ 1 * (1 + Real.exp (1 / 2))
  have hA : 0 ≤ A := by dsimp only [A, completeWeilPoleShift]; positivity
  refine ⟨4 * (2 * Real.exp 2) ^ 3 * A ^ 2, by positivity, ?_⟩
  intro m hm c hc N hN hcN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hcN, hc0])
  have hα : |completeWeilPoleShift φ c| = c * completeWeilPoleShift φ 1 := by
    rw [abs_of_nonneg (show 0 ≤ completeWeilPoleShift φ c by unfold completeWeilPoleShift; positivity)]
    unfold completeWeilPoleShift
    ring
  have hentry (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ nearRowIndices c N n) :
      |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
        normalizedRamanujanMode m j| ≤ A * (m : ℝ) * c := by
    have hb := abs_nearCenter_entry_le (φ := φ) hm hN hcN hn hj
    rw [hα] at hb
    have hmass := mul_le_mul_of_nonneg_left (sum_range_abs_normalizedRamanujanMode_le hm)
      (show 0 ≤ c * A by positivity)
    have hmass' : c * completeWeilPoleShift φ 1 * (1 + Real.exp (1 / 2)) *
        (∑ i ∈ range m, |normalizedRamanujanMode m i|) ≤ c * A * (m : ℝ) := by
      simpa only [A, mul_assoc] using hmass
    exact (hb.trans hmass').trans_eq (by ring)
  rw [nearCenterVector_norm_sq]
  apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
  exact (sum_near_div_sqrt_sq_le_small_width hc0 hN hw
    (fun n j => completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
      normalizedRamanujanMode m j) hentry).trans_eq (by unfold linearNearRowRadius; ring)

#print axioms fullWeilCenter_residual_uniform_conductor_bound
#print axioms exists_centerError_uniform_conductor_bound
#print axioms exists_nearCenter_uniform_conductor_bound

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
