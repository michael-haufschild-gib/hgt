import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeNearGram

/-!
# The overlap form retains the coherent divisor mean

Subtract the logarithmic near Gram before estimating the archimedean
overlap. The remainder has bounded near entries and gains the terminal
mass of a conductor packet. The polar coefficient remains explicit.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalArithmeticCorrelationTheory
  CompletedArithmeticForms SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-- The overlap kernel after removal of its logarithmic near Gram. -/
def receivingOverlapSubKernel (φ : ℝ → ℝ) (c : ℝ) (N n j : ℕ) : ℝ :=
  atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) +
    (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j -
    Real.log (1 / (c / N)) *
      (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2))

/-- Subtracting the near logarithm leaves an overlap entry of size at most a constant times `c`. -/
theorem exists_receivingOverlapSubKernel_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {N : ℕ} {c : ℝ}, 1 ≤ N → 1 ≤ c → c / N ≤ 1 / 3 →
      ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
        |receivingOverlapSubKernel φ c N n j| ≤ A * c := by
  obtain ⟨A, hA, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  refine ⟨A + (1 + Real.exp (1 / 2)), by positivity, ?_⟩
  intro N c hN hc hw n hn j hj
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hcN : 2 * c ≤ N := by
    have h := (div_le_iff₀ hN0).mp hw
    linarith only [h, hc0]
  have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
    simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
  have hrem := hpair (c / N) (div_pos hc0 hN0) hw n j hs
  have hcenter : |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| ≤
      (1 + Real.exp (1 / 2)) * c := by
    have h := abs_nearCenter_entry_le (φ := φ) (m := 1) zero_lt_one hN hcN hn hj
    have hm1 (k : ℕ) : normalizedRamanujanMode 1 k = 1 := by
      rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
        Real.sqrt_one, div_one]
    rw [hm1 j, mul_one, range_one, sum_singleton, hm1 0, abs_one, mul_one,
      abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)] at h
    exact h.trans ((mul_le_mul_of_nonneg_right
      (completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le) (by positivity)).trans_eq
        (mul_comm _ _))
  have he : receivingOverlapSubKernel φ c N n j =
      (atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) -
        Real.log (1 / (c / N)) * shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) /
          (∫ u, φ u ^ 2)) +
        (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j := by
    unfold receivingOverlapSubKernel
    ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hrem hcenter).trans (by
    have hAc := mul_le_mul_of_nonneg_left hc hA
    nlinarith only [hAc]))

/-- A conductor packet gives a square-root logarithmic gain in the overlap remainder. -/
theorem exists_receivingOverlapSubKernel_form_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Q N : ℕ} {c : ℝ},
      2 ≤ Q → 1 ≤ N → 18 * (1 + Real.log Q) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 →
      ((Q * Q : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u ∈ conductorSubspace Q N →
      |∑ n ∈ Icc 1 N, primeHorizonExtension u n *
        ∑ j ∈ nearRowIndices c N n,
          receivingOverlapSubKernel φ c N n j * primeHorizonExtension u j| ≤
        C * c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 := by
  obtain ⟨A, hA, hentry⟩ := exists_receivingOverlapSubKernel_bound hφ hsupp hM
  let D : ℝ := 80 * (2 * Real.exp 2) ^ 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨Real.sqrt D * A, by positivity, ?_⟩
  intro Q N c hQ hN hlog hc hw hsize u hu
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg Q]
  have hratio : 0 ≤ (1 + Real.log c) / Real.log N := by
    have h := Real.log_nonneg hc
    positivity
  have hrow := CriticalArithmeticCorrelationTheory.sum_nearBand_sq_le_of_mem_conductorSubspace
    hQ hlog hc (hw.trans (by norm_num)) (mul_nonneg hA (zero_le_one.trans hc))
    hsize (receivingOverlapSubKernel φ c N) (hentry hN hc hw) hu
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 N) (primeHorizonExtension u)
    (fun n => ∑ j ∈ nearRowIndices c N n,
      receivingOverlapSubKernel φ c N n j * primeHorizonExtension u j)
  rw [sum_primeHorizonExtension_sq] at hcs
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hrow (sq_nonneg ‖u‖))
  have he : ‖u‖ ^ 2 * (D * c ^ 2 * (A * c) ^ 2 *
      ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) =
      (Real.sqrt D * A * c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hD, Real.sq_sqrt hratio]
    ring
  change _ ≤ ‖u‖ ^ 2 * (D * c ^ 2 * (A * c) ^ 2 *
    ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) at hbound
  rw [he] at hbound
  have hnonneg : 0 ≤ Real.sqrt D * A * c ^ 2 *
      Real.sqrt ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 := by positivity
  have habs : |∑ n ∈ Icc 1 N, primeHorizonExtension u n *
      ∑ j ∈ nearRowIndices c N n,
        receivingOverlapSubKernel φ c N n j * primeHorizonExtension u j| ^ 2 ≤
      (Real.sqrt D * A * c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) ^ 2 := by
    simpa only [sq_abs] using hbound
  nlinarith only [habs, hnonneg, abs_nonneg
    (∑ n ∈ Icc 1 N, primeHorizonExtension u n *
      ∑ j ∈ nearRowIndices c N n,
        receivingOverlapSubKernel φ c N n j * primeHorizonExtension u j)]

/-- The complete overlap retains its logarithmic near Gram and an exact remainder. -/
theorem overlapMatrix_inner_eq_receiving_nearGram (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫ =
      (∑ n ∈ Icc 1 N, primeHorizonExtension u n *
        ∑ j ∈ nearRowIndices c N n,
          receivingOverlapSubKernel φ c N n j * primeHorizonExtension u j) +
      Real.log (1 / (c / N)) *
        (∑ n ∈ Icc 1 N, primeHorizonExtension u n * nearGram φ c N (primeHorizonExtension u) n) := by
  have hrow : ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫ =
      ∑ n ∈ Icc 1 N, primeHorizonExtension u n *
        ∑ j ∈ nearRowIndices c N n,
          (atomArchPair (atomDilate φ (c / N)) n j / (∫ v, atomDilate φ (c / N) v ^ 2) +
            (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) *
            primeHorizonExtension u j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ n : PrimeHorizonIndex N, u.ofLp n *
      ∑ j : PrimeHorizonIndex N, overlapMatrix φ c N n j * u.ofLp j) = _
    rw [← sum_coe_sort (Icc 1 N) (fun n => primeHorizonExtension u n *
      ∑ j ∈ nearRowIndices c N n,
        (atomArchPair (atomDilate φ (c / N)) n j / (∫ v, atomDilate φ (c / N) v ^ 2) +
          (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) *
          primeHorizonExtension u j)]
    apply sum_congr rfl
    intro n _
    rw [primeHorizonExtension_coe u n]
    congr 1
    rw [nearRowIndices, sum_filter, ← sum_coe_sort (Icc 1 N)]
    apply sum_congr rfl
    intro j _
    rw [primeHorizonExtension_coe u j]
    dsimp only [overlapMatrix]
    by_cases h : (j : ℕ) ≠ (n : ℕ) ∧ |Real.log (j : ℕ) - Real.log (n : ℕ)| ≤ 2 * c / N
    · rw [if_pos ⟨Ne.symm h.1, by rw [← mul_div_assoc]; exact h.2⟩, if_pos h]
    · rw [if_neg (fun h' => h ⟨Ne.symm h'.1, by rw [mul_div_assoc]; exact h'.2⟩),
        if_neg h, zero_mul]
  rw [hrow, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  unfold nearGram
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  unfold receivingOverlapSubKernel
  ring

/-- The full overlap form costs each nonpolar divisor mean and the explicit polar coefficient. -/
theorem exists_receivingOverlap_packet_form_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Q N : ℕ} {c : ℝ},
      2 ≤ Q → Q * Q ≤ N → 18 * (1 + Real.log Q) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ((Q * Q : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ a : ℕ → ℝ,
      let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
      |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫| ≤
        C * ((c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 5 * Real.log N / N + c ^ 3 * (Q : ℝ) ^ 4 / N) * ‖u‖ ^ 2 +
          (1 + Real.log c) *
            ((∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
              a m ^ 2 * ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)) + c * a 1 ^ 2)) := by
  obtain ⟨A, hA, hsub⟩ := exists_receivingOverlapSubKernel_form_bound hφ hsupp hM
  obtain ⟨B, hB, hgram⟩ := exists_nearGram_packet_form_polar_bound hφ hsupp hM
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro Q N c hQ hQN hlog hc hw hrad hsize a
  dsimp only
  let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  let V := ∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
    a m ^ 2 * ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hN : 1 ≤ N := (Nat.mul_pos (by omega : 0 < Q) (by omega : 0 < Q)).trans_le hQN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg Q]
  have hlogc := Real.log_nonneg hc
  have hcN : c ≤ (N : ℝ) := by
    have h := (div_le_iff₀ hN0).mp hw
    linarith only [h, hN0]
  have hlogcN := Real.log_le_log hc0 hcN
  have hlogw : |Real.log (1 / (c / N))| ≤ Real.log N := by
    rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne', neg_sub,
      abs_of_nonneg (sub_nonneg.mpr hlogcN)]
    linarith only [hlogc]
  have hs := hsub hQ hN hlog hc hw hsize
    (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q N a)
  have hg := hgram hQ hQN hlog hc (hw.trans (by norm_num)) hrad a
  have hgp := mul_le_mul hlogw hg (abs_nonneg _) hL.le
  have hg' : |Real.log (1 / (c / N))| *
      |∑ n ∈ Icc 1 N, primeHorizonExtension u n * nearGram φ c N (primeHorizonExtension u) n| ≤
      B * ((c ^ 5 * Real.log N / N + c ^ 3 * (Q : ℝ) ^ 4 / N) * ‖u‖ ^ 2 +
        (1 + Real.log c) * (V + c * a 1 ^ 2)) := by
    exact hgp.trans_eq (by dsimp only [V]; field_simp [hL.ne']; ring)
  have hA' : A ≤ A + B := le_add_of_nonneg_right hB
  have hB' : B ≤ A + B := le_add_of_nonneg_left hA
  have hs' := hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA'
      (sq_nonneg c)) (Real.sqrt_nonneg _)) (sq_nonneg ‖u‖))
  have hg'' := hg'.trans (mul_le_mul_of_nonneg_right hB' (by positivity))
  rw [overlapMatrix_inner_eq_receiving_nearGram]
  exact (abs_add_le _ _).trans ((add_le_add hs' (by simpa only [abs_mul] using hg'')).trans_eq
    (by dsimp only [V]; ring))

#print axioms exists_receivingOverlapSubKernel_form_bound
#print axioms overlapMatrix_inner_eq_receiving_nearGram
#print axioms exists_receivingOverlap_packet_form_bound

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
