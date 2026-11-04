import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeOverlap
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandQuadraticCancellation
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandQuadraticCenterBounds

/-!
# Quadratic channels of a neutral receiving packet

The transpose identity removes the upward prime channel from the quadratic
form. The remaining overlap keeps the coefficient-weighted divisor mean;
the center and separated cross terms retain their full horizon decay.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalArithmeticCorrelationTheory

/-- The literal neutral complete form after quadratic upward/downward transposition. -/
theorem neutral_complete_energy_quadratic_channels {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 2 ≤ N) {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu : u ∈ (conductorSubspace 1 N)ᗮ) :
    completeWeilEnergy φ c N u =
      (Real.log N * ‖u‖ ^ 2 - ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) +
      (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) * ‖u‖ ^ 2 +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) u, u⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, u⟫ -
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫ +
      2 * ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u, u⟫ := by
  rw [completeWeilEnergy,
    completeWeilMatrix_inner_eq_decomposition_at_every_overlap hφ hsupp hM hc (by omega),
    fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one φ c hN hu hu,
    overlap_sub_nonRatio_inner_eq hφ hsupp hM hc (by omega)]
  ring

/-- All non-diagonal quadratic channels retain the individual divisor costs of the packet. -/
theorem exists_neutral_receiving_quadratic_channels_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 < B ∧ ∀ {Q N : ℕ} {c : ℝ},
      2 ≤ Q → Q ^ 4 ≤ N → 18 * (1 + Real.log Q) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ((Q * Q : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ a : ℕ → ℝ,
      let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
      u ∈ (conductorSubspace 1 N)ᗮ →
      |completeWeilEnergy φ c N u -
        ((Real.log N * ‖u‖ ^ 2 - ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) +
          (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
            completeWeilSelfError φ c N) * ‖u‖ ^ 2)| ≤
        (600 * c * (1 + Real.log Q) / Real.log N +
          36 * (152 * (∫ v, |φ v|) ^ 2 / (∫ v, φ v ^ 2)) * c ^ 2 / Real.log N) * ‖u‖ ^ 2 +
        A * ((c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 5 * Real.log N / N + c ^ 3 * (Q : ℝ) ^ 4 / N) * ‖u‖ ^ 2 +
          (1 + Real.log c) *
            ((∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
              a m ^ 2 * ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)) + c * a 1 ^ 2)) +
        2 * B * (c ^ 2 * (1 + Real.log Q) * (1 + Real.log c) / Real.log N +
          c ^ 2 * (Q : ℝ) * Real.sqrt (Real.log N / N)) * ‖u‖ ^ 2 := by
  obtain ⟨A, hA, hOv⟩ := exists_receivingOverlap_packet_form_bound hφ hsupp hM
  obtain ⟨B, hB, hDown⟩ := exists_overlap_sub_downward_inner_le_of_mem_conductorSubspace hφ hsupp hM
  refine ⟨A, B, hA, hB, ?_⟩
  intro Q N c hQ hQ4 hlog hc hw hrad hsize a
  dsimp only
  intro hu1
  let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  have hu := sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q N a
  have hQ2 : Q * Q ≤ N := by
    have h := (Nat.pow_le_pow_right (by omega : 0 < Q) (by norm_num : 2 ≤ 4)).trans hQ4
    simpa only [sq] using h
  have hN : 2 ≤ N := by have h := Nat.mul_le_mul hQ hQ; omega
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg Q]
  have hlogQ : 0 ≤ 1 + Real.log Q := by linarith only [Real.log_natCast_nonneg Q]
  have hCenter := abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace
    (completeWeilPoleShift φ c) hQ hQ4 hlog hu hu1
  rw [abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)] at hCenter
  have hCenter' := hCenter.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le) (by norm_num : (0 : ℝ) ≤ 600))
      hlogQ) hL.le) (sq_nonneg ‖u‖))
  have hCross := abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
    hφ hsupp hM hc0 hQ hQ4 hlog hu
  have hOverlap := hOv hQ hQ2 hlog hc hw hrad hsize a
  have hD := mul_le_mul_of_nonneg_left (hDown hQ hQ2 hlog hc hw hsize hu) zero_le_two
  rw [neutral_complete_energy_quadratic_channels hφ hsupp hM hc0 hN hu1]
  have he : ∀ base center cross overlap down : ℝ,
      |base + center - cross - overlap + 2 * down - base| ≤
        |center| + |cross| + |overlap| + 2 * |down| := by
    intro base center cross overlap down
    calc
      _ = |((center - cross) - overlap) + 2 * down| := by congr 1; ring
      _ ≤ |(center - cross) - overlap| + |2 * down| := abs_add_le _ _
      _ ≤ (|center| + |cross|) + |overlap| + 2 * |down| := by
        rw [abs_mul, abs_two]
        exact add_le_add ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl
  exact (he _ _ _ _ _).trans
    ((add_le_add (add_le_add (add_le_add hCenter' hCross) hOverlap) hD).trans_eq (by ring))

#print axioms neutral_complete_energy_quadratic_channels
#print axioms exists_neutral_receiving_quadratic_channels_bound

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
