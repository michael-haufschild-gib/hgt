import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeUniformFiniteBounds
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCompleteEnergy

/-!
# Complete quadratic cost above the smallest conductor cutoffs

The exact neutral decomposition retains the prime dilation form. All other
channels cost the reciprocal-prime coefficient mass, except for the explicit
centered polar coefficient in the near Gram.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  CompletedArithmeticForms CriticalArithmeticCorrelationTheory SelectiveMultiscaleArithmeticPositivity

/-- The literal physical prime form is nonnegative and costs at most twice adjunction mass. -/
theorem harmonicPrimeCharge_physical_jump_bounds {Q N : ℕ} (hQ : 2 ≤ Q) (hL : 1 ≤ Real.log N) (t : ℝ) :
    0 ≤ jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) /
        Real.log N ∧
    jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) /
        Real.log N ≤ 2 * t ^ 2 / primePoleScale Q := by
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL
  have hB := primePoleScale_pos hQ
  have hH : harmonicMass N ≤ 2 * Real.log N := by
    have h := harmonic_le_one_add_log N
    have he : (harmonic N : ℝ) = harmonicMass N := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
    rw [he] at h
    linarith only [h, hL]
  have hHp (p : ℕ) : harmonicMass (N / p) ≤ 2 * Real.log N := by
    refine le_trans ?_ hH
    exact sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc le_rfl (Nat.div_le_self N p)) (fun _ _ _ => by positivity)
  have hs : (∑ p ∈ (Icc 1 Q).filter Nat.Prime,
      Real.log p / p * harmonicMass (N / p)) ≤ primePoleScale Q * (2 * Real.log N) := by
    unfold primePoleScale
    rw [sum_mul]
    exact sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hHp p)
      (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  rw [harmonicPrimeCharge_jumpEnergy (by omega : 1 ≤ Q)]
  constructor
  · apply div_nonneg (mul_nonneg (sq_nonneg _) ?_) hL0.le
    exact sum_nonneg fun p _ => mul_nonneg
      (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
      (sum_nonneg fun _ _ => by positivity)
  · refine (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) hL0.le).trans_eq ?_
    field_simp [hL0.ne', hB.ne']

/-- Physical normalization removes the horizon logarithm from the complete moment error. -/
theorem exists_harmonicPrimeCharge_physical_moment_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q N : ℕ) (c t : ℝ),
      2 ≤ Q → 1 ≤ N → 1 ≤ Real.log N → 1 ≤ c → c / N ≤ 1 / 3 →
      |completeWeilEnergy φ c N (harmonicPrimeChargeVector Q N t) -
          jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) /
            Real.log N| ≤
        C * c ^ 3 * (t / primePoleScale Q) ^ 2 *
          (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
            2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := exists_harmonicPrimeCharge_complete_error_bound hφ hφ0 hsupp hM
  refine ⟨2 * C, by positivity, ?_⟩
  intro Q N c t hQ hN hL hc hw
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL
  rw [harmonicPrimeChargeVector_energy, ← sub_div, abs_div, abs_of_pos hL0]
  have h := div_le_div_of_nonneg_right (hb Q N c t hQ hN hc hw) hL0.le
  have hr : (Real.log N + 1) / Real.log N ≤ 2 := by
    apply (div_le_iff₀ hL0).mpr
    linarith only [hL]
  refine h.trans ?_
  calc
    _ = (C * c ^ 3 * (t / primePoleScale Q) ^ 2 *
        (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
          2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ))) *
            ((Real.log N + 1) / Real.log N) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq (by ring)

/-- Every complete correction keeps its reciprocal-prime gain or its exact polar square. -/
theorem exists_harmonicPrimeCharge_quadratic_error_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ A B D : ℝ, 0 ≤ A ∧ 0 < B ∧ 0 < D ∧ ∀ {Q N : ℕ} {c : ℝ},
      2 ≤ Q → Q ^ 4 ≤ N → 18 * (1 + Real.log Q) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ((Q * Q : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N → ∀ t : ℝ,
      let V := (t / primePoleScale Q) ^ 2 *
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)
      let P := (|t| + 8 * |t| / primePoleScale Q) / Real.log N
      |completeWeilEnergy φ c N (harmonicPrimeChargeVector Q N t) -
          jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) /
            Real.log N| ≤
        52 * V * (D + Real.log c + 600 * c * (1 + Real.log Q) / Real.log N +
          36 * (152 * (∫ v, |φ v|) ^ 2 / (∫ v, φ v ^ 2)) * c ^ 2 / Real.log N +
          A * (c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N) +
            c ^ 5 * Real.log N / N + c ^ 3 * (Q : ℝ) ^ 4 / N) +
          2 * B * (c ^ 2 * (1 + Real.log Q) * (1 + Real.log c) / Real.log N +
            c ^ 2 * (Q : ℝ) * Real.sqrt (Real.log N / N))) +
        A * (1 + Real.log c) * ((3 / 2 : ℝ) * V + c * P ^ 2) := by
  obtain ⟨A, B, hA, hB, hchannels⟩ :=
    exists_neutral_receiving_quadratic_channels_bound hφ hsupp hM
  let scalar := |completeWeilSelfFinitePart φ 1| + Real.exp (1 / 2) / 2 +
    Real.log 2 + (Real.log 4 + 4 + Real.eulerMascheroniConstant)
  let D := |scalar| + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hscalar : scalar ≤ D := by
    have h := (abs_le.mp (le_refl |scalar|)).2
    dsimp only [D]
    linarith only [h]
  refine ⟨A, B, D, hA, hB, hD, ?_⟩
  intro Q N c hQ hQ4 hframe hc hw hrad hsize t
  dsimp only
  let a := harmonicPrimeChargeCoefficients Q N t
  let F := normalizedConductorPacket Q a
  let u := harmonicPrimeChargeVector Q N t
  let base := (Real.log N * ‖u‖ ^ 2 -
    ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) +
    (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
      completeWeilSelfError φ c N) * ‖u‖ ^ 2
  let C := D + Real.log c + 600 * c * (1 + Real.log Q) / Real.log N +
    36 * (152 * (∫ v, |φ v|) ^ 2 / (∫ v, φ v ^ 2)) * c ^ 2 / Real.log N +
    A * (c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N) +
      c ^ 5 * Real.log N / N + c ^ 3 * (Q : ℝ) ^ 4 / N) +
    2 * B * (c ^ 2 * (1 + Real.log Q) * (1 + Real.log c) / Real.log N +
      c ^ 2 * (Q : ℝ) * Real.sqrt (Real.log N / N))
  have hQN : Q ≤ N := (Nat.le_pow (by omega : 0 < 4)).trans hQ4
  have hN : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < Real.log N := by linarith only [hframe, Real.log_natCast_nonneg Q]
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlogQ := Real.log_natCast_nonneg Q
  have hcN : c ≤ N := (div_le_one hNR).mp (hw.trans (by norm_num))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hu := harmonicPrimeChargeVector_mem_pole_orthogonal hQ hN t
  rw [harmonicPrimeChargeVector_eq_sum] at hu
  have hch := hchannels hQ hQ4 hframe hc hw hrad hsize a hu
  rw [← harmonicPrimeChargeVector_eq_sum Q N t] at hch
  have hsc := abs_physicalPacket_scalar_diagonal_le hφ hsupp hM hc hN hcN F
  change |base - jumpEnergy N F / Real.log N| ≤
    (|completeWeilSelfFinitePart φ 1| + Real.log c + Real.exp (1 / 2) / 2 +
      Real.log 2 + (Real.log 4 + 4 + Real.eulerMascheroniConstant)) * ‖u‖ ^ 2 at hsc
  have hsc' : |base - jumpEnergy N F / Real.log N| ≤ (D + Real.log c) * ‖u‖ ^ 2 := by
    refine hsc.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    dsimp only [scalar] at hscalar
    linarith only [hscalar]
  have herr : |completeWeilEnergy φ c N u - jumpEnergy N F / Real.log N| ≤
      C * ‖u‖ ^ 2 + A * (1 + Real.log c) *
        ((∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
          a m ^ 2 * ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)) + c * a 1 ^ 2) := by
    refine (abs_sub_le _ base _).trans ((add_le_add hch hsc').trans_eq ?_)
    dsimp only [C]
    ring
  have hnorm := harmonicPrimeChargeVector_norm_sq_le hQ hQN t
  have hdiv := harmonicPrimeCharge_nonpolar_divisorMean_le Q N t
  have hpole := harmonicPrimeCharge_pole_abs_le hQ hQN t
  have hpole2 := mul_le_mul hpole hpole (abs_nonneg _) ((abs_nonneg _).trans hpole)
  simp only [← sq, sq_abs] at hpole2
  refine herr.trans ((add_le_add (mul_le_mul_of_nonneg_left hnorm hC)
    (mul_le_mul_of_nonneg_left
      (add_le_add hdiv (mul_le_mul_of_nonneg_left hpole2 hc0))
      (show 0 ≤ A * (1 + Real.log c) from
        mul_nonneg hA (by linarith only [hlogc])))).trans_eq ?_)
  dsimp only [C]
  ring

#print axioms harmonicPrimeCharge_physical_jump_bounds
#print axioms exists_harmonicPrimeCharge_physical_moment_bound
#print axioms exists_harmonicPrimeCharge_quadratic_error_bound

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
