import GaloisForLFunctions.HTGeometry.FiniteWalshObservationCapacityLaw
import GaloisForLFunctions.HTGeometry.LBitBoundaryTemporalDimensionBudgetLaw
import GaloisForLFunctions.HTGeometry.LBitSupportLocalReporterLaw

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance boundaryBoolCubeFintype
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

/-- Boundary interaction energy with its two endpoint signs exposed. -/
noncomputable def lbitBoundaryPacketEnergy
    (r : ℕ) (left right : Bool)
    (x : ↥(lbitBoundaryInterior r) → Bool) : ℝ :=
  ∑ S : Finset ↥(lbitBoundaryInterior r),
    (((lbitSign left * lbitSign right *
      lbitWalshCharacter S x : ℚ) : ℝ) *
        lbitBoundaryCoefficient r S)

/-- Mixed endpoint phase generator carried by the complete boundary packet. -/
noncomputable def lbitBoundaryPhaseGenerator
    (r : ℕ) (x : ↥(lbitBoundaryInterior r) → Bool) : ℝ :=
  4 * ∑ S : Finset ↥(lbitBoundaryInterior r),
    lbitWalshCharacterReal S x * lbitBoundaryCoefficient r S

/-- The boundary generator is exactly the double endpoint-flip energy. -/
theorem lbitBoundaryPacketEnergy_doubleFlip_eq_generator
    (r : ℕ) (x : ↥(lbitBoundaryInterior r) → Bool) :
    lbitBoundaryPacketEnergy r true true x -
        lbitBoundaryPacketEnergy r true false x -
        lbitBoundaryPacketEnergy r false true x +
        lbitBoundaryPacketEnergy r false false x =
      lbitBoundaryPhaseGenerator r x := by
  simp only [lbitBoundaryPacketEnergy, lbitBoundaryPhaseGenerator,
    lbitSign, lbitWalshCharacterReal]
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  push_cast
  ring

/-- The double-flip generator is bounded by four times packet mass. -/
theorem abs_lbitBoundaryPhaseGenerator_le
    (r : ℕ) (x : ↥(lbitBoundaryInterior r) → Bool) :
    |lbitBoundaryPhaseGenerator r x| ≤
      4 * lbitBoundaryPacketAbsMass r := by
  unfold lbitBoundaryPhaseGenerator
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    4 * |∑ S : Finset ↥(lbitBoundaryInterior r),
          lbitWalshCharacterReal S x * lbitBoundaryCoefficient r S| ≤
        4 * ∑ S : Finset ↥(lbitBoundaryInterior r),
          |lbitWalshCharacterReal S x * lbitBoundaryCoefficient r S| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ = 4 * lbitBoundaryPacketAbsMass r := by
      rw [lbitBoundaryPacketAbsMass]
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      rw [abs_mul, lbitWalshCharacterReal,
        abs_lbitWalshCharacter]
      norm_num

/-- Demodulated endpoint OTO phase response. -/
noncomputable def lbitBoundaryPhaseResponse
    (r : ℕ) (t : ℝ)
    (x : ↥(lbitBoundaryInterior r) → Bool) : ℂ :=
  Complex.exp
      (t • (Complex.I * (lbitBoundaryPhaseGenerator r x : ℂ))) -
    1

/-- Unit-circle chord bound for the boundary response. -/
theorem norm_lbitBoundaryPhaseResponse_le_generator
    (r : ℕ) (t : ℝ)
    (x : ↥(lbitBoundaryInterior r) → Bool) :
    ‖lbitBoundaryPhaseResponse r t x‖ ≤
      |t| * |lbitBoundaryPhaseGenerator r x| := by
  let z : ℂ :=
    Complex.I * (lbitBoundaryPhaseGenerator r x : ℂ)
  have hz : z ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff]
    simp [z]
  have hzero : (0 : ℂ) ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff]
    simp
  have hduhamel :=
    exp_skewAdjoint_sub_exp_skewAdjoint_norm_le
      z 0 hz hzero t
  change ‖Complex.exp (t • z) - 1‖ ≤ _
  calc
    ‖Complex.exp (t • z) - 1‖ =
        ‖Complex.exp (t • z) - Complex.exp (t • (0 : ℂ))‖ := by
      simp
    _ ≤ |t| * ‖z - 0‖ := by
      simpa only [Complex.exp_eq_exp_ℂ] using hduhamel
    _ = |t| * |lbitBoundaryPhaseGenerator r x| := by
      simp [z, Complex.norm_real, Real.norm_eq_abs]

/-- Packet mass controls every finite-time boundary response. -/
theorem norm_lbitBoundaryPhaseResponse_le_packetMass
    (r : ℕ) (t : ℝ)
    (x : ↥(lbitBoundaryInterior r) → Bool) :
    ‖lbitBoundaryPhaseResponse r t x‖ ≤
      4 * |t| * lbitBoundaryPacketAbsMass r := by
  calc
    ‖lbitBoundaryPhaseResponse r t x‖ ≤
        |t| * |lbitBoundaryPhaseGenerator r x| :=
      norm_lbitBoundaryPhaseResponse_le_generator r t x
    _ ≤ |t| * (4 * lbitBoundaryPacketAbsMass r) := by
      gcongr
      exact abs_lbitBoundaryPhaseGenerator_le r x
    _ = 4 * |t| * lbitBoundaryPacketAbsMass r := by ring

/-- Finite-time operational dimension is bounded by the same packet mass. -/
theorem lbitBoundaryResponse_capacity_le_packetMass
    (r : ℕ) (t : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    η ^ 2 *
        (walshThresholdCount (lbitBoundaryPhaseResponse r t) η : ℝ) ≤
      (4 * |t| * lbitBoundaryPacketAbsMass r) ^ 2 := by
  exact sq_mul_walshThresholdCount_le_bound_sq
    (lbitBoundaryPhaseResponse r t) hη
    (norm_lbitBoundaryPhaseResponse_le_packetMass r t)

/-- **Operational boundary--time capacity law.** The number of boundary
Walsh directions visible at resolution `η` and time `t` pays the square of
the exact boundary dimension against the global quasi-locality budget. -/
theorem lbitBoundaryResponse_dimension_time_capacity
    (r : ℕ) (t : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    η ^ 2 *
        (walshThresholdCount (lbitBoundaryPhaseResponse r t) η : ℝ) *
        ((2 : ℝ) ^ r) ^ 2 ≤
      4 * t ^ 2 * quasiLocalInfiniteLBitWeightedMass ^ 2 := by
  let D : ℝ := (2 : ℝ) ^ r
  let M : ℝ := lbitBoundaryPacketAbsMass r
  let K : ℝ := quasiLocalInfiniteLBitWeightedMass
  have hM : 0 ≤ M := by
    unfold M lbitBoundaryPacketAbsMass
    positivity
  have hK : 0 ≤ K := by
    unfold K quasiLocalInfiniteLBitWeightedMass
    exact tsum_nonneg fun S =>
      mul_nonneg (by positivity) (abs_nonneg _)
  have hbudget : 2 * D * M ≤ K := by
    have h := two_pow_mul_lbitBoundaryPacketAbsMass_le_weightedMass r
    change (2 : ℝ) ^ (r + 1) * M ≤ K at h
    rw [pow_succ] at h
    nlinarith
  have hbudgetSq : (2 * D * M) ^ 2 ≤ K ^ 2 := by
    simpa only [pow_two] using
      (mul_self_le_mul_self (by positivity : 0 ≤ 2 * D * M) hbudget)
  have hcap := lbitBoundaryResponse_capacity_le_packetMass r t hη
  have hscaled := mul_le_mul_of_nonneg_right hcap (sq_nonneg D)
  change
    η ^ 2 *
        (walshThresholdCount (lbitBoundaryPhaseResponse r t) η : ℝ) *
        D ^ 2 ≤ 4 * t ^ 2 * K ^ 2
  calc
    η ^ 2 *
          (walshThresholdCount (lbitBoundaryPhaseResponse r t) η : ℝ) *
          D ^ 2 ≤
        (4 * |t| * M) ^ 2 * D ^ 2 := hscaled
    _ = 4 * t ^ 2 * (2 * D * M) ^ 2 := by
      simp only [mul_pow, sq_abs]
      ring
    _ ≤ 4 * t ^ 2 * K ^ 2 := by
      gcongr

/-- Resolving every one of the `2 ^ r` boundary directions forces the cubic
dimension--time budget `η² D³ ≤ 4 K² t²`. -/
theorem lbitBoundaryResponse_fullVisibility_time_lower_sq
    (r : ℕ) (t : ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hvisible :
      ∀ A : Finset ↥(lbitBoundaryInterior r),
        η ≤ ‖inverseWalshCoefficient
          (lbitBoundaryPhaseResponse r t) A‖) :
    η ^ 2 * ((2 : ℝ) ^ r) ^ 3 ≤
      4 * t ^ 2 * quasiLocalInfiniteLBitWeightedMass ^ 2 := by
  classical
  have hcount :
      walshThresholdCount (lbitBoundaryPhaseResponse r t) η =
        2 ^ r := by
    unfold walshThresholdCount
    rw [Finset.filter_eq_self.mpr]
    · simp [card_lbitBoundaryInterior]
    · intro A hA
      exact hvisible A
  have hcap := lbitBoundaryResponse_dimension_time_capacity r t hη
  calc
    η ^ 2 * ((2 : ℝ) ^ r) ^ 3 =
        η ^ 2 *
          (walshThresholdCount
            (lbitBoundaryPhaseResponse r t) η : ℝ) *
          ((2 : ℝ) ^ r) ^ 2 := by
      rw [hcount]
      norm_num [Nat.cast_pow]
      ring
    _ ≤ 4 * t ^ 2 * quasiLocalInfiniteLBitWeightedMass ^ 2 := hcap

end

end GaloisForLFunctions.HTGeometry
