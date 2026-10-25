import GaloisForLFunctions.ArithmeticDefectRigidity.PaidWienerKernelsAnnihilateTheCofactorLimit

/-!
# Complete Wiener pairings along the actual common limit

The sharp two-coordinate Gram radius provides a summable majorant in both
Wiener indices. Two dominated limits recover the full cyclic inner product.
At each finite horizon this covariance is exactly the normalized pairing of
the finite-cell source rows.
-/

noncomputable section
set_option autoImplicit false

open Finset Filter Topology RHTower
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Retaining both cofactor radii gives a summable bound in both Wiener indices. -/
theorem norm_wienerCofactorCovariance_le (ε : SubcriticalDamping) (T : ℕ)
    (j : ℕ+) (a : WienerAlgebraAt (1 / 2)) :
    ‖wienerCofactorCovariance ε T j a‖ ≤ ‖a‖ * (1 / Real.sqrt (j : ℝ)) := by
  let V : ℕ → ℂ := fun n => (naturalCofactorGram ε T n j : ℂ)
  have hV0 : V 0 = 0 := by
    dsimp only [V]
    rw [naturalCofactorGram_zero, Complex.ofReal_zero]
  have hV : ∀ n, n ≠ 0 → ‖V n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    norm_naturalCofactorGram_le ε T j
  have hterm (n : ℕ) : ‖a.toFn n * V n‖ ≤
      ‖LSeries.term (⇑a.toFn) ((1 / 2 : ℝ) : ℂ) n‖ * (1 / Real.sqrt (j : ℝ)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hV0, mul_zero, norm_zero]
      positivity
    · rw [norm_mul]
      have hGram : ‖V n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (1 / Real.sqrt (j : ℝ)) := by
        dsimp only [V]
        rw [naturalCofactorGram_pos ε T n j hn, Complex.norm_real, Real.norm_eq_abs]
        have hr := abs_cofactorGram_le ε T ⟨n, hn⟩ j
        change |cofactorGram ε T ⟨n, hn⟩ j| ≤
          (1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (j : ℝ)) at hr
        refine hr.trans_eq ?_
        rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n)]
        simp only [one_div]
      calc
        _ ≤ ‖a.toFn n‖ * ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
            (1 / Real.sqrt (j : ℝ))) := mul_le_mul_of_nonneg_left hGram (norm_nonneg _)
        _ = _ := by
          rw [LSeries.norm_term_eq, if_neg hn.ne', Complex.ofReal_re,
            Real.rpow_neg (Nat.cast_nonneg n)]
          ring
  calc
    _ ≤ ∑' n, ‖a.toFn n * V n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_coefficient_smul V hV0 hV a)
    _ ≤ ∑' n, ‖LSeries.term (⇑a.toFn) ((1 / 2 : ℝ) : ℂ) n‖ *
        (1 / Real.sqrt (j : ℝ)) :=
      (summable_norm_coefficient_smul V hV0 hV a).tsum_le_tsum hterm
        (a.summable_norm.mul_right _)
    _ = _ := by rw [tsum_mul_right]; rfl

/-- Covariance of two complete Wiener actions, linear in the first coefficient row. -/
def wienerPairCovariance (ε : SubcriticalDamping) (T : ℕ)
    (a b : WienerAlgebraAt (1 / 2)) : ℂ :=
  ∑' n, conj (b.toFn n) *
    (if hn : 0 < n then wienerCofactorCovariance ε T ⟨n, hn⟩ a else 0)

theorem norm_wienerPairCovariance_summand_le (ε : SubcriticalDamping) (T : ℕ)
    (a b : WienerAlgebraAt (1 / 2)) (n : ℕ) :
    ‖conj (b.toFn n) *
      (if hn : 0 < n then wienerCofactorCovariance ε T ⟨n, hn⟩ a else 0)‖ ≤
      ‖LSeries.term (⇑b.toFn) ((1 / 2 : ℝ) : ℂ) n‖ * ‖a‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [dif_neg (Nat.not_lt_zero 0), mul_zero, norm_zero]
    positivity
  · rw [dif_pos hn, norm_mul, Complex.norm_conj]
    calc
      _ ≤ ‖b.toFn n‖ * (‖a‖ * (1 / Real.sqrt (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (norm_wienerCofactorCovariance_le ε T ⟨n, hn⟩ a)
          (norm_nonneg _)
      _ = _ := by
        rw [LSeries.norm_term_eq, if_neg hn.ne', Complex.ofReal_re, Real.sqrt_eq_rpow]
        ring

namespace ActualCofactorLimit

/-- Expanding the first inner-product argument gives the second Wiener coefficient series. -/
theorem inner_wiener_vectors_eq_tsum {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (a b : WienerAlgebraAt (1 / 2)) :
    ⟪wienerRepresentation L b (vector L 1), wienerRepresentation L a (vector L 1)⟫_ℂ =
      ∑' n, conj (b.toFn n) *
        (if hn : 0 < n then wienerCoordinate L ⟨n, hn⟩ a else 0) := by
  let w := wienerRepresentation L a (vector L 1)
  let f : WienerAlgebraAt (1 / 2) →L[ℂ] ℂ :=
    (innerSL ℂ w).comp
      ((ContinuousLinearMap.apply ℂ (Hilbert L) (vector L 1)).comp (wienerLinear L))
  have hs := Complex.hasSum_conj'.mpr (f.hasSum (hasSum_pointMass b))
  have hterm (n : ℕ) : conj (f (b.toFn n • pointMass n)) =
      conj (b.toFn n) *
        (if hn : 0 < n then wienerCoordinate L ⟨n, hn⟩ a else 0) := by
    rw [map_smul]
    change conj (b.toFn n * ⟪w, wienerRepresentation L (pointMass n) (vector L 1)⟫_ℂ) = _
    rw [map_mul, inner_conj_symm]
    have hp : wienerRepresentation L (pointMass n) = naturalDilation L n :=
      sequenceExtension_pointMass (naturalDilation L) (naturalDilation_zero L)
        (norm_naturalDilation_le L) n
    rw [hp]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [naturalDilation_zero, dif_neg (Nat.not_lt_zero 0)]
      simp only [zero_apply, inner_zero_left, mul_zero]
    · rw [naturalDilation_pos L n hn, dilation_vector, mul_one, dif_pos hn]
      rfl
  simp_rw [hterm] at hs
  have heq : conj (f b) =
      ⟪wienerRepresentation L b (vector L 1), wienerRepresentation L a (vector L 1)⟫_ℂ := by
    change conj ⟪wienerRepresentation L a (vector L 1),
      wienerRepresentation L b (vector L 1)⟫_ℂ = _
    exact inner_conj_symm (𝕜 := ℂ) _ _
  rw [heq] at hs
  exact hs.tsum_eq.symm

/-- The same actual Gram subsequence controls all complete Wiener pairings. -/
theorem wienerPairCovariance_tendsto {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (a b : WienerAlgebraAt (1 / 2)) :
    Tendsto (fun m => wienerPairCovariance ε (L.subsequence m) a b) atTop
      (𝓝 ⟪wienerRepresentation L b (vector L 1),
        wienerRepresentation L a (vector L 1)⟫_ℂ) := by
  rw [inner_wiener_vectors_eq_tsum]
  apply tendsto_tsum_of_dominated_convergence (b.summable_norm.mul_right ‖a‖)
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [dif_neg (Nat.not_lt_zero 0), mul_zero]
      exact tendsto_const_nhds
    · simp only [dif_pos hn]
      exact tendsto_const_nhds.mul (wienerCofactorCovariance_tendsto_coordinate L a ⟨n, hn⟩)
  · exact Eventually.of_forall fun m n =>
      norm_wienerPairCovariance_summand_le ε (L.subsequence m) a b n

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity

open Finset Filter Topology RHTower
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The complete complex Wiener action on the actual row; each cell uses finitely many coefficients. -/
def complexWienerRow (ε : SubcriticalDamping) (a : WienerAlgebraAt (1 / 2)) (n : ℕ) : ℂ :=
  ∑ j ∈ Icc 1 n, a.toFn j * (pmPowerDampedCenteredDivisorPrefix ε (n / j) : ℂ)

theorem complexWienerRow_eq_sum_horizon (ε : SubcriticalDamping)
    (a : WienerAlgebraAt (1 / 2)) {n T : ℕ} (hn : n ≤ T) :
    complexWienerRow ε a n =
      ∑ j ∈ Icc 1 T, a.toFn j * (pmPowerDampedCenteredDivisorPrefix ε (n / j) : ℂ) := by
  apply sum_subset (Icc_subset_Icc le_rfl hn)
  intro j hj hjn
  have hnj : n < j := by simp only [mem_Icc] at hj hjn; omega
  rw [Nat.div_eq_of_lt hnj,
    ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
    Complex.ofReal_zero, mul_zero]

theorem naturalCofactorGram_right_eq_zero_of_lt (ε : SubcriticalDamping)
    (T n : ℕ) (j : ℕ+) (hj : T + 1 < j) : naturalCofactorGram ε T n j = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact naturalCofactorGram_zero ε T j
  · rw [naturalCofactorGram_pos ε T n j hn, cofactorGram_symm]
    have h := naturalCofactorGram_eq_zero_of_lt ε T j ⟨n, hn⟩ hj
    rwa [naturalCofactorGram_pos ε T j ⟨n, hn⟩ j.property] at h

theorem wienerCofactorCovariance_eq_zero_of_lt (ε : SubcriticalDamping)
    (T : ℕ) (j : ℕ+) (a : WienerAlgebraAt (1 / 2)) (hj : T + 1 < j) :
    wienerCofactorCovariance ε T j a = 0 := by
  have hterm (n : ℕ) : a.toFn n * (naturalCofactorGram ε T n j : ℂ) = 0 := by
    rw [naturalCofactorGram_right_eq_zero_of_lt ε T n j hj, Complex.ofReal_zero, mul_zero]
  simp only [wienerCofactorCovariance, hterm, tsum_zero]

theorem wienerPairCovariance_eq_sum (ε : SubcriticalDamping) (T : ℕ)
    (a b : WienerAlgebraAt (1 / 2)) :
    wienerPairCovariance ε T a b = ∑ n ∈ Icc 1 (T + 1), conj (b.toFn n) *
      (if hn : 0 < n then wienerCofactorCovariance ε T ⟨n, hn⟩ a else 0) := by
  apply tsum_eq_sum
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [dif_neg (Nat.not_lt_zero 0), mul_zero]
  · rw [dif_pos hpos, wienerCofactorCovariance_eq_zero_of_lt ε T ⟨n, hpos⟩ a
      (by change T + 1 < n; simp only [mem_Icc] at hn; omega), mul_zero]

/-- The Wiener covariance series is exactly the normalized finite-cell source pairing. -/
theorem wienerCofactorCovariance_eq_source (ε : SubcriticalDamping) (T : ℕ)
    (j : ℕ+) (a : WienerAlgebraAt (1 / 2)) :
    wienerCofactorCovariance ε T j a =
      (∑ m ∈ Icc 1 (T + 1), complexWienerRow ε a m *
        (pmPowerDampedCenteredDivisorPrefix ε (m / j) : ℂ) /
          ((m : ℂ) * ((m : ℂ) + 1))) / (dampedMobiusEnergy ε (T + 1) : ℂ) := by
  have hentry (n : ℕ) (hn : n ∈ Icc 1 (T + 1)) :
      (naturalCofactorGram ε T n j : ℂ) =
        (∑ m ∈ Icc 1 (T + 1),
          (pmPowerDampedCenteredDivisorPrefix ε (m / n) : ℂ) *
          (pmPowerDampedCenteredDivisorPrefix ε (m / j) : ℂ) /
            ((m : ℂ) * ((m : ℂ) + 1))) / (dampedMobiusEnergy ε (T + 1) : ℂ) := by
    rw [naturalCofactorGram_pos ε T n j (mem_Icc.mp hn).1]
    unfold cofactorGram pronicPairing rowDilate
    push_cast
    rfl
  rw [wienerCofactorCovariance_eq_sum]
  have hleft : (∑ n ∈ Icc 1 (T + 1), a.toFn n * (naturalCofactorGram ε T n j : ℂ)) =
      ∑ n ∈ Icc 1 (T + 1), a.toFn n *
        ((∑ m ∈ Icc 1 (T + 1),
          (pmPowerDampedCenteredDivisorPrefix ε (m / n) : ℂ) *
          (pmPowerDampedCenteredDivisorPrefix ε (m / j) : ℂ) /
            ((m : ℂ) * ((m : ℂ) + 1))) / (dampedMobiusEnergy ε (T + 1) : ℂ)) := by
    exact sum_congr rfl fun n hn => by rw [hentry n hn]
  rw [hleft]
  simp only [mul_div_assoc, mul_sum, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  rw [complexWienerRow_eq_sum_horizon ε a (mem_Icc.mp hm).2]
  simp only [sum_mul]
  exact sum_congr rfl fun n _ => by ring

/-- Complex source pairing at the original receiver's energy scale. -/
def wienerSourcePairing (ε : SubcriticalDamping) (T : ℕ)
    (a b : WienerAlgebraAt (1 / 2)) : ℂ :=
  (∑ n ∈ Icc 1 (T + 1), conj (complexWienerRow ε b n) * complexWienerRow ε a n /
    ((n : ℂ) * ((n : ℂ) + 1))) / (dampedMobiusEnergy ε (T + 1) : ℂ)

theorem wienerPairCovariance_eq_source (ε : SubcriticalDamping) (T : ℕ)
    (a b : WienerAlgebraAt (1 / 2)) :
    wienerPairCovariance ε T a b = wienerSourcePairing ε T a b := by
  rw [wienerPairCovariance_eq_sum]
  have hterm (j : ℕ) (hj : j ∈ Icc 1 (T + 1)) :
      (if hn : 0 < j then wienerCofactorCovariance ε T ⟨j, hn⟩ a else 0) =
        (∑ m ∈ Icc 1 (T + 1), complexWienerRow ε a m *
          (pmPowerDampedCenteredDivisorPrefix ε (m / j) : ℂ) /
            ((m : ℂ) * ((m : ℂ) + 1))) / (dampedMobiusEnergy ε (T + 1) : ℂ) := by
    have hjpos : 0 < j := (mem_Icc.mp hj).1
    rw [dif_pos hjpos, wienerCofactorCovariance_eq_source]
    rfl
  have hleft := sum_congr (s₁ := Icc 1 (T + 1)) rfl fun j hj =>
    congrArg (fun z : ℂ => conj (b.toFn j) * z) (hterm j hj)
  rw [hleft]
  unfold wienerSourcePairing
  simp only [mul_div_assoc, mul_sum, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  rw [complexWienerRow_eq_sum_horizon ε b (mem_Icc.mp hm).2]
  simp only [map_sum, map_mul, Complex.conj_ofReal, sum_mul]
  exact sum_congr rfl fun j _ => by ring

namespace ActualCofactorLimit

/-- Every complete Wiener source pairing converges along the original common subsequence. -/
theorem wienerSourcePairing_tendsto {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (a b : WienerAlgebraAt (1 / 2)) :
    Tendsto (fun m => wienerSourcePairing ε (L.subsequence m) a b) atTop
      (𝓝 ⟪wienerRepresentation L b (vector L 1),
        wienerRepresentation L a (vector L 1)⟫_ℂ) := by
  simpa only [wienerPairCovariance_eq_source] using wienerPairCovariance_tendsto L a b

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity
