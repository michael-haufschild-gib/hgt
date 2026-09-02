import GaloisForLFunctions.RHTower.Sieve.KloostermanCrossPhaseGeometric

/-!
# Geometric cancellation in terminal Kloosterman correlations

An unequal-modulus Kloosterman terminal block is expanded coefficient-faithfully into cross-unit
phase orbits. Every orbit has the nontrivial ratio proved in the preceding module, so its partial
sum has a bound independent of terminal length. Combining this with the exact-length cardinality
bound gives an unconditional hybrid minimum estimate. This is genuine finite phase cancellation,
not the still-missing collective spectral modulus average.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Physical-index-independent coefficient of one cross-unit phase orbit. -/
def kloostermanCrossPhaseCoefficient
    (q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) : ℂ :=
  star (ZMod.stdAddChar
      (n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) *
    ZMod.stdAddChar
      (k * ((y⁻¹ : (ZMod r)ˣ) : ZMod r))

@[simp] theorem norm_kloostermanCrossPhaseCoefficient
    (q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    ‖kloostermanCrossPhaseCoefficient q r n k x y‖ = 1 := by
  simp [kloostermanCrossPhaseCoefficient]

/-- One physical cross-column value is the sum of its cross-unit geometric phases. -/
theorem kloostermanNaturalCrossColumnProductTerm_eq_phaseSum
    (q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) (m : ℕ) :
    kloostermanNaturalCrossColumnProductTerm q r n k m =
      ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        kloostermanCrossPhaseCoefficient q r n k x y *
          (kloostermanCrossPhaseRatio q r x y) ^ m := by
  unfold kloostermanNaturalCrossColumnProductTerm kloostermanSum
  change (starRingEnd ℂ) (∑ x : (ZMod q)ˣ,
      kloostermanPhase q (m : ZMod q) n x) *
      (∑ y : (ZMod r)ˣ, kloostermanPhase r (m : ZMod r) k y) = _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  unfold kloostermanPhase kloostermanCrossPhaseCoefficient
    kloostermanCrossPhaseRatio
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, map_mul]
  rw [show (m : ZMod q) * (x : ZMod q) = m • (x : ZMod q) by
    simp [nsmul_eq_mul],
    show (m : ZMod r) * (y : ZMod r) = m • (y : ZMod r) by
    simp [nsmul_eq_mul],
    stdAddChar_nsmul_eq_pow, stdAddChar_nsmul_eq_pow]
  rw [map_pow]
  rw [show star (ZMod.stdAddChar
      (n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      (starRingEnd ℂ) (ZMod.stdAddChar
        (n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) by rfl,
    show star (ZMod.stdAddChar (x : ZMod q)) =
      (starRingEnd ℂ) (ZMod.stdAddChar (x : ZMod q)) by rfl]
  ring

/-- Exact orbit expansion of the literal terminal common-period block. -/
theorem kloostermanNaturalCrossIntervalTerminalBlock_eq_phaseOrbits
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalCrossIntervalTerminalBlock M q r n k =
      ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        kloostermanCrossPhaseCoefficient q r n k x y *
          ∑ i ∈ Finset.range (M % Nat.lcm q r),
            (kloostermanCrossPhaseRatio q r x y) ^ (i + 1) := by
  unfold kloostermanNaturalCrossIntervalTerminalBlock
  simp_rw [kloostermanNaturalCrossColumnProductTerm_eq_phaseSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.mul_sum]

/-- Terminal block bound from cross-unit geometric cancellation, independent of block length. -/
theorem norm_kloostermanNaturalCrossIntervalTerminalBlock_le_geometric
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalTerminalBlock M q r n k‖ ≤
      ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖ := by
  rw [kloostermanNaturalCrossIntervalTerminalBlock_eq_phaseOrbits]
  calc
    ‖∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        kloostermanCrossPhaseCoefficient q r n k x y *
          ∑ i ∈ Finset.range (M % Nat.lcm q r),
            (kloostermanCrossPhaseRatio q r x y) ^ (i + 1)‖ ≤
        ∑ x : (ZMod q)ˣ, ‖∑ y : (ZMod r)ˣ,
          kloostermanCrossPhaseCoefficient q r n k x y *
            ∑ i ∈ Finset.range (M % Nat.lcm q r),
              (kloostermanCrossPhaseRatio q r x y) ^ (i + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        ‖kloostermanCrossPhaseCoefficient q r n k x y *
          ∑ i ∈ Finset.range (M % Nat.lcm q r),
            (kloostermanCrossPhaseRatio q r x y) ^ (i + 1)‖ := by
      apply Finset.sum_le_sum
      intro x hx
      exact norm_sum_le _ _
    _ = ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        ‖∑ i ∈ Finset.range (M % Nat.lcm q r),
          (kloostermanCrossPhaseRatio q r x y) ^ (i + 1)‖ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [norm_mul, norm_kloostermanCrossPhaseCoefficient, one_mul]
    _ ≤ ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖ := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      rw [show (∑ i ∈ Finset.range (M % Nat.lcm q r),
          (kloostermanCrossPhaseRatio q r x y) ^ (i + 1)) =
          kloostermanCrossPhaseRatio q r x y *
            ∑ i ∈ Finset.range (M % Nat.lcm q r),
              (kloostermanCrossPhaseRatio q r x y) ^ i by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ']]
      rw [norm_mul, norm_kloostermanCrossPhaseRatio, one_mul]
      exact norm_sum_range_kloostermanCrossPhaseRatio_pow_le
        (M % Nat.lcm q r) q r hqr x y

/-- Best unconditional terminal estimate: exact-length cardinality versus geometric cancellation. -/
theorem norm_kloostermanNaturalCrossIntervalTerminalBlock_le_min
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalTerminalBlock M q r n k‖ ≤
      min
        (((M % Nat.lcm q r : ℕ) : ℝ) * Nat.totient q * Nat.totient r)
        (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
          2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) := by
  exact le_min
    (norm_kloostermanNaturalCrossIntervalTerminalBlock_le M q r n k)
    (norm_kloostermanNaturalCrossIntervalTerminalBlock_le_geometric
      M q r hqr n k)

/-- Stored-index unequal-modulus Gram correlation with the same hybrid terminal bound. -/
theorem norm_kloostermanCrossModulusCorrelation_Icc_le_terminal_min
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
      min
        (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
          Nat.totient (q + 1) * Nat.totient (r + 1))
        (∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
          2 / ‖1 - kloostermanCrossPhaseRatio (q + 1) (r + 1) x y‖) := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_terminalBlock_of_ne
    M q r hqr n k]
  exact norm_kloostermanNaturalCrossIntervalTerminalBlock_le_min
    M (q + 1) (r + 1) (Nat.succ_ne_succ_iff.mpr hqr) (Int.cast n) (Int.cast k)

end

end RHTower.Sieve
