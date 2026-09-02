import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionWeighted

/-!
# Symmetric elementary global Kloosterman collision envelope

Each mixed response average has two unconditional bounds, according to which modulus response is
charged pointwise and which uses its global-period L2 average. Taking their minimum pair by pair
gives a symmetric improvement of the weight-separated collision receiver. Exact interval residue
multiplicities are propagated through both orientations without weakening the minimum.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Minimum of the two elementary pointwise-times-average bounds for one response pair. -/
def kloostermanGlobalResponsePairElementaryBudget
    (q r : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  min
    (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
      (∑ z : ZMod (q + 1),
        Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
      ∑ z : ZMod (r + 1),
        Complex.normSq (kloostermanSourceResidue (r + 1) B b z))
    (((r + 1 : ℕ) : ℝ) ^ 2 * ((q + 1 : ℕ) : ℝ) *
      (∑ z : ZMod (r + 1),
        Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) *
      ∑ z : ZMod (q + 1),
        Complex.normSq (kloostermanSourceResidue (q + 1) B b z))

/-- The mixed response average obeys both orientations of the elementary bound. -/
theorem average_normSq_kloostermanGlobalModulusTimeResponse_mul_le_symmetric
    (Q : Finset ℕ) (q r : ℕ) (hq : q ∈ Q) (hr : r ∈ Q)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
            Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) ≤
      kloostermanGlobalResponsePairElementaryBudget q r B b := by
  unfold kloostermanGlobalResponsePairElementaryBudget
  apply le_min
  · exact average_normSq_kloostermanGlobalModulusTimeResponse_mul_le Q q r hr B b
  · calc
      (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
          ∑ k : ZMod (kloostermanGlobalPeriod Q),
            Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
              Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) =
        (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
          ∑ k : ZMod (kloostermanGlobalPeriod Q),
            Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) *
              Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) := by
        congr 1
        apply Fintype.sum_congr
        intro k
        ring
      _ ≤ _ :=
        average_normSq_kloostermanGlobalModulusTimeResponse_mul_le Q r q hq B b

/-- Exact structural receiver before any response-pair average is estimated. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_weightPairAverage
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ((kloostermanGlobalPeriod Q : ℝ)⁻¹ *
            ∑ k : ZMod (kloostermanGlobalPeriod Q),
              Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
                Complex.normSq
                  (kloostermanGlobalModulusTimeResponse r B b k.val)) := by
  rw [kloostermanGlobalFrequencyCollisionEnergy_eq_average_timeTransform]
  simp_rw [Complex.sq_norm]
  let W : ℝ := kloostermanDistinctModulusWeightPairEnergy Q w
  have hpoint : ∀ k : ZMod (kloostermanGlobalPeriod Q),
      Complex.normSq (kloostermanGlobalCollisionTimeTransform Q w B b k) ≤
        W * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
            Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) :=
    fun k => normSq_kloostermanGlobalCollisionTimeTransform_le_weightPairResponseEnergy
      Q w B b k
  have hsum :
      (∑ k : ZMod (kloostermanGlobalPeriod Q),
        Complex.normSq (kloostermanGlobalCollisionTimeTransform Q w B b k)) ≤
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          W * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
            Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
              Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) :=
    Finset.sum_le_sum fun k _ => hpoint k
  have hreorder :
      (∑ k : ZMod (kloostermanGlobalPeriod Q),
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
            Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val)) =
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ∑ k : ZMod (kloostermanGlobalPeriod Q),
            Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
              Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) := by
    simp_rw [Finset.sum_sigma' Q (fun q => Q.erase q)]
    rw [Finset.sum_comm]
  calc
    (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Complex.normSq (kloostermanGlobalCollisionTimeTransform Q w B b k) ≤
      (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          W * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
            Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
              Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = W * ((kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          ∑ q ∈ Q, ∑ r ∈ Q.erase q,
            Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
              Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val)) := by
      rw [← Finset.mul_sum]
      ring
    _ = W * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ((kloostermanGlobalPeriod Q : ℝ)⁻¹ *
          ∑ k : ZMod (kloostermanGlobalPeriod Q),
            Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
              Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val)) := by
      congr 1
      rw [hreorder]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
    _ = kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ((kloostermanGlobalPeriod Q : ℝ)⁻¹ *
            ∑ k : ZMod (kloostermanGlobalPeriod Q),
              Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
                Complex.normSq
                  (kloostermanGlobalModulusTimeResponse r B b k.val)) := by rfl

/-- Symmetric weight-separated elementary envelope, using the better orientation for every pair. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_weightPair_symmetric
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanGlobalResponsePairElementaryBudget q r B b := by
  calc
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ((kloostermanGlobalPeriod Q : ℝ)⁻¹ *
            ∑ k : ZMod (kloostermanGlobalPeriod Q),
              Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
                Complex.normSq
                  (kloostermanGlobalModulusTimeResponse r B b k.val)) :=
      kloostermanGlobalFrequencyCollisionEnergy_le_weightPairAverage Q w B b
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanGlobalResponsePairElementaryBudget q r B b := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro r hr
        exact average_normSq_kloostermanGlobalModulusTimeResponse_mul_le_symmetric
          Q q r hq (Finset.mem_of_mem_erase hr) B b
      · unfold kloostermanDistinctModulusWeightPairEnergy
        positivity

/-- Literal-interval form of the symmetric elementary response-pair budget. -/
def kloostermanGlobalIntervalResponsePairElementaryBudget
    (q r N : ℕ) (b : ℕ → ℂ) : ℝ :=
  min
    (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
      ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
        ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
      ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
        ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)))
    (((r + 1 : ℕ) : ℝ) ^ 2 * ((q + 1 : ℕ) : ℝ) *
      ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
        ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
      ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
        ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)))

/-- Exact residue multiplicity bounds both orientations of the literal pair budget. -/
theorem kloostermanGlobalResponsePairElementaryBudget_Icc_le_interval
    (q r N : ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalResponsePairElementaryBudget q r (Finset.Icc 1 N) b ≤
      kloostermanGlobalIntervalResponsePairElementaryBudget q r N b := by
  unfold kloostermanGlobalResponsePairElementaryBudget
    kloostermanGlobalIntervalResponsePairElementaryBudget
  have hqEnergy := sum_normSq_kloostermanSourceResidue_Icc_le_interval q N b
  have hrEnergy := sum_normSq_kloostermanSourceResidue_Icc_le_interval r N b
  have hproduct :
      (∑ z : ZMod (q + 1),
          Complex.normSq
            (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) *
        (∑ z : ZMod (r + 1),
          Complex.normSq
            (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) ≤
      ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
          ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
        ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
          ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) :=
    mul_le_mul hqEnergy hrEnergy
      (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _))
  have hproductSwap :
      (∑ z : ZMod (r + 1),
          Complex.normSq
            (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) *
        (∑ z : ZMod (q + 1),
          Complex.normSq
            (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) ≤
      ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
          ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
        ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
          ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) := by
    nlinarith
  apply min_le_min
  · calc
      (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
          (∑ z : ZMod (q + 1),
            Complex.normSq
              (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) *
          ∑ z : ZMod (r + 1),
            Complex.normSq
              (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) =
        (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ)) *
          ((∑ z : ZMod (q + 1),
              Complex.normSq
                (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) *
            ∑ z : ZMod (r + 1),
              Complex.normSq
                (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) := by ring
      _ ≤ (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ)) *
          (((kloostermanIntervalResidueMultiplicity q N : ℝ) *
              ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
            ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
              ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))) :=
        mul_le_mul_of_nonneg_left hproduct
          (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      _ = _ := by ring
  · calc
      (((r + 1 : ℕ) : ℝ) ^ 2 * ((q + 1 : ℕ) : ℝ) *
          (∑ z : ZMod (r + 1),
            Complex.normSq
              (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) *
          ∑ z : ZMod (q + 1),
            Complex.normSq
              (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) =
        (((r + 1 : ℕ) : ℝ) ^ 2 * ((q + 1 : ℕ) : ℝ)) *
          ((∑ z : ZMod (r + 1),
              Complex.normSq
                (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) *
            ∑ z : ZMod (q + 1),
              Complex.normSq
                (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) := by ring
      _ ≤ (((r + 1 : ℕ) : ℝ) ^ 2 * ((q + 1 : ℕ) : ℝ)) *
          (((kloostermanIntervalResidueMultiplicity r N : ℝ) *
              ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
            ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
              ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))) :=
        mul_le_mul_of_nonneg_left hproductSwap
          (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      _ = _ := by ring

/-- Literal-source symmetric weight-separated global collision envelope. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_Icc_le_weightPair_symmetric
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanGlobalIntervalResponsePairElementaryBudget q r N b := by
  calc
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanGlobalResponsePairElementaryBudget q r (Finset.Icc 1 N) b :=
      kloostermanGlobalFrequencyCollisionEnergy_le_weightPair_symmetric
        Q w (Finset.Icc 1 N) b
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanGlobalIntervalResponsePairElementaryBudget q r N b := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro r hr
        exact kloostermanGlobalResponsePairElementaryBudget_Icc_le_interval q r N b
      · unfold kloostermanDistinctModulusWeightPairEnergy
        positivity

end

end RHTower.Sieve
