import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionInterval

/-!
# Weight-separated global Kloosterman collision envelope

Finite Cauchy--Schwarz can separate the signed modulus weights from the complete-response Gram
terms before averaging over the global period.  This replaces the raw ordered-pair cardinality
factor by the exact squared L2 energy of ordered unequal-modulus weight pairs.  The general and
literal-source results remain unconditional and expose every response/source scale explicitly.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem norm_dependent_sum_mul_sq_le_sq_mul_sq_global
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (D : α → Finset β)
    (a s : α → β → ℂ) :
    ‖∑ i ∈ A, ∑ j ∈ D i, a i j * s i j‖ ^ 2 ≤
      (∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ ^ 2) *
        ∑ i ∈ A, ∑ j ∈ D i, ‖s i j‖ ^ 2 := by
  have htri :
      ‖∑ i ∈ A, ∑ j ∈ D i, a i j * s i j‖ ≤
        ∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ * ‖s i j‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro i hi
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul]
  have hsum0 : 0 ≤ ∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ * ‖s i j‖ := by
    positivity
  calc
    ‖∑ i ∈ A, ∑ j ∈ D i, a i j * s i j‖ ^ 2 ≤
        (∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ * ‖s i j‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ i ∈ A, ∑ j ∈ D i, a i j * s i j)]
    _ ≤ (∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ ^ 2) *
        ∑ i ∈ A, ∑ j ∈ D i, ‖s i j‖ ^ 2 := by
      rw [Finset.sum_sigma' A D (fun i j => ‖a i j‖ * ‖s i j‖)]
      rw [Finset.sum_sigma' A D (fun i j => ‖a i j‖ ^ 2)]
      rw [Finset.sum_sigma' A D (fun i j => ‖s i j‖ ^ 2)]
      exact Finset.sum_mul_sq_le_sq_mul_sq (A.sigma D)
        (fun p => ‖a p.1 p.2‖) (fun p => ‖s p.1 p.2‖)

/-- Pointwise global collision time energy separates into exact modulus-weight pair energy and
unweighted response-pair energy. -/
theorem normSq_kloostermanGlobalCollisionTimeTransform_le_weightPairResponseEnergy
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (k : ZMod (kloostermanGlobalPeriod Q)) :
    Complex.normSq (kloostermanGlobalCollisionTimeTransform Q w B b k) ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
            Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) := by
  rw [kloostermanGlobalCollisionTimeTransform_eq_modulusResponseGram]
  rw [← Complex.sq_norm]
  calc
    ‖∑ q ∈ Q, ∑ r ∈ Q.erase q,
        star (w q * kloostermanGlobalModulusTimeResponse q B b k.val) *
          (w r * kloostermanGlobalModulusTimeResponse r B b k.val)‖ ^ 2 =
      ‖∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (star (w q) * w r) *
          (star (kloostermanGlobalModulusTimeResponse q B b k.val) *
            kloostermanGlobalModulusTimeResponse r B b k.val)‖ ^ 2 := by
      congr 2
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      rw [star_mul]
      ring
    _ ≤ (∑ q ∈ Q, ∑ r ∈ Q.erase q, ‖star (w q) * w r‖ ^ 2) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ‖star (kloostermanGlobalModulusTimeResponse q B b k.val) *
            kloostermanGlobalModulusTimeResponse r B b k.val‖ ^ 2 :=
      norm_dependent_sum_mul_sq_le_sq_mul_sq_global Q (fun q => Q.erase q)
        (fun q r => star (w q) * w r)
        (fun q r => star (kloostermanGlobalModulusTimeResponse q B b k.val) *
          kloostermanGlobalModulusTimeResponse r B b k.val)
    _ = kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
            Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) := by
      unfold kloostermanDistinctModulusWeightPairEnergy
      simp only [norm_mul, norm_star, mul_pow, Complex.sq_norm]

/-- Weight-separated unconditional elementary envelope for global collision energy. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_weightPair
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
            (∑ z : ZMod (q + 1),
              Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
            ∑ z : ZMod (r + 1),
              Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) := by
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
    _ ≤ W * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
          (∑ z : ZMod (q + 1),
            Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
          ∑ z : ZMod (r + 1),
            Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro r hr
        exact average_normSq_kloostermanGlobalModulusTimeResponse_mul_le
          Q q r (Finset.mem_of_mem_erase hr) B b
      · unfold W kloostermanDistinctModulusWeightPairEnergy
        positivity
    _ = kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
            (∑ z : ZMod (q + 1),
              Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
            ∑ z : ZMod (r + 1),
              Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) := by rfl

/-- Literal-source form of the weight-separated elementary global collision envelope. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_Icc_le_weightPair
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
            ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
              ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
            ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
              ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))) := by
  calc
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
            (∑ z : ZMod (q + 1),
              Complex.normSq
                (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) *
            ∑ z : ZMod (r + 1),
              Complex.normSq
                (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) :=
      kloostermanGlobalFrequencyCollisionEnergy_le_weightPair
        Q w (Finset.Icc 1 N) b
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
            ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
              ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
            ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
              ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro r hr
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
        calc
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
          _ = (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
              ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
              ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))) := by ring
      · unfold kloostermanDistinctModulusWeightPairEnergy
        positivity

end

end RHTower.Sieve
