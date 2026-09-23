import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionWeightIdentity
import GaloisForLFunctions.RHTower.Sieve.DirichletYoung

/-!
# Pair-local Minkowski receiver for global Kloosterman collisions

Finite `ell^(2 : ℕ)` Minkowski is applied to the exact erased-diagonal response Gram before any
modulus-pair Cauchy--Schwarz.  Each weight pair therefore stays beside its own normalized response
pair average.  The resulting elementary receiver is proved no larger than the earlier global
weight-pair-energy product, and exact interval residue multiplicities are retained pair by pair.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Finite complex `ell^(2 : ℕ)` Minkowski for a nested erased-diagonal sum. -/
theorem sqrt_sum_norm_sq_finset_sum_erase_le
    {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (S : Finset ι) (f : ι → ι → κ → ℂ) :
    Real.sqrt (∑ k : κ, ‖∑ i ∈ S, ∑ j ∈ S.erase i, f i j k‖ ^ (2 : ℕ)) ≤
      ∑ i ∈ S, ∑ j ∈ S.erase i,
        Real.sqrt (∑ k : κ, ‖f i j k‖ ^ (2 : ℕ)) := by
  calc
    Real.sqrt (∑ k : κ, ‖∑ i ∈ S, ∑ j ∈ S.erase i, f i j k‖ ^ (2 : ℕ)) ≤
        ∑ i ∈ S, Real.sqrt (∑ k : κ, ‖∑ j ∈ S.erase i, f i j k‖ ^ (2 : ℕ)) :=
      sqrt_sum_norm_sq_finset_sum_le S (fun i k => ∑ j ∈ S.erase i, f i j k)
    _ ≤ ∑ i ∈ S, ∑ j ∈ S.erase i,
        Real.sqrt (∑ k : κ, ‖f i j k‖ ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact sqrt_sum_norm_sq_finset_sum_le (S.erase i) (fun j k => f i j k)

/-- Exact pair-local Minkowski receiver using normalized mixed response averages. -/
def kloostermanGlobalCollisionMinkowskiBudget
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  (∑ q ∈ Q, ∑ r ∈ Q.erase q,
      ‖w q‖ * ‖w r‖ *
        Real.sqrt
          ((kloostermanGlobalPeriod Q : ℝ)⁻¹ *
            ∑ k : ZMod (kloostermanGlobalPeriod Q),
              Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
                Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val))) ^ (2 : ℕ)

/-- Global collision energy is bounded by the exact pair-local Minkowski receiver. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_minkowski
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      kloostermanGlobalCollisionMinkowskiBudget Q w B b := by
  classical
  let P : ℝ := (kloostermanGlobalPeriod Q : ℝ)
  let R : ℕ → ℕ → ℂ := fun q n =>
    kloostermanGlobalModulusTimeResponse q B b n
  let f : ℕ → ℕ → ZMod (kloostermanGlobalPeriod Q) → ℂ := fun q r k =>
    star (w q * R q k.val) * (w r * R r k.val)
  have htransform : ∀ k : ZMod (kloostermanGlobalPeriod Q),
      (∑ q ∈ Q, ∑ r ∈ Q.erase q, f q r k) =
        kloostermanGlobalCollisionTimeTransform Q w B b k := by
    intro k
    dsimp only [f, R]
    exact (kloostermanGlobalCollisionTimeTransform_eq_modulusResponseGram Q w B b k).symm
  have hpair : ∀ q r,
      (∑ k : ZMod (kloostermanGlobalPeriod Q), ‖f q r k‖ ^ (2 : ℕ)) =
        (‖w q‖ * ‖w r‖) ^ (2 : ℕ) *
          ∑ k : ZMod (kloostermanGlobalPeriod Q),
            Complex.normSq (R q k.val) * Complex.normSq (R r k.val) := by
    intro q r
    calc
      (∑ k : ZMod (kloostermanGlobalPeriod Q), ‖f q r k‖ ^ (2 : ℕ)) =
          ∑ k : ZMod (kloostermanGlobalPeriod Q),
            (‖w q‖ * ‖w r‖) ^ (2 : ℕ) *
              (Complex.normSq (R q k.val) * Complex.normSq (R r k.val)) := by
        apply Fintype.sum_congr
        intro k
        dsimp only [f]
        rw [norm_mul, norm_star, norm_mul, norm_mul]
        simp_rw [← Complex.sq_norm]
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hM := sqrt_sum_norm_sq_finset_sum_erase_le Q f
  simp_rw [htransform] at hM
  simp_rw [hpair] at hM
  have hM' :
      Real.sqrt
          (∑ k : ZMod (kloostermanGlobalPeriod Q),
            ‖kloostermanGlobalCollisionTimeTransform Q w B b k‖ ^ (2 : ℕ)) ≤
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ‖w q‖ * ‖w r‖ *
            Real.sqrt
              (∑ k : ZMod (kloostermanGlobalPeriod Q),
                Complex.normSq (R q k.val) * Complex.normSq (R r k.val)) := by
    convert hM using 1
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq]
    positivity
  have hsum_nonneg :
      0 ≤ ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ‖w q‖ * ‖w r‖ *
          Real.sqrt
            (∑ k : ZMod (kloostermanGlobalPeriod Q),
              Complex.normSq (R q k.val) * Complex.normSq (R r k.val)) := by
    positivity
  have htime_nonneg :
      0 ≤ ∑ k : ZMod (kloostermanGlobalPeriod Q),
        ‖kloostermanGlobalCollisionTimeTransform Q w B b k‖ ^ (2 : ℕ) := by
    positivity
  have hsq :
      (∑ k : ZMod (kloostermanGlobalPeriod Q),
        ‖kloostermanGlobalCollisionTimeTransform Q w B b k‖ ^ (2 : ℕ)) ≤
        (∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ‖w q‖ * ‖w r‖ *
            Real.sqrt
              (∑ k : ZMod (kloostermanGlobalPeriod Q),
                Complex.normSq (R q k.val) * Complex.normSq (R r k.val))) ^ (2 : ℕ) := by
    calc
      (∑ k : ZMod (kloostermanGlobalPeriod Q),
          ‖kloostermanGlobalCollisionTimeTransform Q w B b k‖ ^ (2 : ℕ)) =
        Real.sqrt
            (∑ k : ZMod (kloostermanGlobalPeriod Q),
              ‖kloostermanGlobalCollisionTimeTransform Q w B b k‖ ^ (2 : ℕ)) ^ (2 : ℕ) :=
          (Real.sq_sqrt htime_nonneg).symm
      _ ≤ (∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ‖w q‖ * ‖w r‖ *
            Real.sqrt
              (∑ k : ZMod (kloostermanGlobalPeriod Q),
                Complex.normSq (R q k.val) * Complex.normSq (R r k.val))) ^ (2 : ℕ) :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) hsum_nonneg).2 hM'
  have hPinv : 0 ≤ P⁻¹ := by
    dsimp only [P]
    positivity
  rw [kloostermanGlobalFrequencyCollisionEnergy_eq_average_timeTransform]
  unfold kloostermanGlobalCollisionMinkowskiBudget
  calc
    (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        (∑ k : ZMod (kloostermanGlobalPeriod Q),
          ‖kloostermanGlobalCollisionTimeTransform Q w B b k‖ ^ (2 : ℕ)) ≤
      P⁻¹ *
        (∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ‖w q‖ * ‖w r‖ *
            Real.sqrt
              (∑ k : ZMod (kloostermanGlobalPeriod Q),
                Complex.normSq (R q k.val) * Complex.normSq (R r k.val))) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hsq hPinv
    _ = (∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ‖w q‖ * ‖w r‖ *
          Real.sqrt
            (P⁻¹ *
              ∑ k : ZMod (kloostermanGlobalPeriod Q),
                Complex.normSq (R q k.val) * Complex.normSq (R r k.val))) ^ (2 : ℕ) := by
      have hsumscale :
          (∑ q ∈ Q, ∑ r ∈ Q.erase q,
              ‖w q‖ * ‖w r‖ *
                Real.sqrt
                  (P⁻¹ *
                    ∑ k : ZMod (kloostermanGlobalPeriod Q),
                      Complex.normSq (R q k.val) * Complex.normSq (R r k.val))) =
            Real.sqrt P⁻¹ *
              ∑ q ∈ Q, ∑ r ∈ Q.erase q,
                ‖w q‖ * ‖w r‖ *
                  Real.sqrt
                    (∑ k : ZMod (kloostermanGlobalPeriod Q),
                      Complex.normSq (R q k.val) * Complex.normSq (R r k.val)) := by
        simp_rw [Real.sqrt_mul hPinv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      rw [hsumscale, mul_pow, Real.sq_sqrt hPinv]
    _ = _ := by rfl

/-- Pair-local Minkowski receiver after the exact symmetric elementary pair estimate. -/
def kloostermanGlobalCollisionMinkowskiElementaryBudget
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  (∑ q ∈ Q, ∑ r ∈ Q.erase q,
      ‖w q‖ * ‖w r‖ *
        Real.sqrt (kloostermanGlobalResponsePairElementaryBudget q r B b)) ^ (2 : ℕ)

/-- Symmetric elementary collision bound with weights retained pair locally. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_minkowski_elementary
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      kloostermanGlobalCollisionMinkowskiElementaryBudget Q w B b := by
  calc
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
        kloostermanGlobalCollisionMinkowskiBudget Q w B b :=
      kloostermanGlobalFrequencyCollisionEnergy_le_minkowski Q w B b
    _ ≤ kloostermanGlobalCollisionMinkowskiElementaryBudget Q w B b := by
      unfold kloostermanGlobalCollisionMinkowskiBudget
        kloostermanGlobalCollisionMinkowskiElementaryBudget
      apply (sq_le_sq₀ (by positivity) (by positivity)).2
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left
      · apply Real.sqrt_le_sqrt
        exact average_normSq_kloostermanGlobalModulusTimeResponse_mul_le_symmetric
          Q q r hq (Finset.mem_of_mem_erase hr) B b
      · positivity

/-- Pair-local Minkowski is never worse than the global pairwise Cauchy receiver. -/
theorem kloostermanGlobalCollisionMinkowskiElementaryBudget_le_weightPair
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalCollisionMinkowskiElementaryBudget Q w B b ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanGlobalResponsePairElementaryBudget q r B b := by
  classical
  have hbudget : ∀ q r,
      0 ≤ kloostermanGlobalResponsePairElementaryBudget q r B b := by
    intro q r
    unfold kloostermanGlobalResponsePairElementaryBudget
    apply le_min
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _))
        (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _))
        (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
  unfold kloostermanGlobalCollisionMinkowskiElementaryBudget
    kloostermanDistinctModulusWeightPairEnergy
  rw [Finset.sum_sigma' Q (fun q => Q.erase q)
      (fun q r => ‖w q‖ * ‖w r‖ *
        Real.sqrt (kloostermanGlobalResponsePairElementaryBudget q r B b))]
  rw [Finset.sum_sigma' Q (fun q => Q.erase q)
      (fun q r => ‖w q‖ ^ (2 : ℕ) * ‖w r‖ ^ (2 : ℕ))]
  rw [Finset.sum_sigma' Q (fun q => Q.erase q)
      (fun q r => kloostermanGlobalResponsePairElementaryBudget q r B b)]
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Q.sigma fun q => Q.erase q)
    (fun p => ‖w p.1‖ * ‖w p.2‖)
    (fun p => Real.sqrt
      (kloostermanGlobalResponsePairElementaryBudget p.1 p.2 B b))
  simpa only [mul_pow, Real.sq_sqrt (hbudget _ _)] using h

/-- Literal-interval pair-local Minkowski elementary receiver. -/
def kloostermanGlobalCollisionMinkowskiIntervalElementaryBudget
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) : ℝ :=
  (∑ q ∈ Q, ∑ r ∈ Q.erase q,
      ‖w q‖ * ‖w r‖ *
        Real.sqrt (kloostermanGlobalIntervalResponsePairElementaryBudget q r N b)) ^ (2 : ℕ)

/-- Literal-source symmetric elementary collision bound with pair-local weights. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_Icc_le_minkowski_elementary
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
      kloostermanGlobalCollisionMinkowskiIntervalElementaryBudget Q w N b := by
  calc
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
        kloostermanGlobalCollisionMinkowskiElementaryBudget Q w (Finset.Icc 1 N) b :=
      kloostermanGlobalFrequencyCollisionEnergy_le_minkowski_elementary
        Q w (Finset.Icc 1 N) b
    _ ≤ kloostermanGlobalCollisionMinkowskiIntervalElementaryBudget Q w N b := by
      unfold kloostermanGlobalCollisionMinkowskiElementaryBudget
        kloostermanGlobalCollisionMinkowskiIntervalElementaryBudget
      apply (sq_le_sq₀ (by positivity) (by positivity)).2
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left
      · apply Real.sqrt_le_sqrt
        exact kloostermanGlobalResponsePairElementaryBudget_Icc_le_interval q r N b
      · positivity

end

end RHTower.Sieve
