import GaloisForLFunctions.RHTower.SoninCoupledPrimeArchGramTransfer
import GaloisForLFunctions.RHTower.PrimeArchBernsteinPurityDivergence

/-!
# Coupled-Sonin Bernstein collar comparison

This file compares the endpoint prime--Gamma Bernstein energy with the Bernstein energy of the
actual normalized coupled-Sonin replica sequence.  The comparison is two-sided: the collar
estimate is equivalent to subexponential growth of one concrete spectral-source mismatch, once
the standard Hausdorff positivity of the normalized density-operator moments is supplied.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Squared Hilbert distance between two complete degree-`n` Bernstein coefficient packets. -/
def bernsteinCoefficientSquareDiscrepancy
    (m a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (bernsteinCoefficient m n i - bernsteinCoefficient a n i) ^ 2

theorem bernsteinCoefficientSquareDiscrepancy_nonneg
    (m a : ℕ → ℝ) (n : ℕ) :
    0 ≤ bernsteinCoefficientSquareDiscrepancy m a n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- One half of the exact Hilbert-space comparison: target energy is controlled by source energy
and squared packet mismatch. -/
theorem bernsteinCoefficientPurity_le_two_discrepancy_add_two_purity
    (m a : ℕ → ℝ) (n : ℕ) :
    bernsteinCoefficientPurity m n ≤
      2 * bernsteinCoefficientSquareDiscrepancy m a n +
        2 * bernsteinCoefficientPurity a n := by
  have hpoint (i : ℕ) :
      bernsteinCoefficient m n i ^ 2 ≤
        2 * (bernsteinCoefficient m n i - bernsteinCoefficient a n i) ^ 2 +
          2 * bernsteinCoefficient a n i ^ 2 := by
    nlinarith [sq_nonneg (bernsteinCoefficient m n i -
      2 * bernsteinCoefficient a n i)]
  rw [bernsteinCoefficientPurity, bernsteinCoefficientSquareDiscrepancy,
    bernsteinCoefficientPurity]
  calc
    (∑ i ∈ Finset.range (n + 1), bernsteinCoefficient m n i ^ 2) ≤
        ∑ i ∈ Finset.range (n + 1),
          (2 * (bernsteinCoefficient m n i - bernsteinCoefficient a n i) ^ 2 +
            2 * bernsteinCoefficient a n i ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 2 * ∑ i ∈ Finset.range (n + 1),
          (bernsteinCoefficient m n i - bernsteinCoefficient a n i) ^ 2 +
        2 * ∑ i ∈ Finset.range (n + 1), bernsteinCoefficient a n i ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The reverse Hilbert-space comparison: squared packet mismatch is controlled by the two
coefficient energies. -/
theorem bernsteinCoefficientSquareDiscrepancy_le_two_purities
    (m a : ℕ → ℝ) (n : ℕ) :
    bernsteinCoefficientSquareDiscrepancy m a n ≤
      2 * bernsteinCoefficientPurity m n +
        2 * bernsteinCoefficientPurity a n := by
  have hpoint (i : ℕ) :
      (bernsteinCoefficient m n i - bernsteinCoefficient a n i) ^ 2 ≤
        2 * bernsteinCoefficient m n i ^ 2 +
          2 * bernsteinCoefficient a n i ^ 2 := by
    nlinarith [sq_nonneg (bernsteinCoefficient m n i + bernsteinCoefficient a n i)]
  rw [bernsteinCoefficientSquareDiscrepancy, bernsteinCoefficientPurity,
    bernsteinCoefficientPurity]
  calc
    (∑ i ∈ Finset.range (n + 1),
        (bernsteinCoefficient m n i - bernsteinCoefficient a n i) ^ 2) ≤
      ∑ i ∈ Finset.range (n + 1),
        (2 * bernsteinCoefficient m n i ^ 2 +
          2 * bernsteinCoefficient a n i ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 2 * ∑ i ∈ Finset.range (n + 1), bernsteinCoefficient m n i ^ 2 +
        2 * ∑ i ∈ Finset.range (n + 1), bernsteinCoefficient a n i ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- A Hausdorff-positive comparison source replaces its whole Bernstein energy by its exact
mass-squared ceiling in the forward comparison. -/
theorem bernsteinCoefficientPurity_le_two_discrepancy_add_two_mass_sq
    (m a : ℕ → ℝ) (n : ℕ) (ha : HausdorffBernsteinNonnegative a) :
    bernsteinCoefficientPurity m n ≤
      2 * bernsteinCoefficientSquareDiscrepancy m a n + 2 * a 0 ^ 2 := by
  exact (bernsteinCoefficientPurity_le_two_discrepancy_add_two_purity m a n).trans
    (add_le_add_left
      (mul_le_mul_of_nonneg_left
        (bernsteinCoefficientPurity_le_mass_sq_of_hausdorffBernsteinNonnegative ha n)
        (by norm_num)) _)

/-- The same mass ceiling gives the reverse comparison. -/
theorem bernsteinCoefficientSquareDiscrepancy_le_two_purity_add_two_mass_sq
    (m a : ℕ → ℝ) (n : ℕ) (ha : HausdorffBernsteinNonnegative a) :
    bernsteinCoefficientSquareDiscrepancy m a n ≤
      2 * bernsteinCoefficientPurity m n + 2 * a 0 ^ 2 := by
  exact (bernsteinCoefficientSquareDiscrepancy_le_two_purities m a n).trans
    (add_le_add_left
      (mul_le_mul_of_nonneg_left
        (bernsteinCoefficientPurity_le_mass_sq_of_hausdorffBernsteinNonnegative ha n)
        (by norm_num)) _)

/-- The normalized replica source has mass one at every nondegenerate coupled aperture. -/
theorem soninAllPrimeCoupledRenyiReplicaMoment_zero_eq_one
    (a : SoninCoupledNondegenerateAperture) :
    soninAllPrimeCoupledRenyiReplicaMoment a.1 0 = 1 := by
  have hmass : 0 < (soninAllPrimeCoupledTraceMoment a.1 0).re :=
    (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero a.1).2 a.2
  simp [soninAllPrimeCoupledRenyiReplicaMoment, hmass.ne']

/-- The concrete degree-`n` Bernstein mismatch between the endpoint source and the actual
normalized coupled-Sonin spectral source. -/
def soninCoupledEndpointBernsteinMismatch
    (a : SoninCoupledNondegenerateAperture) (n : ℕ) : ℝ :=
  bernsteinCoefficientSquareDiscrepancy
    (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment)
    (soninAllPrimeCoupledRenyiReplicaMoment a.1) n

theorem soninCoupledEndpointBernsteinMismatch_nonneg
    (a : SoninCoupledNondegenerateAperture) (n : ℕ) :
    0 ≤ soninCoupledEndpointBernsteinMismatch a n :=
  bernsteinCoefficientSquareDiscrepancy_nonneg _ _ _

/-- **Forward actual-source comparison.**  Full Hausdorff positivity of the coupled replica
sequence turns the endpoint purity into at most twice the concrete mismatch plus two. -/
theorem primeArchEndpointBernsteinPurity_le_two_add_two_soninCoupledMismatch
    (a : SoninCoupledNondegenerateAperture)
    (ha : HausdorffBernsteinNonnegative
      (soninAllPrimeCoupledRenyiReplicaMoment a.1)) (n : ℕ) :
    primeArchEndpointBernsteinPurity n ≤
      2 + 2 * soninCoupledEndpointBernsteinMismatch a n := by
  have h := bernsteinCoefficientPurity_le_two_discrepancy_add_two_mass_sq
    (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment)
    (soninAllPrimeCoupledRenyiReplicaMoment a.1) n ha
  rw [soninAllPrimeCoupledRenyiReplicaMoment_zero_eq_one a] at h
  change primeArchEndpointBernsteinPurity n ≤ _ at h
  simpa only [soninCoupledEndpointBernsteinMismatch, one_pow, mul_one, add_comm] using h

/-- **Reverse actual-source comparison.**  The same source law bounds the concrete mismatch by
twice the endpoint purity plus two. -/
theorem soninCoupledEndpointBernsteinMismatch_le_two_add_two_primeArchEndpointPurity
    (a : SoninCoupledNondegenerateAperture)
    (ha : HausdorffBernsteinNonnegative
      (soninAllPrimeCoupledRenyiReplicaMoment a.1)) (n : ℕ) :
    soninCoupledEndpointBernsteinMismatch a n ≤
      2 + 2 * primeArchEndpointBernsteinPurity n := by
  have h := bernsteinCoefficientSquareDiscrepancy_le_two_purity_add_two_mass_sq
    (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment)
    (soninAllPrimeCoupledRenyiReplicaMoment a.1) n ha
  rw [soninAllPrimeCoupledRenyiReplicaMoment_zero_eq_one a] at h
  change soninCoupledEndpointBernsteinMismatch a n ≤ _ at h
  simpa only [one_pow, mul_one, add_comm] using h

/-- The direct `C_ε(1+ε)^n` formulation of zero exponential growth. -/
def UnitCollarExponentialEnvelope (E : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, E n ≤ C * (1 + ε) ^ n

/-- Additive-multiplicative two-sided comparison preserves every arbitrarily thin exponential
envelope. -/
theorem unitCollarExponentialEnvelope_iff_of_twoSidedComparison
    {E D : ℕ → ℝ}
    (hED : ∀ n, E n ≤ 2 + 2 * D n)
    (hDE : ∀ n, D n ≤ 2 + 2 * E n) :
    UnitCollarExponentialEnvelope E ↔ UnitCollarExponentialEnvelope D := by
  constructor
  · intro hE ε hε
    obtain ⟨C, hC, hEC⟩ := hE ε hε
    refine ⟨2 + 2 * C, by linarith, fun n => ?_⟩
    have hpow : 1 ≤ (1 + ε) ^ n := one_le_pow₀ (by linarith)
    calc
      D n ≤ 2 + 2 * E n := hDE n
      _ ≤ 2 + 2 * (C * (1 + ε) ^ n) := by nlinarith [hEC n]
      _ ≤ (2 + 2 * C) * (1 + ε) ^ n := by nlinarith
  · intro hD ε hε
    obtain ⟨C, hC, hDC⟩ := hD ε hε
    refine ⟨2 + 2 * C, by linarith, fun n => ?_⟩
    have hpow : 1 ≤ (1 + ε) ^ n := one_le_pow₀ (by linarith)
    calc
      E n ≤ 2 + 2 * D n := hED n
      _ ≤ 2 + 2 * (C * (1 + ε) ^ n) := by nlinarith [hDC n]
      _ ≤ (2 + 2 * C) * (1 + ε) ^ n := by nlinarith

/-- **Coupled-Sonin collar equivalence.**  Once the actual normalized coupled source is proved
Hausdorff-positive, the boxed endpoint estimate is equivalent—not merely implied by—the same
estimate for the concrete coupled-Sonin Bernstein mismatch. -/
theorem primeArchEndpoint_unitCollarEnvelope_iff_soninCoupledMismatch
    (a : SoninCoupledNondegenerateAperture)
    (ha : HausdorffBernsteinNonnegative
      (soninAllPrimeCoupledRenyiReplicaMoment a.1)) :
    UnitCollarExponentialEnvelope primeArchEndpointBernsteinPurity ↔
      UnitCollarExponentialEnvelope (soninCoupledEndpointBernsteinMismatch a) :=
  unitCollarExponentialEnvelope_iff_of_twoSidedComparison
    (primeArchEndpointBernsteinPurity_le_two_add_two_soninCoupledMismatch a ha)
    (soninCoupledEndpointBernsteinMismatch_le_two_add_two_primeArchEndpointPurity a ha)

end

end RHTower
