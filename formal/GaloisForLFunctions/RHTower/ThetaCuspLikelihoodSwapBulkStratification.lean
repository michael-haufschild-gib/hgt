import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodNormalCrossingPrimeFace

/-!
# Swap-invariant theta-likelihood bulk and arithmetic corner stratification

The two legs of a Wigner pair have independent intrinsic likelihood temperatures.  The natural
source operation is therefore not to identify the temperatures, but to add the two leg orders.
This file proves that the resulting swap-invariant shell is an exact bulk extension of the paired
normal-crossing face and retains every composite factor pair.

At the zero-temperature corner, its real mass vanishes exactly on prime shells and is strictly
positive on composite shells.  On prime shells, the complete swap-invariant phase factors through
one positive scalar throughout the closed nonnegative temperature quadrant away from the corner.
Consequently the strict upper-half-plane arithmetic current transports from both faces through the
full positive two-temperature interior.  The same statement holds for literal theta-source traces.

All statements are exact and unconditional.
-/

open Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Leg-exchange invariant two-temperature likelihood shell.  Both orders are retained, so this
definition contains every factor pair on composite shells. -/
def thetaCuspLikelihoodSwapMassShellPhase
    (k : ℕ) (B D : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) D +
        thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) D *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B : ℝ) : ℂ) *
      Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Spectral derivative of the swap-invariant two-temperature shell. -/
def thetaCuspLikelihoodSwapMassShellPhaseDerivative
    (k : ℕ) (B D : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) D +
        thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) D *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B : ℝ) : ℂ) *
      (Complex.I * (thetaFactorPairLogDisplacement q : ℂ)) *
        Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Real mass of the ray--ray likelihood shell at the normal-crossing corner. -/
def thetaCuspLikelihoodRayBoundaryCornerMass (k : ℕ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaCuspLikelihoodRayWeight (q.1 + 1) *
      thetaCuspLikelihoodRayWeight (q.2 + 1)

/-- Positive scalar multiplying a prime shell after the two temperature orders are added. -/
def thetaCuspLikelihoodPrimeSwapScale (k : ℕ) (B D : ℝ) : ℝ :=
  B * thetaCuspLikelihoodScaledBoundaryTerm k D +
    D * thetaCuspLikelihoodScaledBoundaryTerm k B

/-- Literal theta-source shell with both orders of its two source legs. -/
def thetaCuspSourceSwapMassShellPhase
    (k : ℕ) (x y : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspSourceTerm x (q.1 + 1) * thetaCuspSourceTerm y (q.2 + 1) +
        thetaCuspSourceTerm y (q.1 + 1) * thetaCuspSourceTerm x (q.2 + 1) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Spectral derivative of the literal swap-invariant theta-source shell. -/
def thetaCuspSourceSwapMassShellPhaseDerivative
    (k : ℕ) (x y : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspSourceTerm x (q.1 + 1) * thetaCuspSourceTerm y (q.2 + 1) +
        thetaCuspSourceTerm y (q.1 + 1) * thetaCuspSourceTerm x (q.2 + 1) : ℝ) : ℂ) *
      (Complex.I * (thetaFactorPairLogDisplacement q : ℂ)) *
        Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Ray weights are nonnegative on every positive arithmetic index. -/
theorem thetaCuspLikelihoodRayWeight_nonneg_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ thetaCuspLikelihoodRayWeight n := by
  rcases eq_or_lt_of_le hn with rfl | hn
  · simp [thetaCuspLikelihoodRayWeight, thetaCuspLikelihoodGap]
  · exact (thetaCuspLikelihoodRayWeight_pos (by omega)).le

/-- Every higher scaled channel is positive on the closed nonnegative temperature ray, including
the zero-temperature endpoint. -/
theorem thetaCuspLikelihoodScaledBoundaryTerm_pos_of_nonneg
    {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 0 ≤ B) :
    0 < thetaCuspLikelihoodScaledBoundaryTerm n B := by
  have hAtom := thetaCuspLikelihoodAtomWeight_pos
    (n := n) (lt_of_lt_of_le (by omega) hn)
  have hRay := thetaCuspLikelihoodRayWeight_pos hn
  unfold thetaCuspLikelihoodScaledBoundaryTerm
  exact mul_pos (Real.exp_pos _)
    (add_pos_of_nonneg_of_pos (mul_nonneg hB hAtom.le) hRay)

/-- Restricting the swap-invariant bulk to either coordinate face gives exactly the paired face
already used by the normal-crossing theorem. -/
theorem thetaCuspLikelihoodSwapMassShellPhase_boundary
    (k : ℕ) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhase k B 0 z =
      thetaCuspLikelihoodTwoFaceMassShellPhase k B z := by
  rfl

/-- Derivative form of the exact boundary restriction. -/
theorem thetaCuspLikelihoodSwapMassShellPhaseDerivative_boundary
    (k : ℕ) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhaseDerivative k B 0 z =
      thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative k B z := by
  rfl

/-- At the normal-crossing corner, the complete swap bulk is twice the full ray--ray shell. -/
theorem thetaCuspLikelihoodSwapMassShellPhase_corner
    (k : ℕ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhase k 0 0 z =
      2 * thetaCuspLikelihoodRayBoundaryMassShellPhase k z := by
  unfold thetaCuspLikelihoodSwapMassShellPhase
    thetaCuspLikelihoodRayBoundaryMassShellPhase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [thetaCuspLikelihoodScaledBoundaryTerm_zero]
  push_cast
  ring

/-- The derivative corner is twice the differentiated ray--ray shell. -/
theorem thetaCuspLikelihoodSwapMassShellPhaseDerivative_corner
    (k : ℕ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhaseDerivative k 0 0 z =
      2 * thetaCuspLikelihoodRayBoundaryMassShellPhaseDerivative k z := by
  unfold thetaCuspLikelihoodSwapMassShellPhaseDerivative
    thetaCuspLikelihoodRayBoundaryMassShellPhaseDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [thetaCuspLikelihoodScaledBoundaryTerm_zero]
  push_cast
  ring

/-- Evaluation of the ray--ray shell at spectral zero is its real corner mass. -/
theorem thetaCuspLikelihoodRayBoundaryMassShellPhase_zero_eq_cornerMass
    (k : ℕ) :
    thetaCuspLikelihoodRayBoundaryMassShellPhase k 0 =
      (thetaCuspLikelihoodRayBoundaryCornerMass k : ℂ) := by
  unfold thetaCuspLikelihoodRayBoundaryMassShellPhase
    thetaCuspLikelihoodRayBoundaryCornerMass
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  simp

/-- The swap corner at spectral zero is twice the real arithmetic corner mass. -/
theorem thetaCuspLikelihoodSwapMassShellPhase_corner_zero_eq_mass
    (k : ℕ) :
    thetaCuspLikelihoodSwapMassShellPhase k 0 0 0 =
      ((2 * thetaCuspLikelihoodRayBoundaryCornerMass k : ℝ) : ℂ) := by
  rw [thetaCuspLikelihoodSwapMassShellPhase_corner,
    thetaCuspLikelihoodRayBoundaryMassShellPhase_zero_eq_cornerMass]
  push_cast
  ring

/-- Every arithmetic corner mass is nonnegative. -/
theorem thetaCuspLikelihoodRayBoundaryCornerMass_nonneg (k : ℕ) :
    0 ≤ thetaCuspLikelihoodRayBoundaryCornerMass k := by
  unfold thetaCuspLikelihoodRayBoundaryCornerMass
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg
    (thetaCuspLikelihoodRayWeight_nonneg_of_one_le (by omega))
    (thetaCuspLikelihoodRayWeight_nonneg_of_one_le (by omega))

/-- Prime shells have zero corner mass because every factorization contains the ground index. -/
theorem thetaCuspLikelihoodRayBoundaryCornerMass_eq_zero_of_prime
    {k : ℕ} (hk : k.Prime) :
    thetaCuspLikelihoodRayBoundaryCornerMass k = 0 := by
  unfold thetaCuspLikelihoodRayBoundaryCornerMass
  apply Finset.sum_eq_zero
  intro q hq
  exact thetaCuspLikelihoodRayWeight_pair_mul_eq_zero_of_prime hk hq

/-- Every nonprime shell above one has a strictly positive ray--ray corner mass. -/
theorem thetaCuspLikelihoodRayBoundaryCornerMass_pos_of_not_prime
    {k : ℕ} (hk : 1 < k) (hnp : ¬ k.Prime) :
    0 < thetaCuspLikelihoodRayBoundaryCornerMass k := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hnp
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp at hab
    omega
  have ha1 : a ≠ 1 := by
    intro h
    subst a
    simp at hab
    omega
  have hb0 : b ≠ 0 := by
    intro h
    subst b
    simp at hab
    omega
  have hb1 : b ≠ 1 := by
    intro h
    subst b
    simp at hab
    omega
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  let q : ℕ × ℕ := (a - 1, b - 1)
  have hq1 : q.1 + 1 = a := by
    dsimp [q]
    omega
  have hq2 : q.2 + 1 = b := by
    dsimp [q]
    omega
  have hq : q ∈ thetaPositiveFactorPairs k := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_range.mpr
        dsimp [q]
        omega
      · apply Finset.mem_range.mpr
        dsimp [q]
        omega
    · rw [hq1, hq2, hab]
  unfold thetaCuspLikelihoodRayBoundaryCornerMass
  apply (Finset.sum_pos_iff_of_nonneg (fun r hr =>
    mul_nonneg
      (thetaCuspLikelihoodRayWeight_nonneg_of_one_le (by omega))
      (thetaCuspLikelihoodRayWeight_nonneg_of_one_le (by omega)))).2
  refine ⟨q, hq, ?_⟩
  rw [hq1, hq2]
  exact mul_pos (thetaCuspLikelihoodRayWeight_pos ha2)
    (thetaCuspLikelihoodRayWeight_pos hb2)

/-- **Arithmetic normal-crossing classifier.**  Above the unit shell, zero ray--ray corner mass
is equivalent to primality. -/
theorem thetaCuspLikelihoodRayBoundaryCornerMass_eq_zero_iff_prime
    {k : ℕ} (hk : 1 < k) :
    thetaCuspLikelihoodRayBoundaryCornerMass k = 0 ↔ k.Prime := by
  constructor
  · intro hzero
    by_contra hnp
    have hpos := thetaCuspLikelihoodRayBoundaryCornerMass_pos_of_not_prime hk hnp
    linarith
  · exact thetaCuspLikelihoodRayBoundaryCornerMass_eq_zero_of_prime

/-- Equivalently, strict positive corner mass detects precisely the composite shells above one. -/
theorem thetaCuspLikelihoodRayBoundaryCornerMass_pos_iff_not_prime
    {k : ℕ} (hk : 1 < k) :
    0 < thetaCuspLikelihoodRayBoundaryCornerMass k ↔ ¬ k.Prime := by
  constructor
  · intro hpos hp
    rw [thetaCuspLikelihoodRayBoundaryCornerMass_eq_zero_of_prime hp] at hpos
    exact (lt_irrefl 0) hpos
  · exact thetaCuspLikelihoodRayBoundaryCornerMass_pos_of_not_prime hk

/-- On a prime shell, leg exchange makes the coefficient identical on both ordered factor pairs. -/
theorem thetaCuspLikelihoodSwap_pair_coefficient_eq_prime
    {k : ℕ} (hk : k.Prime) {q : ℕ × ℕ}
    (hq : q ∈ thetaPositiveFactorPairs k) (B D : ℝ) :
    thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) D +
        thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) D *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B =
      thetaCuspLikelihoodPrimeSwapScale k B D := by
  rcases thetaFactorPair_indices_of_prime hk hq with h | h
  · rw [h.1, h.2]
    simp only [thetaCuspLikelihoodScaledBoundaryTerm_one]
    unfold thetaCuspLikelihoodPrimeSwapScale
    ring
  · rw [h.1, h.2]
    simp only [thetaCuspLikelihoodScaledBoundaryTerm_one]
    unfold thetaCuspLikelihoodPrimeSwapScale
    ring

/-- **Prime swap-bulk rigidity.**  The entire two-temperature prime shell is the original
arithmetic phase multiplied by one symmetric real scale. -/
theorem thetaCuspLikelihoodSwapMassShellPhase_eq_prime
    {k : ℕ} (hk : k.Prime) (B D : ℝ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhase k B D z =
      (thetaCuspLikelihoodPrimeSwapScale k B D : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z := by
  rw [thetaCuspLikelihoodMassShellPhase_eq_productFiber]
  unfold thetaCuspLikelihoodSwapMassShellPhase thetaProductFiberCenteredPhase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspLikelihoodSwap_pair_coefficient_eq_prime hk hq]

/-- The differentiated swap bulk has the same rigid prime scale. -/
theorem thetaCuspLikelihoodSwapMassShellPhaseDerivative_eq_prime
    {k : ℕ} (hk : k.Prime) (B D : ℝ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhaseDerivative k B D z =
      (thetaCuspLikelihoodPrimeSwapScale k B D : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z := by
  rw [thetaCuspLikelihoodMassShellPhaseDerivative_eq_productFiber]
  unfold thetaCuspLikelihoodSwapMassShellPhaseDerivative
    thetaProductFiberCenteredPhaseDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspLikelihoodSwap_pair_coefficient_eq_prime hk hq]
  ring

/-- The prime swap scale is positive on the closed nonnegative quadrant away from its corner. -/
theorem thetaCuspLikelihoodPrimeSwapScale_pos
    {k : ℕ} (hk : k.Prime) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hBD : 0 < B + D) :
    0 < thetaCuspLikelihoodPrimeSwapScale k B D := by
  have hSB := thetaCuspLikelihoodScaledBoundaryTerm_pos_of_nonneg hk.two_le hB
  have hSD := thetaCuspLikelihoodScaledBoundaryTerm_pos_of_nonneg hk.two_le hD
  unfold thetaCuspLikelihoodPrimeSwapScale
  by_cases hB0 : B = 0
  · subst B
    simp only [zero_mul, zero_add] at hBD ⊢
    exact mul_pos hBD hSB
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    exact add_pos_of_pos_of_nonneg (mul_pos hBpos hSD)
      (mul_nonneg hD hSB.le)

/-- **Closed-quadrant prime trace-to-bulk orientation.**  Prime current is strictly negative on
both boundary faces and throughout the full positive two-temperature interior. -/
theorem thetaCuspLikelihoodSwapPrimeMassShellPhase_current_lt_zero
    {k : ℕ} (hk : k.Prime) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hBD : 0 < B + D)
    {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspLikelihoodSwapMassShellPhaseDerivative k B D z *
      (starRingEnd ℂ) (thetaCuspLikelihoodSwapMassShellPhase k B D z)).im < 0 := by
  rw [thetaCuspLikelihoodSwapMassShellPhaseDerivative_eq_prime hk,
    thetaCuspLikelihoodSwapMassShellPhase_eq_prime hk]
  exact thetaCuspLikelihoodMassShellPhase_realScale_current_lt_zero hk
    (thetaCuspLikelihoodPrimeSwapScale_pos hk hB hD hBD) hz

/-- The literal source leg-exchange shell is the desingularizer product times the exact
two-temperature likelihood swap bulk, on every arithmetic shell. -/
theorem thetaCuspSourceSwapMassShellPhase_eq_likelihood
    (k : ℕ) (x y : ℝ) (z : ℂ) :
    thetaCuspSourceSwapMassShellPhase k x y z =
      ((thetaCuspLikelihoodBoundaryDesingularizer x *
          thetaCuspLikelihoodBoundaryDesingularizer y : ℝ) : ℂ) *
        thetaCuspLikelihoodSwapMassShellPhase k
          (thetaCuspLikelihoodCoordinate x) (thetaCuspLikelihoodCoordinate y) z := by
  unfold thetaCuspSourceSwapMassShellPhase thetaCuspLikelihoodSwapMassShellPhase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm]
  push_cast
  ring

/-- Derivative form of the exact source-to-likelihood bulk identity. -/
theorem thetaCuspSourceSwapMassShellPhaseDerivative_eq_likelihood
    (k : ℕ) (x y : ℝ) (z : ℂ) :
    thetaCuspSourceSwapMassShellPhaseDerivative k x y z =
      ((thetaCuspLikelihoodBoundaryDesingularizer x *
          thetaCuspLikelihoodBoundaryDesingularizer y : ℝ) : ℂ) *
        thetaCuspLikelihoodSwapMassShellPhaseDerivative k
          (thetaCuspLikelihoodCoordinate x) (thetaCuspLikelihoodCoordinate y) z := by
  unfold thetaCuspSourceSwapMassShellPhaseDerivative
    thetaCuspLikelihoodSwapMassShellPhaseDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm]
  push_cast
  ring

/-- The earlier literal boundary-face trace is the boundary restriction of the new source bulk. -/
theorem thetaCuspSourceSwapMassShellPhase_boundary
    (k : ℕ) (x : ℝ) (z : ℂ) :
    thetaCuspSourceSwapMassShellPhase k x thetaCuspLikelihoodBoundaryPoint z =
      thetaCuspSourceBoundaryFaceMassShellPhase k x z := by
  rfl

/-- Derivative boundary connector for literal source traces. -/
theorem thetaCuspSourceSwapMassShellPhaseDerivative_boundary
    (k : ℕ) (x : ℝ) (z : ℂ) :
    thetaCuspSourceSwapMassShellPhaseDerivative k x thetaCuspLikelihoodBoundaryPoint z =
      thetaCuspSourceBoundaryFaceMassShellPhaseDerivative k x z := by
  rfl

/-- Literal source prime bulk factors through the complete arithmetic phase. -/
theorem thetaCuspSourceSwapMassShellPhase_eq_prime
    {k : ℕ} (hk : k.Prime) (x y : ℝ) (z : ℂ) :
    thetaCuspSourceSwapMassShellPhase k x y z =
      ((thetaCuspLikelihoodBoundaryDesingularizer x *
          thetaCuspLikelihoodBoundaryDesingularizer y *
          thetaCuspLikelihoodPrimeSwapScale k
            (thetaCuspLikelihoodCoordinate x) (thetaCuspLikelihoodCoordinate y) : ℝ) : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z := by
  rw [thetaCuspSourceSwapMassShellPhase_eq_likelihood,
    thetaCuspLikelihoodSwapMassShellPhase_eq_prime hk]
  push_cast
  ring

/-- The differentiated literal source prime bulk has the same positive real scale. -/
theorem thetaCuspSourceSwapMassShellPhaseDerivative_eq_prime
    {k : ℕ} (hk : k.Prime) (x y : ℝ) (z : ℂ) :
    thetaCuspSourceSwapMassShellPhaseDerivative k x y z =
      ((thetaCuspLikelihoodBoundaryDesingularizer x *
          thetaCuspLikelihoodBoundaryDesingularizer y *
          thetaCuspLikelihoodPrimeSwapScale k
            (thetaCuspLikelihoodCoordinate x) (thetaCuspLikelihoodCoordinate y) : ℝ) : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z := by
  rw [thetaCuspSourceSwapMassShellPhaseDerivative_eq_likelihood,
    thetaCuspLikelihoodSwapMassShellPhaseDerivative_eq_prime hk]
  push_cast
  ring

/-- **Literal theta-source prime bulk orientation.**  At any two source points in the closed
nonnegative likelihood region, not both on the boundary, the complete leg-exchange prime trace is
strictly oriented throughout the upper half-plane. -/
theorem thetaCuspSourceSwapPrimeMassShellPhase_current_lt_zero
    {k : ℕ} (hk : k.Prime) {x y : ℝ}
    (hx : 0 ≤ thetaCuspLikelihoodCoordinate x)
    (hy : 0 ≤ thetaCuspLikelihoodCoordinate y)
    (hxy : 0 < thetaCuspLikelihoodCoordinate x + thetaCuspLikelihoodCoordinate y)
    {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspSourceSwapMassShellPhaseDerivative k x y z *
      (starRingEnd ℂ) (thetaCuspSourceSwapMassShellPhase k x y z)).im < 0 := by
  rw [thetaCuspSourceSwapMassShellPhaseDerivative_eq_prime hk,
    thetaCuspSourceSwapMassShellPhase_eq_prime hk]
  exact thetaCuspLikelihoodMassShellPhase_realScale_current_lt_zero hk
    (mul_pos
      (mul_pos (thetaCuspLikelihoodBoundaryDesingularizer_pos x)
        (thetaCuspLikelihoodBoundaryDesingularizer_pos y))
      (thetaCuspLikelihoodPrimeSwapScale_pos hk hx hy hxy)) hz

end

end RHTower
