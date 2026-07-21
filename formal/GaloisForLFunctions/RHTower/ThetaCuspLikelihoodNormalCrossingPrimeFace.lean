import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodRayBoundaryResidue

/-!
# The theta-likelihood normal crossing has a rigid prime face

The equal-temperature likelihood boundary layer is not itself a Wigner pair: two source legs
generally have different intrinsic temperatures.  This file replaces that invalid identification
with an exact two-temperature theorem.

Each theta atom admits a global, division-free factorization through the scaled likelihood
coefficient.  On a prime product shell, the sum of the two coordinate-boundary faces is the
original strictly oriented arithmetic phase times `B * R_p`.  After division by the ground
coordinate, this prime conormal phase is independent of position along the boundary face.  The
same law holds for the literal theta-source atom traces at the zero-likelihood point.

All statements are exact and unconditional.
-/

open Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Product-shell phase with independent intrinsic likelihood temperatures on its two legs. -/
def thetaCuspLikelihoodTwoTemperatureMassShellPhase
    (k : ℕ) (B D : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
        thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) D : ℝ) : ℂ) *
      Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Spectral derivative of the two-temperature product-shell phase. -/
def thetaCuspLikelihoodTwoTemperatureMassShellPhaseDerivative
    (k : ℕ) (B D : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
        thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) D : ℝ) : ℂ) *
      (Complex.I * (thetaFactorPairLogDisplacement q : ℂ)) *
        Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Sum of the two coordinate faces of the two-temperature normal crossing. -/
def thetaCuspLikelihoodTwoFaceMassShellPhase
    (k : ℕ) (B : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) 0 +
        thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) 0 *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B : ℝ) : ℂ) *
      Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Spectral derivative of the paired normal-crossing face. -/
def thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative
    (k : ℕ) (B : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) 0 +
        thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) 0 *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B : ℝ) : ℂ) *
      (Complex.I * (thetaFactorPairLogDisplacement q : ℂ)) *
        Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Literal theta-source product-shell trace on the two faces meeting the zero-likelihood point. -/
def thetaCuspSourceBoundaryFaceMassShellPhase
    (k : ℕ) (x : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspSourceTerm x (q.1 + 1) *
          thetaCuspSourceTerm thetaCuspLikelihoodBoundaryPoint (q.2 + 1) +
        thetaCuspSourceTerm thetaCuspLikelihoodBoundaryPoint (q.1 + 1) *
          thetaCuspSourceTerm x (q.2 + 1) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Spectral derivative of the literal theta-source two-face trace. -/
def thetaCuspSourceBoundaryFaceMassShellPhaseDerivative
    (k : ℕ) (x : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspSourceTerm x (q.1 + 1) *
          thetaCuspSourceTerm thetaCuspLikelihoodBoundaryPoint (q.2 + 1) +
        thetaCuspSourceTerm thetaCuspLikelihoodBoundaryPoint (q.1 + 1) *
          thetaCuspSourceTerm x (q.2 + 1) : ℝ) : ℂ) *
      (Complex.I * (thetaFactorPairLogDisplacement q : ℂ)) *
        Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- **Global atomwise desingularization.**  The scaled likelihood channel is the exact
division-free coefficient of every theta atom, with no positivity assumption on the intrinsic
coordinate. -/
theorem thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm
    (x : ℝ) (n : ℕ) :
    thetaCuspSourceTerm x n =
      thetaCuspLikelihoodBoundaryDesingularizer x *
        thetaCuspLikelihoodScaledBoundaryTerm n
          (thetaCuspLikelihoodCoordinate x) := by
  have hsource : thetaCuspSourceTerm x n =
      Real.exp (x / 2) * 2 * Real.pi * Real.exp x ^ 2 * (n : ℝ) ^ 2 *
        (2 * (Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2 - 3) *
        Real.exp (-(Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2) := by
    unfold thetaCuspSourceTerm thetaCuspSeed
    ring
  have hexp :
      Real.exp (-(Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2) =
        Real.exp (-(Real.pi * Real.exp x ^ 2)) *
          Real.exp (-(Real.pi * Real.exp x ^ 2 - 3 / 2) * ((n : ℝ) ^ 2 - 1)) *
            Real.exp (-(3 / 2 : ℝ) * ((n : ℝ) ^ 2 - 1)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hsource, hexp]
  unfold thetaCuspLikelihoodBoundaryDesingularizer
    thetaCuspLikelihoodScaledBoundaryTerm thetaCuspLikelihoodCoordinate
    thetaCuspLikelihoodAtomWeight thetaCuspLikelihoodRayWeight
    thetaCuspLikelihoodGap
  ring

/-- The paired face is literally the sum of the two restrictions of the two-temperature phase. -/
theorem thetaCuspLikelihoodTwoFaceMassShellPhase_eq_add
    (k : ℕ) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodTwoFaceMassShellPhase k B z =
      thetaCuspLikelihoodTwoTemperatureMassShellPhase k B 0 z +
        thetaCuspLikelihoodTwoTemperatureMassShellPhase k 0 B z := by
  unfold thetaCuspLikelihoodTwoFaceMassShellPhase
    thetaCuspLikelihoodTwoTemperatureMassShellPhase
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  push_cast
  ring

/-- The derivative face is likewise the sum of the two differentiated restrictions. -/
theorem thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative_eq_add
    (k : ℕ) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative k B z =
      thetaCuspLikelihoodTwoTemperatureMassShellPhaseDerivative k B 0 z +
        thetaCuspLikelihoodTwoTemperatureMassShellPhaseDerivative k 0 B z := by
  unfold thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative
    thetaCuspLikelihoodTwoTemperatureMassShellPhaseDerivative
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  push_cast
  ring

/-- On a prime shell, the two boundary faces give the same constant coefficient on both ordered
factor pairs. -/
theorem thetaCuspLikelihoodTwoFace_pair_coefficient_eq_prime
    {k : ℕ} (hk : k.Prime) {q : ℕ × ℕ}
    (hq : q ∈ thetaPositiveFactorPairs k) (B : ℝ) :
    thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) 0 +
        thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) 0 *
          thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B =
      B * thetaCuspLikelihoodRayWeight k := by
  rcases thetaFactorPair_indices_of_prime hk hq with h | h
  · rw [h.1, h.2, thetaCuspLikelihoodScaledBoundaryTerm_one,
      thetaCuspLikelihoodScaledBoundaryTerm_zero]
    simp [thetaCuspLikelihoodRayWeight, thetaCuspLikelihoodGap]
  · rw [h.1, h.2, thetaCuspLikelihoodScaledBoundaryTerm_one,
      thetaCuspLikelihoodScaledBoundaryTerm_zero]
    simp [thetaCuspLikelihoodRayWeight, thetaCuspLikelihoodGap]
    ring

/-- **Prime normal-crossing face rigidity.**  The paired face is the original arithmetic shell
times `B R_p`; after ground-coordinate normalization it is independent of position on the face. -/
theorem thetaCuspLikelihoodTwoFaceMassShellPhase_eq_prime
    {k : ℕ} (hk : k.Prime) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodTwoFaceMassShellPhase k B z =
      ((B * thetaCuspLikelihoodRayWeight k : ℝ) : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z := by
  rw [thetaCuspLikelihoodMassShellPhase_eq_productFiber]
  unfold thetaCuspLikelihoodTwoFaceMassShellPhase thetaProductFiberCenteredPhase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspLikelihoodTwoFace_pair_coefficient_eq_prime hk hq]

/-- The differentiated two-face shell has the same rigid scalar factor. -/
theorem thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative_eq_prime
    {k : ℕ} (hk : k.Prime) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative k B z =
      ((B * thetaCuspLikelihoodRayWeight k : ℝ) : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z := by
  rw [thetaCuspLikelihoodMassShellPhaseDerivative_eq_productFiber]
  unfold thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative
    thetaProductFiberCenteredPhaseDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspLikelihoodTwoFace_pair_coefficient_eq_prime hk hq]
  push_cast
  ring

/-- Ground-coordinate normalization identifies every nonzero face point with the prime corner
conormal phase. -/
theorem thetaCuspLikelihoodTwoFaceMassShellPhase_div_eq_primeConormal
    {k : ℕ} (hk : k.Prime) {B : ℝ} (hB : B ≠ 0) (z : ℂ) :
    (B : ℂ)⁻¹ * thetaCuspLikelihoodTwoFaceMassShellPhase k B z =
      (thetaCuspLikelihoodRayWeight k : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z := by
  rw [thetaCuspLikelihoodTwoFaceMassShellPhase_eq_prime hk]
  push_cast
  field_simp [hB]

/-- The normalized differentiated face is the same position-independent prime conormal. -/
theorem thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative_div_eq_primeConormal
    {k : ℕ} (hk : k.Prime) {B : ℝ} (hB : B ≠ 0) (z : ℂ) :
    (B : ℂ)⁻¹ * thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative k B z =
      (thetaCuspLikelihoodRayWeight k : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z := by
  rw [thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative_eq_prime hk]
  push_cast
  field_simp [hB]

/-- Positive real scaling preserves the strict upper-half-plane arithmetic current. -/
theorem thetaCuspLikelihoodMassShellPhase_realScale_current_lt_zero
    {k : ℕ} (hk : k.Prime) {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : 0 < z.im) :
    (((c : ℂ) * thetaCuspLikelihoodMassShellPhaseDerivative k z) *
      (starRingEnd ℂ) ((c : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z)).im < 0 := by
  have hbase := thetaCuspLikelihoodMassShellPhase_current_lt_zero hk.one_lt hz
  have heq :
      (((c : ℂ) * thetaCuspLikelihoodMassShellPhaseDerivative k z) *
        (starRingEnd ℂ) ((c : ℂ) * thetaCuspLikelihoodMassShellPhase k z)).im =
        c ^ 2 *
          (thetaCuspLikelihoodMassShellPhaseDerivative k z *
            (starRingEnd ℂ) (thetaCuspLikelihoodMassShellPhase k z)).im := by
    rw [map_mul, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [heq]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hc) hbase

/-- Every positive prime boundary face retains strict arithmetic orientation. -/
theorem thetaCuspLikelihoodTwoFacePrimeMassShellPhase_current_lt_zero
    {k : ℕ} (hk : k.Prime) {B : ℝ} (hB : 0 < B)
    {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative k B z *
      (starRingEnd ℂ)
        (thetaCuspLikelihoodTwoFaceMassShellPhase k B z)).im < 0 := by
  rw [thetaCuspLikelihoodTwoFaceMassShellPhaseDerivative_eq_prime hk,
    thetaCuspLikelihoodTwoFaceMassShellPhase_eq_prime hk]
  exact thetaCuspLikelihoodMassShellPhase_realScale_current_lt_zero hk
    (mul_pos hB (thetaCuspLikelihoodRayWeight_pos hk.two_le)) hz

/-- Literal source coefficients on the two zero-likelihood faces have the same prime rigidity. -/
theorem thetaCuspSourceBoundaryFace_pair_coefficient_eq_prime
    {k : ℕ} (hk : k.Prime) {q : ℕ × ℕ}
    (hq : q ∈ thetaPositiveFactorPairs k) (x : ℝ) :
    thetaCuspSourceTerm x (q.1 + 1) *
          thetaCuspSourceTerm thetaCuspLikelihoodBoundaryPoint (q.2 + 1) +
        thetaCuspSourceTerm thetaCuspLikelihoodBoundaryPoint (q.1 + 1) *
          thetaCuspSourceTerm x (q.2 + 1) =
      thetaCuspLikelihoodBoundaryDesingularizer x *
        thetaCuspLikelihoodBoundaryDesingularizer thetaCuspLikelihoodBoundaryPoint *
          thetaCuspLikelihoodCoordinate x * thetaCuspLikelihoodRayWeight k := by
  rw [thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspSourceTerm_eq_boundaryDesingularizer_mul_scaledBoundaryTerm,
    thetaCuspLikelihoodCoordinate_boundaryPoint]
  calc
    _ = thetaCuspLikelihoodBoundaryDesingularizer x *
          thetaCuspLikelihoodBoundaryDesingularizer thetaCuspLikelihoodBoundaryPoint *
            (thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1)
                (thetaCuspLikelihoodCoordinate x) *
                  thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) 0 +
              thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) 0 *
                thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1)
                  (thetaCuspLikelihoodCoordinate x)) := by ring
    _ = _ := by
      rw [thetaCuspLikelihoodTwoFace_pair_coefficient_eq_prime hk hq]
      ring

/-- **Literal theta-source prime-face law.**  The paired source boundary trace is a positive
source scalar times the complete likelihood/Eisenstein prime phase. -/
theorem thetaCuspSourceBoundaryFaceMassShellPhase_eq_prime
    {k : ℕ} (hk : k.Prime) (x : ℝ) (z : ℂ) :
    thetaCuspSourceBoundaryFaceMassShellPhase k x z =
      ((thetaCuspLikelihoodBoundaryDesingularizer x *
          thetaCuspLikelihoodBoundaryDesingularizer thetaCuspLikelihoodBoundaryPoint *
            thetaCuspLikelihoodCoordinate x * thetaCuspLikelihoodRayWeight k : ℝ) : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z := by
  rw [thetaCuspLikelihoodMassShellPhase_eq_productFiber]
  unfold thetaCuspSourceBoundaryFaceMassShellPhase thetaProductFiberCenteredPhase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspSourceBoundaryFace_pair_coefficient_eq_prime hk hq]

/-- The literal differentiated source face has the same prime scalar. -/
theorem thetaCuspSourceBoundaryFaceMassShellPhaseDerivative_eq_prime
    {k : ℕ} (hk : k.Prime) (x : ℝ) (z : ℂ) :
    thetaCuspSourceBoundaryFaceMassShellPhaseDerivative k x z =
      ((thetaCuspLikelihoodBoundaryDesingularizer x *
          thetaCuspLikelihoodBoundaryDesingularizer thetaCuspLikelihoodBoundaryPoint *
            thetaCuspLikelihoodCoordinate x * thetaCuspLikelihoodRayWeight k : ℝ) : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z := by
  rw [thetaCuspLikelihoodMassShellPhaseDerivative_eq_productFiber]
  unfold thetaCuspSourceBoundaryFaceMassShellPhaseDerivative
    thetaProductFiberCenteredPhaseDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspSourceBoundaryFace_pair_coefficient_eq_prime hk hq]
  push_cast
  ring

/-- **The actual theta-source prime face is strictly oriented.**  At every positive opposite-leg
likelihood temperature, the two literal zero-likelihood boundary traces retain the strict
upper-half-plane arithmetic current. -/
theorem thetaCuspSourceBoundaryFacePrimeMassShellPhase_current_lt_zero
    {k : ℕ} (hk : k.Prime) {x : ℝ}
    (hx : 0 < thetaCuspLikelihoodCoordinate x)
    {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspSourceBoundaryFaceMassShellPhaseDerivative k x z *
      (starRingEnd ℂ)
        (thetaCuspSourceBoundaryFaceMassShellPhase k x z)).im < 0 := by
  rw [thetaCuspSourceBoundaryFaceMassShellPhaseDerivative_eq_prime hk,
    thetaCuspSourceBoundaryFaceMassShellPhase_eq_prime hk]
  have hc : 0 <
      thetaCuspLikelihoodBoundaryDesingularizer x *
        thetaCuspLikelihoodBoundaryDesingularizer thetaCuspLikelihoodBoundaryPoint *
          thetaCuspLikelihoodCoordinate x * thetaCuspLikelihoodRayWeight k :=
    mul_pos
    (mul_pos
      (mul_pos (thetaCuspLikelihoodBoundaryDesingularizer_pos x)
        (thetaCuspLikelihoodBoundaryDesingularizer_pos
          thetaCuspLikelihoodBoundaryPoint)) hx)
    (thetaCuspLikelihoodRayWeight_pos hk.two_le)
  exact thetaCuspLikelihoodMassShellPhase_realScale_current_lt_zero hk hc hz

end

end RHTower
