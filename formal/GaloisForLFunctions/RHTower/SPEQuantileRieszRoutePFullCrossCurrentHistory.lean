import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePExteriorCurrentCongruence

/-!
# Full SP-E strict-cross current in literal Route-P chronology

The SP-E strict-cross current has two inseparable parts: the signed
displacement--centroid orientation and both orientations of quadratic
displacement debt.  This leaf gives their exact finite source carrier.  Its
entries use only five literal profiles
`w`, `w d`, `w c`, `w d c`, and `w d²`; no target coefficient is chosen.

The carrier is inserted unchanged between the actual P-G186 child and pivot
incidence legs.  The forward word has coefficient `63 / 64 * H * C * H`,
while reversed chronology vanishes.  Consequently every finite P packet has
an actual off-diagonal ordered history which retains the complete signed
strict-cross source payload, not only the previous determinant line or its
positive debt.

This is a finite ordered action.  It neither closes the cofinal graph,
estimates the non-Bessel/non-nuclear limit, nor establishes divisor landing.
-/

open Complex Matrix
open scoped Kronecker

namespace RHTower

noncomputable section

/-- Exact signed two-cell strict-cross current, expressed through the five literal
weight/displacement/centroid profiles. -/
def speQuantileRieszAtomCrossCurrent {ι : Type*} (atom : ι → ℕ) : Matrix ι ι ℂ :=
  - Matrix.vecMulVec
      (fun i => (criticalMellinAtomWeight (atom i) : ℂ))
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedQuantilePolarDisplacement (atom i) *
        ccmActualHeadMatchedPolarCentroid (atom i) : ℝ) : ℂ)) -
    Matrix.vecMulVec
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedQuantilePolarDisplacement (atom i) *
        ccmActualHeadMatchedPolarCentroid (atom i) : ℝ) : ℂ))
      (fun i => (criticalMellinAtomWeight (atom i) : ℂ)) +
    Matrix.vecMulVec
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedPolarCentroid (atom i) : ℝ) : ℂ))
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedQuantilePolarDisplacement (atom i) : ℝ) : ℂ)) +
    Matrix.vecMulVec
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedQuantilePolarDisplacement (atom i) : ℝ) : ℂ))
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedPolarCentroid (atom i) : ℝ) : ℂ)) +
    Matrix.vecMulVec
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedQuantilePolarDisplacement (atom i) : ℝ) : ℂ))
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedQuantilePolarDisplacement (atom i) : ℝ) : ℂ)) -
    (1 / 2 : ℂ) • Matrix.vecMulVec
      (fun i => (criticalMellinAtomWeight (atom i) : ℂ))
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedQuantilePolarDisplacement (atom i) ^ 2 : ℝ) : ℂ)) -
    (1 / 2 : ℂ) • Matrix.vecMulVec
      (fun i => ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedQuantilePolarDisplacement (atom i) ^ 2 : ℝ) : ℂ))
      (fun i => (criticalMellinAtomWeight (atom i) : ℂ))

/-- The five-profile carrier is entrywise the literal strict-cross kernel: signed orientation
minus both-cell quadratic debt. -/
theorem speQuantileRieszAtomCrossCurrent_apply {ι : Type*} (atom : ι → ℕ) (i j : ι) :
    speQuantileRieszAtomCrossCurrent atom i j =
      (ccmActualHeadMatchedQuantileParabolicCrossKernelValue (atom i) (atom j) : ℂ) := by
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_orientation_sub_debt]
  unfold speQuantileRieszAtomCrossCurrent
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply]
  push_cast
  unfold ccmActualHeadMatchedQuantileParabolicOrientationLedger
    ccmActualHeadMatchedQuantileParabolicOrientationCoefficient
    ccmActualHeadMatchedQuantileParabolicDisplacementDebt
  push_cast
  ring

/-- The complete finite SP-E strict-cross source is exactly the ordered off-diagonal sum of the
five-profile carrier.  This retains all orientation and debt terms. -/
theorem ccmActualHeadMatchedQuantileParabolic_sourceBoundary_eq_atomCrossCurrent_sum
    (K : ℕ) :
    (ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) : ℂ) =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 1)).erase m,
        speQuantileRieszAtomCrossCurrent (fun q : ℕ => q + 2) m n := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_strictCross]
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  symm
  simpa [Nat.add_assoc, ccmActualHeadMatchedQuantileParabolicCrossKernelValue] using
    (speQuantileRieszAtomCrossCurrent_apply (fun q : ℕ => q + 2) m n)

/-- Full strict-cross source carrier on the literal prime-power labels of a finite P-G186 packet. -/
def routePPrimitiveBurnolSourceCrossCurrent {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  speQuantileRieszAtomCrossCurrent
    (fun i => xiGammaEulerValuationNat (pe i))

/-- Source-defined matrix payload between P child and pivot incidence legs. -/
def routePJuliaKreinIncidenceMiddlePayload {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ C

/-- An inserted source payload preserves the P ordered `1/0` chronology.  The forward word
has exact all-path coefficient `H * C * H`; reversed chronology vanishes. -/
theorem routePJuliaKreinIncidence_payload_ordered_coordinate_asymmetry
    {N : ℕ} (H C : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (routePJuliaKreinIncidenceChildHistoryStep H *
        routePJuliaKreinIncidenceMiddlePayload C *
        routePJuliaKreinIncidenceNegativePivotHistoryStep H) (0, i) (0, j) =
        (63 / 64 : ℂ) * (H * C * H) i j ∧
      (routePJuliaKreinIncidenceNegativePivotHistoryStep H *
        routePJuliaKreinIncidenceMiddlePayload C *
        routePJuliaKreinIncidenceChildHistoryStep H) (0, i) (0, j) = 0 := by
  rw [routePJuliaKreinIncidenceChildHistoryStep_eq_kronecker,
    routePJuliaKreinIncidenceNegativePivotHistoryStep_eq_kronecker]
  unfold routePJuliaKreinIncidenceMiddlePayload
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  constructor
  · rw [Matrix.kronecker_apply]
    rw [show routePJuliaKreinChildHistoryStep * 1 *
          routePJuliaKreinNegativePivotHistoryStep =
          routePJuliaKreinChildHistoryStep * routePJuliaKreinNegativePivotHistoryStep by simp,
      routePJuliaKrein_history_ordered_coordinate_asymmetry.1]
  · rw [Matrix.kronecker_apply]
    rw [show routePJuliaKreinNegativePivotHistoryStep * 1 *
          routePJuliaKreinChildHistoryStep =
          routePJuliaKreinNegativePivotHistoryStep * routePJuliaKreinChildHistoryStep by simp,
      routePJuliaKrein_history_ordered_coordinate_asymmetry.2, zero_mul]

/-- Literal P-G186 source-current history.  Its middle carrier is precisely the full SP-E
strict-cross matrix, so forward P chronology keeps both signed orientation and debt. -/
theorem routePPrimitiveBurnol_sourceCrossCurrent_history_ordered_coordinate_asymmetry
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) (i j : Fin N) :
    let H := routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)
    (routePJuliaKreinIncidenceChildHistoryStep H *
        routePJuliaKreinIncidenceMiddlePayload (routePPrimitiveBurnolSourceCrossCurrent pe) *
        routePJuliaKreinIncidenceNegativePivotHistoryStep H) (0, i) (0, j) =
        (63 / 64 : ℂ) * (H * routePPrimitiveBurnolSourceCrossCurrent pe * H) i j ∧
      (routePJuliaKreinIncidenceNegativePivotHistoryStep H *
        routePJuliaKreinIncidenceMiddlePayload (routePPrimitiveBurnolSourceCrossCurrent pe) *
        routePJuliaKreinIncidenceChildHistoryStep H) (0, i) (0, j) = 0 := by
  exact routePJuliaKreinIncidence_payload_ordered_coordinate_asymmetry _ _ i j

/-- The forward literal P-G186 source-current history coordinate is the exact sum over all
ordered two-leg P paths and all source-current entries. -/
theorem routePPrimitiveBurnol_sourceCrossCurrent_history_apply
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) (i j : Fin N) :
    let H := routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)
    (H * routePPrimitiveBurnolSourceCrossCurrent pe * H) i j =
      ∑ a, ∑ b,
        H i a * routePPrimitiveBurnolSourceCrossCurrent pe a b * H b j := by
  let H := routePPrimitiveJointDepthPrimeLogConjugate pe
    (routePPrimitiveBurnolWindowGramMatrix pe kappa)
  change (H * routePPrimitiveBurnolSourceCrossCurrent pe * H) i j =
    ∑ a, ∑ b, H i a * routePPrimitiveBurnolSourceCrossCurrent pe a b * H b j
  simp only [Matrix.mul_apply]
  calc
    ∑ b, (∑ a, H i a * routePPrimitiveBurnolSourceCrossCurrent pe a b) * H b j =
        ∑ b, ∑ a, H i a * routePPrimitiveBurnolSourceCrossCurrent pe a b * H b j := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
    _ = ∑ a, ∑ b,
        H i a * routePPrimitiveBurnolSourceCrossCurrent pe a b * H b j := by
      rw [Finset.sum_comm]

end

end RHTower
