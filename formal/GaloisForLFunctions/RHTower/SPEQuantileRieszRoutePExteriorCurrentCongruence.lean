import GaloisForLFunctions.RHTower.RoutePJuliaKreinZeroClockHistoryDensity
import GaloisForLFunctions.RHTower.CCMFirstClockExteriorPositivePartNoGo
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePPluckerCocycle

/-!
# SP-E exterior current under literal Route-P incidence

The atom-level SP-E covariance plaquette is the alternating rank-two current
`a_i a_j (c_i - c_j)`: its two literal source profiles are the atom weight
`a` and the centroid-weighted profile `a c`.  This file transports that
current by the actual finite P-G186 prime-log incidence matrix.

Congruence by that matrix preserves the alternating two-profile form exactly.
Entrywise it is a double sum over every intermediate primitive label, so the
transport accounts for the all-path feature of the ordered P history without
fitting any source coefficient.

This handles only the exterior component.  It does not identify the full
SP-E exterior-history-minus-debt increment with this congruence current,
establish graph closure, or prove a cofinal bound.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- The literal atom-level SP-E exterior current on a finite packet. -/
def speQuantileRieszAtomExteriorCurrent {ι : Type*} (atom : ι → ℕ) : Matrix ι ι ℂ :=
  sourceExteriorAlternatingOuterMatrix
    (fun i => (criticalMellinAtomWeight (atom i) : ℂ))
    (fun i =>
      ((criticalMellinAtomWeight (atom i) *
        ccmActualHeadMatchedPolarCentroid (atom i) : ℝ) : ℂ))

/-- The SP-E exterior current on the literal prime-power labels of a finite P-G186 packet. -/
def routePPrimitiveBurnolSourceExteriorCurrent {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  speQuantileRieszAtomExteriorCurrent
    (fun i => xiGammaEulerValuationNat (pe i))

private theorem alternating_outer_congruence
    {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix β α ℂ) (u v : α → ℂ) :
    A * sourceExteriorAlternatingOuterMatrix u v * A.transpose =
      sourceExteriorAlternatingOuterMatrix (A.mulVec u) (A.mulVec v) := by
  unfold sourceExteriorAlternatingOuterMatrix
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  have hrow : ∀ z : α → ℂ, Matrix.vecMul z A.transpose = A.mulVec z := by
    intro z
    ext i
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, transpose_apply]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hrow u, hrow v]

/-- P-G186 congruence transports the literal SP-E exterior current into the alternating
current of its two P-propagated source profiles.  No coefficient is fitted. -/
theorem routePPrimitiveBurnol_sourceExteriorCurrent_congruence
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    let H := routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)
    H * routePPrimitiveBurnolSourceExteriorCurrent pe * H.transpose =
      sourceExteriorAlternatingOuterMatrix
        (H.mulVec (fun i =>
          (criticalMellinAtomWeight (xiGammaEulerValuationNat (pe i)) : ℂ)))
        (H.mulVec (fun i =>
          ((criticalMellinAtomWeight (xiGammaEulerValuationNat (pe i)) *
            ccmActualHeadMatchedPolarCentroid (xiGammaEulerValuationNat (pe i)) : ℝ) : ℂ))) := by
  let H := routePPrimitiveJointDepthPrimeLogConjugate pe
    (routePPrimitiveBurnolWindowGramMatrix pe kappa)
  change H * routePPrimitiveBurnolSourceExteriorCurrent pe * H.transpose =
    sourceExteriorAlternatingOuterMatrix
      (H.mulVec (fun i =>
        (criticalMellinAtomWeight (xiGammaEulerValuationNat (pe i)) : ℂ)))
      (H.mulVec (fun i =>
        ((criticalMellinAtomWeight (xiGammaEulerValuationNat (pe i)) *
          ccmActualHeadMatchedPolarCentroid (xiGammaEulerValuationNat (pe i)) : ℝ) : ℂ)))
  unfold routePPrimitiveBurnolSourceExteriorCurrent speQuantileRieszAtomExteriorCurrent
  exact alternating_outer_congruence H _ _

/-- Every transported exterior-current coordinate is the exact sum over all source-label paths.
This is the finite all-path law required by a graph-closed continuation. -/
theorem routePPrimitiveBurnol_sourceExteriorCurrent_congruence_apply
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) (i j : Fin N) :
    let H := routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)
    (H * routePPrimitiveBurnolSourceExteriorCurrent pe * H.transpose) i j =
      ∑ a, ∑ b,
        H i a * routePPrimitiveBurnolSourceExteriorCurrent pe a b * H j b := by
  let H := routePPrimitiveJointDepthPrimeLogConjugate pe
    (routePPrimitiveBurnolWindowGramMatrix pe kappa)
  change (H * routePPrimitiveBurnolSourceExteriorCurrent pe * H.transpose) i j =
    ∑ a, ∑ b,
      H i a * routePPrimitiveBurnolSourceExteriorCurrent pe a b * H j b
  simp only [Matrix.mul_apply, transpose_apply]
  calc
    ∑ b, (∑ a, H i a * routePPrimitiveBurnolSourceExteriorCurrent pe a b) * H j b =
        ∑ b, ∑ a, H i a * routePPrimitiveBurnolSourceExteriorCurrent pe a b * H j b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
    _ = ∑ a, ∑ b,
        H i a * routePPrimitiveBurnolSourceExteriorCurrent pe a b * H j b := by
      rw [Finset.sum_comm]

end

end RHTower
