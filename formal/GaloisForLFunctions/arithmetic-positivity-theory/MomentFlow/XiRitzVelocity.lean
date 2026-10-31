import GaloisForLFunctions.HilbertMetric.MomentFlow.RitzVelocity
import GaloisForLFunctions.RHTower.XiGaussianHeatEndpointRigidity

/-!
# A spectral-motion obstruction to RH

The actual Xi heat moments satisfy the negative moment-shift derivative law.
Under RH their form is positive definite. Hence every differentiable Ritz
eigenvalue in every fixed finite polynomial space has strictly negative velocity.
A stationary or right-moving branch at any positive time falsifies RH.
-/

open Polynomial Filter Topology HTGeometry
open GaloisForLFunctions.HTGeometry
open HilbertMetric.MomentFlow

noncomputable section
namespace RHTower

theorem positiveMomentForm_heatRealMoments_of_rh
    (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 < a) :
    PositiveMomentForm (heatRealMoments a) := by
  apply positiveMomentForm_iff_momentHankelMatrix_posDef.mpr
  intro n
  rw [heatMomentMatrix_eq]
  exact (forall_posDef_leadingMatrix_iff (heatMomentArray_symm a)).mpr
    ((riemannHypothesis_iff_heatMomentDet_pos ha).mp hRH) n

/-- Strict leftward motion holds for arbitrary finite polynomial trial spaces;
no eigenvalue simplicity or choice of orthogonal basis is needed. -/
theorem xiHeatRitz_velocity_neg_of_rh
    (hRH : RiemannHypothesis) {n : ℕ} {a : ℝ} (ha : 0 < a)
    (b : Fin n → ℝ[X]) {v : ℝ → Fin n → ℝ} {v' : Fin n → ℝ}
    {lam : ℝ → ℝ} {lam' : ℝ}
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) a)
    (hlam : HasDerivAt lam lam' a)
    (heig : ∀ᶠ t in 𝓝 a, ∀ w : Fin n → ℝ,
      momentInner (heatRealMoments t) (polynomialCombination b (v t))
          (X * polynomialCombination b w) =
        lam t * momentInner (heatRealMoments t) (polynomialCombination b (v t))
          (polynomialCombination b w))
    (hne : polynomialCombination b (v a) ≠ 0) : lam' < 0 :=
  ritz_velocity_neg b (fun P Q => hasDerivAt_heatMomentInner P Q ha)
    hv hlam heig (positiveMomentForm_heatRealMoments_of_rh hRH ha) hne

/-- A finite Xi heat-moment eigenbranch with nonnegative velocity falsifies RH. -/
theorem not_riemannHypothesis_of_xiHeatRitz_nonnegative_velocity :
    (∃ (n : ℕ) (a : ℝ) (b : Fin n → ℝ[X])
      (v : ℝ → Fin n → ℝ) (v' : Fin n → ℝ) (lam : ℝ → ℝ) (lam' : ℝ),
      0 < a ∧ polynomialCombination b (v a) ≠ 0 ∧
      (∀ i, HasDerivAt (fun t => v t i) (v' i) a) ∧
      HasDerivAt lam lam' a ∧
      (∀ᶠ t in 𝓝 a, ∀ w : Fin n → ℝ,
        momentInner (heatRealMoments t) (polynomialCombination b (v t))
            (X * polynomialCombination b w) =
          lam t * momentInner (heatRealMoments t) (polynomialCombination b (v t))
            (polynomialCombination b w)) ∧
      0 ≤ lam') → ¬ RiemannHypothesis := by
  rintro ⟨n, a, b, v, v', lam, lam', ha, hne, hv, hlam, heig, hnonneg⟩ hRH
  exact (not_lt_of_ge hnonneg)
    (xiHeatRitz_velocity_neg_of_rh hRH ha b hv hlam heig hne)

#print axioms positiveMomentForm_heatRealMoments_of_rh
#print axioms xiHeatRitz_velocity_neg_of_rh
#print axioms not_riemannHypothesis_of_xiHeatRitz_nonnegative_velocity

end RHTower
