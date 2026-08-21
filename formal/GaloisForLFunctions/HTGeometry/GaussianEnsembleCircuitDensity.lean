/-
# The completed-time circuit bound on the Gaussian Pauli ensemble

Instantiating the physical-time complete-union bound at the centred Pauli Gaussian ensemble: almost
every bounded, collision-good coefficient vector has completed-time circuit density at most
`2^{-r/2}`, and the collision-good set carries at least half the Gaussian mass.

Main results:
* `finiteComplexInner_self_eq_sum_normSq`, `occupationCollision_eigenCoords` — the two dictionary
  identifications.
* `ae_limsup_physicalCapture_le_of_gaussianGoodSet` — **`(6)` on the ensemble**.
-/
import GaloisForLFunctions.HTGeometry.PhysicalTimeCircuitCapture
import GaloisForLFunctions.HTGeometry.GaussianGoodCoefficientSet
import GaloisForLFunctions.HTGeometry.CliffordEnsembleCollisionMean

open MeasureTheory Complex Matrix Set Filter ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem finiteComplexInner_self_eq_sum_normSq {α : Type*} [Fintype α] (u : α → ℂ) :
    finiteComplexInner u u = ((∑ x, ‖u x‖ ^ 2 : ℝ) : ℂ) := by
  rw [finiteComplexInner, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.sq_norm]
  exact (Complex.normSq_eq_conj_mul_self).symm

theorem occupationCollision_eigenCoords {α : Type*} [Fintype α] (e : α → α → ℂ) (psi : α → ℂ) :
    occupationCollision (fun j => ‖eigenCoords e psi j‖ ^ 2) = spectralCollision e psi := by
  rw [occupationCollision, spectralCollision]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finitePureStateFidelity, eigenCoords]

variable {n q : ℕ}

/-- **`(6)` on the ensemble.**  Almost every coefficient vector of the centred Pauli Gaussian
ensemble which lies in the bounded, collision-good set has completed-time circuit density at most
`2^{-r/2}` against any dictionary satisfying the counting condition. -/
theorem ae_limsup_physicalCapture_le_of_gaussianGoodSet
    (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    (ref : FiniteQubitConfiguration (Fin n))
    {C : Type} [Fintype C] [Nonempty C]
    (Z : C → (FiniteQubitConfiguration (Fin n) → ℂ))
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r)
    (hscale : 16 * (4 * (2 / 3 : ℝ) ^ n) / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    {B : ℝ} :
    ∀ᵐ J ∂(centredProductGaussian (Fin n → Option (Fin 3)) 1),
      J ∈ gaussianGoodSet w B 4 →
        atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ)
            (physicalCaptureSet (pauliEnsemble w J) (zeroProductState (Fin n)) a Z))
          ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) := by
  classical
  have hOmega : finiteComplexInner (zeroProductState (Fin n)) (zeroProductState (Fin n)) = 1 := by
    rw [finiteComplexInner_self_eq_sum_normSq, sum_normSq_zeroProductState]
    norm_num
  filter_upwards [isOrthoEigenBasis_injective_pauliEnsemble_ae (q := q) w hq hw
      (v := 1) (by norm_num) hwne,
    maximallyProjectiveEnergy_pauliEnsemble_ae (q := q) w hq hw (v := 1) (by norm_num) hwne]
    with J hJbasis hJmax hJgood
  have hcoll : occupationCollision
      (fun j => ‖eigenCoords
        (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
        (zeroProductState (Fin n)) j‖ ^ 2) ≤ 4 * (2 / 3 : ℝ) ^ n := by
    rw [occupationCollision_eigenCoords]
    exact le_of_lt hJgood.2
  exact limsup_oneSided_physicalCapture_le hJbasis.1 hJmax ref
    (zeroProductState (Fin n)) hOmega Z hZ ha hr hcoll hscale hM hcard hs

end GaloisForLFunctions.HTGeometry

end
