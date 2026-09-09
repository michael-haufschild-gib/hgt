import GaloisForLFunctions.HTGeometry.GomesCanonicalMomentGeometry
import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleCoordinateLaw
import GaloisForLFunctions.HTGeometry.FreeFockMatrixValuedSpectralLaw

/-!
Concrete corpus applications of the internal-frame and tensor-observation viewpoint in
Gomes, arXiv:2404.10461 and arXiv:2509.25276v7. Source equality is proved before
transferring the geometry. These are applications, not numbered paper transcriptions.
-/
open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry
open GaloisForLFunctions.HTGeometry

/-- Completed Fock vector observations are positive exactly for a nonzero observing vector. -/
theorem gomesFockVector_positive_iff {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    PositiveMomentForm (freeFockVectorMoment (gomesCompletedFockGenerators B) x) ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    have hp := h.pos_of_ne_zero (1 : Polynomial ℝ) one_ne_zero
    simp [momentInner_def,momentFunctional_one,freeFockVectorMoment_zero] at hp
  · intro hx
    exact freeFockVectorMoment_positiveMomentForm _ (gomesCompletedFockGenerators_hermitian B)
      (gomesCompletedFockGenerators_commonKernel B) x hx

/-- Canonical reconstruction detects exactly the vector observation's zero degeneracy. -/
theorem gomesFockVector_canonical_recovery_iff {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    (gomesCanonicalMomentModel (freeFockVectorMoment (gomesCompletedFockGenerators B) x)).moments =
      freeFockVectorMoment (gomesCompletedFockGenerators B) x ↔ x ≠ 0 := by
  rw [gomesCanonicalMomentModel_moments_iff,gomesFockVector_positive_iff]

/-- An affine observation chart supplies a nonzero vector from arbitrary coordinates. -/
def gomesFockObservationVector {d : ℕ} (y : Fin d → ℂ) : Fin (d+1) → ℂ := Fin.cons 1 y

/-- The fixed leading coordinate makes this entire observation chart nondegenerate. -/
theorem gomesFockObservationVector_ne_zero {d : ℕ} (y : Fin d → ℂ) :
    gomesFockObservationVector y ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [gomesFockObservationVector] at h0


/-- The canonical frame model of this concrete corpus source. -/
def gomesFockCoordinateModel {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (i : Fin (d+1)) : GomesMomentModel := gomesCanonicalMomentModel (freeFockCoordinateMoment (gomesCompletedFockGenerators B) i)

/-- Exact source identification, retaining its original mass. -/
theorem gomesFockCoordinateModel_moments {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (i : Fin (d+1)) :
    (gomesFockCoordinateModel B i).moments = (freeFockCoordinateMoment (gomesCompletedFockGenerators B) i) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  exact freeFockCoordinateMoment_positiveMomentForm _ (gomesCompletedFockGenerators_hermitian B)
    (gomesCompletedFockGenerators_commonKernel B) i

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesFockCoordinate_quotient_height {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (i : Fin (d+1)) (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (freeFockCoordinateMoment (gomesCompletedFockGenerators B) i) ((n+1)+1) z /
      monicOrthoC (freeFockCoordinateMoment (gomesCompletedFockGenerators B) i) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesFockCoordinateModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesFockCoordinateModel B i) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesFockCoordinate_flux_signature {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (i : Fin (d+1)) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesFockCoordinateModel B i) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesFockCoordinateModel B i) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesFockCoordinate_mass_probe {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (i : Fin (d+1)) :
    gomesMomentNormalizedFlux (gomesFockCoordinateModel B i) 0 Complex.I 0 0 = ((2/(freeFockCoordinateMoment (gomesCompletedFockGenerators B) i) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesFockCoordinateModel_moments]

/-- The canonical frame model of this concrete corpus source. -/
def gomesFockObservationModel {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) : GomesMomentModel := gomesCanonicalMomentModel (freeFockVectorMoment (gomesCompletedFockGenerators B) (gomesFockObservationVector y))

/-- Exact source identification, retaining its original mass. -/
theorem gomesFockObservationModel_moments {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) :
    (gomesFockObservationModel B y).moments = (freeFockVectorMoment (gomesCompletedFockGenerators B) (gomesFockObservationVector y)) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  exact (gomesFockVector_positive_iff B _).mpr (gomesFockObservationVector_ne_zero y)

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesFockObservation_quotient_height {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (freeFockVectorMoment (gomesCompletedFockGenerators B) (gomesFockObservationVector y)) ((n+1)+1) z /
      monicOrthoC (freeFockVectorMoment (gomesCompletedFockGenerators B) (gomesFockObservationVector y)) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesFockObservationModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesFockObservationModel B y) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesFockObservation_flux_signature {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesFockObservationModel B y) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesFockObservationModel B y) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesFockObservation_mass_probe {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) :
    gomesMomentNormalizedFlux (gomesFockObservationModel B y) 0 Complex.I 0 0 = ((2/(freeFockVectorMoment (gomesCompletedFockGenerators B) (gomesFockObservationVector y)) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesFockObservationModel_moments]

end GaloisForLFunctions.HTGeometry
