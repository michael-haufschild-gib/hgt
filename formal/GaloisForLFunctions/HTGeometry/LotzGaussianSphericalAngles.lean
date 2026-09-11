import GaloisForLFunctions.HTGeometry.LotzStellarSolidAngles
import GaloisForLFunctions.HTGeometry.GaussianRadialAllLateHardnessTransferLaw

/-!
# Lotz subdivision in native Gaussian spherical averages

The Gaussian solid-angle valuation agrees with the existing sphere-average
interface via the corpus's independent angular-radius disintegration.
This transfers Lotz's signed stellar identity directly into that interface.
Existing angular and radial normalization is reused.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory ProbabilityTheory Module Metric Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The normalized sphere average is integration against the corpus's angular law. -/
theorem lotz_integral_gaussianAngular (n : ℕ)
    (f : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 → ℝ) :
    (∫ ω,f ω ∂gaussianAngularMeasure (n+1)) = gaussianSphereAverage (n+1) f := by
  have hN : 0 ≤ gaussianAngularNormalization (n+1) := by
    unfold gaussianAngularNormalization
    positivity
  rw [gaussianAngularMeasure,withDensity_const,integral_smul_measure,
    ENNReal.toReal_ofReal hN]
  rfl

/-- Positive scaling leaves every pointed-cone indicator unchanged. -/
theorem lotzConeIndicator_positive_scale {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : PointedCone ℝ E) (r : Ioi (0 : ℝ)) (x : E) :
    lotzConeIndicator C (r.val • x)=lotzConeIndicator C x := by
  simp only [lotzConeIndicator,PointedCone.smul_mem_iff C r.property]

/-- Gaussian cone solid angle agrees with the sphere-average interface already used in the corpus. -/
theorem lotzGaussianConeVal_eq_sphereAverage (n : ℕ)
    (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n+1)))) :
    lotzGaussianConeVal C = gaussianSphereAverage (n+1)
      (fun ω => lotzConeIndicator C.toPointedCone ω.val) := by
  letI : SFinite (gaussianAngularMeasure (n+1)) := by
    unfold gaussianAngularMeasure
    infer_instance
  letI : SFinite (gaussianRadiusMeasure (n+1)) := by
    unfold gaussianRadiusMeasure
    infer_instance
  have h := integral_stdGaussian_independent_polar (Nat.succ_pos n)
    (lotzConeIndicator C.toPointedCone)
  have hi : (∫ x,lotzConeIndicator C.toPointedCone x ∂stdGaussian _) =
      lotzGaussianConeVal C := by
    change (∫ x,(C : Set (EuclideanSpace ℝ (Fin (n+1)))).indicator (fun _ => (1 : ℝ)) x ∂stdGaussian _) = _
    exact lotzGaussianCone_integral C
  rw [hi] at h
  simp_rw [lotzConeIndicator_positive_scale C.toPointedCone] at h
  have hp := integral_prod_mul (μ := gaussianAngularMeasure (n+1))
    (ν := gaussianRadiusMeasure (n+1))
    (fun ω => lotzConeIndicator C.toPointedCone ω.val) (fun _ => (1 : ℝ))
  simp only [mul_one,integral_const,smul_eq_mul,mul_one,
    Measure.real,gaussianRadiusMeasure_univ (Nat.succ_pos n),ENNReal.toReal_one,
    mul_one,lotz_integral_gaussianAngular] at hp
  exact h.trans hp

/-- Lotz's signed subdivision now applies directly to native spherical averages. -/
theorem lotz_signed_stellar_sphereAverage (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (b : Basis ι ℝ (EuclideanSpace ℝ (Fin (n+1)))) (a : ι → ℝˣ) :
    gaussianSphereAverage (n+1) (fun ω => lotzConeIndicator (lotzBasisCone b) ω.val)-
      ∑ j, (if 0 < (a j : ℝ) then (1 : ℝ) else -1)*
        gaussianSphereAverage (n+1) (fun ω =>
          lotzConeIndicator (lotzBasisCone (lotzStellarBasis b a j)) ω.val) =
      if ∀ j, (a j : ℝ)<0 then (1 : ℝ) else 0 := by
  have h := lotz_signed_stellar_solid_angle b a
  simpa only [lotzGaussianConeVal_eq_sphereAverage,lotzProperBasisCone] using h

end GaloisForLFunctions.HTGeometry
