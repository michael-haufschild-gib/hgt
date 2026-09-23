import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteAngularProjectionMeromorphy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalHorizonDomain

/-! Actual angular mode and complete source pairing at all physical Xi fundamental frequencies. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMJointWave D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section
set_option autoImplicit false

/-- The literal scalar field at parameter `i*chi` has the original radial separation eigenvalue. -/
theorem scalar_radialMomentum_equation (chi : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (scalar (Complex.I*chi)) z = -(1/4+chi^(2 : ℕ))*scalar (Complex.I*chi) z := by
  have h := scalarCusp_hyperbolicLaplacian (Complex.I*chi) z hz
  change hyperbolicLaplacian (scalar (Complex.I*chi)) z =
    ((Complex.I*chi)^(2 : ℕ)-1/4)*scalar (Complex.I*chi) z at h
  rw [h,mul_pow,Complex.I_sq]
  ring

/-- Every Xi target has its actual angular equation and a complete absolutely convergent,
radial-L² meromorphic source projection at both fundamental frequencies, for every Xi source.
No spectral, endpoint, integral-admission, projection-value, or RH premise is supplied. -/
theorem allXi_fundamental_complete_angular_source_pairing (q r : XiZeroCopy) (branch : Bool) (a : ℂ) :
    let chi := thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint r)
    (∀ z : Fin 2 → ℝ, 0 < z 1 →
      hyperbolicLaplacian (scalar (Complex.I*chi)) z = -(1/4+chi^(2 : ℕ))*scalar (Complex.I*chi) z) ∧
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint r),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint r)} : Set ℂ),
      (∀ t : ℝ, Integrable (fun z : UpperHalfPlane => scalar (Complex.I*chi) (coordinates z)*
        continuedCuspResidualForcing q branch w a (t,z)) D4BMModularCore.measure) ∧
      MemLp (continuedAngularSourceProjection q branch (Complex.I*chi) a w) 2 radialMeasure ∧
      MeromorphicAt (continuedAngularSourceL2 q branch (Complex.I*chi) a) w := by
  dsimp only
  refine ⟨fun z hz => scalar_radialMomentum_equation _ z hz,?_⟩
  intro w hw
  have hstrip := D4BMLaplaceRadial.allXi_fundamental_frequency_strip r w hw
  exact ⟨fun t => continuedAngularSourceProjection_integrable q branch _ a w t,
    continuedAngularSourceProjection_memLp q branch _ a w hstrip.1 hstrip.2,
    continuedAngularSourceL2_meromorphicAt q branch _ a w hstrip.1 hstrip.2⟩

end
end RHTower.D4BMJointSource
