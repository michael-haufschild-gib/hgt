import GaloisForLFunctions.HTGeometry.LotzGaussianSphericalAngles
import GaloisForLFunctions.HTGeometry.GaussianRadialContinuousReporter

/-!
# Cone sectors of Gaussian radial spectral completion

The Gaussian solid-angle valuation used to instantiate Lotz's signed
subdivision also controls radial observations on every proper cone. Polar
independence factors a cone-restricted observation into its solid angle and
full Gaussian expectation. Applying the native continuous spectral-reporter
completion law gives the corresponding sectorwise Bohr-mean limit.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory ProbabilityTheory Module Metric Set Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Independent polar coordinates identify arbitrary complex radial observations with the native radius law. -/
theorem lotzGaussian_radial_integral (n : ℕ) (f : ℝ → ℂ) :
    (∫ x : EuclideanSpace ℝ (Fin (n+1)), f ‖x‖ ∂stdGaussian _) =
      ∫ r : Ioi (0 : ℝ),f r.val ∂gaussianRadiusMeasure (n+1) := by
  letI : IsProbabilityMeasure (gaussianAngularMeasure (n+1)) :=
    ⟨gaussianAngularMeasure_univ (Nat.succ_pos n)⟩
  letI : IsProbabilityMeasure (gaussianRadiusMeasure (n+1)) :=
    ⟨gaussianRadiusMeasure_univ (Nat.succ_pos n)⟩
  have h := integral_stdGaussian_independent_polar (Nat.succ_pos n) (fun x => f ‖x‖)
  have he (p : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 × Ioi (0 : ℝ)) :
      f ‖p.2.val • p.1.val‖ = f p.2.val := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos p.2.property,norm_eq_of_mem_sphere,mul_one]
  simp_rw [he] at h
  have hp := integral_prod_smul (μ := gaussianAngularMeasure (n+1))
    (ν := gaussianRadiusMeasure (n+1)) (fun _ => (1 : ℝ)) (fun r => f r.val)
  simp only [one_smul,integral_const,probReal_univ] at hp
  exact h.trans hp

/-- Conditioning a radial observation on a cone multiplies its unnormalized expectation by solid angle. -/
theorem lotzGaussian_radial_cone_factorization (n : ℕ)
    (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n+1)))) (f : ℝ → ℂ) :
    (∫ x, (C : Set (EuclideanSpace ℝ (Fin (n+1)))).indicator (fun x => f ‖x‖) x
      ∂stdGaussian _) = lotzGaussianConeVal C •
        ∫ x : EuclideanSpace ℝ (Fin (n+1)), f ‖x‖ ∂stdGaussian _ := by
  letI : IsProbabilityMeasure (gaussianAngularMeasure (n+1)) :=
    ⟨gaussianAngularMeasure_univ (Nat.succ_pos n)⟩
  letI : IsProbabilityMeasure (gaussianRadiusMeasure (n+1)) :=
    ⟨gaussianRadiusMeasure_univ (Nat.succ_pos n)⟩
  have h := integral_stdGaussian_independent_polar (Nat.succ_pos n)
    ((C : Set (EuclideanSpace ℝ (Fin (n+1)))).indicator (fun x => f ‖x‖))
  have he (p : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 × Ioi (0 : ℝ)) :
      (C : Set (EuclideanSpace ℝ (Fin (n+1)))).indicator (fun x => f ‖x‖)
        (p.2.val • p.1.val) = lotzConeIndicator C.toPointedCone p.1.val • f p.2.val := by
    have hn : ‖p.2.val • p.1.val‖ = p.2.val := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos p.2.property,norm_eq_of_mem_sphere,mul_one]
    change (if p.2.val • p.1.val ∈ C.toPointedCone then f ‖p.2.val • p.1.val‖ else 0) =
      (if p.1.val ∈ C.toPointedCone then (1 : ℝ) else 0) • f p.2.val
    rw [PointedCone.smul_mem_iff C.toPointedCone p.2.property,hn]
    split_ifs <;> simp
  simp_rw [he] at h
  have hp := integral_prod_smul (μ := gaussianAngularMeasure (n+1))
    (ν := gaussianRadiusMeasure (n+1))
    (fun ω => lotzConeIndicator C.toPointedCone ω.val) (fun r => f r.val)
  rw [lotz_integral_gaussianAngular,← lotzGaussianConeVal_eq_sphereAverage n C,
    ← lotzGaussian_radial_integral n f] at hp
  exact h.trans hp

/-- Each Gaussian cone sector has the same radial completion law, scaled by its solid angle. -/
theorem lotz_spectral_reporter_cone_completion (n : ℕ)
    (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n+1))))
    {κ V : Type*} [Fintype κ] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Ev : κ → ℝ) (w : κ → V) (F : C(V,ℂ)) :
    Tendsto (fun time : ℝ => ∫ x,
      (C : Set (EuclideanSpace ℝ (Fin (n+1)))).indicator
        (fun x => F (spectralStateCurve Ev w (time * ‖x‖))) x ∂stdGaussian _)
      atTop (𝓝 (lotzGaussianConeVal C •
        bohrMean (fun s : ℝ => F (spectralStateCurve Ev w s)))) := by
  have h := (tendsto_integral_radial_bohrMean_continuous_reporter (Nat.succ_pos n)
    Ev w F.continuous).const_smul (lotzGaussianConeVal C)
  convert h using 1
  funext time
  exact lotzGaussian_radial_cone_factorization n C (fun r => F (spectralStateCurve Ev w (time*r)))

end GaloisForLFunctions.HTGeometry
