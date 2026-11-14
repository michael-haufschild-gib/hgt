import GaloisForLFunctions.HTGeometry.SphereBlockTail
import GaloisForLFunctions.HTGeometry.GaussianAngularPolarDisintegrationLaw
import GaloisForLFunctions.RHTower.GaussianAbsoluteMoment
import GaloisForLFunctions.RHTower.Deninger.DeningerRadialIntegral

/-!
# Complex-coordinate moments on a sphere

Cartesian Gaussian integration separates a complex coordinate from its orthogonal complement.
Polar integration separates the same moment into an angular moment and a radial factorial.
Comparing the two gives the exact complex-coordinate sphere moments.
-/

open MeasureTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The odd radial Gaussian moments are factorials divided by two. -/
theorem integral_Ioi_odd_pow_gaussian (k : ℕ) :
    (∫ r in Ioi (0 : ℝ), r ^ (2 * k + 1) * Real.exp (-r ^ 2)) =
      (k.factorial : ℝ) / 2 := by
  have h := RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := ((2 * k + 1 : ℕ) : ℝ)) (by positivity) (b := 1) zero_lt_one
  have he : (((2 * k + 1 : ℕ) : ℝ) + 1) / 2 = (k : ℝ) + 1 := by
    push_cast
    ring
  simpa only [Real.rpow_natCast, neg_one_mul, one_div_one, Real.one_rpow,
    he, one_mul, Real.Gamma_nat_eq_factorial, mul_one, div_eq_mul_inv, mul_comm] using h

/-- The Gaussian moment of a complex coordinate. -/
theorem integral_complex_norm_even_pow_gaussian (k : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ (2 * k) * Real.exp (-‖z‖ ^ 2)) =
      Real.pi * (k.factorial : ℝ) := by
  rw [RHTower.deningerComplex_integral_norm
    (fun r => r ^ (2 * k) * Real.exp (-r ^ 2))]
  have he : (fun r : ℝ => r * (r ^ (2 * k) * Real.exp (-r ^ 2))) =
      fun r => r ^ (2 * k + 1) * Real.exp (-r ^ 2) := by
    funext r
    rw [pow_succ]
    ring
  rw [he, integral_Ioi_odd_pow_gaussian]
  ring

/-- Polar separation for a homogeneous Gaussian-weighted observable. -/
theorem integral_homogeneous_mul_gaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (g : E → ℝ) (k : ℕ)
    (hg : ∀ (r : ℝ), 0 < r → ∀ x : E, g (r • x) = r ^ k * g x) :
    (∫ x, g x * Real.exp (-‖x‖ ^ 2)) =
      (∫ ω : sphere (0 : E) 1, g ω.1 ∂volume.toSphere) *
        ∫ r in Ioi (0 : ℝ),
          r ^ (Module.finrank ℝ E - 1 + k) * Real.exp (-r ^ 2) := by
  let F : E → ℝ := fun x => g x * Real.exp (-‖x‖ ^ 2)
  have hpolar : (∫ x, F x) =
      ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), F (p.2.1 • p.1.1)
        ∂((volume : Measure E).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    calc
      _ = ∫ x : ({0}ᶜ : Set E), F x.1 ∂((volume : Measure E).comap (↑)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl F,
          restrict_compl_singleton]
      _ = _ := by
        simpa only [homeomorphUnitSphereProd_symm_apply_coe] using
          (volume : Measure E).measurePreserving_homeomorphUnitSphereProd.integral_comp
            (Homeomorph.measurableEmbedding _)
            (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
              F (((homeomorphUnitSphereProd E).symm p).1))
  change (∫ x, F x) = _
  rw [hpolar]
  have he : (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => F (p.2.1 • p.1.1)) =
      fun p => g p.1.1 * (p.2.1 ^ k * Real.exp (-p.2.1 ^ 2)) := by
    funext p
    have hnorm : ‖(p.1.1 : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    simp only [F, hg _ p.2.2, norm_smul, Real.norm_eq_abs,
      abs_of_pos p.2.2, hnorm, mul_one]
    ring
  rw [he, integral_prod_mul, integral_volumeIoiPow_comp_subtype]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  simp only [smul_eq_mul, pow_add]
  ring

end GaloisForLFunctions.HTGeometry
