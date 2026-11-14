import GaloisForLFunctions.HTGeometry.GaussianAngularPolarDisintegrationLaw
import GaloisForLFunctions.RHTower.GaussianAbsoluteMoment

/-!
# Polar integrals of real-homogeneous observables

Homogeneity separates angular and radial integration in any finite-dimensional real Hilbert
space. Gaussian profiles give Gamma factors, including for negative homogeneous degrees.
-/

open MeasureTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Lebesgue integration separated into unit direction and positive radius. -/
theorem integral_polar_sphere_radius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (F : E → ℝ) :
    (∫ x, F x) =
      ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), F (p.2.1 • p.1.1)
        ∂((volume : Measure E).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  calc
    _ = ∫ x : ({0}ᶜ : Set E), F x.1 ∂((volume : Measure E).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl F,
        restrict_compl_singleton]
    _ = _ := by
      have hp :=
        (volume : Measure E).measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _)
          (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
            F (((homeomorphUnitSphereProd E).symm p).1))
      simp only [Homeomorph.symm_apply_apply] at hp
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hp

/-- A real-homogeneous observable separates from an arbitrary radial profile. -/
theorem integral_real_homogeneous_mul_radial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (g : E → ℝ) (a : ℝ) (φ : ℝ → ℝ)
    (hg : ∀ (r : ℝ), 0 < r → ∀ x : E, g (r • x) = r ^ a * g x) :
    (∫ x, g x * φ ‖x‖) =
      (∫ ω : sphere (0 : E) 1, g ω.1 ∂volume.toSphere) *
        ∫ r in Ioi (0 : ℝ), r ^ ((Module.finrank ℝ E : ℝ) - 1 + a) * φ r := by
  rw [integral_polar_sphere_radius]
  have he : (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
      g (p.2.1 • p.1.1) * φ ‖p.2.1 • p.1.1‖) =
      fun p => g p.1.1 * (p.2.1 ^ a * φ p.2.1) := by
    funext p
    have hnorm : ‖(p.1.1 : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    have hr : (0 : ℝ) < p.2.1 := p.2.2
    simp only [hg _ hr, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hnorm, mul_one]
    ring
  rw [he, integral_prod_mul (fun ω : sphere (0 : E) 1 => g ω.1)
    (fun r : Ioi (0 : ℝ) => r.1 ^ a * φ r.1),
    integral_volumeIoiPow_comp_subtype (Module.finrank ℝ E - 1)
      (fun r : ℝ => r ^ a * φ r)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hd : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hcast : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) = (Module.finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
  dsimp only
  rw [Real.rpow_add hr, ← hcast, Real.rpow_natCast]
  simp only [smul_eq_mul, mul_assoc]

/-- Polar separation for a Gaussian-weighted observable of real homogeneous degree. -/
theorem integral_real_homogeneous_mul_gaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (g : E → ℝ) (a : ℝ)
    (hg : ∀ (r : ℝ), 0 < r → ∀ x : E, g (r • x) = r ^ a * g x) :
    (∫ x, g x * Real.exp (-‖x‖ ^ 2)) =
      (∫ ω : sphere (0 : E) 1, g ω.1 ∂volume.toSphere) *
        ∫ r in Ioi (0 : ℝ),
          r ^ ((Module.finrank ℝ E : ℝ) - 1 + a) * Real.exp (-r ^ 2) :=
  integral_real_homogeneous_mul_radial g a (fun r => Real.exp (-r ^ 2)) hg

/-- Surface measure on the unit sphere of a nonzero finite-dimensional Hilbert space has
positive total mass. -/
theorem unitSphere_volume_real_pos
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    0 < (volume.toSphere : Measure (sphere (0 : E) 1)).real univ := by
  rw [Measure.toSphere_real_apply_univ]
  apply mul_pos (Nat.cast_pos.mpr Module.finrank_pos)
  exact ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume 0 zero_lt_one))
    (ne_of_lt measure_ball_lt_top)

/-- A radial real-power Gaussian moment is surface mass times its one-dimensional Gamma factor. -/
theorem integral_norm_rpow_gaussian_polar
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) / 2 < s) :
    (∫ x : E, ‖x‖ ^ (2 * s) * Real.exp (-‖x‖ ^ 2)) =
      (volume.toSphere : Measure (sphere (0 : E) 1)).real univ *
        (Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + s) / 2) := by
  rw [integral_real_homogeneous_mul_gaussian (fun x : E => ‖x‖ ^ (2 * s)) (2 * s) (by
    intro r hr x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, Real.mul_rpow hr.le (norm_nonneg _)])]
  have hang : (∫ ω : sphere (0 : E) 1, ‖(ω.1 : E)‖ ^ (2 * s) ∂volume.toSphere) =
      (volume.toSphere : Measure (sphere (0 : E) 1)).real univ := by
    have he : (fun ω : sphere (0 : E) 1 => ‖(ω.1 : E)‖ ^ (2 * s)) = fun _ => (1 : ℝ) := by
      funext ω
      rw [mem_sphere_zero_iff_norm.mp ω.2, Real.one_rpow]
    rw [he, integral_const, smul_eq_mul, mul_one]
  rw [hang]
  have h := RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := (Module.finrank ℝ E : ℝ) - 1 + 2 * s)
    (by linarith only [hs]) (b := 1) zero_lt_one
  have he : (((Module.finrank ℝ E : ℝ) - 1 + 2 * s) + 1) / 2 =
      (Module.finrank ℝ E : ℝ) / 2 + s := by ring
  simp only [div_self one_ne_zero, Real.one_rpow, mul_one, neg_mul, one_mul, he] at h
  rw [h]
  ring

end GaloisForLFunctions.HTGeometry
