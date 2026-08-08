import GaloisForLFunctions.HTGeometry.GaussianRadialPolarLaw

/-!
# Gaussian angular--radial disintegration law

The standard multivariate Gaussian disintegrates exactly into an independent
chi-distributed radius and normalized uniform direction on the Euclidean unit
sphere.  Unlike a radius-only polar formula, this theorem applies to arbitrary
Banach-valued observables and therefore retains angular Hamiltonian geometry.

The final radial-time mixture theorem applies whenever scaling the coefficient
vector only rescales the observable's time parameter.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integral_stdGaussian_fullPolar {m : ℕ} (hm : 0 < m)
    (f : EuclideanSpace ℝ (Fin m) → F) :
    ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) =
      ∫ p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ),
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
          Real.exp (-p.2.1 ^ 2 / 2)) • f (p.2.1 • p.1.1)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere.prod
          (Measure.volumeIoiPow (m - 1))) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hm)
  have hmeas : Measurable
      (fun x : EuclideanSpace ℝ (Fin m) =>
        ENNReal.ofReal (euclideanGaussianDensityReal x)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold euclideanGaussianDensityReal
    fun_prop
  rw [stdGaussian_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) _]
  have hpt : ∀ x : EuclideanSpace ℝ (Fin m),
      (ENNReal.ofReal (euclideanGaussianDensityReal x)).toReal • f x =
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
          Real.exp (-‖x‖ ^ 2 / 2)) • f x := by
    intro x
    rw [ENNReal.toReal_ofReal (euclideanGaussianDensityReal_nonneg x)]
    simp only [euclideanGaussianDensityReal, Fintype.card_fin]
  rw [funext hpt]
  calc
    (∫ x : EuclideanSpace ℝ (Fin m),
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
          Real.exp (-‖x‖ ^ 2 / 2)) • f x ∂volume) =
      ∫ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin m))),
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
          Real.exp (-‖x.1‖ ^ 2 / 2)) • f x.1
          ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun x => ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
          Real.exp (-‖x‖ ^ 2 / 2)) • f x), restrict_compl_singleton]
    _ = ∫ p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ),
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
          Real.exp (-‖((homeomorphUnitSphereProd
            (EuclideanSpace ℝ (Fin m))).symm p).1‖ ^ 2 / 2)) •
          f (((homeomorphUnitSphereProd
            (EuclideanSpace ℝ (Fin m))).symm p).1)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere.prod
          (Measure.volumeIoiPow (m - 1))) := by
      simpa using
        (volume : Measure (EuclideanSpace ℝ (Fin m))).measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _)
          (fun p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ) =>
            ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
              Real.exp (-‖((homeomorphUnitSphereProd
                (EuclideanSpace ℝ (Fin m))).symm p).1‖ ^ 2 / 2)) •
              f (((homeomorphUnitSphereProd
                (EuclideanSpace ℝ (Fin m))).symm p).1))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      rw [homeomorphUnitSphereProd_symm_apply_coe]
      have hpSphere : ‖(p.1.1 : EuclideanSpace ℝ (Fin m))‖ = 1 := by
        have hp := p.1.2
        rw [mem_sphere_zero_iff_norm] at hp
        exact hp
      have hpRadius : 0 ≤ p.2.1 := p.2.2.le
      simp [norm_smul, abs_of_nonneg hpRadius, hpSphere]

theorem integral_volumeIoiPow_comp_subtype (n : ℕ) (g : ℝ → F) :
    ∫ r : Ioi (0 : ℝ), g r.1 ∂(Measure.volumeIoiPow n) =
      ∫ y in Ioi (0 : ℝ), y ^ n • g y := by
  rw [Measure.volumeIoiPow]
  simp only [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi
      (fun y : ℝ => Real.toNNReal (y ^ n) • g y)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change ((Real.toNNReal (y ^ n) : ℝ) • g y) = y ^ n • g y
    rw [Real.coe_toNNReal _ (pow_nonneg hy.le n)]
  · exact (measurable_subtype_coe.pow_const n).real_toNNReal

def gaussianAngularNormalization (m : ℕ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ m /
    ((2 : ℝ) ^ (1 - (m : ℝ) / 2) /
      Real.Gamma ((m : ℝ) / 2))

def gaussianSphereAverage (m : ℕ)
    (f : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → F) : F :=
  gaussianAngularNormalization m •
    ∫ ω, f ω ∂(volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere

theorem gaussianAngularNormalization_mul_sphereMass
    {m : ℕ} (hm : 0 < m) :
    gaussianAngularNormalization m *
        (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere.real Set.univ = 1 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hm)
  have hsphere :
      (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere.real Set.univ =
        (m : ℝ) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal := by
    rw [Measure.toSphere_real_apply_univ, Measure.real]
    simp
  have hconstant := gaussian_polar_constant m hm
  have hmpos : (0 : ℝ) < (m : ℝ) / 2 := by positivity
  have hGamma : 0 < Real.Gamma ((m : ℝ) / 2) :=
    Real.Gamma_pos_of_pos hmpos
  have hchi : (2 : ℝ) ^ (1 - (m : ℝ) / 2) /
      Real.Gamma ((m : ℝ) / 2) ≠ 0 := by positivity
  rw [gaussianAngularNormalization, hsphere]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ ^ m /
          ((2 : ℝ) ^ (1 - (m : ℝ) / 2) /
            Real.Gamma ((m : ℝ) / 2)) *
        ((m : ℝ) *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal) =
      ((m : ℝ) *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal *
        (Real.sqrt (2 * Real.pi))⁻¹ ^ m) /
          ((2 : ℝ) ^ (1 - (m : ℝ) / 2) /
            Real.Gamma ((m : ℝ) / 2)) := by ring
    _ = ((2 : ℝ) ^ (1 - (m : ℝ) / 2) /
          Real.Gamma ((m : ℝ) / 2)) /
        ((2 : ℝ) ^ (1 - (m : ℝ) / 2) /
          Real.Gamma ((m : ℝ) / 2)) := by rw [hconstant]
    _ = 1 := div_self hchi

theorem gaussianSphereAverage_const {m : ℕ} (hm : 0 < m)
    [CompleteSpace F] (v : F) :
    gaussianSphereAverage m (fun _ => v) = v := by
  rw [gaussianSphereAverage, integral_const]
  rw [smul_smul]
  change (gaussianAngularNormalization m *
    (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere.real Set.univ) • v = v
  rw [gaussianAngularNormalization_mul_sphereMass hm, one_smul]

theorem integral_stdGaussian_sphere_radius {m : ℕ} (hm : 0 < m)
    [CompleteSpace F]
    (f : EuclideanSpace ℝ (Fin m) → F)
    (hpolar : Integrable
      (fun p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ) =>
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
          Real.exp (-p.2.1 ^ 2 / 2)) • f (p.2.1 • p.1.1))
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere.prod
        (Measure.volumeIoiPow (m - 1)))) :
    ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) =
      ∫ y in Ioi (0 : ℝ), gaussianRadialDensity m y •
        gaussianSphereAverage m (fun ω => f (y • ω.1)) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [integral_stdGaussian_fullPolar hm f]
  rw [integral_prod_symm _ hpolar]
  simp_rw [integral_smul]
  rw [integral_volumeIoiPow_comp_subtype (F := F) (m - 1)
    (fun y => ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
      Real.exp (-y ^ 2 / 2)) •
        ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          f (y • ω.1)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  unfold gaussianRadialDensity gaussianSphereAverage
    gaussianAngularNormalization
  dsimp only
  rw [smul_smul, smul_smul]
  let I := ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
    f (y • ω.1) ∂(volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere
  change (y ^ (m - 1) *
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ m * Real.exp (-y ^ 2 / 2))) • I =
    ((2 : ℝ) ^ (1 - (m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2) *
      y ^ (m - 1) * Real.exp (-y ^ 2 / 2) *
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ m /
        ((2 : ℝ) ^ (1 - (m : ℝ) / 2) /
          Real.Gamma ((m : ℝ) / 2)))) • I
  congr 1
  have hmpos : (0 : ℝ) < (m : ℝ) / 2 := by positivity
  have hGamma : 0 < Real.Gamma ((m : ℝ) / 2) :=
    Real.Gamma_pos_of_pos hmpos
  have hchi : (2 : ℝ) ^ (1 - (m : ℝ) / 2) /
      Real.Gamma ((m : ℝ) / 2) ≠ 0 := by positivity
  field_simp

theorem integral_stdGaussian_radialTimeMixture
    {m : ℕ} (hm : 0 < m) [CompleteSpace F]
    (Q : EuclideanSpace ℝ (Fin m) → ℝ → F)
    (hradial : ∀ (ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1)
      (r : ℝ), 0 < r → ∀ t,
        Q (r • ω.1) t = Q ω.1 (r * t))
    (t : ℝ)
    (hpolar : Integrable
      (fun p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ) =>
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
          Real.exp (-p.2.1 ^ 2 / 2)) • Q (p.2.1 • p.1.1) t)
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere.prod
        (Measure.volumeIoiPow (m - 1)))) :
    ∫ x, Q x t ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) =
      ∫ r in Ioi (0 : ℝ), gaussianRadialDensity m r •
        gaussianSphereAverage m (fun ω => Q ω.1 (r * t)) := by
  rw [integral_stdGaussian_sphere_radius hm (fun x => Q x t) hpolar]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  unfold gaussianSphereAverage
  dsimp only
  apply congrArg (fun z : F =>
    gaussianRadialDensity m r • (gaussianAngularNormalization m • z))
  apply integral_congr_ae
  filter_upwards with ω
  exact hradial ω r hr (t)

end

end GaloisForLFunctions.HTGeometry

