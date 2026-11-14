import GaloisForLFunctions.HTGeometry.SphereBlockTail
import GaloisForLFunctions.HTGeometry.Probability.HomogeneousPolarIntegral
import GaloisForLFunctions.RHTower.Deninger.DeningerRadialIntegral

/-!
# Mellin moments of a complex coordinate on a sphere

Comparing Cartesian and polar Gaussian integration evaluates the spherical integral of
`‖z₁‖^(2s)` for every real `s > -1`. Negative exponents are included: positivity of the
computed integral also proves integrability. The orthogonal complement may have dimension zero.
-/

open MeasureTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The complex Gaussian Mellin integral, including integrable negative powers. -/
theorem integral_complex_norm_rpow_gaussian {s : ℝ} (hs : -1 < s) :
    (∫ z : ℂ, ‖z‖ ^ (2 * s) * Real.exp (-‖z‖ ^ 2)) =
      Real.pi * Real.Gamma (s + 1) := by
  rw [RHTower.deningerComplex_integral_norm
    (fun r => r ^ (2 * s) * Real.exp (-r ^ 2))]
  have he : (∫ r in Ioi (0 : ℝ), r * (r ^ (2 * s) * Real.exp (-r ^ 2))) =
      ∫ r in Ioi (0 : ℝ), r ^ (2 * s + 1) * Real.exp (-r ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [Real.rpow_add hr, Real.rpow_one]
    ring
  rw [he]
  have h := RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := 2 * s + 1) (by linarith only [hs]) (b := 1) zero_lt_one
  have ha : ((2 * s + 1) + 1) / 2 = s + 1 := by ring
  simp only [div_self one_ne_zero, Real.one_rpow, mul_one, neg_mul, one_mul, ha] at h
  rw [h]
  ring

section ComplexBlock

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A complex coordinate supplies at least two real dimensions. -/
theorem complexBlock_finrank_ge_two : 2 ≤ Module.finrank ℝ (BlockSpace ℂ V) := by
  rw [(WithLp.linearEquiv 2 ℝ (ℂ × V)).finrank_eq,
    Module.finrank_prod, Complex.finrank_real_complex]
  omega

variable [MeasurableSpace V] [BorelSpace V]

/-- The spherical measure has positive total mass, even for a zero-dimensional complement. -/
theorem complexBlock_sphere_mass_pos :
    0 < (volume.toSphere : Measure (sphere (0 : BlockSpace ℂ V) 1)).real univ :=
  unitSphere_volume_real_pos (BlockSpace ℂ V)

/-- Mellin moment of the squared complex-coordinate norm for normalized spherical measure. -/
def complexBlockSphereMellin (s : ℝ) : ℝ :=
  (∫ ω : sphere (0 : BlockSpace ℂ V) 1, ‖(ω.1 : BlockSpace ℂ V).fst‖ ^ (2 * s)
    ∂volume.toSphere) / (volume.toSphere : Measure (sphere (0 : BlockSpace ℂ V) 1)).real univ

/-- Cartesian factorization of a real-power complex-coordinate Gaussian moment. -/
theorem integral_complexBlock_rpow_gaussian {s : ℝ} (hs : -1 < s) :
    (∫ x : BlockSpace ℂ V, ‖x.fst‖ ^ (2 * s) * Real.exp (-‖x‖ ^ 2)) =
      Real.pi * Real.Gamma (s + 1) * ∫ y : V, Real.exp (-‖y‖ ^ 2) := by
  have he (x : BlockSpace ℂ V) :
      ‖x.fst‖ ^ (2 * s) * Real.exp (-‖x‖ ^ 2) =
        (‖x.fst‖ ^ (2 * s) * Real.exp (-‖x.fst‖ ^ 2)) * Real.exp (-‖x.snd‖ ^ 2) := by
    rw [WithLp.prod_norm_sq_eq_of_L2, neg_add, Real.exp_add]
    ring
  simp_rw [he]
  have hm := (WithLp.volume_preserving_ofLp ℂ V).integral_comp
    (MeasurableEquiv.toLp 2 (ℂ × V)).symm.measurableEmbedding
    (fun p : ℂ × V => (‖p.1‖ ^ (2 * s) * Real.exp (-‖p.1‖ ^ 2)) *
      Real.exp (-‖p.2‖ ^ 2))
  change (∫ x : BlockSpace ℂ V,
    (‖x.fst‖ ^ (2 * s) * Real.exp (-‖x.fst‖ ^ 2)) * Real.exp (-‖x.snd‖ ^ 2)) =
      ∫ p : ℂ × V, (‖p.1‖ ^ (2 * s) * Real.exp (-‖p.1‖ ^ 2)) *
        Real.exp (-‖p.2‖ ^ 2) at hm
  rw [hm, Measure.volume_eq_prod ℂ V,
    integral_prod_mul (fun z : ℂ => ‖z‖ ^ (2 * s) * Real.exp (-‖z‖ ^ 2))
      (fun y : V => Real.exp (-‖y‖ ^ 2)), integral_complex_norm_rpow_gaussian hs]

/-- Polar factorization of the same real-power moment. -/
theorem integral_complexBlock_rpow_gaussian_polar {s : ℝ} (hs : -1 < s) :
    (∫ x : BlockSpace ℂ V, ‖x.fst‖ ^ (2 * s) * Real.exp (-‖x‖ ^ 2)) =
      (∫ ω : sphere (0 : BlockSpace ℂ V) 1,
        ‖(ω.1 : BlockSpace ℂ V).fst‖ ^ (2 * s) ∂volume.toSphere) *
        (Real.Gamma ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2 + s) / 2) := by
  rw [integral_real_homogeneous_mul_gaussian
    (fun x : BlockSpace ℂ V => ‖x.fst‖ ^ (2 * s)) (2 * s) (by
      intro r hr x
      simp only [WithLp.smul_fst, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        Real.mul_rpow hr.le (norm_nonneg _)])]
  have hd : (2 : ℝ) ≤ Module.finrank ℝ (BlockSpace ℂ V) :=
    Nat.cast_le.mpr (complexBlock_finrank_ge_two V)
  have h := RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := (Module.finrank ℝ (BlockSpace ℂ V) : ℝ) - 1 + 2 * s)
    (by linarith only [hs, hd]) (b := 1) zero_lt_one
  have ha : (((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) - 1 + 2 * s) + 1) / 2 =
      (Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2 + s := by ring
  simp only [div_self one_ne_zero, Real.one_rpow, mul_one, neg_mul, one_mul, ha] at h
  rw [h]
  ring

/-- The exact normalized spherical Mellin transform of a complex coordinate. -/
theorem complexBlockSphereMellin_eq {s : ℝ} (hs : -1 < s) :
    complexBlockSphereMellin V s =
      Real.Gamma (s + 1) * Real.Gamma ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2) /
        Real.Gamma ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2 + s) := by
  have hzero := (integral_complexBlock_rpow_gaussian V (s := 0) (by norm_num)).symm.trans
    (integral_complexBlock_rpow_gaussian_polar V (s := 0) (by norm_num))
  have hsphere := (integral_complexBlock_rpow_gaussian V hs).symm.trans
    (integral_complexBlock_rpow_gaussian_polar V hs)
  simp only [zero_add, Real.Gamma_one, mul_one, add_zero, mul_zero, Real.rpow_zero,
    integral_const, smul_eq_mul] at hzero
  have hd : (2 : ℝ) ≤ Module.finrank ℝ (BlockSpace ℂ V) :=
    Nat.cast_le.mpr (complexBlock_finrank_ge_two V)
  have hGamma : Real.Gamma ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2 + s) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith only [hs, hd])).ne'
  unfold complexBlockSphereMellin
  apply (div_eq_div_iff (complexBlock_sphere_mass_pos V).ne' hGamma).mpr
  linear_combination -2 * hsphere + 2 * Real.Gamma (s + 1) * hzero

/-- Every Mellin moment in the range `s > -1` is positive. -/
theorem complexBlockSphereMellin_pos {s : ℝ} (hs : -1 < s) :
    0 < complexBlockSphereMellin V s := by
  rw [complexBlockSphereMellin_eq V hs]
  have hd : (2 : ℝ) ≤ Module.finrank ℝ (BlockSpace ℂ V) :=
    Nat.cast_le.mpr (complexBlock_finrank_ge_two V)
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos (by linarith only [hs]))
    (Real.Gamma_pos_of_pos (by linarith only [hd])))
    (Real.Gamma_pos_of_pos (by linarith only [hs, hd]))

/-- The coordinate singularity is integrable throughout the range `s > -1`. -/
theorem integrable_complexBlock_sphere_rpow {s : ℝ} (hs : -1 < s) :
    Integrable (fun ω : sphere (0 : BlockSpace ℂ V) 1 =>
      ‖(ω.1 : BlockSpace ℂ V).fst‖ ^ (2 * s)) volume.toSphere := by
  by_contra h
  have hp := complexBlockSphereMellin_pos V hs
  rw [complexBlockSphereMellin, integral_undef h, zero_div] at hp
  exact (lt_irrefl 0) hp

end ComplexBlock

end GaloisForLFunctions.HTGeometry
