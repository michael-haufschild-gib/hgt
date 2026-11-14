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
    (sig := ((2 * k + 1 : ℕ) : ℝ))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
    (b := 1) zero_lt_one
  have he : (((2 * k + 1 : ℕ) : ℝ) + 1) / 2 = (k : ℝ) + 1 := by
    push_cast
    ring
  simp only [Real.rpow_natCast, he, div_self one_ne_zero, Real.one_rpow,
    mul_one, neg_mul, one_mul, Real.Gamma_nat_eq_factorial] at h
  convert h using 1
  ring

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
        have hp :=
          (volume : Measure E).measurePreserving_homeomorphUnitSphereProd.integral_comp
            (Homeomorph.measurableEmbedding _)
            (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
              F (((homeomorphUnitSphereProd E).symm p).1))
        simp only [Homeomorph.symm_apply_apply] at hp
        simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hp
  change (∫ x, F x) = _
  rw [hpolar]
  have he : (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => F (p.2.1 • p.1.1)) =
      fun p => g p.1.1 * (p.2.1 ^ k * Real.exp (-p.2.1 ^ 2)) := by
    funext p
    have hnorm : ‖(p.1.1 : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    have hr : (0 : ℝ) < p.2.1 := p.2.2
    simp only [F, hg _ hr, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, hnorm, mul_one]
    ring
  rw [he, integral_prod_mul (fun ω : sphere (0 : E) 1 => g ω.1)
    (fun r : Ioi (0 : ℝ) => r.1 ^ k * Real.exp (-r.1 ^ 2)),
    integral_volumeIoiPow_comp_subtype (Module.finrank ℝ E - 1)
      (fun r : ℝ => r ^ k * Real.exp (-r ^ 2))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  simp only [smul_eq_mul, pow_add]
  ring

/-- The radial factor in real dimension `d` for a homogeneous observable of degree `2k`. -/
theorem integral_Ioi_dimension_pow_gaussian {d : ℕ} (hd : 0 < d) (k : ℕ) :
    (∫ r in Ioi (0 : ℝ), r ^ (d - 1 + 2 * k) * Real.exp (-r ^ 2)) =
      Real.Gamma ((d : ℝ) / 2 + k) / 2 := by
  have h := RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := ((d - 1 + 2 * k : ℕ) : ℝ))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
    (b := 1) zero_lt_one
  have he : (((d - 1 + 2 * k : ℕ) : ℝ) + 1) / 2 = (d : ℝ) / 2 + k := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    ring
  simp only [Real.rpow_natCast, he, div_self one_ne_zero, Real.one_rpow,
    mul_one, neg_mul, one_mul] at h
  convert h using 1
  ring

section ComplexBlock

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- Moment of the squared norm of a complex coordinate on the normalized unit sphere. -/
def complexBlockSphereMoment (k : ℕ) : ℝ :=
  (∫ ω : sphere (0 : BlockSpace ℂ V) 1, ‖(ω.1 : BlockSpace ℂ V).fst‖ ^ (2 * k)
    ∂volume.toSphere) / (volume.toSphere : Measure (sphere (0 : BlockSpace ℂ V) 1)).real univ

/-- Cartesian factorization of the complex-coordinate Gaussian moment. -/
theorem integral_complexBlock_gaussian (k : ℕ) :
    (∫ x : BlockSpace ℂ V, ‖x.fst‖ ^ (2 * k) * Real.exp (-‖x‖ ^ 2)) =
      Real.pi * (k.factorial : ℝ) * ∫ y : V, Real.exp (-‖y‖ ^ 2) := by
  have he (x : BlockSpace ℂ V) :
      ‖x.fst‖ ^ (2 * k) * Real.exp (-‖x‖ ^ 2) =
        (‖x.fst‖ ^ (2 * k) * Real.exp (-‖x.fst‖ ^ 2)) *
          Real.exp (-‖x.snd‖ ^ 2) := by
    rw [WithLp.prod_norm_sq_eq_of_L2, neg_add, Real.exp_add]
    ring
  simp_rw [he]
  have hm := (WithLp.volume_preserving_ofLp ℂ V).integral_comp
    (MeasurableEquiv.toLp 2 (ℂ × V)).symm.measurableEmbedding
    (fun p : ℂ × V => (‖p.1‖ ^ (2 * k) * Real.exp (-‖p.1‖ ^ 2)) *
      Real.exp (-‖p.2‖ ^ 2))
  change (∫ x : BlockSpace ℂ V,
    (‖x.fst‖ ^ (2 * k) * Real.exp (-‖x.fst‖ ^ 2)) * Real.exp (-‖x.snd‖ ^ 2)) =
      ∫ p : ℂ × V, (‖p.1‖ ^ (2 * k) * Real.exp (-‖p.1‖ ^ 2)) *
        Real.exp (-‖p.2‖ ^ 2) at hm
  rw [hm, Measure.volume_eq_prod ℂ V,
    integral_prod_mul (fun z : ℂ => ‖z‖ ^ (2 * k) * Real.exp (-‖z‖ ^ 2))
      (fun y : V => Real.exp (-‖y‖ ^ 2)),
    integral_complex_norm_even_pow_gaussian]

/-- Polar factorization of the same moment. -/
theorem integral_complexBlock_gaussian_polar (k : ℕ) :
    (∫ x : BlockSpace ℂ V, ‖x.fst‖ ^ (2 * k) * Real.exp (-‖x‖ ^ 2)) =
      (∫ ω : sphere (0 : BlockSpace ℂ V) 1,
        ‖(ω.1 : BlockSpace ℂ V).fst‖ ^ (2 * k) ∂volume.toSphere) *
        (Real.Gamma ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2 + k) / 2) := by
  haveI := nontrivial_blockSpace ℂ V
  rw [integral_homogeneous_mul_gaussian (fun x : BlockSpace ℂ V => ‖x.fst‖ ^ (2 * k))
    (2 * k) (by
      intro r hr x
      simp only [WithLp.smul_fst, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]),
    integral_Ioi_dimension_pow_gaussian Module.finrank_pos]

/-- The exact normalized sphere moments, obtained by cancelling the Gaussian radial factor. -/
theorem complexBlockSphereMoment_eq (k : ℕ) :
    complexBlockSphereMoment V k =
      (k.factorial : ℝ) * Real.Gamma ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2) /
        Real.Gamma ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2 + k) := by
  haveI := nontrivial_blockSpace ℂ V
  have hzero := (integral_complexBlock_gaussian V 0).symm.trans
    (integral_complexBlock_gaussian_polar V 0)
  have hk := (integral_complexBlock_gaussian V k).symm.trans
    (integral_complexBlock_gaussian_polar V k)
  simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, mul_one, add_zero,
    Nat.mul_zero, pow_zero, integral_const, smul_eq_mul] at hzero
  have hdim : 0 < (Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2 := by
    exact div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos
  have hGamma : Real.Gamma ((Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2 + k) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos_of_pos_of_nonneg hdim (Nat.cast_nonneg k))).ne'
  have hmass : (volume.toSphere : Measure (sphere (0 : BlockSpace ℂ V) 1)).real univ ≠ 0 :=
    (toSphere_univ_toReal_pos ℂ V).ne'
  unfold complexBlockSphereMoment
  apply (div_eq_div_iff hmass hGamma).mpr
  linear_combination -2 * hk + 2 * (k.factorial : ℝ) * hzero

end ComplexBlock

end GaloisForLFunctions.HTGeometry
