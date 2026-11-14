import GaloisForLFunctions.HTGeometry.SphereBlockTail
import GaloisForLFunctions.HTGeometry.Probability.HomogeneousPolarIntegral

/-!
# Mellin moments of an orthogonal block on a sphere

For a nonzero real block `U` and an orthogonal complement `V`, normalized spherical moments
of the squared block radius are Gamma quotients with parameters `dim(U)/2` and `dim(V)/2`.
Cartesian Gaussian factorization and polar integration prove the formula without choosing a basis.
-/

open MeasureTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

section Block

variable (U V : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The real dimension of an orthogonal sum is the sum of its block dimensions. -/
theorem blockSpace_finrank :
    Module.finrank ℝ (BlockSpace U V) = Module.finrank ℝ U + Module.finrank ℝ V := by
  rw [(WithLp.linearEquiv 2 ℝ (U × V)).finrank_eq, Module.finrank_prod]

variable [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]

/-- A Gaussian profile separates along an orthogonal direct sum. -/
theorem integral_block_gaussian_factor (f : U → ℝ) :
    (∫ x : BlockSpace U V, f x.fst * Real.exp (-‖x‖ ^ 2)) =
      (∫ u : U, f u * Real.exp (-‖u‖ ^ 2)) * ∫ v : V, Real.exp (-‖v‖ ^ 2) := by
  have he (x : BlockSpace U V) :
      f x.fst * Real.exp (-‖x‖ ^ 2) =
        (f x.fst * Real.exp (-‖x.fst‖ ^ 2)) * Real.exp (-‖x.snd‖ ^ 2) := by
    rw [WithLp.prod_norm_sq_eq_of_L2, neg_add, Real.exp_add]
    ring
  simp_rw [he]
  have hm := (WithLp.volume_preserving_ofLp U V).integral_comp
    (MeasurableEquiv.toLp 2 (U × V)).symm.measurableEmbedding
    (fun p : U × V => (f p.1 * Real.exp (-‖p.1‖ ^ 2)) * Real.exp (-‖p.2‖ ^ 2))
  change (∫ x : BlockSpace U V,
    (f x.fst * Real.exp (-‖x.fst‖ ^ 2)) * Real.exp (-‖x.snd‖ ^ 2)) =
      ∫ p : U × V, (f p.1 * Real.exp (-‖p.1‖ ^ 2)) * Real.exp (-‖p.2‖ ^ 2) at hm
  rw [hm, Measure.volume_eq_prod U V,
    integral_prod_mul (fun u : U => f u * Real.exp (-‖u‖ ^ 2))
      (fun v : V => Real.exp (-‖v‖ ^ 2))]

/-- Mellin moment of the squared block radius on the normalized sphere. -/
def blockSphereMellin (s : ℝ) : ℝ :=
  (∫ ω : sphere (0 : BlockSpace U V) 1, ‖(ω.1 : BlockSpace U V).fst‖ ^ (2 * s)
    ∂volume.toSphere) / (volume.toSphere : Measure (sphere (0 : BlockSpace U V) 1)).real univ

variable [Nontrivial U]

/-- Polar factorization of a block Gaussian moment. -/
theorem integral_block_rpow_gaussian_polar {s : ℝ}
    (hs : -(Module.finrank ℝ U : ℝ) / 2 < s) :
    (∫ x : BlockSpace U V, ‖x.fst‖ ^ (2 * s) * Real.exp (-‖x‖ ^ 2)) =
      (∫ ω : sphere (0 : BlockSpace U V) 1, ‖(ω.1 : BlockSpace U V).fst‖ ^ (2 * s)
        ∂volume.toSphere) *
          (Real.Gamma ((Module.finrank ℝ (BlockSpace U V) : ℝ) / 2 + s) / 2) := by
  rw [integral_real_homogeneous_mul_gaussian
    (fun x : BlockSpace U V => ‖x.fst‖ ^ (2 * s)) (2 * s) (by
      intro r hr x
      simp only [WithLp.smul_fst, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        Real.mul_rpow hr.le (norm_nonneg _)])]
  have hd : (Module.finrank ℝ U : ℝ) ≤ Module.finrank ℝ (BlockSpace U V) := by
    rw [blockSpace_finrank, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have h := RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := (Module.finrank ℝ (BlockSpace U V) : ℝ) - 1 + 2 * s)
    (by linarith only [hs, hd]) (b := 1) zero_lt_one
  have he : (((Module.finrank ℝ (BlockSpace U V) : ℝ) - 1 + 2 * s) + 1) / 2 =
      (Module.finrank ℝ (BlockSpace U V) : ℝ) / 2 + s := by ring
  simp only [div_self one_ne_zero, Real.one_rpow, mul_one, neg_mul, one_mul, he] at h
  rw [h]
  ring

/-- Exact normalized block moments, valid up to the block's inverse-power threshold. -/
theorem blockSphereMellin_eq {s : ℝ} (hs : -(Module.finrank ℝ U : ℝ) / 2 < s) :
    blockSphereMellin U V s =
      Real.Gamma ((Module.finrank ℝ U : ℝ) / 2 + s) *
        Real.Gamma ((Module.finrank ℝ (BlockSpace U V) : ℝ) / 2) /
      (Real.Gamma ((Module.finrank ℝ U : ℝ) / 2) *
        Real.Gamma ((Module.finrank ℝ (BlockSpace U V) : ℝ) / 2 + s)) := by
  have ha : 0 < (Module.finrank ℝ U : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos
  have hzero := (integral_block_gaussian_factor U V (fun u => ‖u‖ ^ (2 * (0 : ℝ)))).symm.trans
    (integral_block_rpow_gaussian_polar U V (s := 0) (by linarith only [ha]))
  have hmoment := (integral_block_gaussian_factor U V (fun u => ‖u‖ ^ (2 * s))).symm.trans
    (integral_block_rpow_gaussian_polar U V hs)
  rw [integral_norm_rpow_gaussian_polar U (s := 0) (by linarith only [ha])] at hzero
  rw [integral_norm_rpow_gaussian_polar U hs] at hmoment
  simp only [mul_zero, Real.rpow_zero, add_zero, integral_const, smul_eq_mul, mul_one] at hzero
  have hd : (Module.finrank ℝ U : ℝ) ≤ Module.finrank ℝ (BlockSpace U V) := by
    rw [blockSpace_finrank, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hG : Real.Gamma ((Module.finrank ℝ (BlockSpace U V) : ℝ) / 2 + s) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith only [hs, hd])).ne'
  have hA : Real.Gamma ((Module.finrank ℝ U : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  unfold blockSphereMellin
  apply (div_eq_div_iff (unitSphere_volume_real_pos (BlockSpace U V)).ne' (mul_ne_zero hA hG)).mpr
  linear_combination -2 * Real.Gamma ((Module.finrank ℝ U : ℝ) / 2) * hmoment +
    2 * Real.Gamma ((Module.finrank ℝ U : ℝ) / 2 + s) * hzero

/-- Every moment in the admissible inverse-power range is positive. -/
theorem blockSphereMellin_pos {s : ℝ} (hs : -(Module.finrank ℝ U : ℝ) / 2 < s) :
    0 < blockSphereMellin U V s := by
  rw [blockSphereMellin_eq U V hs]
  have ha : 0 < (Module.finrank ℝ U : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos
  have hd : (Module.finrank ℝ U : ℝ) ≤ Module.finrank ℝ (BlockSpace U V) := by
    rw [blockSpace_finrank, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  exact div_pos
    (mul_pos (Real.Gamma_pos_of_pos (by linarith only [hs]))
      (Real.Gamma_pos_of_pos (by linarith only [ha, hd])))
    (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos (by linarith only [hs, hd])))

/-- Negative block powers are integrable whenever their degree is greater than minus the
real block dimension. -/
theorem integrable_blockSphere_rpow {s : ℝ} (hs : -(Module.finrank ℝ U : ℝ) / 2 < s) :
    Integrable (fun ω : sphere (0 : BlockSpace U V) 1 =>
      ‖(ω.1 : BlockSpace U V).fst‖ ^ (2 * s)) volume.toSphere := by
  by_contra h
  have hp := blockSphereMellin_pos U V hs
  rw [blockSphereMellin, integral_undef h, zero_div] at hp
  exact (lt_irrefl 0) hp

end Block

end GaloisForLFunctions.HTGeometry
