import GaloisForLFunctions.HTGeometry.Probability.BlockSphereMellin
import GaloisForLFunctions.HTGeometry.BetaGammaFactorization
import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-!
# Beta laws of orthogonal spherical projections

For nonzero orthogonal real blocks `U` and `V`, the squared `U`-radius of a uniformly
distributed unit vector has law `Beta(dim(U)/2, dim(V)/2)`. Power weighting shifts the first
shape parameter, and the mean transverse squared radius is the complementary shape divided
by the sum of the shifted shapes.
-/

open MeasureTheory ProbabilityTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

section Coordinate

variable (U V : Type*) [NormedAddCommGroup U] [NormedAddCommGroup V]

/-- Squared radius of the first orthogonal block on the unit sphere. -/
def blockSphereCoordinate (ω : sphere (0 : BlockSpace U V) 1) : ℝ :=
  ‖(ω.1 : BlockSpace U V).fst‖ ^ 2

theorem continuous_blockSphereCoordinate : Continuous (blockSphereCoordinate U V) := by
  unfold blockSphereCoordinate
  fun_prop

/-- A squared block radius lies in `[0,1]`. -/
theorem blockSphereCoordinate_mem (ω : sphere (0 : BlockSpace U V) 1) :
    blockSphereCoordinate U V ω ∈ Icc (0 : ℝ) 1 := by
  have hnorm : ‖(ω.1 : BlockSpace U V)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (ω.1 : BlockSpace U V)
  rw [hnorm, one_pow] at hsq
  exact ⟨sq_nonneg _, by
    change ‖(ω.1 : BlockSpace U V).fst‖ ^ 2 ≤ 1
    linarith only [hsq, sq_nonneg ‖(ω.1 : BlockSpace U V).snd‖]⟩

variable [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Law of the squared block radius under normalized surface measure. -/
def blockCoordinateLaw : Measure ℝ :=
  ((volume.toSphere : Measure (sphere (0 : BlockSpace U V) 1)) univ)⁻¹ •
    Measure.map (blockSphereCoordinate U V) volume.toSphere

instance blockCoordinateLaw_isProbability [Nontrivial U] :
    IsProbabilityMeasure (blockCoordinateLaw U V) where
  measure_univ := by
    have hmass : (volume.toSphere : Measure (sphere (0 : BlockSpace U V) 1)) univ ≠ 0 := by
      intro hzero
      have hp := unitSphere_volume_real_pos (BlockSpace U V)
      simp only [Measure.real, hzero, ENNReal.toReal_zero] at hp
      exact (lt_irrefl 0) hp
    rw [blockCoordinateLaw, Measure.smul_apply,
      Measure.map_apply (continuous_blockSphereCoordinate U V).measurable MeasurableSet.univ,
      Set.preimage_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass (measure_ne_top _ _)

/-- The block-coordinate law is carried by the unit interval. -/
theorem blockCoordinateLaw_carried : blockCoordinateLaw U V (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [blockCoordinateLaw, Measure.smul_apply,
    Measure.map_apply (continuous_blockSphereCoordinate U V).measurable measurableSet_Icc.compl]
  have he : (blockSphereCoordinate U V) ⁻¹' (Icc (0 : ℝ) 1)ᶜ = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact blockSphereCoordinate_mem U V ω
  rw [he, measure_empty, smul_zero]

theorem integrable_blockCoordinateLaw_pow [Nontrivial U] (k : ℕ) :
    Integrable (fun u : ℝ => u ^ k) (blockCoordinateLaw U V) := by
  have hmem : ∀ᵐ u ∂blockCoordinateLaw U V, u ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact blockCoordinateLaw_carried U V
  refine Integrable.of_bound (C := 1) (by fun_prop) ?_
  filter_upwards [hmem] with u hu
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hu.1]
  exact pow_le_one₀ hu.1 hu.2

/-- The coordinate law's moments coincide with the normalized spherical Mellin moments. -/
theorem integral_blockCoordinateLaw_pow (k : ℕ) :
    (∫ u : ℝ, u ^ k ∂blockCoordinateLaw U V) = blockSphereMellin U V k := by
  rw [blockCoordinateLaw, integral_smul_measure,
    integral_map (continuous_blockSphereCoordinate U V).measurable.aemeasurable (by fun_prop),
    ENNReal.toReal_inv, smul_eq_mul]
  have he : (fun ω : sphere (0 : BlockSpace U V) 1 => blockSphereCoordinate U V ω ^ k) =
      fun ω => ‖(ω.1 : BlockSpace U V).fst‖ ^ (2 * (k : ℝ)) := by
    funext ω
    rw [blockSphereCoordinate, ← pow_mul, ← Real.rpow_natCast]
    push_cast
    rfl
  rw [he]
  unfold blockSphereMellin
  rw [div_eq_mul_inv, mul_comm]
  rfl

end Coordinate

section Beta

variable (U V : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [Nontrivial U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- Exact beta distribution of a squared orthogonal projection of a uniform unit vector. -/
theorem blockCoordinateLaw_eq_beta :
    blockCoordinateLaw U V =
      betaMeasure ((Module.finrank ℝ U : ℝ) / 2) ((Module.finrank ℝ V : ℝ) / 2) := by
  have ha : 0 < (Module.finrank ℝ U : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos
  have hb : 0 < (Module.finrank ℝ V : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos
  haveI := betaMeasure_isProbability ha hb
  have hdim : (Module.finrank ℝ (BlockSpace U V) : ℝ) / 2 =
      (Module.finrank ℝ U : ℝ) / 2 + (Module.finrank ℝ V : ℝ) / 2 := by
    rw [blockSpace_finrank, Nat.cast_add, add_div]
  apply _root_.HTGeometry.measure_eq_of_moments_eq_of_one_carried
    (s := fun k => blockSphereMellin U V k) (c := 1 / 2) (r := 1 / 2) (by norm_num)
    (by simpa only [show (1 / 2 : ℝ) - 1 / 2 = 0 by norm_num,
      show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using blockCoordinateLaw_carried U V)
  · exact fun k => (integral_blockCoordinateLaw_pow U V k).symm
  · exact integrable_blockCoordinateLaw_pow U V
  · intro k
    rw [blockSphereMellin_eq U V (by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith only [ha, hk]), hdim, integral_pow_betaMeasure ha hb]
  · exact fun k => integrable_pow_betaMeasure ha hb k

/-- Normalized power weighting of the block-coordinate law. -/
def blockCoordinateTilt (k : ℕ) : Measure ℝ :=
  (blockCoordinateLaw U V).withDensity
    (fun u => ENNReal.ofReal (u ^ k / blockSphereMellin U V k))

/-- A degree-`k` power tilt adds `k` to the block's beta shape. -/
theorem blockCoordinateTilt_eq_beta (k : ℕ) :
    blockCoordinateTilt U V k =
      betaMeasure ((Module.finrank ℝ U : ℝ) / 2 + k) ((Module.finrank ℝ V : ℝ) / 2) := by
  unfold blockCoordinateTilt
  rw [← integral_blockCoordinateLaw_pow, blockCoordinateLaw_eq_beta]
  exact withDensity_pow_betaMeasure
    (div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos)
    (div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos) k

/-- Exact transverse squared radius under the power-tilted spherical law. -/
theorem integral_blockCoordinateTilt_transverse (k : ℕ) :
    (∫ u : ℝ, 1 - u ∂blockCoordinateTilt U V k) =
      ((Module.finrank ℝ V : ℝ) / 2) /
        ((Module.finrank ℝ U : ℝ) / 2 + k + (Module.finrank ℝ V : ℝ) / 2) := by
  have ha : 0 < (Module.finrank ℝ U : ℝ) / 2 + k :=
    add_pos_of_pos_of_nonneg (div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos) (Nat.cast_nonneg k)
  have hb : 0 < (Module.finrank ℝ V : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos
  haveI := betaMeasure_isProbability ha hb
  have hi : Integrable (fun u : ℝ => u)
      (betaMeasure ((Module.finrank ℝ U : ℝ) / 2 + k) ((Module.finrank ℝ V : ℝ) / 2)) := by
    simpa only [pow_one] using integrable_pow_betaMeasure ha hb 1
  rw [blockCoordinateTilt_eq_beta, integral_sub (integrable_const 1) hi,
    integral_const, probReal_univ, one_smul, integral_id_betaMeasure ha hb]
  have hden : (Module.finrank ℝ U : ℝ) / 2 + k + (Module.finrank ℝ V : ℝ) / 2 ≠ 0 :=
    (add_pos ha hb).ne'
  field_simp
  ring

end Beta

end GaloisForLFunctions.HTGeometry
