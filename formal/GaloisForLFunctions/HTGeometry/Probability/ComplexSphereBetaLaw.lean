import GaloisForLFunctions.HTGeometry.Probability.ComplexSphereMellin
import GaloisForLFunctions.HTGeometry.BetaGammaFactorization
import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-!
# The beta law of a complex spherical coordinate

The squared norm of a complex coordinate on the normalized sphere has law
`Beta(1, dim(V)/2)`, where `V` is its nonzero real orthogonal complement.
Compact moment determinacy upgrades the Gaussian moment calculation to an equality of measures.
Power weighting then gives exact concentration laws for high coordinate monomials.
-/

open MeasureTheory ProbabilityTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

section Coordinate

variable (V : Type*) [NormedAddCommGroup V]

/-- Squared complex-coordinate modulus on the unit sphere. -/
def complexBlockSphereCoordinate (ω : sphere (0 : BlockSpace ℂ V) 1) : ℝ :=
  ‖(ω.1 : BlockSpace ℂ V).fst‖ ^ 2

theorem continuous_complexBlockSphereCoordinate : Continuous (complexBlockSphereCoordinate V) := by
  unfold complexBlockSphereCoordinate
  fun_prop

/-- The squared coordinate lies in the unit interval. -/
theorem complexBlockSphereCoordinate_mem (ω : sphere (0 : BlockSpace ℂ V) 1) :
    complexBlockSphereCoordinate V ω ∈ Icc (0 : ℝ) 1 := by
  have hnorm : ‖(ω.1 : BlockSpace ℂ V)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (ω.1 : BlockSpace ℂ V)
  rw [hnorm, one_pow] at hsq
  exact ⟨sq_nonneg _, by
    change ‖(ω.1 : BlockSpace ℂ V).fst‖ ^ 2 ≤ 1
    linarith only [hsq, sq_nonneg ‖(ω.1 : BlockSpace ℂ V).snd‖]⟩

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Probability law of the squared coordinate under normalized spherical measure. -/
def complexBlockCoordinateLaw : Measure ℝ :=
  ((volume.toSphere : Measure (sphere (0 : BlockSpace ℂ V) 1)) univ)⁻¹ •
    Measure.map (complexBlockSphereCoordinate V) volume.toSphere

instance complexBlockCoordinateLaw_isProbability : IsProbabilityMeasure (complexBlockCoordinateLaw V) where
  measure_univ := by
    have hmass : (volume.toSphere : Measure (sphere (0 : BlockSpace ℂ V) 1)) univ ≠ 0 := by
      intro hzero
      have hp := complexBlock_sphere_mass_pos V
      simp only [Measure.real, hzero, ENNReal.toReal_zero] at hp
      exact (lt_irrefl 0) hp
    rw [complexBlockCoordinateLaw, Measure.smul_apply,
      Measure.map_apply (continuous_complexBlockSphereCoordinate V).measurable MeasurableSet.univ,
      Set.preimage_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass (measure_ne_top _ _)

/-- The coordinate law is carried by `[0,1]`. -/
theorem complexBlockCoordinateLaw_carried :
    complexBlockCoordinateLaw V (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [complexBlockCoordinateLaw, Measure.smul_apply,
    Measure.map_apply (continuous_complexBlockSphereCoordinate V).measurable measurableSet_Icc.compl]
  have he : (complexBlockSphereCoordinate V) ⁻¹' (Icc (0 : ℝ) 1)ᶜ = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact complexBlockSphereCoordinate_mem V ω
  rw [he, measure_empty, smul_zero]

/-- All coordinate moments are integrable, since the coordinate lies in a compact interval. -/
theorem integrable_complexBlockCoordinateLaw_pow (k : ℕ) :
    Integrable (fun u : ℝ => u ^ k) (complexBlockCoordinateLaw V) := by
  have hmem : ∀ᵐ u ∂complexBlockCoordinateLaw V, u ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact complexBlockCoordinateLaw_carried V
  refine Integrable.of_bound (C := 1) (by fun_prop) ?_
  filter_upwards [hmem] with u hu
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hu.1]
  exact pow_le_one₀ hu.1 hu.2

/-- Moments of the coordinate probability law are the spherical Mellin moments. -/
theorem integral_complexBlockCoordinateLaw_pow (k : ℕ) :
    (∫ u : ℝ, u ^ k ∂complexBlockCoordinateLaw V) = complexBlockSphereMellin V k := by
  rw [complexBlockCoordinateLaw, integral_smul_measure,
    integral_map (continuous_complexBlockSphereCoordinate V).measurable.aemeasurable (by fun_prop),
    ENNReal.toReal_inv, smul_eq_mul]
  have he : (fun ω : sphere (0 : BlockSpace ℂ V) 1 => complexBlockSphereCoordinate V ω ^ k) =
      fun ω => ‖(ω.1 : BlockSpace ℂ V).fst‖ ^ (2 * (k : ℝ)) := by
    funext ω
    rw [complexBlockSphereCoordinate, ← pow_mul, ← Real.rpow_natCast]
    push_cast
    rfl
  rw [he]
  unfold complexBlockSphereMellin
  rw [div_eq_mul_inv, mul_comm]
  rfl

end Coordinate

section Beta

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- The full squared-coordinate law is beta, in every real dimension with a nonzero complement. -/
theorem complexBlockCoordinateLaw_eq_beta :
    complexBlockCoordinateLaw V = betaMeasure 1 ((Module.finrank ℝ V : ℝ) / 2) := by
  have hb : 0 < (Module.finrank ℝ V : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos
  haveI := betaMeasure_isProbability zero_lt_one hb
  have hdim : (Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / 2 =
      1 + (Module.finrank ℝ V : ℝ) / 2 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℂ × V)).finrank_eq,
      Module.finrank_prod, Complex.finrank_real_complex]
    push_cast
    ring
  apply _root_.HTGeometry.measure_eq_of_moments_eq_of_one_carried
    (s := fun k => complexBlockSphereMellin V k) (c := 1 / 2) (r := 1 / 2) (by norm_num)
    (by simpa only [show (1 / 2 : ℝ) - 1 / 2 = 0 by norm_num,
      show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using complexBlockCoordinateLaw_carried V)
  · exact fun k => (integral_complexBlockCoordinateLaw_pow V k).symm
  · exact integrable_complexBlockCoordinateLaw_pow V
  · intro k
    rw [complexBlockSphereMellin_eq V (by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith only [hk]), hdim, integral_pow_betaMeasure zero_lt_one hb,
      Real.Gamma_one, one_mul, add_comm (k : ℝ) 1]
  · exact fun k => integrable_pow_betaMeasure zero_lt_one hb k

/-- The normalized monomial-power tilt of the squared-coordinate law. -/
def complexBlockCoordinateTilt (k : ℕ) : Measure ℝ :=
  (complexBlockCoordinateLaw V).withDensity
    (fun u => ENNReal.ofReal (u ^ k / complexBlockSphereMellin V k))

/-- Weighting by `|z₁|^(2k)` shifts the first beta parameter from `1` to `k+1`. -/
theorem complexBlockCoordinateTilt_eq_beta (k : ℕ) :
    complexBlockCoordinateTilt V k =
      betaMeasure (1 + (k : ℝ)) ((Module.finrank ℝ V : ℝ) / 2) := by
  unfold complexBlockCoordinateTilt
  rw [← integral_complexBlockCoordinateLaw_pow, complexBlockCoordinateLaw_eq_beta]
  exact withDensity_pow_betaMeasure zero_lt_one
    (div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos) k

/-- Exact mean transverse squared radius under a high-coordinate-power tilt. -/
theorem integral_complexBlockCoordinateTilt_transverse (k : ℕ) :
    (∫ u : ℝ, 1 - u ∂complexBlockCoordinateTilt V k) =
      ((Module.finrank ℝ V : ℝ) / 2) /
        (1 + (k : ℝ) + (Module.finrank ℝ V : ℝ) / 2) := by
  have ha : 0 < 1 + (k : ℝ) := by positivity
  have hb : 0 < (Module.finrank ℝ V : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr Module.finrank_pos) two_pos
  haveI := betaMeasure_isProbability ha hb
  have hi : Integrable (fun u : ℝ => u)
      (betaMeasure (1 + (k : ℝ)) ((Module.finrank ℝ V : ℝ) / 2)) := by
    simpa only [pow_one] using integrable_pow_betaMeasure ha hb 1
  rw [complexBlockCoordinateTilt_eq_beta, integral_sub (integrable_const 1) hi,
    integral_const, probReal_univ, one_smul, integral_id_betaMeasure ha hb]
  have hden : 1 + (k : ℝ) + (Module.finrank ℝ V : ℝ) / 2 ≠ 0 := (add_pos ha hb).ne'
  field_simp
  ring

end Beta

end GaloisForLFunctions.HTGeometry
