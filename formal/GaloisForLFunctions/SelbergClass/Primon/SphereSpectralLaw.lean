import GaloisForLFunctions.HTGeometry.Probability.BlockSphereBetaLaw
import GaloisForLFunctions.HTGeometry.SphereMeasureIsometryInvariance
import GaloisForLFunctions.SelbergClass.Primon.SemicircleBetaLaw

/-!
# The scalar Fock law as a spherical coordinate law

Twice a real coordinate of a uniform vector on the unit three-sphere has the semicircle
spectral law. The squared coordinate follows `Beta(1/2,3/2)` by orthogonal block projection;
antipodal invariance supplies the vanishing odd moments. Compact moment determinacy then
identifies the full signed law with the scalar free Fock spectral law.
-/

open MeasureTheory ProbabilityTheory Set Metric
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.SelbergClass.Primon

/-- Euclidean four-space split into a real coordinate and its orthogonal complement. -/
abbrev SphereSpectralSpace := BlockSpace ℝ (EuclideanSpace ℝ (Fin 3))

/-- Twice the first real coordinate on the unit three-sphere. -/
def sphereThreeHeckeCoordinate (ω : sphere (0 : SphereSpectralSpace) 1) : ℝ :=
  2 * (ω.1 : SphereSpectralSpace).fst

theorem continuous_sphereThreeHeckeCoordinate : Continuous sphereThreeHeckeCoordinate := by
  unfold sphereThreeHeckeCoordinate
  fun_prop

/-- The signed coordinate law under normalized surface measure. -/
def sphereThreeSpectralLaw : Measure ℝ :=
  ((volume.toSphere : Measure (sphere (0 : SphereSpectralSpace) 1)) univ)⁻¹ •
    Measure.map sphereThreeHeckeCoordinate volume.toSphere

instance sphereThreeSpectralLaw_isProbability : IsProbabilityMeasure sphereThreeSpectralLaw where
  measure_univ := by
    have hmass : (volume.toSphere : Measure (sphere (0 : SphereSpectralSpace) 1)) univ ≠ 0 := by
      intro hzero
      have hp := unitSphere_volume_real_pos SphereSpectralSpace
      simp only [Measure.real, hzero, ENNReal.toReal_zero] at hp
      exact (lt_irrefl 0) hp
    rw [sphereThreeSpectralLaw, Measure.smul_apply,
      Measure.map_apply continuous_sphereThreeHeckeCoordinate.measurable MeasurableSet.univ,
      Set.preimage_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass (measure_ne_top _ _)

/-- The spherical Hecke coordinate lies in the spectral interval. -/
theorem sphereThreeHeckeCoordinate_mem (ω : sphere (0 : SphereSpectralSpace) 1) :
    sphereThreeHeckeCoordinate ω ∈ Icc (-2 : ℝ) 2 := by
  have h := (blockSphereCoordinate_mem ℝ (EuclideanSpace ℝ (Fin 3)) ω).2
  change ‖(ω.1 : SphereSpectralSpace).fst‖ ^ 2 ≤ 1 at h
  rw [Real.norm_eq_abs, sq_abs] at h
  change -2 ≤ 2 * (ω.1 : SphereSpectralSpace).fst ∧
    2 * (ω.1 : SphereSpectralSpace).fst ≤ 2
  constructor <;> nlinarith only [h]

/-- The spherical spectral law is carried by the Hecke interval. -/
theorem sphereThreeSpectralLaw_carried : sphereThreeSpectralLaw (Icc (-2 : ℝ) 2)ᶜ = 0 := by
  rw [sphereThreeSpectralLaw, Measure.smul_apply,
    Measure.map_apply continuous_sphereThreeHeckeCoordinate.measurable measurableSet_Icc.compl]
  have he : sphereThreeHeckeCoordinate ⁻¹' (Icc (-2 : ℝ) 2)ᶜ = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact sphereThreeHeckeCoordinate_mem ω
  rw [he, measure_empty, smul_zero]

theorem integrable_sphereThreeSpectralLaw_pow (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) sphereThreeSpectralLaw := by
  have hmem : ∀ᵐ x ∂sphereThreeSpectralLaw, x ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact sphereThreeSpectralLaw_carried
  refine Integrable.of_bound (C := 2 ^ k) (by fun_prop) ?_
  filter_upwards [hmem] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr hx) k

/-- Even moments are Catalan numbers, from the exact squared block-coordinate law. -/
theorem integral_sphereThreeSpectralLaw_even (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂sphereThreeSpectralLaw) = (catalan k : ℝ) := by
  have hbeta : blockCoordinateLaw ℝ (EuclideanSpace ℝ (Fin 3)) =
      betaMeasure (1 / 2) (3 / 2) := by
    simpa using blockCoordinateLaw_eq_beta ℝ (EuclideanSpace ℝ (Fin 3))
  have hm := integral_blockCoordinateLaw_pow ℝ (EuclideanSpace ℝ (Fin 3)) k
  rw [hbeta, integral_semicircleBeta_pow] at hm
  rw [sphereThreeSpectralLaw, integral_smul_measure,
    integral_map continuous_sphereThreeHeckeCoordinate.measurable.aemeasurable (by fun_prop),
    ENNReal.toReal_inv, smul_eq_mul]
  have he (ω : sphere (0 : SphereSpectralSpace) 1) :
      sphereThreeHeckeCoordinate ω ^ (2 * k) =
        4 ^ k * ‖(ω.1 : SphereSpectralSpace).fst‖ ^ (2 * (k : ℝ)) := by
    rw [sphereThreeHeckeCoordinate, mul_pow, pow_mul, Real.norm_eq_abs,
      show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast, pow_mul, sq_abs]
    norm_num
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ = 4 ^ k * blockSphereMellin ℝ (EuclideanSpace ℝ (Fin 3)) k := by
      unfold blockSphereMellin Measure.real
      ring
    _ = _ := by
      rw [← hm, mul_div_cancel₀ _ (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0))]

/-- Antipodal invariance annihilates every odd signed coordinate moment. -/
theorem integral_sphereThreeSpectralLaw_odd (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k + 1) ∂sphereThreeSpectralLaw) = 0 := by
  have hi := integral_comp_sphereMap (LinearIsometryEquiv.neg ℝ (E := SphereSpectralSpace))
    (fun ω => sphereThreeHeckeCoordinate ω ^ (2 * k + 1))
  have he (ω : sphere (0 : SphereSpectralSpace) 1) :
      sphereThreeHeckeCoordinate (sphereMap (LinearIsometryEquiv.neg ℝ) ω) =
        -sphereThreeHeckeCoordinate ω := by
    change 2 * (-(ω.1 : SphereSpectralSpace)).fst = -(2 * (ω.1 : SphereSpectralSpace).fst)
    rw [WithLp.neg_fst]
    ring
  have hk : Odd (2 * k + 1) := ⟨k, by omega⟩
  simp_rw [he, hk.neg_pow, integral_neg] at hi
  have hz : (∫ ω : sphere (0 : SphereSpectralSpace) 1,
      sphereThreeHeckeCoordinate ω ^ (2 * k + 1) ∂volume.toSphere) = 0 := by
    exact eq_zero_of_neg_eq hi
  rw [sphereThreeSpectralLaw, integral_smul_measure,
    integral_map continuous_sphereThreeHeckeCoordinate.measurable.aemeasurable (by fun_prop),
    hz, smul_zero]

/-- The full signed spherical coordinate distribution is the semicircle law. -/
theorem sphereThreeSpectralLaw_eq_semicircle :
    sphereThreeSpectralLaw = (semicircleSpectralLaw : Measure ℝ) := by
  apply _root_.HTGeometry.measure_eq_of_moments_eq_of_one_carried
    (s := semicircleMoment) (c := 0) (r := 2) (by norm_num)
    (by simpa only [zero_sub, zero_add] using sphereThreeSpectralLaw_carried)
  · intro k
    rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with h | h
    · have hk : k = 2 * (k / 2) := by omega
      rw [hk, semicircleMoment_even, integral_sphereThreeSpectralLaw_even]
    · have hk : k = 2 * (k / 2) + 1 := by omega
      rw [hk, semicircleMoment_odd, integral_sphereThreeSpectralLaw_odd]
  · exact integrable_sphereThreeSpectralLaw_pow
  · exact fun k => (semicircleSpectralLaw_hasMoments k).2.symm
  · exact fun k => (semicircleSpectralLaw_hasMoments k).1

/-- The scalar free Fock spectral law is twice a real coordinate of a uniform vector on `S³`. -/
theorem sphereThreeSpectralLaw_eq_scalarFock :
    sphereThreeSpectralLaw = (scalarFockSpectralLaw : Measure ℝ) := by
  rw [sphereThreeSpectralLaw_eq_semicircle, semicircleSpectralLaw_eq_scalarFockSpectralLaw]

end GaloisForLFunctions.SelbergClass.Primon
