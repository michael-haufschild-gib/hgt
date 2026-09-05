import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaFrenetConservation
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSpatialFrame
import Mathlib.Tactic

/-!
# Magnitude of the conserved elastica force

The variational force is expanded in an orthonormal Frenet frame.  This supplies the analytic
bridge between force conservation and the paper's spatial normalization radius `ℛ`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Stationary elastica with an orthonormal Frenet frame at every arclength. -/
structure OrthonormalStationaryElasticaData
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  geometry : StationaryElasticaData V
  tangent_self : ∀ s, inner ℝ (geometry.tangent s) (geometry.tangent s) = 1
  normal_self : ∀ s, inner ℝ (geometry.normal s) (geometry.normal s) = 1
  binormal_self : ∀ s, inner ℝ (geometry.binormal s) (geometry.binormal s) = 1
  tangent_normal : ∀ s, inner ℝ (geometry.tangent s) (geometry.normal s) = 0
  tangent_binormal : ∀ s, inner ℝ (geometry.tangent s) (geometry.binormal s) = 0
  normal_binormal : ∀ s, inner ℝ (geometry.normal s) (geometry.binormal s) = 0

/-- Pythagorean magnitude of paper equation (13). -/
theorem elasticaForce_norm_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : OrthonormalStationaryElasticaData V) (s : ℝ) :
    ‖elasticaForce E.geometry.toFrenetElasticaData s‖ ^ 2 =
      E.geometry.curvature₁ s ^ 2 +
        (E.geometry.curvature s * E.geometry.torsion s) ^ 2 +
        (E.geometry.curvature s ^ 2 + E.geometry.lagrange s) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  unfold elasticaForce
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [E.tangent_self, E.normal_self, E.binormal_self,
    E.tangent_normal, E.tangent_binormal, E.normal_binormal]
  rw [show inner ℝ (E.geometry.normal s) (E.geometry.tangent s) = 0 by
      rw [real_inner_comm, E.tangent_normal],
    show inner ℝ (E.geometry.binormal s) (E.geometry.tangent s) = 0 by
      rw [real_inner_comm, E.tangent_binormal],
    show inner ℝ (E.geometry.binormal s) (E.geometry.normal s) = 0 by
      rw [real_inner_comm, E.normal_binormal]]
  ring

/-- Data selecting paper's centered `(γ,ν)` normalization. -/
structure CenteredElasticaNormalization
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  frame : OrthonormalStationaryElasticaData V
  gamma : ℝ
  nu : ℝ
  curvature₁_zero : frame.geometry.curvature₁ 0 = 0
  multiplier_selected :
    elasticaLambdaScale frame.geometry =
      -(gamma ^ 2) * frame.geometry.curvature 0 ^ 2 / 2
  torsion_selected :
    nu = 2 * frame.geometry.torsion 0 / frame.geometry.curvature 0

noncomputable def CenteredElasticaNormalization.curvatureUnit
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) : ℝˣ :=
  Units.mk0 (E.frame.geometry.curvature 0)
    (ne_of_gt (E.frame.geometry.curvature_pos 0))

/-- Exact paper formula `|W|² = k₀⁴[(1+γ²/2)²+ν²]/4`. -/
theorem centered_elasticaForce_norm_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖ ^ 2 =
      E.frame.geometry.curvature 0 ^ 4 / 4 *
        ((1 + E.gamma ^ 2 / 2) ^ 2 + E.nu ^ 2) := by
  rw [elasticaForce_norm_sq, E.curvature₁_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
  have hlagrange := stationaryElastica_lagrange_eq E.frame.geometry 0
  rw [E.multiplier_selected] at hlagrange
  rw [hlagrange, E.torsion_selected]
  have hk : E.frame.geometry.curvature 0 ≠ 0 :=
    ne_of_gt (E.frame.geometry.curvature_pos 0)
  field_simp [hk]
  ring

/-- The spatial radius is exactly inverse fourth root normalization of conserved force. -/
theorem spatialRadiusFourth_mul_force_norm_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    spatialRadiusFourth E.curvatureUnit E.gamma E.nu *
      ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖ ^ 2 = 1 := by
  rw [centered_elasticaForce_norm_sq, spatialRadiusFourth]
  change 16 /
      (E.frame.geometry.curvature 0 ^ 4 *
        ((2 + E.gamma ^ 2) ^ 2 + 4 * E.nu ^ 2)) *
      (E.frame.geometry.curvature 0 ^ 4 / 4 *
        ((1 + E.gamma ^ 2 / 2) ^ 2 + E.nu ^ 2)) = 1
  have hk : E.frame.geometry.curvature 0 ≠ 0 :=
    ne_of_gt (E.frame.geometry.curvature_pos 0)
  have hden : (2 + E.gamma ^ 2) ^ 2 + 4 * E.nu ^ 2 ≠ 0 :=
    ne_of_gt (spatialOmegaSq_den_pos E.gamma E.nu)
  field_simp [hk, hden]
  ring

theorem centered_elasticaForce_norm_pos
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) :
    0 < ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖ := by
  have hsq := centered_elasticaForce_norm_sq E
  have hk4 : 0 < E.frame.geometry.curvature 0 ^ 4 :=
    (show Even 4 by decide).pow_pos
      (ne_of_gt (E.frame.geometry.curvature_pos 0))
  have hbase : 0 < 1 + E.gamma ^ 2 / 2 := by
    nlinarith [sq_nonneg E.gamma]
  have hbracket : 0 < (1 + E.gamma ^ 2 / 2) ^ 2 + E.nu ^ 2 := by
    nlinarith [sq_pos_of_pos hbase, sq_nonneg E.nu]
  have hfactor : 0 < E.frame.geometry.curvature 0 ^ 4 / 4 :=
    div_pos hk4 (by norm_num)
  have hsqpos : 0 < ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖ ^ 2 := by
    rw [hsq]
    exact mul_pos hfactor hbracket
  nlinarith [norm_nonneg (elasticaForce E.frame.geometry.toFrenetElasticaData 0)]

/-- Fixed vertical unit vector selected by the conserved variational force. -/
noncomputable def elasticaVerticalAxis
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) : V :=
  ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖⁻¹ •
    elasticaForce E.frame.geometry.toFrenetElasticaData s

theorem elasticaVerticalAxis_constant
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    elasticaVerticalAxis E s = elasticaVerticalAxis E 0 := by
  rw [elasticaVerticalAxis, elasticaVerticalAxis,
    stationaryElasticaForce_constant E.frame.geometry s]

theorem norm_elasticaVerticalAxis
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    ‖elasticaVerticalAxis E s‖ = 1 := by
  rw [elasticaVerticalAxis, norm_smul,
    stationaryElasticaForce_constant E.frame.geometry s]
  have hnorm := centered_elasticaForce_norm_pos E
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hnorm, inv_mul_cancel₀ (ne_of_gt hnorm)]

theorem elasticaVerticalAxis_hasDerivAt_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : CenteredElasticaNormalization V) (s : ℝ) :
    HasDerivAt (elasticaVerticalAxis E) 0 s := by
  have h := (stationaryElasticaForce_hasDerivAt_zero E.frame.geometry s).const_smul
    ‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖⁻¹
  change HasDerivAt
    (‖elasticaForce E.frame.geometry.toFrenetElasticaData 0‖⁻¹ •
      elasticaForce E.frame.geometry.toFrenetElasticaData) 0 s
  simpa only [smul_zero] using h

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
