import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeightedAdelicAdjacencyHasSharpSpectralEdge
import GaloisForLFunctions.HyperbolicArakelovTheory.TheCriticalSphericalAverageRecoversTheAdelicGreenKernel

/-!
# The critical adelic Green inverse is unbounded

Finite charges approaching the actual all-prime edge give arbitrarily small
critical residuals. The subcritical spherical resolvent has exact norm equal
to the reciprocal mass. At criticality the spherical average exists entrywise
but cannot be a Bochner integral of bounded charge operators.
-/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Classical Topology BigOperators InnerProductSpace
namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic

/-- Precision at the full weighted adelic spectral edge. -/
def criticalPrecision : ChargeOperator := edge • 1 - adjacencyOperator

private theorem criticalPrecision_apply (f : ChargeSpace) :
    criticalPrecision f = edge • f - adjacencyOperator f := rfl

private theorem adjacency_quadratic_le (f : ChargeSpace) :
    ⟪adjacencyOperator f, f⟫_ℝ ≤ edge * ‖f‖ ^ 2 := by
  have hn := (adjacencyOperator.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right adjacencyOperator_norm_le (norm_nonneg f))
  exact ((real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg f))).trans_eq (by ring)

private theorem criticalPrecision_quadratic (f : ChargeSpace) :
    ⟪criticalPrecision f, f⟫_ℝ = edge * ‖f‖ ^ 2 - ⟪adjacencyOperator f, f⟫_ℝ := by
  rw [criticalPrecision_apply, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

private theorem criticalPrecision_symmetric (f g : ChargeSpace) :
    ⟪criticalPrecision f, g⟫_ℝ = ⟪f, criticalPrecision g⟫_ℝ := by
  rw [criticalPrecision_apply, criticalPrecision_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, adjacencyOperator_symmetric]

private theorem criticalPrecision_norm_sq_le (f : ChargeSpace) :
    ‖criticalPrecision f‖ ^ 2 ≤ 2 * edge * ⟪criticalPrecision f, f⟫_ℝ := by
  have hn : ‖adjacencyOperator f‖ ≤ edge * ‖f‖ :=
    (adjacencyOperator.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right adjacencyOperator_norm_le (norm_nonneg f))
  have hs := sq_le_sq₀ (norm_nonneg (adjacencyOperator f))
    (mul_nonneg edge_pos.le (norm_nonneg f))
  have hsq := hs.mpr hn
  rw [criticalPrecision_quadratic, criticalPrecision_apply, norm_sub_sq_real, norm_smul,
    Real.norm_of_nonneg edge_pos.le, real_inner_smul_left]
  rw [real_inner_comm f (adjacencyOperator f)]
  nlinarith only [hsq]

private theorem exists_unit_charge_above (c : ℝ) (hc : c < edge) :
    ∃ f : ChargeSpace, ‖f‖ = 1 ∧ c < ⟪adjacencyOperator f, f⟫_ℝ := by
  obtain ⟨g, _, hg⟩ := exists_finite_charge_above c hc
  let u := finiteChargeEmbedding g
  have hu : u ≠ 0 := by
    intro h
    change c * ‖u‖ ^ 2 < ⟪adjacencyOperator u, u⟫_ℝ at hg
    simp only [h, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, map_zero,
      inner_zero_left, lt_self_iff_false] at hg
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  · have h := mul_lt_mul_of_pos_left hg (sq_pos_of_pos (inv_pos.mpr hn))
    change ‖u‖⁻¹ ^ 2 * (c * ‖u‖ ^ 2) <
      ‖u‖⁻¹ ^ 2 * ⟪adjacencyOperator u, u⟫_ℝ at h
    have hc' : ‖u‖⁻¹ ^ 2 * (c * ‖u‖ ^ 2) = c := by field_simp [hn.ne']
    rw [hc'] at h
    simpa only [map_smul, real_inner_smul_left, real_inner_smul_right,
      pow_two, mul_assoc] using h

/-- Unit charges have arbitrarily small critical precision residuals. -/
theorem exists_unit_critical_residual_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ChargeSpace, ‖f‖ = 1 ∧ ‖criticalPrecision f‖ < ε := by
  let d := ε ^ 2 / (2 * edge)
  have hd : 0 < d := div_pos (sq_pos_of_pos hε) (mul_pos (by norm_num) edge_pos)
  obtain ⟨f, hf, hq⟩ := exists_unit_charge_above (edge - d) (sub_lt_self edge hd)
  refine ⟨f, hf, ?_⟩
  have hsmall : ⟪criticalPrecision f, f⟫_ℝ < d := by
    rw [criticalPrecision_quadratic, hf, one_pow, mul_one]
    linarith only [hq]
  have hnorm := (criticalPrecision_norm_sq_le f).trans_lt
    (mul_lt_mul_of_pos_left hsmall (mul_pos (by norm_num) edge_pos))
  have he : 2 * edge * d = ε ^ 2 := by
    dsimp only [d]
    field_simp [edge_pos.ne']
  rw [he] at hnorm
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hnorm

/-- No bounded operator is a right inverse of the critical precision. -/
theorem criticalPrecision_no_bounded_right_inverse (C : ChargeOperator) :
    criticalPrecision * C ≠ 1 := by
  intro hC
  let ε := 1 / (‖C‖ + 1)
  have hε : 0 < ε := one_div_pos.mpr (by positivity)
  obtain ⟨f, hf, hsmall⟩ := exists_unit_critical_residual_lt ε hε
  have hid : criticalPrecision (C f) = f :=
    congrArg (fun T : ChargeOperator => T f) hC
  have hone : (1 : ℝ) = ⟪C f, criticalPrecision f⟫_ℝ := by
    rw [← criticalPrecision_symmetric, hid, real_inner_self_eq_norm_sq, hf, one_pow]
  have hbound : (1 : ℝ) ≤ ‖C‖ * ε := by
    rw [hone]
    calc
      _ ≤ ‖C f‖ * ‖criticalPrecision f‖ := real_inner_le_norm _ _
      _ ≤ (‖C‖ * ‖f‖) * ε := mul_le_mul (C.le_opNorm f) hsmall.le
        (norm_nonneg _) (mul_nonneg (norm_nonneg C) (norm_nonneg f))
      _ = _ := by rw [hf, mul_one]
  have hlt : ‖C‖ * ε < 1 := by
    dsimp only [ε]
    rw [one_div, ← div_eq_mul_inv]
    exact (div_lt_one (by positivity)).mpr (lt_add_one ‖C‖)
  exact (not_le_of_gt hlt) hbound

private theorem sphericalPrecision_decomposition (ν : ℝ) :
    sphericalPrecision ν = criticalPrecision + (1 / 4 - ν ^ 2) • 1 := by
  rw [sphericalPrecision, criticalPrecision]
  module

private theorem sphericalPrecision_symmetric (ν : ℝ) (f g : ChargeSpace) :
    ⟪sphericalPrecision ν f, g⟫_ℝ = ⟪f, sphericalPrecision ν g⟫_ℝ := by
  rw [sphericalPrecision_decomposition]
  change ⟪criticalPrecision f + (1 / 4 - ν ^ 2) • f, g⟫_ℝ =
    ⟪f, criticalPrecision g + (1 / 4 - ν ^ 2) • g⟫_ℝ
  rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    criticalPrecision_symmetric]

private theorem sphericalPrecision_coercive (ν : ℝ) (f : ChargeSpace) :
    (1 / 4 - ν ^ 2) * ‖f‖ ^ 2 ≤ ⟪sphericalPrecision ν f, f⟫_ℝ := by
  rw [sphericalPrecision_decomposition]
  change (1 / 4 - ν ^ 2) * ‖f‖ ^ 2 ≤
    ⟪criticalPrecision f + (1 / 4 - ν ^ 2) • f, f⟫_ℝ
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have h := adjacency_quadratic_le f
  rw [criticalPrecision_quadratic]
  linarith only [h]

/-- The exact spherical resolvent norm is the reciprocal distance from the edge. -/
theorem sphericalGreenTransform_norm_eq {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2) :
    ‖sphericalGreenTransform ν‖ = (1 / 4 - ν ^ 2)⁻¹ := by
  let m : ℝ := 1 / 4 - ν ^ 2
  have hm : 0 < m := by
    dsimp only [m]
    nlinarith only [mul_pos hν0 (sub_pos.mpr hν1), hν0, hν1]
  let B := sphericalGreenTransform ν
  have hB : sphericalPrecision ν * B = 1 := sphericalPrecision_mul_transform hν0 hν1
  have hright (f : ChargeSpace) : sphericalPrecision ν (B f) = f :=
    congrArg (fun T : ChargeOperator => T f) hB
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hm.le)
    intro f
    have hc := sphericalPrecision_coercive ν (B f)
    rw [hright] at hc
    change m * ‖B f‖ ^ 2 ≤ ⟪f, B f⟫_ℝ at hc
    have hi := real_inner_le_norm f (B f)
    by_cases hz : B f = 0
    · rw [hz, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hm.le) (norm_nonneg f)
    have hn : 0 < ‖B f‖ := norm_pos_iff.mpr hz
    have hb : m * ‖B f‖ ≤ ‖f‖ := by
      by_contra h
      have hbad := mul_lt_mul_of_pos_right (lt_of_not_ge h) hn
      nlinarith only [hc, hi, hbad]
    have h : ‖B f‖ ≤ ‖f‖ / m :=
      (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hb)
    simpa only [div_eq_mul_inv, mul_comm] using h
  · by_contra h
    have hlt : ‖B‖ < m⁻¹ := lt_of_not_ge h
    have hBm : ‖B‖ * m < 1 := by
      simpa only [inv_mul_cancel₀ hm.ne'] using mul_lt_mul_of_pos_right hlt hm
    let ε := (1 - ‖B‖ * m) / (‖B‖ + 1)
    have hε : 0 < ε := div_pos (sub_pos.mpr hBm) (by positivity)
    obtain ⟨f, hf, hsmall⟩ := exists_unit_critical_residual_lt ε hε
    have hprec : ‖sphericalPrecision ν f‖ ≤ ε + m := by
      rw [sphericalPrecision_decomposition]
      calc
        _ ≤ ‖criticalPrecision f‖ + ‖m • f‖ := norm_add_le _ _
        _ ≤ ε + m := by
          rw [norm_smul, Real.norm_of_nonneg hm.le, hf, mul_one]
          linarith only [hsmall]
    have hone : (1 : ℝ) = ⟪B f, sphericalPrecision ν f⟫_ℝ := by
      rw [← sphericalPrecision_symmetric, hright, real_inner_self_eq_norm_sq, hf, one_pow]
    have hbnd : (1 : ℝ) ≤ ‖B‖ * (ε + m) := by
      rw [hone]
      calc
        _ ≤ ‖B f‖ * ‖sphericalPrecision ν f‖ := real_inner_le_norm _ _
        _ ≤ (‖B‖ * ‖f‖) * (ε + m) :=
          mul_le_mul (B.le_opNorm f) hprec (norm_nonneg _)
            (mul_nonneg (norm_nonneg B) (norm_nonneg f))
        _ = _ := by rw [hf, mul_one]
    have hεeq : ε * (‖B‖ + 1) = 1 - ‖B‖ * m :=
      div_mul_cancel₀ _ (by positivity : ‖B‖ + 1 ≠ 0)
    nlinarith only [hbnd, hεeq, hε]

/-- A bounded operator with the critical Green matrix would be a right inverse. -/
private theorem green_matrix_right_inverse (C : ChargeOperator)
    (hC : ∀ x y : FiniteVertices, C (lp.single 2 x (1 : ℝ)) y = green x y) :
    criticalPrecision * C = 1 := by
  have hdelta (x : FiniteVertices) :
      criticalPrecision (C (lp.single 2 x (1 : ℝ))) = lp.single 2 x 1 := by
    apply lp.ext
    funext y
    have he : (C (lp.single 2 x (1 : ℝ)) : FiniteVertices → ℝ) = green x :=
      funext (hC x)
    change edge * C (lp.single 2 x (1 : ℝ)) y -
      adjacencyOperator (C (lp.single 2 x (1 : ℝ))) y = (lp.single 2 x (1 : ℝ) : ChargeSpace) y
    rw [hC, adjacencyOperator_apply, he, green_source]
    simp only [pointMass, lp.coeFn_single, Pi.single_apply, eq_comm]
  apply ContinuousLinearMap.ext
  intro v
  change criticalPrecision (C v) = v
  refine finiteChargeEmbedding_dense.induction_on
    (p := fun f => criticalPrecision (C f) = f) v ?_ ?_
  · exact isClosed_eq (criticalPrecision.continuous.comp C.continuous) continuous_id
  intro f
  rw [finiteChargeEmbedding_eq]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro y _
  have he : (lp.single 2 y (f y) : ChargeSpace) =
      f y • (lp.single 2 y (1 : ℝ) : ChargeSpace) := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [he, map_smul, map_smul, hdelta]

/-- The critical Green matrix defines no bounded operator on counting square-summable charges. -/
theorem no_bounded_critical_green_matrix :
    ¬ ∃ C : ChargeOperator, ∀ x y : FiniteVertices,
      C (lp.single 2 x (1 : ℝ)) y = green x y := by
  rintro ⟨C, hC⟩
  exact criticalPrecision_no_bounded_right_inverse C (green_matrix_right_inverse C hC)

/-- Critical spherical integration is entrywise finite but not Bochner integrable in operator norm. -/
theorem not_integrable_critical_spherical_operator :
    ¬ IntegrableOn (fun r => sphericalWeight (1 / 2) r • hyperbolicEvolution r)
      (Ioi (0 : ℝ)) := by
  intro hi
  apply no_bounded_critical_green_matrix
  refine ⟨sphericalGreenTransform (1 / 2), ?_⟩
  intro x y
  let E : ChargeOperator →L[ℝ] ℝ :=
    (lp.evalCLM ℝ (fun _ : FiniteVertices => ℝ) 2 y).comp
      (ContinuousLinearMap.apply ℝ ChargeSpace (lp.single 2 x (1 : ℝ)))
  have he := E.integral_comp_comm hi
  change (∫ r in Ioi (0 : ℝ), sphericalGreenDensity (1 / 2) x y r) =
    sphericalGreenTransform (1 / 2) (lp.single 2 x (1 : ℝ)) y at he
  rw [← he]
  exact integral_critical_sphericalGreenDensity x y

#print axioms exists_unit_critical_residual_lt
#print axioms criticalPrecision_no_bounded_right_inverse
#print axioms sphericalGreenTransform_norm_eq
#print axioms no_bounded_critical_green_matrix
#print axioms not_integrable_critical_spherical_operator
end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
