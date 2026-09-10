import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionBicommutant

/-!
# The full Hermite creation commutant

The actual Hermite recurrence operator is a nonzero scalar multiple of a degree-one
polynomial connection. The general matrix classification therefore collapses to one
polynomial variable: every real-linear Hermite symmetry is a unique polynomial in
Hermite creation itself. This applies the reconstruction experiment directly to the
corpus Hermite operator and its existing polynomial basis.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Rescaling the formal variable converts connection polynomials to Hermite operator polynomials. -/
theorem gomesHermite_aeval_rescale (F : ℝ[X]) :
    (Polynomial.aeval gomesHermiteStepLinearMap)
      (F.comp (C gomesHermiteConnectionScale⁻¹ * X)) =
        (Polynomial.aeval
          (gomesPolynomialFirstOrderLinearMap gomesHermiteConnectionCoefficient.val)) F := by
  rw [Polynomial.aeval_comp, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    ← Algebra.smul_def, gomesHermiteStepLinearMap, smul_smul,
    inv_mul_cancel₀ gomesHermiteConnectionScale_ne_zero, one_smul]

/-- The forward scalar substitution expresses Hermite polynomials in the connection operator. -/
theorem gomesHermite_aeval_scale (F : ℝ[X]) :
    (Polynomial.aeval
      (gomesPolynomialFirstOrderLinearMap gomesHermiteConnectionCoefficient.val))
        (F.comp (C gomesHermiteConnectionScale * X)) =
          (Polynomial.aeval gomesHermiteStepLinearMap) F := by
  rw [Polynomial.aeval_comp, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    ← Algebra.smul_def]
  rfl

/-- The scalar substitution has an exact symbolic inverse. -/
theorem gomesHermite_operator_polynomial_rescale_cancel (F : ℝ[X]) :
    (F.comp (C gomesHermiteConnectionScale * X)).comp
      (C gomesHermiteConnectionScale⁻¹ * X) = F := by
  rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    ← mul_assoc, ← map_mul, mul_inv_cancel₀ gomesHermiteConnectionScale_ne_zero,
    map_one, one_mul, Polynomial.comp_X]

/-- Hermite creation satisfies no nonzero polynomial relation as a real-linear operator. -/
theorem gomesHermiteStep_aeval_injective :
    Function.Injective (Polynomial.aeval (R := ℝ) gomesHermiteStepLinearMap) := by
  intro F G h
  have hs : (Polynomial.aeval
      (gomesPolynomialFirstOrderLinearMap gomesHermiteConnectionCoefficient.val))
        (F.comp (C gomesHermiteConnectionScale * X)) =
      (Polynomial.aeval
        (gomesPolynomialFirstOrderLinearMap gomesHermiteConnectionCoefficient.val))
          (G.comp (C gomesHermiteConnectionScale * X)) := by
    simpa only [gomesHermite_aeval_scale] using h
  have hp := gomesPolynomialConnection_aeval_injective gomesHermiteConnectionCoefficient hs
  have hc := congrArg (fun P : ℝ[X] => P.comp (C gomesHermiteConnectionScale⁻¹ * X)) hp
  simpa only [gomesHermite_operator_polynomial_rescale_cancel] using hc

/-- Every real-linear map commuting with actual Hermite creation is a polynomial in that operator. -/
theorem gomesHermiteStep_full_commutant_iff (E : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    E.comp gomesHermiteStepLinearMap = gomesHermiteStepLinearMap.comp E ↔
      ∃ F : ℝ[X], E = (Polynomial.aeval gomesHermiteStepLinearMap) F := by
  constructor
  · intro h
    have hc := (gomesHermiteStep_commutes_connection_iff E).mp h
    have he := (gomesPolynomialConnectionCommutant_mem_iff
      gomesHermiteConnectionCoefficient.val E).mpr hc
    obtain ⟨P, hP, _⟩ := gomesPolynomialConnection_degree_one_symmetries
      ⟨gomesHermiteConnectionCoefficient, gomesHermiteConnectionCoefficient_degree⟩ ⟨E, he⟩
    refine ⟨P.comp (C gomesHermiteConnectionScale⁻¹ * X), ?_⟩
    rw [gomesHermite_aeval_rescale]
    exact congrArg Subtype.val hP
  · rintro ⟨F, rfl⟩
    have h := congrArg (Polynomial.aeval gomesHermiteStepLinearMap) (mul_comm F X)
    simpa only [map_mul, Polynomial.aeval_X, Module.End.mul_eq_comp] using h

/-- Every Hermite symmetry determines a unique polynomial in actual Hermite creation. -/
theorem gomesHermiteStep_full_commutant_unique_iff (E : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    E.comp gomesHermiteStepLinearMap = gomesHermiteStepLinearMap.comp E ↔
      ∃! F : ℝ[X], E = (Polynomial.aeval gomesHermiteStepLinearMap) F := by
  rw [gomesHermiteStep_full_commutant_iff]
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨F, hF, ?_⟩
    intro G hG
    exact gomesHermiteStep_aeval_injective (hG.symm.trans hF)
  · rintro ⟨F, hF, _⟩
    exact ⟨F, hF⟩

/-- The entire Hermite symmetry algebra is commutative. -/
theorem gomesHermiteStep_all_symmetries_commute
    (E F : {E : ℝ[X] →ₗ[ℝ] ℝ[X] //
      E.comp gomesHermiteStepLinearMap = gomesHermiteStepLinearMap.comp E}) :
    E.val.comp F.val = F.val.comp E.val := by
  obtain ⟨P, hP⟩ := (gomesHermiteStep_full_commutant_iff E.val).mp E.property
  obtain ⟨Q, hQ⟩ := (gomesHermiteStep_full_commutant_iff F.val).mp F.property
  rw [hP, hQ]
  have h := congrArg (Polynomial.aeval gomesHermiteStepLinearMap) (mul_comm P Q)
  simpa only [map_mul, Module.End.mul_eq_comp] using h

end GaloisForLFunctions.HTGeometry
