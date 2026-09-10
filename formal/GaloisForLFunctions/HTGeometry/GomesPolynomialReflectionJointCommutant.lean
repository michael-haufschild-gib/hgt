import GaloisForLFunctions.HTGeometry.GomesReflectionJointMatrixCommutant

/-!
# Complete actual polynomial symmetries shared by differentiation and reflection

This transports the exact matrix boundary back to every polynomial endomorphism.
The survivor is one formal scalar on both residue chains, independently of the
reflection center. No commutation assumption is hidden in the final classification.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- The full higher-derivative matrix model preserves and reflects actual operator commutation. -/
theorem gomesPolynomialDerivativePowerCommutant_matrix_commute_iff
    (m : ℕ) [NeZero m] (E F : GomesPolynomialDerivativePowerCommutant K m) :
    Commute (gomesPolynomialDerivativePowerCommutantEquiv K m E)
      (gomesPolynomialDerivativePowerCommutantEquiv K m F) ↔ Commute E.val F.val := by
  constructor
  · intro h
    have hs : E * F = F * E := (gomesPolynomialDerivativePowerCommutantEquiv K m).injective
      (by rw [map_mul, map_mul]; exact h.eq)
    exact congrArg Subtype.val hs
  · intro h
    have hs : E * F = F * E := Subtype.ext h.eq
    change gomesPolynomialDerivativePowerCommutantEquiv K m E *
      gomesPolynomialDerivativePowerCommutantEquiv K m F =
        gomesPolynomialDerivativePowerCommutantEquiv K m F *
          gomesPolynomialDerivativePowerCommutantEquiv K m E
    simpa only [map_mul] using congrArg (gomesPolynomialDerivativePowerCommutantEquiv K m) hs

/-- Actual second-derivative symmetries commute with differentiation and reflection exactly when scalar. -/
theorem gomesPolynomialReflectionSymmetry_joint_iff
    (c : K) (E : GomesPolynomialDerivativePowerCommutant K 2) :
    (Commute E.val (Polynomial.derivative : Module.End K K[X]) ∧
      Commute E.val (gomesPolynomialReflectionEnd K c)) ↔
        ∃ F : PowerSeries K,
          gomesPolynomialDerivativePowerCommutantEquiv K 2 E = Matrix.scalar (Fin 2) F := by
  have hD := gomesPolynomialDerivativePowerCommutant_matrix_commute_iff K 2 E
    (gomesFormalSeriesDerivativePowerHom K 2 PowerSeries.X)
  change Commute (gomesPolynomialDerivativePowerCommutantEquiv K 2 E)
    (gomesFormalSeriesDerivativePowerMatrixHom K 2 PowerSeries.X) ↔
      Commute E.val (gomesFormalSeriesPolynomialOperator K PowerSeries.X) at hD
  rw [gomesFormalSeriesDerivativePowerMatrixHom_two_X, gomesFormalSeriesPolynomialOperator_X] at hD
  have hR := gomesPolynomialDerivativePowerCommutant_matrix_commute_iff K 2 E
    (gomesPolynomialReflectionSymmetry K c)
  change Commute (gomesPolynomialDerivativePowerCommutantEquiv K 2 E)
    (gomesPolynomialReflectionMatrix K c) ↔ Commute E.val (gomesPolynomialReflectionEnd K c) at hR
  exact (and_congr hD.symm hR.symm).trans
    (gomesDerivativeReflectionMatrix_joint_commutant K c _)

/-- One formal differentiation series acting identically on both residue chains. -/
def gomesEvenFormalPolynomialOperator (F : PowerSeries K) : Module.End K K[X] :=
  ((gomesPolynomialDerivativePowerCommutantEquiv K 2).symm (Matrix.scalar (Fin 2) F)).val

/-- The full shared commutant on all polynomial endomorphisms, at every reflection center. -/
theorem gomesPolynomialDerivativeReflection_joint_commutant
    (c : K) (E : Module.End K K[X]) :
    (Commute E Polynomial.derivative ∧ Commute E (gomesPolynomialReflectionEnd K c)) ↔
      ∃ F : PowerSeries K, E = gomesEvenFormalPolynomialOperator K F := by
  constructor
  · rintro ⟨hD, hR⟩
    let e : GomesPolynomialDerivativePowerCommutant K 2 :=
      ⟨E, (gomesCentralizerSingleton_mem_iff K _ _).mpr (hD.pow_right 2).eq.symm⟩
    obtain ⟨F, hF⟩ := (gomesPolynomialReflectionSymmetry_joint_iff K c e).mp ⟨hD, hR⟩
    refine ⟨F, ?_⟩
    have he := congrArg (gomesPolynomialDerivativePowerCommutantEquiv K 2).symm hF
    rw [AlgEquiv.symm_apply_apply] at he
    exact congrArg Subtype.val he
  · rintro ⟨F, rfl⟩
    exact (gomesPolynomialReflectionSymmetry_joint_iff K c
      ((gomesPolynomialDerivativePowerCommutantEquiv K 2).symm (Matrix.scalar (Fin 2) F))).mpr
        ⟨F, (gomesPolynomialDerivativePowerCommutantEquiv K 2).apply_symm_apply _⟩

/-- The shared commutant is independent of the affine reflection center. -/
theorem gomesPolynomialDerivativeReflection_joint_center_independent
    (c d : K) (E : Module.End K K[X]) :
    (Commute E Polynomial.derivative ∧ Commute E (gomesPolynomialReflectionEnd K c)) ↔
      (Commute E Polynomial.derivative ∧ Commute E (gomesPolynomialReflectionEnd K d)) := by
  rw [gomesPolynomialDerivativeReflection_joint_commutant, gomesPolynomialDerivativeReflection_joint_commutant]

end GaloisForLFunctions.HTGeometry
