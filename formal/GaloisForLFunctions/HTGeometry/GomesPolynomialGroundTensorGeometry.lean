import GaloisForLFunctions.HTGeometry.GomesPolynomialKernelClassification

/-!
# Tensor geometry of the complete polynomial ground sector

Experimental scalar half-density analogue of the Gomes shared-connection and tensor
representation viewpoint. Pointwise tensor multiplication adds polynomial profiles.
The canonical ground state reconstructs the complete density; its projective line
reconstructs exactly the connection and normalized probability law.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Pointwise tensor multiplication of canonical states is the canonical state of the sum. -/
theorem gomesPolynomialGroundState_tensor (P Q : GomesFinitePolynomialProfile) :
    mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q) =
      gomesPolynomialGroundState (P + Q) := by
  ext x
  rw [mulS_apply, gomesPolynomialGroundState_apply, gomesPolynomialGroundState_apply,
    gomesPolynomialGroundState_apply]
  change (Real.exp (P.val.eval x / 2) : ℂ) * (Real.exp (Q.val.eval x / 2) : ℂ) =
    (Real.exp ((P.val + Q.val).eval x / 2) : ℂ)
  rw [← Complex.ofReal_mul, ← Real.exp_add, eval_add]
  congr 2
  ring

/-- The actual tensor product solves the Hamiltonian induced by the summed connection. -/
theorem gomesPolynomialGroundState_tensor_kernel (P Q : GomesFinitePolynomialProfile) :
    dilatonHamiltonianCLM (P.val + Q.val)
      (mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) = 0 := by
  rw [gomesPolynomialGroundState_tensor]
  exact gomesPolynomialGroundState_kernel (P + Q)

/-- The unnormalized canonical ground field reconstructs every polynomial coefficient. -/
theorem gomesPolynomialGroundState_injective : Function.Injective gomesPolynomialGroundState := by
  intro P Q h
  apply Subtype.ext
  apply gomesDilatonWeight_injective
  funext x
  rw [← gomesPolynomialGroundState_norm_sq P, ← gomesPolynomialGroundState_norm_sq Q, h]

/-- Projective ground-state equality loses exactly the constant log-amplitude. -/
theorem gomesPolynomialGroundState_projective_constant_iff (P Q : GomesFinitePolynomialProfile) :
    (∃ c : ℂ, c ≠ 0 ∧ gomesPolynomialGroundState P = c • gomesPolynomialGroundState Q) ↔
      ∃ r : ℝ, P.val = Q.val + C r := by
  constructor
  · rintro ⟨c, hc, h⟩
    have hc2 : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
    refine ⟨Real.log (‖c‖ ^ 2), ?_⟩
    apply gomesDilatonWeight_injective
    funext x
    rw [gomesDilatonWeight_constant, Real.exp_log hc2,
      ← gomesPolynomialGroundState_norm_sq P, ← gomesPolynomialGroundState_norm_sq Q, h]
    simp only [smul_apply, norm_smul, mul_pow]
  · rintro ⟨r, hr⟩
    refine ⟨(Real.exp (r / 2) : ℂ), Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _), ?_⟩
    ext x
    change gomesPolynomialGroundState P x =
      (Real.exp (r / 2) : ℂ) * gomesPolynomialGroundState Q x
    rw [gomesPolynomialGroundState_apply, gomesPolynomialGroundState_apply, hr,
      eval_add, eval_C, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

/-- The projective ground field reconstructs precisely the shared first-order connection. -/
theorem gomesPolynomialGroundState_projective_connection_iff (P Q : GomesFinitePolynomialProfile) :
    (∃ c : ℂ, c ≠ 0 ∧ gomesPolynomialGroundState P = c • gomesPolynomialGroundState Q) ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val := by
  rw [gomesPolynomialGroundState_projective_constant_iff, gomesDilatonConnection_constant_iff]

/-- Normalized observations and projective ground fields carry exactly the same information. -/
theorem gomesPolynomialGroundState_projective_probability_iff (P Q : GomesFinitePolynomialProfile) :
    (∃ c : ℂ, c ≠ 0 ∧ gomesPolynomialGroundState P = c • gomesPolynomialGroundState Q) ↔
      gomesDilatonMassNormalized P.val = gomesDilatonMassNormalized Q.val := by
  rw [gomesPolynomialGroundState_projective_constant_iff,
    gomesFinitePolynomialProfile_normalized_eq_iff]

/-- The ground field's squared norm reconstructs the actual raw measure. -/
theorem gomesPolynomialGroundState_measure (P : GomesFinitePolynomialProfile) :
    volume.withDensity (fun x => ENNReal.ofReal (‖gomesPolynomialGroundState P x‖ ^ 2)) =
      gomesDilatonMeasure P.val := by
  simp only [gomesPolynomialGroundState_norm_sq]
  rfl

end GaloisForLFunctions.HTGeometry
