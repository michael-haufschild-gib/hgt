import GaloisForLFunctions.HTGeometry.DifferentialConnectionModule

/-!
# Affine translations of the differential Ore generator

For every element `a` of a commutative differential ring, substitution
`∂ ↦ ∂ + a` is a ring automorphism of its differential operators. The
connection construction proves multiplicativity even when `a` is nonconstant.
This is the differential specialization of the affine change in Proposition
4.16 of Ait Mohamed–El-Baz.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.DiffOp

variable {K : Type*} [CommRing K] [Differential K]

/-- Left multiplication by the translated differential generator. -/
def affineConnection (a : K) : DiffOp K →+ DiffOp K where
  toFun p := (X + C a) * p
  map_zero' := mul_zero _
  map_add' := mul_add _

theorem affineConnection_leibniz (a c : K) (p : DiffOp K) :
    affineConnection a (c • p) =
      c • affineConnection a p + (Differential.deriv c) • p := by
  simp only [affineConnection, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    add_mul, X_mul, C_mul, dpartial_smul, smul_add, smul_smul]
  rw [mul_comm a c]
  abel

theorem affineConnection_iterate (a : K) (n : ℕ) (p : DiffOp K) :
    (affineConnection a : DiffOp K → DiffOp K)^[n] p = (X + C a) ^ n * p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    exact (mul_assoc _ _ _).symm

theorem affineConnection_action_mul (a : K) (p q : DiffOp K) :
    connectionDiffOpSMul (affineConnection a) p q =
      connectionDiffOpSMul (affineConnection a) p 1 * q := by
  induction p using induction_linear with
  | h0 => simp
  | hadd p p' hp hp' =>
    rw [connectionDiffOpSMul_add_op, connectionDiffOpSMul_add_op, hp, hp', add_mul]
  | hmono n c =>
    rw [connectionDiffOpSMul_mono, connectionDiffOpSMul_mono,
      affineConnection_iterate, affineConnection_iterate, mul_one, smul_mul_assoc]

/-- Substitution `∂ ↦ ∂ + a`, fixing the coefficient ring. -/
def affineTranslationHom (a : K) : DiffOp K →+* DiffOp K where
  toFun p := connectionDiffOpSMul (affineConnection a) p 1
  map_zero' := connectionDiffOpSMul_zero_op _ _
  map_one' := connectionDiffOpSMul_one _ _
  map_add' p q := connectionDiffOpSMul_add_op _ p q _
  map_mul' p q := by
    rw [connectionDiffOpSMul_mul _ (affineConnection_leibniz a),
      affineConnection_action_mul]

@[simp] theorem affineTranslationHom_C (a c : K) :
    affineTranslationHom a (C c) = C c := by
  change connectionDiffOpSMul (affineConnection a) (mono 0 c) 1 = C c
  rw [connectionDiffOpSMul_mono, affineConnection_iterate, pow_zero, one_mul,
    ← C_mul, mul_one]

@[simp] theorem affineTranslationHom_X (a : K) :
    affineTranslationHom a X = X + C a := by
  change connectionDiffOpSMul (affineConnection a) (mono 1 1) 1 = X + C a
  rw [connectionDiffOpSMul_mono, affineConnection_iterate, pow_one, mul_one, one_smul]

/-- Translations compose by adding their coefficient shifts. -/
theorem affineTranslationHom_comp (a b : K) (p : DiffOp K) :
    affineTranslationHom a (affineTranslationHom b p) = affineTranslationHom (a + b) p := by
  induction p using induction_linear with
  | h0 => simp only [map_zero]
  | hadd p q hp hq => simp only [map_add, hp, hq]
  | hmono n c =>
    rw [mono_eq_C_mul_X_pow]
    simp only [map_mul, map_pow, map_add, affineTranslationHom_C, affineTranslationHom_X]
    rw [show C (a + b) = C a + C b from mono_add 0 a b, add_assoc]

theorem affineTranslationHom_zero (p : DiffOp K) : affineTranslationHom (0 : K) p = p := by
  induction p using induction_linear with
  | h0 => exact map_zero _
  | hadd p q hp hq => simp only [map_add, hp, hq]
  | hmono n c =>
    rw [mono_eq_C_mul_X_pow]
    rw [map_mul, map_pow, affineTranslationHom_C, affineTranslationHom_X]
    simp only [C_apply, mono_zero, add_zero]

/-- Every affine translation is invertible, with inverse shift `-a`. -/
def affineTranslation (a : K) : DiffOp K ≃+* DiffOp K :=
  { affineTranslationHom a with
    invFun := affineTranslationHom (-a)
    left_inv p := by
      change affineTranslationHom (-a) (affineTranslationHom a p) = p
      rw [affineTranslationHom_comp, neg_add_cancel, affineTranslationHom_zero]
    right_inv p := by
      change affineTranslationHom a (affineTranslationHom (-a) p) = p
      rw [affineTranslationHom_comp, add_neg_cancel, affineTranslationHom_zero] }

end GaloisForLFunctions.HTGeometry.DiffOp

#print axioms GaloisForLFunctions.HTGeometry.DiffOp.affineTranslation
