import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.StableCycles
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The Raynaud cœur of a two-term complex

Every integral linear map `u : A → B` gives a Raynaud module on `B × A`:
`F(b,a) = (b,pa)`, `V(b,a) = (pb,a)`, and `d(b,a) = (u(a),0)`.
Its stable cycles are `B × ker u`, its saturated boundaries are
`range u × 0`, and its cœur is `coker u × ker u`. Thus the operator
construction recovers both homology groups without a finiteness assumption.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.TwoTerm

open RaynaudGenerator RaynaudAlgebra

variable (p : ℕ) {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable (u : A →ₗ[ℤ] B)

/-- The underlying group, labelled by its differential and Raynaud prime. -/
abbrev Model (_p : ℕ) {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (_u : A →ₗ[ℤ] B) := B × A

instance : AddCommGroup (Model p u) := inferInstanceAs (AddCommGroup (B × A))

def frobenius : Module.End ℤ (Model p u) :=
  LinearMap.prodMap LinearMap.id (p • LinearMap.id)

def verschiebung : Module.End ℤ (Model p u) :=
  LinearMap.prodMap (p • LinearMap.id) LinearMap.id

def differential : Module.End ℤ (Model p u) :=
  (u.comp (LinearMap.snd ℤ B A)).prod 0

/-- An actual representation of the integral Raynaud algebra on a two-term complex. -/
def representation : RaynaudAlgebra p →ₐ[ℤ] Module.End ℤ (Model p u) :=
  RingQuot.liftAlgHom ℤ ⟨FreeAlgebra.lift ℤ (fun
    | .frobenius => frobenius p u
    | .verschiebung => verschiebung p u
    | .differential => differential p u), by
      intro x y h
      cases h <;>
        simp only [map_mul, map_natCast, map_zero, FreeAlgebra.lift_ι_apply] <;>
        ext x <;>
        simp [frobenius, verschiebung, differential, Module.End.mul_apply]⟩

instance : Module (RaynaudAlgebra p) (Model p u) :=
  Module.compHom (Model p u) (representation p u).toRingHom

theorem F_smul (x : Model p u) : F p • x = (x.1, p • x.2) := by
  change representation p u (F p) x = _
  simp only [representation, F, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply]
  rfl

theorem V_smul (x : Model p u) : V p • x = (p • x.1, x.2) := by
  change representation p u (V p) x = _
  simp only [representation, V, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply]
  rfl

theorem d_smul (x : Model p u) : d p • x = (u x.2, 0) := by
  change representation p u (d p) x = _
  simp only [representation, d, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply]
  rfl

theorem F_pow_smul (n : ℕ) (x : Model p u) : F p ^ n • x = (x.1, p ^ n • x.2) := by
  induction n with
  | zero => simp only [pow_zero, one_smul]
  | succ n ih =>
      rw [pow_succ', mul_smul, ih, F_smul, pow_succ', mul_smul]

theorem V_pow_smul (n : ℕ) (x : Model p u) : V p ^ n • x = (p ^ n • x.1, x.2) := by
  induction n with
  | zero => simp only [pow_zero, one_smul]
  | succ n ih =>
      rw [pow_succ', mul_smul, ih, V_smul, pow_succ', mul_smul]

theorem mem_stableCycles_iff (x : Model p u) :
    x ∈ stableCycles p (Model p u) ↔ u x.2 = 0 := by
  rw [mem_stableCycles]
  simp only [mul_smul, V_pow_smul, d_smul, Prod.mk.injEq, and_true,
    Prod.zero_eq_mk, forall_const]

theorem mem_saturatedBoundaries_iff (x : Model p u) :
    x ∈ saturatedBoundaries p (Model p u) ↔ x.1 ∈ LinearMap.range u ∧ x.2 = 0 := by
  rcases x with ⟨b, a⟩
  rw [mem_saturatedBoundaries]
  simp only [mul_smul, d_smul, F_pow_smul, smul_zero, Prod.mk.injEq]
  constructor
  · rintro ⟨n, y, h₁, h₂⟩
    exact ⟨⟨y.2, h₁⟩, h₂.symm⟩
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨0, (0, a), ha, h.symm⟩

/-- The homology coordinates of a stable cycle. -/
def homologyMap : stableCycles p (Model p u) →ₗ[ℤ] (B ⧸ LinearMap.range u) × LinearMap.ker u where
  toFun x := (Submodule.Quotient.mk x.1.1,
    ⟨x.1.2, (mem_stableCycles_iff p u x.1).mp x.2⟩)
  map_add' x y := by rfl
  map_smul' n x := by rfl

theorem homologyMap_surjective : Function.Surjective (homologyMap p u) := by
  rintro ⟨b, a⟩
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range u) b
  exact ⟨⟨(b, a.1), (mem_stableCycles_iff p u _).mpr a.2⟩, rfl⟩

theorem homologyMap_ker : LinearMap.ker (homologyMap p u) =
    (saturatedBoundaries p (Model p u)).comap (stableCycles p (Model p u)).subtype := by
  ext x
  change (Submodule.Quotient.mk x.1.1, (⟨x.1.2, _⟩ : LinearMap.ker u)) = 0 ↔ _
  change _ ↔ x.1 ∈ saturatedBoundaries p (Model p u)
  rw [mem_saturatedBoundaries_iff]
  simp only [Prod.zero_eq_mk, Prod.mk.injEq, Submodule.Quotient.mk_eq_zero]
  exact and_congr_right fun _ => ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩

/-- The cœur of the two-term Raynaud module is its cokernel times its kernel. -/
def coeurEquiv :
    (stableCycles p (Model p u) ⧸
      (saturatedBoundaries p (Model p u)).comap (stableCycles p (Model p u)).subtype) ≃ₗ[ℤ] (B ⧸ LinearMap.range u) × LinearMap.ker u :=
  (Submodule.quotEquivOfEq _ _ (homologyMap_ker p u).symm).trans
    ((homologyMap p u).quotKerEquivOfSurjective (homologyMap_surjective p u))

#print axioms representation
#print axioms coeurEquiv

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.TwoTerm
