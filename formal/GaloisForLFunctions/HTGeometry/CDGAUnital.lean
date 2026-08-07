import GaloisForLFunctions.HTGeometry.CDGATensor

/-!
# Units of a commutative differential graded algebra

`CDGAStructure` has no unit: it is a commutative differential graded algebra in the non-unital
sense, which is all the formality comparison needs.  A unit is extra data, and unitality of an
action is extra data on a module, so both are supplied separately here rather than added to the
structures — nothing already built has to change.

The unit is what makes a free module free in the usual sense, and hence what makes the tensor
product over the algebra computable on a cell.

* `HTGeometry.CDGAUnit` : a unit, with `mul_one` derived from graded commutativity.
* `HTGeometry.CDGAModuleUnital` : the action of the unit is the identity.
* `HTGeometry.tensorModule_unital`, `HTGeometry.twisted_unital` : unitality is inherited by the
  tensor product and by a cell attachment.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)]

/-- **A unit for a commutative differential graded algebra**: a degree-zero element acting as the
identity on the left, and a cocycle. -/
structure CDGAUnit (A : CDGAStructure R X) where
  /-- The unit element, in degree zero. -/
  one : X 0
  one_mul : ∀ (b : ℕ) (y : X b), A.mul (Nat.zero_add b) one y = y
  d_one : A.d 0 one = 0

namespace CDGAUnit

variable {A : CDGAStructure R X}

/-- The unit acts as the identity on the right as well, by graded commutativity. -/
theorem mul_one (u : CDGAUnit A) (b : ℕ) (y : X b) :
    A.mul (Nat.add_zero b) y u.one = y := by
  rw [A.mul_comm (Nat.add_zero b) (Nat.zero_add b) y u.one, u.one_mul b y,
    Nat.mul_zero, pow_zero, one_smul]

end CDGAUnit

variable {A : CDGAStructure R X} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- **A module on which the unit acts as the identity.** -/
structure CDGAModuleUnital (u : CDGAUnit A) (P : CDGAModuleStructure A M) : Prop where
  act_one : ∀ (b : ℕ) (m : M b), P.act (Nat.zero_add b) u.one m = m

/-- An algebra with a unit is a unital module over itself. -/
theorem selfModule_unital (u : CDGAUnit A) :
    CDGAModuleUnital u (CDGAStructure.selfModule A) :=
  ⟨fun b y => u.one_mul b y⟩

/-- The action of the unit as a linear map is the identity. -/
theorem actₗ_one {u : CDGAUnit A} {P : CDGAModuleStructure A M} (hP : CDGAModuleUnital u P)
    (b : ℕ) : P.actₗ (Nat.zero_add b) u.one = LinearMap.id :=
  LinearMap.ext fun m => hP.act_one b m

/-- **Unitality is inherited by a cell attachment.** -/
theorem twisted_unital {u : CDGAUnit A} {P : CDGAModuleStructure A M}
    {Q : CDGAModuleStructure A N} (t : CDGATwist P Q) (hP : CDGAModuleUnital u P)
    (hQ : CDGAModuleUnital u Q) :
    CDGAModuleUnital u (CDGAModuleStructure.twisted P Q t) :=
  ⟨fun b m => Prod.ext (hP.act_one b m.1) (hQ.act_one b m.2)⟩

/-- **Unitality is inherited by the tensor product**, the action being through the left factor. -/
theorem tensorModule_unital {u : CDGAUnit A} {P : CDGAModuleStructure A M}
    (hP : CDGAModuleUnital u P) (Q : CDGAModuleStructure A N) :
    CDGAModuleUnital u (tensorModule P Q) := by
  refine ⟨fun n f => ?_⟩
  show tensorAct P Q (Nat.zero_add n) u.one f = f
  funext p
  obtain ⟨⟨a, c⟩, ha⟩ := p
  rw [tensorAct_apply_eq P Q (Nat.zero_add n) u.one f (show 0 + a = a from Nat.zero_add a)
    (show (a, c).1 + (a, c).2 = n by omega) ha,
    show P.actₗ (show 0 + a = a from Nat.zero_add a) u.one = LinearMap.id from actₗ_one hP a,
    TensorProduct.map_id, LinearMap.id_apply]

/-- **Unitality is inherited by a direct sum.** -/
theorem prod_unital {u : CDGAUnit A} {P : CDGAModuleStructure A M}
    {Q : CDGAModuleStructure A N} (hP : CDGAModuleUnital u P) (hQ : CDGAModuleUnital u Q) :
    CDGAModuleUnital u (CDGAModuleStructure.prod P Q) :=
  ⟨fun b m => Prod.ext (hP.act_one b m.1) (hQ.act_one b m.2)⟩

end GaloisForLFunctions.HTGeometry
