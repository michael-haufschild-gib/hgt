import GaloisForLFunctions.HTGeometry.CDGAGround

/-!
# Augmented algebras and the augmentation ideal

An augmentation of a commutative differential graded algebra is a morphism to the ground ring placed
in degree zero.  Its kernel is closed under the differential and under multiplication by the algebra,
so it is a differential graded module over the algebra — the object a bar construction is built on.

* `HTGeometry.augIdealCarrier` : the kernel of an augmentation, degree by degree.
* `HTGeometry.augIdealModule` : it is a differential graded module over the algebra.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}

/-- The augmentation ideal in a degree. -/
abbrev augIdealCarrier (ε : CDGAHom A (groundCDGA R)) (n : ℕ) : Type u :=
  LinearMap.ker (ε.mapₗ n)

/-- The augmentation kills the differential of anything, because the ground algebra has none. -/
theorem aug_d_cDGAAugmentation (ε : CDGAHom A (groundCDGA R)) (n : ℕ) (x : X n) :
    ε.toFun (n + 1) (A.d n x) = 0 := by
  rw [ε.map_d n x]
  exact @Subsingleton.elim _ (groundCarrierSubsingleton R (by omega)) _ _

/-- The augmentation ideal is closed under multiplication by the algebra. -/
theorem aug_mul_mem (ε : CDGAHom A (groundCDGA R)) {a b n : ℕ} (h : a + b = n) (y : X a)
    {x : X b} (hx : ε.toFun b x = 0) : ε.toFun n (A.mul h y x) = 0 := by
  rw [ε.map_mul h y x, hx]
  funext p
  show ε.toFun a y _ * (0 : ConstCellCarrier R 0 b) _ = _
  show ε.toFun a y _ * (0 : R) = (0 : R)
  rw [mul_zero]

/-- The augmentation ideal is closed under multiplication, stated on the kernel. -/
theorem augIdeal_mul_mem (ε : CDGAHom A (groundCDGA R)) {a b n : ℕ} (h : a + b = n) (y : X a)
    (x : augIdealCarrier ε b) : A.mul h y (x : X b) ∈ LinearMap.ker (ε.mapₗ n) := by
  refine LinearMap.mem_ker.mpr ?_
  have hx : ε.toFun b (x : X b) = 0 := LinearMap.mem_ker.mp x.2
  exact aug_mul_mem ε h y hx

/-- **The augmentation ideal is a differential graded module over the algebra.** -/
def augIdealModule (ε : CDGAHom A (groundCDGA R)) :
    CDGAModuleStructure A (augIdealCarrier ε) where
  act h y x := ⟨A.mul h y (x : X _), augIdeal_mul_mem ε h y x⟩
  d n x := ⟨A.d n (x : X n), LinearMap.mem_ker.mpr (aug_d_cDGAAugmentation ε n (x : X n))⟩
  act_add_left h y y' _ := Subtype.ext (A.mul_add_left h y y' _)
  act_add_right h y _ _ := Subtype.ext (A.mul_add_right h y _ _)
  act_smul_left h c y _ := Subtype.ext (A.mul_smul_left h c y _)
  act_smul_right h c y _ := Subtype.ext (A.mul_smul_right h c y _)
  act_assoc h₁ h₂ h₃ h₄ y y' _ := Subtype.ext (A.mul_assoc h₁ h₂ h₃ h₄ y y' _)
  d_add n _ _ := Subtype.ext (A.d_add n _ _)
  d_smul n c _ := Subtype.ext (A.d_smul n c _)
  d_d n _ := Subtype.ext (A.d_d n _)
  d_act h y _ := Subtype.ext (A.d_mul h y _)

@[simp] theorem augIdealModule_act (ε : CDGAHom A (groundCDGA R)) {a b n : ℕ} (h : a + b = n)
    (y : X a) (x : augIdealCarrier ε b) :
    ((augIdealModule ε).act h y x : X n) = A.mul h y (x : X b) := rfl

@[simp] theorem augIdealModule_d (ε : CDGAHom A (groundCDGA R)) (n : ℕ)
    (x : augIdealCarrier ε n) : ((augIdealModule ε).d n x : X (n + 1)) = A.d n (x : X n) := rfl

end GaloisForLFunctions.HTGeometry
