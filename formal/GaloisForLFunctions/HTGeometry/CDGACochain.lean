import GaloisForLFunctions.HTGeometry.CDGAGroundModule
import GaloisForLFunctions.HTGeometry.CDGATensor
import GaloisForLFunctions.HTGeometry.CDGAAugmentationIdealAlgebra

/-!
# Cochain complexes, their tensor product, and the shift of an augmentation ideal

A cochain complex is packaged with its instances so that it can be produced by recursion.  Viewing
it as a module with zero action over the ground algebra makes the tensor product of modules — with
its Koszul sign — the tensor product of complexes, and the corresponding differential squares to
zero for free.

The shift of an augmentation ideal lowers every degree by one and negates the differential.  For a
connected algebra, whose augmentation ideal starts in degree one, the shift stays in nonnegative
degrees, which is what lets the bar construction be built inside this grading.

* `HTGeometry.Cochain` : a cochain complex with its instances.
* `HTGeometry.Cochain.tensor` : the tensor product of two complexes.
* `HTGeometry.augIdealShift` : the shift of an augmentation ideal.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]

/-- **A cochain complex of `R`-modules**, packaged with its instances so that complexes can be
produced by recursion. -/
structure Cochain (R : Type u) [CommRing R] where
  /-- The underlying graded family. -/
  carrier : ℕ → Type u
  /-- Its additive structure. -/
  group : ∀ n, AddCommGroup (carrier n)
  /-- Its module structure. -/
  smul : ∀ n, Module R (carrier n)
  /-- The differential. -/
  d : letI := group; letI := smul; ∀ n : ℕ, carrier n →ₗ[R] carrier (n + 1)
  /-- The differential squares to zero. -/
  d_d : letI := group; letI := smul; ∀ (n : ℕ) (x : carrier n), d (n + 1) (d n x) = 0

attribute [instance] Cochain.group Cochain.smul

namespace Cochain

variable {X : ℕ → Type u} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]

/-- A complex as a differential graded module with zero action. -/
def module (C : Cochain R) (A : CDGAStructure R X) : CDGAModuleStructure A C.carrier :=
  zeroComplexModule A C.d C.d_d

/-- **The tensor product of two cochain complexes**, with the Koszul sign in its differential. -/
noncomputable def tensor (C D : Cochain R) : Cochain R where
  carrier n := TensorCarrier (R := R) C.carrier D.carrier n
  group _ := inferInstance
  smul _ := inferInstance
  d n := (tensorModule (C.module (groundCDGA R)) (D.module (groundCDGA R))).dₗ n
  d_d n x := (tensorModule (C.module (groundCDGA R)) (D.module (groundCDGA R))).d_d n x

/-- The ground ring in degree zero, as a complex. -/
def ground (R : Type u) [CommRing R] : Cochain R where
  carrier := ConstCellCarrier R 0
  group _ := inferInstance
  smul _ := inferInstance
  d _ := 0
  d_d _ _ := rfl

end Cochain

section Shift

variable {X : ℕ → Type u} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))

/-- The differential of the shift of the augmentation ideal: the differential of the ideal, with the
sign of the shift. -/
noncomputable def augIdealShiftD (n : ℕ) :
    augIdealCarrier ε (n + 1) →ₗ[R] augIdealCarrier ε (n + 1 + 1) :=
  -(augIdealModule ε).dₗ (n + 1)

theorem augIdealShiftD_apply (n : ℕ) (x : augIdealCarrier ε (n + 1)) :
    augIdealShiftD ε n x = -(augIdealModule ε).d (n + 1) x := rfl

theorem augIdealShiftD_d (n : ℕ) (x : augIdealCarrier ε (n + 1)) :
    augIdealShiftD ε (n + 1) (augIdealShiftD ε n x) = 0 := by
  rw [augIdealShiftD_apply, augIdealShiftD_apply]
  have hneg : (augIdealModule ε).d (n + 1 + 1) (-(augIdealModule ε).d (n + 1) x)
      = -(augIdealModule ε).d (n + 1 + 1) ((augIdealModule ε).d (n + 1) x) :=
    ((augIdealModule ε).dₗ (n + 1 + 1)).map_neg _
  rw [hneg, (augIdealModule ε).d_d, neg_zero, neg_zero]

/-- **The shift of the augmentation ideal**: degree `n` is degree `n + 1` of the ideal, and the
differential changes sign. -/
noncomputable def augIdealShift : Cochain R where
  carrier n := augIdealCarrier ε (n + 1)
  group _ := inferInstance
  smul _ := inferInstance
  d := augIdealShiftD ε
  d_d := augIdealShiftD_d ε

/-- **The `k`-fold tensor power of the shifted augmentation ideal**, the `k`-th piece of the bar
construction. -/
noncomputable def barPower : ℕ → Cochain R
  | 0 => Cochain.ground R
  | (k + 1) => (augIdealShift ε).tensor (barPower k)

@[simp] theorem barPower_zero : barPower ε 0 = Cochain.ground R := rfl

@[simp] theorem barPower_succ (k : ℕ) :
    barPower ε (k + 1) = (augIdealShift ε).tensor (barPower ε k) := rfl

end Shift

end GaloisForLFunctions.HTGeometry
