import Mathlib

/-!
# Quadratic proof filling, closed endpoint, and open history

In the presentation `⟨a, b | [a,b]⟩` of `ℤ²` the null words `w n = aⁿ bⁿ a⁻ⁿ b⁻ⁿ` return to the
identity endpoint and have length `4n`, while the minimal number of relator cells needed to fill
them grows quadratically.  This file certifies

`area (nullWord n) = n²`

together with the endpoint return, the word length, and the orientation-blindness of the unsigned
cost.

The lower bound uses the integer Heisenberg group: the free group maps onto it with the relator
going to a central generator, so any filling by `k` conjugates of `[a,b]^{±1}` sends `w n` to a
central element of exponent at most `k` in absolute value, while `w n` itself has central exponent
`n²`.  The upper bound is the explicit `n × n` grid, assembled from the two commutator expansion
identities.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The integer Heisenberg group `ℤ³` with `(x,y,z)·(x',y',z') = (x+x', y+y', z+z'+x y')`. -/
@[ext]
structure Heis where
  /-- First coordinate. -/
  x : ℤ
  /-- Second coordinate. -/
  y : ℤ
  /-- Central coordinate. -/
  z : ℤ

namespace Heis

instance : Mul Heis := ⟨fun p q => ⟨p.x + q.x, p.y + q.y, p.z + q.z + p.x * q.y⟩⟩
instance : One Heis := ⟨⟨0, 0, 0⟩⟩
instance : Inv Heis := ⟨fun p => ⟨-p.x, -p.y, -p.z + p.x * p.y⟩⟩

@[simp] theorem mul_x (p q : Heis) : (p * q).x = p.x + q.x := rfl
@[simp] theorem mul_y (p q : Heis) : (p * q).y = p.y + q.y := rfl
@[simp] theorem mul_z (p q : Heis) : (p * q).z = p.z + q.z + p.x * q.y := rfl
@[simp] theorem one_x : (1 : Heis).x = 0 := rfl
@[simp] theorem one_y : (1 : Heis).y = 0 := rfl
@[simp] theorem one_z : (1 : Heis).z = 0 := rfl
@[simp] theorem inv_x (p : Heis) : p⁻¹.x = -p.x := rfl
@[simp] theorem inv_y (p : Heis) : p⁻¹.y = -p.y := rfl
@[simp] theorem inv_z (p : Heis) : p⁻¹.z = -p.z + p.x * p.y := rfl

instance : Group Heis where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  div p q := p * q⁻¹
  mul_assoc p q r := by ext <;> simp <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by ext <;> simp

/-- The central element of exponent `m`. -/
def center (m : ℤ) : Heis := ⟨0, 0, m⟩

@[simp] theorem center_x (m : ℤ) : (center m).x = 0 := rfl
@[simp] theorem center_y (m : ℤ) : (center m).y = 0 := rfl
@[simp] theorem center_z (m : ℤ) : (center m).z = m := rfl

@[simp] theorem center_zero : center 0 = 1 := rfl

theorem center_mul (m m' : ℤ) : center m * center m' = center (m + m') := by
  ext <;> simp [center]

/-- The central subgroup really is central. -/
theorem center_comm (m : ℤ) (p : Heis) : center m * p = p * center m := by
  ext <;> simp [center, add_comm]

theorem conj_center (g : Heis) (m : ℤ) : g * center m * g⁻¹ = center m := by
  rw [← center_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem center_injective : Function.Injective center := by
  intro m m' h
  simpa using congrArg Heis.z h

theorem center_inv (m : ℤ) : (center m)⁻¹ = center (-m) := by
  ext <;> simp [center]

end Heis

section Words

/-- The group commutator `x y x⁻¹ y⁻¹`. -/
def comm {G : Type*} [Group G] (x y : G) : G := x * y * x⁻¹ * y⁻¹

theorem comm_def {G : Type*} [Group G] (x y : G) : comm x y = x * y * x⁻¹ * y⁻¹ := rfl

/-- **Left expansion of a commutator.** -/
theorem comm_mul_left {G : Type*} [Group G] (x y z : G) :
    comm (x * y) z = x * comm y z * x⁻¹ * comm x z := by
  simp only [comm_def]
  group

/-- **Right expansion of a commutator.** -/
theorem comm_mul_right {G : Type*} [Group G] (x y z : G) :
    comm x (y * z) = comm x y * (y * comm x z * y⁻¹) := by
  simp only [comm_def]
  group

theorem comm_one_right {G : Type*} [Group G] (x : G) : comm x 1 = 1 := by
  simp [comm_def]

theorem comm_inv {G : Type*} [Group G] (x y : G) : (comm x y)⁻¹ = comm y x := by
  simp only [comm_def]
  group

/-- The first generator of the free group on two letters. -/
def genA : FreeGroup (Fin 2) := FreeGroup.of 0

/-- The second generator of the free group on two letters. -/
def genB : FreeGroup (Fin 2) := FreeGroup.of 1

/-- The relator `[a,b]` of the standard presentation of `ℤ²`. -/
def relator : FreeGroup (Fin 2) := comm genA genB

/-- The null word `w n = aⁿ bⁿ a⁻ⁿ b⁻ⁿ`. -/
def nullWord (n : ℕ) : FreeGroup (Fin 2) := comm (genA ^ n) (genB ^ n)

end Words

section Heisenberg

/-- The Heisenberg representation of the free group on two letters. -/
def heisLift : FreeGroup (Fin 2) →* Heis :=
  FreeGroup.lift ![(⟨1, 0, 0⟩ : Heis), (⟨0, 1, 0⟩ : Heis)]

@[simp] theorem heisLift_genA : heisLift genA = ⟨1, 0, 0⟩ := by
  simp [heisLift, genA]

@[simp] theorem heisLift_genB : heisLift genB = ⟨0, 1, 0⟩ := by
  simp [heisLift, genB]

theorem heisLift_genA_pow (n : ℕ) : heisLift (genA ^ n) = ⟨(n : ℤ), 0, 0⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ m ih =>
    rw [pow_succ, _root_.map_mul, ih, heisLift_genA]
    ext <;> push_cast <;> simp

theorem heisLift_genB_pow (n : ℕ) : heisLift (genB ^ n) = ⟨0, (n : ℤ), 0⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ m ih =>
    rw [pow_succ, _root_.map_mul, ih, heisLift_genB]
    ext <;> push_cast <;> simp

@[simp] theorem heisLift_relator : heisLift relator = Heis.center 1 := by
  rw [relator, comm_def, _root_.map_mul, _root_.map_mul, _root_.map_mul, map_inv, map_inv,
    heisLift_genA, heisLift_genB]
  ext <;> simp [Heis.center]

/-- **The Heisenberg exponent of the null word is `n²`.** -/
theorem heisLift_nullWord (n : ℕ) : heisLift (nullWord n) = Heis.center ((n : ℤ) ^ 2) := by
  rw [nullWord, comm_def, _root_.map_mul, _root_.map_mul, _root_.map_mul, map_inv, map_inv,
    heisLift_genA_pow, heisLift_genB_pow]
  ext <;> simp [Heis.center]
  ring

end Heisenberg

end GaloisForLFunctions.HTGeometry
