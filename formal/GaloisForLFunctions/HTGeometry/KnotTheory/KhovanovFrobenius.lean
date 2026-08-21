import Mathlib

/-!
# Khovanov Frobenius algebra and an all-merge resolution square

This module formalizes `𝔽₂[X]/(X²)` in the basis `(1, X)`, its Khovanov
Frobenius structure, and the first non-vacuous cube face: two merge orders of three circles yield
the same map, hence cancel in the unsigned characteristic-two differential.
-/

namespace GaloisForLFunctions.HTGeometry.KnotTheory

abbrev KhovanovA := ZMod 2 × ZMod 2
abbrev KhovanovTensorSquare := Fin 2 → Fin 2 → ZMod 2
abbrev KhovanovTensorCube := Fin 2 → Fin 2 → Fin 2 → ZMod 2

def khUnit : KhovanovA := (1, 0)
def khX : KhovanovA := (0, 1)

/-- `𝔽₂[X]/(X²)` in basis `(1, X)`. -/
def khMul (a b : KhovanovA) : KhovanovA :=
  (a.1 * b.1, a.1 * b.2 + a.2 * b.1)

def khCounit (a : KhovanovA) : ZMod 2 := a.2

/-- Khovanov comultiplication: `Δ(1)=1⊗X+X⊗1`, `Δ(X)=X⊗X`. -/
def khDelta (a : KhovanovA) : KhovanovTensorSquare := fun i j =>
  if i = 0 then
    if j = 0 then 0 else a.1
  else if j = 0 then a.1 else a.2

def khLeftCounit (t : KhovanovTensorSquare) : KhovanovA := (t 1 0, t 1 1)
def khRightCounit (t : KhovanovTensorSquare) : KhovanovA := (t 0 1, t 1 1)

def khDeltaLeft (t : KhovanovTensorSquare) : KhovanovTensorCube := fun i j k =>
  khDelta (t 0 k, t 1 k) i j

def khDeltaRight (t : KhovanovTensorSquare) : KhovanovTensorCube := fun i j k =>
  khDelta (t i 0, t i 1) j k

def khPureTensor (a b : KhovanovA) : KhovanovTensorSquare := fun i j =>
  (if i = 0 then a.1 else a.2) * (if j = 0 then b.1 else b.2)

def khTensorDeltaRight (a b : KhovanovA) : KhovanovTensorCube := fun i j k =>
  (if i = 0 then a.1 else a.2) * khDelta b j k

def khTensorDeltaLeft (a b : KhovanovA) : KhovanovTensorCube := fun i j k =>
  khDelta a i j * (if k = 0 then b.1 else b.2)

def khMultiplyLeft (t : KhovanovTensorCube) : KhovanovTensorSquare := fun i k =>
  if i = 0 then t 0 0 k else t 0 1 k + t 1 0 k

def khMultiplyRight (t : KhovanovTensorCube) : KhovanovTensorSquare := fun i k =>
  if k = 0 then t i 0 0 else t i 0 1 + t i 1 0

theorem khMul_assoc (a b c : KhovanovA) : khMul (khMul a b) c = khMul a (khMul b c) := by
  ext <;> simp [khMul] <;> ring

theorem khUnit_mul (a : KhovanovA) : khMul khUnit a = a := by
  ext <;> simp [khMul, khUnit]

theorem khMul_unit (a : KhovanovA) : khMul a khUnit = a := by
  ext <;> simp [khMul, khUnit]

theorem khMul_comm (a b : KhovanovA) : khMul a b = khMul b a := by
  ext <;> simp [khMul] <;> ring

theorem khX_square : khMul khX khX = 0 := by
  ext <;> simp [khMul, khX]

theorem khLeftCounit_delta (a : KhovanovA) : khLeftCounit (khDelta a) = a := by
  ext <;> simp [khLeftCounit, khDelta]

theorem khRightCounit_delta (a : KhovanovA) : khRightCounit (khDelta a) = a := by
  ext <;> simp [khRightCounit, khDelta]

theorem khDelta_coassoc (a : KhovanovA) :
    khDeltaLeft (khDelta a) = khDeltaRight (khDelta a) := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [khDeltaLeft, khDeltaRight, khDelta]

theorem khFrobenius_right (a b : KhovanovA) :
    khDelta (khMul a b) = khMultiplyLeft (khTensorDeltaRight a b) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [khDelta, khMul, khMultiplyLeft, khTensorDeltaRight]

theorem khFrobenius_left (a b : KhovanovA) :
    khDelta (khMul a b) = khMultiplyRight (khTensorDeltaLeft a b) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [khDelta, khMul, khMultiplyRight, khTensorDeltaLeft]

/-- Fully specified rank-two Frobenius data used by the resolution cube. -/
structure KhovanovFrobeniusSystem where
  unit : KhovanovA
  x : KhovanovA
  multiply : KhovanovA → KhovanovA → KhovanovA
  comultiply : KhovanovA → KhovanovTensorSquare
  counit : KhovanovA → ZMod 2
  leftCounit : KhovanovTensorSquare → KhovanovA
  rightCounit : KhovanovTensorSquare → KhovanovA
  deltaLeft : KhovanovTensorSquare → KhovanovTensorCube
  deltaRight : KhovanovTensorSquare → KhovanovTensorCube
  tensorDeltaLeft : KhovanovA → KhovanovA → KhovanovTensorCube
  tensorDeltaRight : KhovanovA → KhovanovA → KhovanovTensorCube
  multiplyLeft : KhovanovTensorCube → KhovanovTensorSquare
  multiplyRight : KhovanovTensorCube → KhovanovTensorSquare
  mul_assoc : ∀ a b c, multiply (multiply a b) c = multiply a (multiply b c)
  unit_mul : ∀ a, multiply unit a = a
  mul_unit : ∀ a, multiply a unit = a
  x_square : multiply x x = 0
  left_counit : ∀ a, leftCounit (comultiply a) = a
  right_counit : ∀ a, rightCounit (comultiply a) = a
  coassoc : ∀ a, deltaLeft (comultiply a) = deltaRight (comultiply a)
  frobenius_right : ∀ a b,
    comultiply (multiply a b) = multiplyLeft (tensorDeltaRight a b)
  frobenius_left : ∀ a b,
    comultiply (multiply a b) = multiplyRight (tensorDeltaLeft a b)

/-- The standard Khovanov Frobenius system over `𝔽₂`. -/
def standardKhovanovFrobenius : KhovanovFrobeniusSystem where
  unit := khUnit
  x := khX
  multiply := khMul
  comultiply := khDelta
  counit := khCounit
  leftCounit := khLeftCounit
  rightCounit := khRightCounit
  deltaLeft := khDeltaLeft
  deltaRight := khDeltaRight
  tensorDeltaLeft := khTensorDeltaLeft
  tensorDeltaRight := khTensorDeltaRight
  multiplyLeft := khMultiplyLeft
  multiplyRight := khMultiplyRight
  mul_assoc := khMul_assoc
  unit_mul := khUnit_mul
  mul_unit := khMul_unit
  x_square := khX_square
  left_counit := khLeftCounit_delta
  right_counit := khRightCounit_delta
  coassoc := khDelta_coassoc
  frobenius_right := khFrobenius_right
  frobenius_left := khFrobenius_left

/-- A two-step chain complex, retaining its closed square-zero witness. -/
structure TwoStepChainComplex where
  C0 : Type
  C1 : Type
  C2 : Type
  zeroC2 : Zero C2
  d0 : C0 → C1
  d1 : C1 → C2
  d_squared : ∀ x, d1 (d0 x) = 0

/-- One oriented face of a cube of resolutions, with its two saddle compositions identified. -/
structure ResolutionSquare where
  C00 : Type
  C10 : Type
  C01 : Type
  C11 : Type
  edge00_10 : C00 → C10
  edge00_01 : C00 → C01
  edge10_11 : C10 → C11
  edge01_11 : C01 → C11
  face_commutes : ∀ x, edge10_11 (edge00_10 x) = edge01_11 (edge00_01 x)

abbrev KhovanovMergeC0 := KhovanovA × KhovanovA × KhovanovA
abbrev KhovanovMergeC1 := (KhovanovA × KhovanovA) × (KhovanovA × KhovanovA)

/-- Merge the first two circles in the all-merge two-crossing resolution square. -/
def khMergeLeft (x : KhovanovMergeC0) : KhovanovA × KhovanovA :=
  (khMul x.1 x.2.1, x.2.2)

/-- Merge the last two circles in the all-merge two-crossing resolution square. -/
def khMergeRight (x : KhovanovMergeC0) : KhovanovA × KhovanovA :=
  (x.1, khMul x.2.1 x.2.2)

/-- Merge the two circles at the terminal resolution. -/
def khMergeFinal (x : KhovanovA × KhovanovA) : KhovanovA :=
  khMul x.1 x.2

/-- Associativity makes the two all-merge paths around this resolution face agree. -/
theorem khMerge_square_commutes (x : KhovanovMergeC0) :
    khMergeFinal (khMergeLeft x) = khMergeFinal (khMergeRight x) :=
  khMul_assoc _ _ _

/-- Explicit commuting all-merge face in the two-crossing cube of resolutions. -/
def khAllMergeResolutionSquare : ResolutionSquare where
  C00 := KhovanovMergeC0
  C10 := KhovanovA × KhovanovA
  C01 := KhovanovA × KhovanovA
  C11 := KhovanovA
  edge00_10 := khMergeLeft
  edge00_01 := khMergeRight
  edge10_11 := khMergeFinal
  edge01_11 := khMergeFinal
  face_commutes := khMerge_square_commutes

/-- The two outgoing saddle maps in the all-merge two-crossing resolution square. -/
def khMergeD0 (x : KhovanovMergeC0) : KhovanovMergeC1 :=
  (khMergeLeft x, khMergeRight x)

/-- The terminal differential is the mod-two sum of the two final merge maps. -/
def khMergeD1 (x : KhovanovMergeC1) : KhovanovA :=
  khMergeFinal x.1 + khMergeFinal x.2

/-- The all-merge two-crossing face anticommutes over `𝔽₂`, hence its unsigned differential squares
to zero. -/
theorem khMerge_d_squared (x : KhovanovMergeC0) : khMergeD1 (khMergeD0 x) = 0 := by
  change khMergeFinal (khMergeLeft x) + khMergeFinal (khMergeRight x) = 0
  rw [khMerge_square_commutes]
  ext <;> exact CharTwo.add_self_eq_zero _

/-- Closed two-crossing all-merge cube-of-resolutions complex. -/
def khAllMergeResolutionCube : TwoStepChainComplex where
  C0 := KhovanovMergeC0
  C1 := KhovanovMergeC1
  C2 := KhovanovA
  zeroC2 := inferInstance
  d0 := khMergeD0
  d1 := khMergeD1
  d_squared := khMerge_d_squared

end GaloisForLFunctions.HTGeometry.KnotTheory
