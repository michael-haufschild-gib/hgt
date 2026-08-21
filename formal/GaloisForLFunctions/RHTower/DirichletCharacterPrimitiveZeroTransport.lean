import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveEulerProduct
import GaloisForLFunctions.RHTower.ChenGuptaLiNonprincipalAnalytic

/-!
# Primitive-conductor transport for CGL critical-strip zero records

This file turns the global primitive Euler-product zero equivalence into the
finite data shape used by Chen--Gupta--Li's reduction from all characters at
an ambient modulus to primitive characters at every divisor conductor.

Every certified nonprincipal critical-strip zero is sent to the same zero
point of its canonical primitive conductor character. The target carries its
positive conductor divisor, primitivity, and nonprincipality as data.

This is record-level transport only. It does not yet prove an equality of
zero-divisor multiplicities or a count inequality after summing fibers.
-/

open Complex LSeries DirichletCharacter

noncomputable section

namespace RHTower

/-- A positive literal divisor of the original modulus. Positivity supplies
the nonzero-modulus instance required to evaluate its `L`-function. -/
structure CGLPositiveModulusDivisor (n : ℕ) where
  value : ℕ
  divides : value ∣ n + 1
  positive : 0 < value

instance (n : ℕ) (d : CGLPositiveModulusDivisor n) : NeZero d.value :=
  ⟨Nat.ne_of_gt d.positive⟩

/-- A nonprincipal primitive-conductor critical-strip zero together with its
literal positive conductor divisor of the original modulus. -/
structure CGLPrimitiveConductorCriticalStripZero (n : ℕ) where
  conductor : CGLPositiveModulusDivisor n
  character : DirichletCharacter ℂ conductor.value
  character_ne_one : character ≠ 1
  primitive : DirichletCharacter.IsPrimitive character
  point : ℂ
  vanishes : DirichletCharacter.LFunction character point = 0
  half_le : (1 / 2 : ℝ) ≤ point.re
  lt_one : point.re < 1

/-- Transport a certified nonprincipal CGL critical-strip zero to its
canonical primitive-conductor zero record. -/
noncomputable def cglPrimitiveConductorCriticalStripZeroOfNonprincipal
    (n : ℕ) (z : CGLNonprincipalCriticalStripLZero n) :
    CGLPrimitiveConductorCriticalStripZero n := by
  let χ : NonprincipalDirichletCharacter n := ⟨z.character, z.character_ne_one⟩
  let s : CGLPositiveRealPartPoint := ⟨z.point, by linarith [z.half_le]⟩
  let d : CGLPositiveModulusDivisor n := {
    value := χ.1.conductor
    divides := (cglPrimitiveCharacterReduction n χ).conductor_dvd_modulus
    positive := (cglPrimitiveCharacterReduction n χ).conductor_pos }
  have hzero : cglPrimitiveLFunction n χ z.point = 0 :=
    (cglPrimitiveLFunction_zero_iff_input n χ s).mpr z.vanishes
  refine {
    conductor := d
    character := (cglPrimitiveCharacterReduction n χ).primitiveCharacter
    character_ne_one := (cglPrimitiveCharacterReduction n χ).nonprincipal
    primitive := (cglPrimitiveCharacterReduction n χ).primitive
    point := z.point
    vanishes := ?_
    half_le := z.half_le
    lt_one := z.lt_one }
  dsimp [d]
  unfold cglPrimitiveLFunction at hzero
  exact hzero

/-- The transport leaves the critical-strip zero point unchanged. -/
theorem cglPrimitiveConductorCriticalStripZeroOfNonprincipal_point_eq
    (n : ℕ) (z : CGLNonprincipalCriticalStripLZero n) :
    (cglPrimitiveConductorCriticalStripZeroOfNonprincipal n z).point = z.point := by
  unfold cglPrimitiveConductorCriticalStripZeroOfNonprincipal
  dsimp

/-- The transported primitive conductor divides the original ambient modulus. -/
theorem cglPrimitiveConductorCriticalStripZeroOfNonprincipal_conductor_dvd
    (n : ℕ) (z : CGLNonprincipalCriticalStripLZero n) :
    (cglPrimitiveConductorCriticalStripZeroOfNonprincipal n z).conductor.value ∣ n + 1 := by
  unfold cglPrimitiveConductorCriticalStripZeroOfNonprincipal
  dsimp
  exact (cglPrimitiveCharacterReduction n ⟨z.character, z.character_ne_one⟩).conductor_dvd_modulus

end RHTower
