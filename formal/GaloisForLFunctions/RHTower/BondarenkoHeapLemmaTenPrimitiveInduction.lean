/-
# Bondarenko--Heap Lemma 10: primitive Dirichlet-character induction

The first step of Lemma 10 replaces each nonprincipal character at an ambient
modulus by its primitive inducer. Mathlib constructs that inducer at the
actual conductor. This module packages the source-facing facts needed before
the prime-power correction and explicit-formula steps: the inducer is primitive
and nonprincipal, its conductor divides the ambient modulus, and it agrees
with the original character at every integer coprime to that modulus.

No RH, GRH, zero-density, conductor, or character premise is accepted by these
public results. The nonprincipal input and coprimality condition are certified
data.
-/
import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaTenConductorAggregation

noncomputable section

namespace RHTower

/-- The literal primitive inducer of a certified nonprincipal Dirichlet character modulo
`n + 1`. -/
def bondarenkoHeapPrimitiveInducer (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    DirichletCharacter ℂ χ.1.conductor := χ.1.primitiveCharacter

/-- The source's primitive inducing character is primitive at its actual conductor. -/
theorem bondarenkoHeapPrimitiveInducer_isPrimitive
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    DirichletCharacter.IsPrimitive (bondarenkoHeapPrimitiveInducer n χ) := by
  exact χ.1.primitiveCharacter_isPrimitive

/-- A nonprincipal character cannot acquire the principal character as its primitive inducer. -/
theorem bondarenkoHeapPrimitiveInducer_ne_one
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    bondarenkoHeapPrimitiveInducer n χ ≠ 1 := by
  intro h
  have h' : χ.1.primitiveCharacter = 1 := by
    simpa only [bondarenkoHeapPrimitiveInducer] using h
  apply χ.2
  rw [← χ.1.changeLevel_primitiveCharacter, h']
  simp

/-- The actual conductor of the primitive inducer divides the source ambient modulus. -/
theorem bondarenkoHeapPrimitiveInducer_conductor_dvd_level
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    χ.1.conductor ∣ n + 1 :=
  χ.1.conductor_dvd_level

/-- An integer supplied together with its source-unit certificate modulo `q`. -/
def BondarenkoHeapSourceUnitInteger (q : ℕ) := {a : ℤ // IsCoprime a q}

/-- Away from the ambient conductor primes, the source character and its primitive inducer agree
exactly. This is the finite algebraic support reduction behind Lemma 10's prime-power error. -/
theorem bondarenkoHeapPrimitiveInducer_apply_sourceUnit
    (n : ℕ) (χ : NonprincipalDirichletCharacter n)
    (a : BondarenkoHeapSourceUnitInteger (n + 1)) :
    bondarenkoHeapPrimitiveInducer n χ a.1 = χ.1 a.1 := by
  exact χ.1.primitiveCharacter_apply_of_isCoprime a.2

end RHTower
