import Mathlib.Algebra.Group.Action.Defs

/-!
# Bar-cochain skeleton for Deninger's arithmetic power transfers

The arithmetic power correspondences form a multiplicative monoid.  Once their framed transfers
act on a coefficient group, the source differential is the inhomogeneous bar coboundary.  This
module records its first three terms and proves the two nilpotence identities needed for the
good degree-two truncation.

No zeta zero, spectral coordinate, positivity statement, or RH hypothesis occurs here.
-/

namespace RHTower

section PowerBar

variable {M V : Type*}
variable [Monoid M] [AddCommGroup V] [DistribMulAction M V]

/-- Degree-zero to degree-one inhomogeneous bar coboundary. -/
def deningerPowerBarD0 (v : V) (n : M) : V :=
  n • v - v

/-- Degree-one to degree-two inhomogeneous bar coboundary. -/
def deningerPowerBarD1 (φ : M → V) (m n : M) : V :=
  m • φ n - φ (m * n) + φ m

/-- Degree-two to degree-three inhomogeneous bar coboundary. -/
def deningerPowerBarD2 (ψ : M → M → V) (l m n : M) : V :=
  l • ψ m n - ψ (l * m) n + ψ l (m * n) - ψ l m

/-- Transfer composition makes the first two bar coboundaries compose to zero. -/
theorem deningerPowerBarD1_comp_D0 (v : V) :
    deningerPowerBarD1 (deningerPowerBarD0 v) = 0 := by
  funext m n
  simp [deningerPowerBarD0, deningerPowerBarD1, smul_sub, mul_smul]
  abel

/-- Associativity makes the second and third bar coboundaries compose to zero. -/
theorem deningerPowerBarD2_comp_D1 (φ : M → V) :
    deningerPowerBarD2 (deningerPowerBarD1 φ) = 0 := by
  funext l m n
  simp [deningerPowerBarD1, deningerPowerBarD2, smul_sub, smul_add,
    mul_smul, mul_assoc]
  abel

/-- Genuine degree-two cocycles used by the good truncation. -/
def DeningerPowerBarCocycle2 :=
  {ψ : M → M → V // deningerPowerBarD2 ψ = 0}

/-- The degree-one coboundary lands in genuine degree-two cocycles. -/
def deningerPowerBarD1Cocycle (φ : M → V) :
    DeningerPowerBarCocycle2 (M := M) (V := V) :=
  ⟨deningerPowerBarD1 φ, deningerPowerBarD2_comp_D1 φ⟩

end PowerBar

end RHTower

