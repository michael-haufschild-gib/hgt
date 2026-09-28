import GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy

/-!
# Canonical modular automorphism of a literal Burnol packet

Companion to `PrimeBurnolFiniteModularSupport` and `PrimeBurnolSourceFrameCubicHolonomy`: the
canonical inner modular automorphism `σ_F(A) = C_F⁻¹ A C_F` of a finite injective literal Burnol
packet is a ring automorphism of the full matrix algebra (PBFMS.3).
-/

open Matrix

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Inner modular automorphism of a ring attached to a unit, packaged as a ring equivalence. -/
def sourceModularRingEquiv {A : Type*} [Ring A] (c : Aˣ) : A ≃+* A :=
  { sourceModularAutomorphism c with
    invFun := sourceModularAutomorphism c⁻¹
    left_inv := fun x => by
      change (↑(c⁻¹⁻¹) : A) * ((↑(c⁻¹) : A) * x * (↑c : A)) * (↑(c⁻¹) : A) = x
      simp [mul_assoc]
    right_inv := fun x => by
      change (↑(c⁻¹) : A) * ((↑(c⁻¹⁻¹) : A) * x * (↑(c⁻¹) : A)) * (↑c : A) = x
      simp [mul_assoc] }

@[simp] theorem sourceModularRingEquiv_apply {A : Type*} [Ring A] (c : Aˣ) (x : A) :
    sourceModularRingEquiv c x = (↑(c⁻¹) : A) * x * (↑c : A) := rfl

/-- **(PBFMS.3)** The canonical inner modular automorphism of an injective finite literal
Burnol packet: `σ_F(A) = C_F⁻¹ A C_F`, with `C_F` the complete literal Burnol Gram. -/
def primeBurnolModularAutomorphism
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ ≃+* Matrix (Fin N) (Fin N) ℂ :=
  sourceModularRingEquiv (primeBurnolWindowGramUnit pe hpe kappa)

theorem primeBurnolModularAutomorphism_apply
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℂ) :
    primeBurnolModularAutomorphism pe hpe kappa A =
      (primeBurnolWindowGramMatrix pe kappa)⁻¹ * A * primeBurnolWindowGramMatrix pe kappa := by
  rw [primeBurnolModularAutomorphism, sourceModularRingEquiv_apply, Matrix.coe_units_inv,
    coe_primeBurnolWindowGramUnit]

end

end RHTower
