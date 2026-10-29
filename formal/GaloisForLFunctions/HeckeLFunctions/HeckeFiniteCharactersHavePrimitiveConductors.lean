import GaloisForLFunctions.HTGeometry.FiniteRingCharactersHavePrimitiveConductors
import GaloisForLFunctions.HeckeLFunctions.HeckeIdealThetaIsUnitPeriodic

/-!
# Primitive conductors of the finite Hecke character

Pulling back the residue character's largest descent ideal gives a
nonzero integral conductor dividing the original finite modulus.
The character descends uniquely to the quotient by this conductor,
where it is primitive. Descent to any divisor modulus is equivalent
to divisibility by the conductor.
-/

noncomputable section
open NumberField
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

local instance : Finite (𝓞 K ⧸ 𝔪.fin) :=
  𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot

/-- The finite conductor of the actual residue character, viewed as an integral ideal. -/
def heckeFiniteConductor (ψ : HeckeCharacter 𝔪) : Ideal (𝓞 K) :=
  Ideal.comap (Ideal.Quotient.mk 𝔪.fin)
    (FiniteRing.conductorIdeal (finiteHeckeWeight 𝔪 ψ))

theorem modulus_le_heckeFiniteConductor (ψ : HeckeCharacter 𝔪) :
    𝔪.fin ≤ heckeFiniteConductor 𝔪 ψ := by
  intro x hx
  change Ideal.Quotient.mk 𝔪.fin x ∈ FiniteRing.conductorIdeal (finiteHeckeWeight 𝔪 ψ)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact Ideal.zero_mem _

theorem heckeFiniteConductor_dvd_modulus (ψ : HeckeCharacter 𝔪) :
    heckeFiniteConductor 𝔪 ψ ∣ 𝔪.fin :=
  Ideal.dvd_iff_le.mpr (modulus_le_heckeFiniteConductor 𝔪 ψ)

theorem heckeFiniteConductor_ne_bot (ψ : HeckeCharacter 𝔪) :
    heckeFiniteConductor 𝔪 ψ ≠ ⊥ := by
  intro h
  apply 𝔪.fin_ne_bot
  apply le_bot_iff.mp
  simpa only [h] using modulus_le_heckeFiniteConductor 𝔪 ψ

/-- Reduction from the given modulus to its finite conductor. -/
def heckeConductorReduction (ψ : HeckeCharacter 𝔪) :
    (𝓞 K ⧸ 𝔪.fin) →+* (𝓞 K ⧸ heckeFiniteConductor 𝔪 ψ) :=
  Ideal.Quotient.factor (modulus_le_heckeFiniteConductor 𝔪 ψ)

theorem heckeConductorReduction_surjective (ψ : HeckeCharacter 𝔪) :
    Function.Surjective (heckeConductorReduction 𝔪 ψ) :=
  Ideal.Quotient.factor_surjective _

theorem ker_heckeConductorReduction (ψ : HeckeCharacter 𝔪) :
    RingHom.ker (heckeConductorReduction 𝔪 ψ) =
      FiniteRing.conductorIdeal (finiteHeckeWeight 𝔪 ψ) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) a = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- The actual finite Hecke character descends uniquely to its conductor. -/
theorem exists_heckePrimitiveFiniteCharacter (ψ : HeckeCharacter 𝔪) :
    ∃ χ : MulChar (𝓞 K ⧸ heckeFiniteConductor 𝔪 ψ) ℂ,
      FiniteRing.inflateChar (heckeConductorReduction 𝔪 ψ) χ = finiteHeckeWeight 𝔪 ψ := by
  apply (FiniteRing.exists_inflateChar_eq_iff_ker_le_conductorIdeal _
    (heckeConductorReduction_surjective 𝔪 ψ) _).mpr
  exact (ker_heckeConductorReduction 𝔪 ψ).le

/-- The primitive character on the integral conductor quotient. -/
def heckePrimitiveFiniteCharacter (ψ : HeckeCharacter 𝔪) :
    MulChar (𝓞 K ⧸ heckeFiniteConductor 𝔪 ψ) ℂ :=
  Classical.choose (exists_heckePrimitiveFiniteCharacter 𝔪 ψ)

theorem inflate_heckePrimitiveFiniteCharacter (ψ : HeckeCharacter 𝔪) :
    FiniteRing.inflateChar (heckeConductorReduction 𝔪 ψ)
      (heckePrimitiveFiniteCharacter 𝔪 ψ) = finiteHeckeWeight 𝔪 ψ :=
  Classical.choose_spec (exists_heckePrimitiveFiniteCharacter 𝔪 ψ)

theorem heckePrimitiveFiniteCharacter_isPrimitive (ψ : HeckeCharacter 𝔪) :
    FiniteRing.IsPrimitive (heckePrimitiveFiniteCharacter 𝔪 ψ) :=
  FiniteRing.isPrimitive_of_ker_eq_conductorIdeal _
    (heckeConductorReduction_surjective 𝔪 ψ) _ _
    (inflate_heckePrimitiveFiniteCharacter 𝔪 ψ) (ker_heckeConductorReduction 𝔪 ψ)

theorem heckePrimitiveFiniteCharacter_unique (ψ : HeckeCharacter 𝔪)
    (χ : MulChar (𝓞 K ⧸ heckeFiniteConductor 𝔪 ψ) ℂ)
    (hχ : FiniteRing.inflateChar (heckeConductorReduction 𝔪 ψ) χ = finiteHeckeWeight 𝔪 ψ) :
    χ = heckePrimitiveFiniteCharacter 𝔪 ψ :=
  FiniteRing.inflateChar_injective _ (heckeConductorReduction_surjective 𝔪 ψ)
    (hχ.trans (inflate_heckePrimitiveFiniteCharacter 𝔪 ψ).symm)

theorem heckePrimitiveFiniteCharacter_unit (ψ : HeckeCharacter 𝔪)
    (u : (𝓞 K ⧸ 𝔪.fin)ˣ) :
    heckePrimitiveFiniteCharacter 𝔪 ψ (heckeConductorReduction 𝔪 ψ (u : 𝓞 K ⧸ 𝔪.fin)) =
      finiteHeckeWeight 𝔪 ψ (u : 𝓞 K ⧸ 𝔪.fin) :=
  (FiniteRing.inflateChar_unit _ _ u).symm.trans
    (DFunLike.congr_fun (inflate_heckePrimitiveFiniteCharacter 𝔪 ψ) (u : 𝓞 K ⧸ 𝔪.fin))

/-- The original finite residue character is primitive exactly at its finite conductor. -/
theorem finiteHeckeWeight_isPrimitive_iff (ψ : HeckeCharacter 𝔪) :
    FiniteRing.IsPrimitive (finiteHeckeWeight 𝔪 ψ) ↔ heckeFiniteConductor 𝔪 ψ = 𝔪.fin := by
  rw [FiniteRing.isPrimitive_iff_conductorIdeal_eq_bot]
  constructor
  · intro h
    ext a
    change Ideal.Quotient.mk 𝔪.fin a ∈ FiniteRing.conductorIdeal (finiteHeckeWeight 𝔪 ψ) ↔ _
    rw [h]
    exact Ideal.Quotient.eq_zero_iff_mem
  · intro h
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ heckeFiniteConductor 𝔪 ψ := hx
    rw [h] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- A divisor modulus admits finite-character descent exactly when it is divisible by the conductor. -/
theorem finiteHeckeWeight_descends_iff (ψ : HeckeCharacter 𝔪)
    (J : Ideal (𝓞 K)) (hJ : 𝔪.fin ≤ J) :
    (∃ χ : MulChar (𝓞 K ⧸ J) ℂ,
      FiniteRing.inflateChar (Ideal.Quotient.factor hJ) χ = finiteHeckeWeight 𝔪 ψ) ↔
      J ≤ heckeFiniteConductor 𝔪 ψ := by
  rw [FiniteRing.exists_inflateChar_eq_iff_ker_le_conductorIdeal _
    (Ideal.Quotient.factor_surjective hJ)]
  constructor
  · intro h a ha
    apply h
    change Ideal.Quotient.mk J a = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  · intro h x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply h
    change Ideal.Quotient.mk J a = 0 at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx

end GaloisForLFunctions.HeckeLFunctions
