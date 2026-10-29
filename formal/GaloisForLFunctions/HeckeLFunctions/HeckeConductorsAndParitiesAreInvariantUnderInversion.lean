import GaloisForLFunctions.HTGeometry.FiniteRingConductorsAreInvariantUnderInversion
import GaloisForLFunctions.HeckeLFunctions.HeckeFiniteCharactersHavePrimitiveConductors
import GaloisForLFunctions.HeckeLFunctions.HeckeGammaFactorsAreArchimedeanMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaHasMellinContinuation

/-!
# Inversion preserves Hecke conductors and real parities

Finite restriction and zero extension commute with inversion of the actual
ray character, so its finite conductor is unchanged. Real signs have
order at most two; the infinite component, all archimedean parities,
the Gamma product, and the Mellin normalizations are therefore unchanged.
-/

noncomputable section
open scoped Classical
open NumberField
namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Finite residue restriction commutes with inversion of the actual ray character. -/
theorem finiteResidueCharacter_inv (ψ : HeckeCharacter 𝔪) :
    finiteResidueCharacter 𝔪 ψ⁻¹ = (finiteResidueCharacter 𝔪 ψ)⁻¹ := rfl

/-- The zero extension to nonunits also commutes with character inversion. -/
theorem finiteHeckeWeight_inv (ψ : HeckeCharacter 𝔪) :
    finiteHeckeWeight 𝔪 ψ⁻¹ = (finiteHeckeWeight 𝔪 ψ)⁻¹ := by
  apply DFunLike.ext
  intro x
  rw [MulChar.inv_apply_eq_inv']
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    rw [finiteHeckeWeight_unit, finiteHeckeWeight_unit]
    rw [finiteResidueCharacter_inv]
    exact Units.val_inv_eq_inv_val _
  · rw [(finiteHeckeWeight 𝔪 ψ⁻¹).map_nonunit hx,
      (finiteHeckeWeight 𝔪 ψ).map_nonunit hx, inv_zero]

/-- Character inversion preserves the actual finite conductor. -/
theorem heckeFiniteConductor_inv (ψ : HeckeCharacter 𝔪) :
    heckeFiniteConductor 𝔪 ψ⁻¹ = heckeFiniteConductor 𝔪 ψ := by
  letI : Finite (𝓞 K ⧸ 𝔪.fin) := 𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot
  rw [heckeFiniteConductor, finiteHeckeWeight_inv, FiniteRing.conductorIdeal_inv]
  rfl

/-- Real signs have order at most two, so the infinite component is unchanged by inversion. -/
theorem infiniteSignCharacter_inv (ψ : HeckeCharacter 𝔪) :
    infiniteSignCharacter 𝔪 ψ⁻¹ = infiniteSignCharacter 𝔪 ψ := by
  apply MonoidHom.ext
  intro σ
  change (infiniteSignCharacter 𝔪 ψ σ)⁻¹ = infiniteSignCharacter 𝔪 ψ σ
  have hσ : σ⁻¹ = σ := by
    funext w
    change (σ w)⁻¹ = σ w
    rcases Int.units_eq_one_or (σ w) with h | h <;> simp [h]
  rw [← map_inv, hσ]

theorem heckeParity_inv (ψ : HeckeCharacter 𝔪) :
    heckeParity 𝔪 ψ⁻¹ = heckeParity 𝔪 ψ := by
  funext w
  simp only [heckeParity, infiniteSignCharacter_inv]

theorem heckeCoordinateParity_inv (ψ : HeckeCharacter 𝔪) :
    heckeCoordinateParity 𝔪 ψ⁻¹ = heckeCoordinateParity 𝔪 ψ := by
  funext i
  cases i <;> simp only [heckeCoordinateParity, heckeParity_inv]

theorem heckePlaceParity_inv (ψ : HeckeCharacter 𝔪) :
    heckePlaceParity 𝔪 ψ⁻¹ = heckePlaceParity 𝔪 ψ := by
  funext v
  simp only [heckePlaceParity, heckeCoordinateParity_inv]

/-- The actual Gamma product is the same for a character and its inverse. -/
theorem heckeGammaFactor_inv (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeGammaFactor 𝔪 ψ⁻¹ s = heckeGammaFactor 𝔪 ψ s := by
  simp only [heckeGammaFactor, heckeCoordinateParity_inv]

theorem heckeThetaMellinWeight_inv (ψ : HeckeCharacter 𝔪) :
    heckeThetaMellinWeight 𝔪 ψ⁻¹ = heckeThetaMellinWeight 𝔪 ψ := by
  simp only [heckeThetaMellinWeight, heckeCoordinateParity_inv]

theorem heckeThetaMellinArgument_inv (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeThetaMellinArgument 𝔪 ψ⁻¹ s = heckeThetaMellinArgument 𝔪 ψ s := by
  simp only [heckeThetaMellinArgument, heckeCoordinateParity_inv]

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.heckeFiniteConductor_inv
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeGammaFactor_inv
