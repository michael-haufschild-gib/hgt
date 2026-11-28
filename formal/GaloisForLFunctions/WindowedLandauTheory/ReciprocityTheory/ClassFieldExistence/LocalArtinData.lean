import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalArtinInertiaImage
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.SmoothWeilAction
import GaloisForLFunctions.HTGeometry.MilnorKTameValuation

/-! The geometric inverse Artin law, including factorization of smooth
Weil characters and matching with arithmetic idelic reciprocity. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GaloisForLFunctions.HTGeometry
open scoped WithZero

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

local notation "C" => CompactIdeleClassQuotient K
local notation "M" => maximalAbelianExtension K Ω
local notation "Fv" => v.adicCompletion K
local notation "ν" => tameValHom (Valued.v : Valuation Fv ℤᵐ⁰)

/-- The inverse local Artin map in geometric normalization. The ambient
idelic Artin map in the last field uses arithmetic normalization. -/
structure IsLocalArtin {h : IsPlaceOver A v} (b : Weil h →* Fvˣ) : Prop where
  surj : Function.Surjective b
  cont : Continuous fun σ : Ine (F := K) A => b (ineIncl h σ)
  ord_eq : ∀ σ, Multiplicative.toAdd (ν (b σ)) = -deg σ
  factor : ∀ ξ : Weil h →* ℂˣ, IsSmooth ξ →
    ∃ χ : Fvˣ →* ℂˣ, IsOpen (χ.ker : Set Fvˣ) ∧ ξ = χ.comp b
  glob : ∀ a : C →* Gal(M/K), MatchesFiniteIdelicArtin K Ω a →
    ∀ σ : Weil h, a (toCompactIdeleClassQuotient K (finiteEmbedding v (b σ)⁻¹)) =
      toMaxAb K Ω σ.val

theorem IsLocalArtin.smooth {h : IsPlaceOver A v} {b : Weil h →* Fvˣ}
    (hb : IsLocalArtin K Ω b) {χ : Fvˣ →* ℂˣ} (hχ : IsOpen (χ.ker : Set Fvˣ)) :
    IsSmooth (χ.comp b) :=
  hχ.preimage hb.cont

end GlobalTheory.Reciprocity
