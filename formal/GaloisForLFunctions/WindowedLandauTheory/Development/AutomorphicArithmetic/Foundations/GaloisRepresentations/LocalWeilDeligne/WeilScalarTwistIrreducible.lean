import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothRepresentationScalarTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.IrreducibleWeilDeligne
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneOperations

/-! Twisting the action by an invertible scalar preserves its
invariant subspaces and hence irreducibility. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem WDRep.irreducible_twist (a : WDRep h V) [a.ρ.IsIrreducible]
    (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    (a.twist χ hχ).ρ.IsIrreducible :=
  Representation.scalarTwist_irreducible a.ρ χ

theorem WD.Irreducible.twist {x : WD h} (hx : x.Irreducible)
    (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : (x.lpTwist χ hχ).Irreducible := by
  obtain ⟨n, a, rfl, ha⟩ := hx
  letI := ha
  rw [WD.lpTwist_mk, WD.irreducible_mk_iff]
  exact a.irreducible_twist χ hχ

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WDRep.irreducible_twist
