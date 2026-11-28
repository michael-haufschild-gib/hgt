import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneClasses
import Mathlib.RepresentationTheory.Irreducible

/-! Irreducible Weil actions have zero monodromy because the monodromy
kernel is invariant. Irreducibility is invariant under isomorphism. -/

noncomputable section

open NumberField IsDedekindDomain Module
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open scoped MonoidAlgebra

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem WDRep.Iso.irreducible {a : WDRep h V} {b : WDRep h V'}
    (hab : a.Iso b) (ha : a.ρ.IsIrreducible) : b.ρ.IsIrreducible := by
  obtain ⟨e, he, -⟩ := hab
  let f : Representation.IntertwiningMap a.ρ b.ρ :=
    { toLinearMap := e.toLinearMap
      isIntertwining' := fun s => LinearMap.ext (he s) }
  let g := Representation.IntertwiningMap.equivLinearMapAsModule a.ρ b.ρ f
  have hg : Function.Bijective g := e.bijective
  exact (Representation.irreducible_iff_isSimpleModule_asModule b.ρ).mpr
    ((LinearEquiv.ofBijective g hg).isSimpleModule_iff.mp
      ((Representation.irreducible_iff_isSimpleModule_asModule a.ρ).mp ha))

theorem WDRep.monodromy_eq_zero_of_irreducible (a : WDRep h V) (hρ : a.ρ.IsIrreducible) :
    a.N = 0 := by
  let U : Subrepresentation a.ρ :=
    { toSubmodule := a.N.ker
      apply_mem_toSubmodule := fun s x hx => by
        have hx0 : a.N x = 0 := LinearMap.mem_ker.mp hx
        apply LinearMap.mem_ker.mpr
        have hc := a.comm_apply s x
        have hq : (normV w : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).pos.ne'
        rw [hx0, map_zero, eq_comm, smul_eq_zero] at hc
        exact hc.resolve_left (zpow_ne_zero _ hq) }
  letI := hρ
  rcases eq_bot_or_eq_top U with h | h
  · have hker : a.N.ker = ⊥ := congrArg Subrepresentation.toSubmodule h
    have hi : Function.Injective a.N := LinearMap.ker_eq_bot.mp hker
    have hp (k : ℕ) : Function.Injective (a.N ^ k : End ℂ V) := by
      induction k with
      | zero =>
        rw [pow_zero]
        intro x y hxy
        exact hxy
      | succ k ih =>
        rw [pow_succ']
        exact hi.comp ih
    obtain ⟨m, hm⟩ := a.nilpotent
    have hz := hp m
    rw [hm] at hz
    exact LinearMap.ext fun x => hz (by simp)
  · have hker : a.N.ker = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact LinearMap.ker_eq_top.mp hker

/-- Irreducibility of the underlying Weil action of a parameter. -/
def WD.Irreducible (x : WD h) : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧ a.ρ.IsIrreducible

theorem WD.irreducible_mk_iff (a : WDRep h V) :
    (WD.mk a).Irreducible ↔ a.ρ.IsIrreducible := by
  constructor
  · rintro ⟨n, b, hb, hρ⟩
    exact (WD.mk_eq_mk.mp hb).irreducible hρ
  · intro hρ
    obtain ⟨n, b, hb⟩ := (WD.mk a).exists_rep
    exact ⟨n, b, hb, (WD.mk_eq_mk.mp hb.symm).irreducible hρ⟩

theorem WD.Irreducible.mono0 {x : WD h} (hx : x.Irreducible) : x.mono0 := by
  obtain ⟨n, a, rfl, hρ⟩ := hx
  exact (WD.mono0_mk _).mpr (a.monodromy_eq_zero_of_irreducible hρ)

end GlobalTheory.WeilDeligne
