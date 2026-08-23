import GaloisForLFunctions.HTGeometry.BorelWeil.FlagGlobalSections

/-!
# Hasse gluing for the Bruhat cover

Compatible chart-local data on the Bruhat cover are exactly global polynomial sections.  For a
dominant weight this is the denominator-clearing gluing theorem; for a nondominant weight both the
global section space and the compatible local space vanish.  Thus the equivalence is unconditional
in the weight.
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- Global polynomial sections are linearly equivalent to compatible Bruhat-chart local sections,
for every natural weight. -/
noncomputable def flagPolySectionsHasseEquivCocycles [CharZero k] (lam : Fin N → ℕ) :
    polySections (k := k) lam ≃ₗ[k]
      flagCocycles N k (fun i => (lam i : ℤ)) 0 :=
  LinearEquiv.ofBijective (polySectionsToCocycles lam) ⟨by
    intro p q h
    apply Subtype.ext
    apply globalCochain_injective (lam := fun i => (lam i : ℤ))
    exact congrArg Subtype.val h, by
    intro ω
    by_cases hlam : Antitone lam
    · obtain ⟨p, hp, hpe⟩ := exists_globalCochain_eq hlam ω.2
      exact ⟨⟨p, hp⟩, Subtype.ext hpe.symm⟩
    · have hω : (ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k) = 0 := by
        have hωbot :
            (ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k) ∈
              (⊥ : Submodule k (Finset (Equiv.Perm (Fin N)) → FlagLoc N k)) := by
          rw [← flagCocycles_zero_eq_bot_of_not_antitone hlam]
          exact ω.2
        simpa only [Submodule.mem_bot] using hωbot
      refine ⟨0, Subtype.ext ?_⟩
      calc
        (polySectionsToCocycles lam (0 : polySections (k := k) lam)).1 =
            (0 : flagCocycles N k (fun i => (lam i : ℤ)) 0).1 :=
          congrArg Subtype.val (map_zero (polySectionsToCocycles lam))
        _ = 0 := rfl
        _ = ω.1 := hω.symm⟩

@[simp] theorem flagPolySectionsHasseEquivCocycles_apply [CharZero k]
    (lam : Fin N → ℕ) (p : polySections (k := k) lam) :
    flagPolySectionsHasseEquivCocycles lam p = polySectionsToCocycles lam p :=
  rfl

/-- Every compatible family of Bruhat-chart local sections has one and only one global polynomial
section. -/
theorem flagCocycle_exists_unique_globalSection [CharZero k] (lam : Fin N → ℕ)
    (ω : flagCocycles N k (fun i => (lam i : ℤ)) 0) :
    ∃! p : polySections (k := k) lam, polySectionsToCocycles lam p = ω := by
  let e : polySections (k := k) lam ≃ₗ[k]
      flagCocycles N k (fun i => (lam i : ℤ)) 0 :=
    flagPolySectionsHasseEquivCocycles (k := k) lam
  refine ⟨e.symm ω, e.apply_symm_apply ω, ?_⟩
  intro p hp
  exact e.injective (hp.trans (e.apply_symm_apply ω).symm)

end GaloisForLFunctions.HTGeometry.BorelWeil
