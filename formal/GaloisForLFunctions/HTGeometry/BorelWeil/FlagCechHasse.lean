import GaloisForLFunctions.HTGeometry.BorelWeil.FlagGlobalSections

/-!
# Čech Hasse gluing for dominant Borel--Weil sections

For a dominant weight, every compatible family of Bruhat-chart values is the Čech cochain of one
unique global polynomial section.  This file packages the degree-zero Borel--Weil result as a Hasse
equivalence and a unique gluing theorem, with dominance carried by the weight type.

Compatibility is essential for existence.  Once two sections are already global, however, their
value on the identity Bruhat chart alone detects equality; the remaining charts are redundant for
separation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

/-- A dominant natural weight, with dominance carried in the type. -/
abbrev BorelWeilDominantWeight (N : ℕ) :=
  {lam : Fin N → ℕ // Antitone lam}

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- Send a global dominant polynomial section to its compatible Bruhat-chart cocycle. -/
noncomputable def dominantGlobalCochainMap (lam : BorelWeilDominantWeight N) :
    polySections (k := k) lam.1 →
      flagCocycles N k (fun i ↦ (lam.1 i : ℤ)) 0 :=
  fun p ↦ ⟨globalCochain (fun i ↦ (lam.1 i : ℤ)) p.1,
    globalCochain_mem_flagCocycles p.2⟩

/-- Compatible Bruhat-chart cocycles distinguish global dominant sections. -/
theorem dominantGlobalCochainMap_injective (lam : BorelWeilDominantWeight N) :
    Function.Injective (dominantGlobalCochainMap (k := k) lam) := by
  intro p q h
  apply Subtype.ext
  exact globalCochain_injective
    (lam := fun i ↦ (lam.1 i : ℤ)) (congrArg Subtype.val h)

/-- Every compatible Bruhat-chart cocycle is realized by a global dominant section. -/
theorem dominantGlobalCochainMap_surjective [CharZero k]
    (lam : BorelWeilDominantWeight N) :
    Function.Surjective (dominantGlobalCochainMap (k := k) lam) := by
  intro ω
  obtain ⟨p, hp, hω⟩ := exists_globalCochain_eq lam.2 ω.2
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  exact hω.symm

/-- Dominant global sections are equivalent to compatible Bruhat local data. -/
noncomputable def dominantGlobalCochainHasseEquiv [CharZero k]
    (lam : BorelWeilDominantWeight N) :
    polySections (k := k) lam.1 ≃
      flagCocycles N k (fun i ↦ (lam.1 i : ℤ)) 0 :=
  Equiv.ofBijective (dominantGlobalCochainMap (k := k) lam)
    ⟨dominantGlobalCochainMap_injective lam,
      dominantGlobalCochainMap_surjective lam⟩

/-- Every compatible Bruhat local packet glues to one unique dominant global section. -/
theorem dominantGlobalCochain_hasse_existsUnique [CharZero k]
    (lam : BorelWeilDominantWeight N)
    (ω : flagCocycles N k (fun i ↦ (lam.1 i : ℤ)) 0) :
    ∃! p : polySections (k := k) lam.1,
      dominantGlobalCochainMap (k := k) lam p = ω := by
  obtain ⟨p, hp⟩ := dominantGlobalCochainMap_surjective lam ω
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact dominantGlobalCochainMap_injective lam (hq.trans hp.symm)

/-- The identity Bruhat chart alone detects equality of global polynomial sections. -/
theorem polySection_congr_identityChart_hasse_iff
    (lam : BorelWeilDominantWeight N)
    (p q : polySections (k := k) lam.1) :
    p = q ↔
      globalCochain (fun i ↦ (lam.1 i : ℤ)) p.1
          ({(1 : Equiv.Perm (Fin N))} : Finset (Equiv.Perm (Fin N))) =
        globalCochain (fun i ↦ (lam.1 i : ℤ)) q.1
          ({(1 : Equiv.Perm (Fin N))} : Finset (Equiv.Perm (Fin N))) := by
  classical
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    apply algebraMap_flagLoc_injective
    simpa [globalCochain] using h

/-- One identity-chart value detects a nonzero dominant global section. -/
theorem identityChart_ne_zero_of_polySection_ne_zero
    (lam : BorelWeilDominantWeight N)
    (p : polySections (k := k) lam.1) (hp : p ≠ 0) :
    globalCochain (fun i ↦ (lam.1 i : ℤ)) p.1
        ({(1 : Equiv.Perm (Fin N))} : Finset (Equiv.Perm (Fin N))) ≠ 0 := by
  intro h
  apply hp
  exact (polySection_congr_identityChart_hasse_iff lam p 0).2
    (by simpa [globalCochain] using h)

end GaloisForLFunctions.HTGeometry.BorelWeil
