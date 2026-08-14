import GaloisForLFunctions.HTGeometry.MilnorKResidueMap

/-!
# The residue on symbols of units

A unit of valuation zero contributes no `ξ` to the residue fold: multiplication by
`[ū_a] + v(a)ξ` is multiplication by `[ū_a]` alone.  So a symbol all of whose entries are units of
the valuation ring has zero residue, and its specialization is the symbol of the residues.  This is
what makes the Gersten complex a complex at the generic point, and it identifies the specialization
with the reduction map on the units.

* `resPairAt_snd_eq_zero`, `milnorResidue_eq_zero_of_units` : **the residue kills symbols of
  units.**
* `resPairAt_fst_eq`, `milnorSpecialization_of_units` : **the specialization of a symbol of units
  is the symbol of their residues.**
-/

namespace GaloisForLFunctions.HTGeometry

section Units

variable {K : Type*} [Field K] {k : Type*} [Field k] (D : ResidueData K k)

/-- **The residue vanishes on a symbol of units of valuation zero.** -/
theorem resPairAt_snd_eq_zero : ∀ (l : List Kˣ) (n : ℕ) (h : l.length = n),
    (∀ a ∈ l, D.val' a = 0) → (resPairAt D n l h).2 = 0 := by
  intro l
  induction l with
  | nil =>
      intro n h _
      cases n with
      | zero => rfl
      | succ m => exact absurd h (by simp)
  | cons a t ih =>
      intro n h hl
      cases n with
      | zero => exact absurd h (by simp)
      | succ m =>
          have hav : D.val' a = 0 := hl a (by simp)
          have ht : ∀ b ∈ t, D.val' b = 0 := fun b hb => hl b (by simp [hb])
          rw [resPairAt_cons]
          cases m with
          | zero => rw [resStepHom_zero_apply_of_val_zero D a hav]
          | succ m' =>
              rw [resStepHom_succ_apply_of_val_zero D a m' hav]
              show mulSymbol (D.residueUnit a) m' (resPairAt D (m' + 1) t _).2 = 0
              rw [ih (m' + 1) _ ht]
              exact map_zero _

/-- **The specialization of a symbol of units of valuation zero is the symbol of their
residues.** -/
theorem resPairAt_fst_eq : ∀ (l : List Kˣ) (n : ℕ) (h : l.length = n),
    (∀ a ∈ l, D.val' a = 0) →
      (resPairAt D n l h).1
        = milnorClassDeg k n ⟨l.map D.residueUnit, by rw [List.length_map]; exact h⟩ := by
  intro l
  induction l with
  | nil =>
      intro n h _
      cases n with
      | zero => rfl
      | succ m => exact absurd h (by simp)
  | cons a t ih =>
      intro n h hl
      cases n with
      | zero => exact absurd h (by simp)
      | succ m =>
          have hav : D.val' a = 0 := hl a (by simp)
          have ht : ∀ b ∈ t, D.val' b = 0 := fun b hb => hl b (by simp [hb])
          rw [resPairAt_cons]
          have hfst : (resStepHom D a m (resPairAt D m t (by simpa using h))).1
              = mulSymbol (D.residueUnit a) m (resPairAt D m t (by simpa using h)).1 := by
            cases m with
            | zero => rw [resStepHom_zero_apply_of_val_zero D a hav]
            | succ m' => rw [resStepHom_succ_apply_of_val_zero D a m' hav]
          rw [hfst, ih m _ ht, mulSymbol_class]
          exact congrArg _ (Subtype.ext rfl)

/-- **The residue of a class of units of valuation zero vanishes.** -/
theorem milnorResidue_eq_zero_of_units (n : ℕ) (s : MilnorSymbolDeg K n)
    (hs : ∀ a ∈ s.val, D.val' a = 0) :
    milnorResidue D n (milnorClassDeg K n s) = 0 := by
  rw [milnorResidue_class]
  exact resPairAt_snd_eq_zero D s.val n s.property hs

/-- **The specialization of a class of units of valuation zero is the class of their residues.** -/
theorem milnorSpecialization_of_units (n : ℕ) (s : MilnorSymbolDeg K n)
    (hs : ∀ a ∈ s.val, D.val' a = 0) :
    milnorSpecialization D n (milnorClassDeg K n s)
      = milnorClassDeg k n ⟨s.val.map D.residueUnit, by rw [List.length_map]; exact s.property⟩ := by
  rw [milnorSpecialization_class]
  exact resPairAt_fst_eq D s.val n s.property hs

end Units

end GaloisForLFunctions.HTGeometry
