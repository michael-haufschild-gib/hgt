import GaloisForLFunctions.HTGeometry.MilnorKResidueUnits
import GaloisForLFunctions.HTGeometry.MilnorKResidueSteinberg

/-!
# The residue of a symbol ending in the uniformizer

Milnor's residue is computed by folding the step `x ↦ ([ū_a] + v(a)ξ)·x` over the entries of a
symbol.  When every entry but the last is a unit of valuation zero and the last is the uniformizer,
the fold collapses: the uniformizer contributes the single `ξ`, and each unit contributes
multiplication by the class of its residue.  So

`∂{u₁, …, u_{n}, π} = {ū₁, …, ū_{n}}`.

This is the computation that makes the total residue **surjective**, which is the right-exactness
half of Milnor's sequence for a rational function field, and the input to the Gersten complex being
exact at its last term.

* `resPairAt_append_unif` : **the fold on a symbol of units followed by the uniformizer.**
* `milnorResidue_append_unif` : **`∂{u₁, …, u_n, π} = {ū₁, …, ū_n}`.**
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {k : Type*} [Field k] (D : ResidueData K k)

/-- **The residue fold on a symbol of units of valuation zero followed by the uniformizer.** -/
theorem resPairAt_append_unif :
    ∀ (l : List Kˣ) (h : (l ++ [D.unif]).length = l.length + 1),
      (∀ a ∈ l, D.val' a = 0) →
      (resPairAt D (l.length + 1) (l ++ [D.unif]) h).2
        = milnorClassDeg k l.length ⟨l.map D.residueUnit, by rw [List.length_map]⟩ := by
  intro l
  induction l with
  | nil =>
      intro h _
      show (resStepHom D D.unif 0 (resPairAt D 0 [] (by simp))).2 = _
      rw [resPairAt_zero, resStepHom_zero_apply]
      show D.val' D.unif • (milnorOne : MilnorKDeg k 0) = _
      rw [D.val'_unif, one_zsmul]
      exact congrArg (milnorClassDeg k 0) (Subtype.ext rfl)
  | cons a t ih =>
      intro h hl
      have hat : D.val' a = 0 := hl a (by simp)
      have ht : ∀ b ∈ t, D.val' b = 0 := fun b hb => hl b (by simp [hb])
      have htail : (t ++ [D.unif]).length = t.length + 1 := by simp
      show (resStepHom D a (t.length + 1)
        (resPairAt D (t.length + 1) (t ++ [D.unif]) htail)).2 = _
      rw [resStepHom_succ_apply, hat]
      simp only [mul_zero, zero_zsmul, add_zero]
      rw [ih htail ht, mulSymbol_class]
      exact congrArg (milnorClassDeg k (t.length + 1)) (Subtype.ext rfl)

/-- **`∂{u₁, …, u_n, π} = {ū₁, …, ū_n}`.**  Every residue class of `k` is therefore hit: lift its
entries to units of valuation zero and append the uniformizer. -/
theorem milnorResidue_append_unif (l : List Kˣ) (hl : ∀ a ∈ l, D.val' a = 0)
    (h : (l ++ [D.unif]).length = l.length + 1) :
    milnorResidue D (l.length + 1)
        (milnorClassDeg K (l.length + 1) ⟨l ++ [D.unif], h⟩)
      = milnorClassDeg k l.length ⟨l.map D.residueUnit, by rw [List.length_map]⟩ := by
  rw [milnorResidue_class]
  exact resPairAt_append_unif D l h hl

/-! ## Surjectivity of the residue -/

/-- A list of residues lifts to a list of units of valuation zero. -/
theorem exists_list_residueUnit
    (hres : ∀ y : kˣ, ∃ a : Kˣ, D.val' a = 0 ∧ D.residueUnit a = y) :
    ∀ m : List kˣ, ∃ l : List Kˣ,
      (∀ a ∈ l, D.val' a = 0) ∧ l.map D.residueUnit = m := by
  intro m
  induction m with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons y t ih =>
      obtain ⟨l, hl, hlm⟩ := ih
      obtain ⟨a, ha0, ha⟩ := hres y
      refine ⟨a :: l, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact ha0
        · exact hl b hb'
      · rw [List.map_cons, ha, hlm]

/-- **The residue is surjective** as soon as the residue map on units of valuation zero is: lift the
entries of a symbol of `k` and append the uniformizer.  For a finite place of a Dedekind domain the
hypothesis holds, so this is the right-exactness of the Gersten complex at its last term. -/
theorem milnorResidue_surjective
    (hres : ∀ y : kˣ, ∃ a : Kˣ, D.val' a = 0 ∧ D.residueUnit a = y) (n : ℕ) :
    Function.Surjective (milnorResidue D (n + 1)) := by
  intro y
  have hmem : y ∈ AddMonoidHom.range (milnorResidue D (n + 1)) := by
    refine milnorKDeg_mem_of_gen _ (fun s => ?_) y
    obtain ⟨l, hl, hlm⟩ := exists_list_residueUnit D hres s.val
    have hprop : s.val.length = n := s.property
    have hlen : l.length = n := by
      rw [← hprop, ← hlm, List.length_map]
    subst hlen
    refine ⟨milnorClassDeg K (l.length + 1) ⟨l ++ [D.unif], by simp⟩, ?_⟩
    rw [milnorResidue_append_unif D l hl]
    exact congrArg (milnorClassDeg k l.length) (Subtype.ext hlm)
  exact hmem

end GaloisForLFunctions.HTGeometry
