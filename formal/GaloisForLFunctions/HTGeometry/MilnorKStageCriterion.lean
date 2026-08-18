import GaloisForLFunctions.HTGeometry.MilnorKUnitRankOne
import GaloisForLFunctions.HTGeometry.DivisibilityFirewall

/-!
# The stage-by-stage criterion for torsion of `K₂^M`

`K₂^M(F)` is the directed union of the symbol subgroups of the finitely generated subgroups of
`Fˣ`, and each of those stages is a **finitely generated** abelian group.  The divisibility firewall
says that no mod-`m` statement about `K₂^M(F)` itself can decide whether it is torsion — a directed
union of infinite cyclic groups can be `ℚ`.  But the firewall is broken one stage at a time: a
finitely generated abelian group is torsion exactly when it has no `ℤ`-quotient, and that *is*
visible modulo every `m`.

Putting the two together turns "the tame kernel of a number field is torsion" — an analytic theorem
of Borel and Garland — into a statement about a directed system of finitely generated abelian
groups, each of which is decided by its `ℤ`-quotients.

* `symbolStage` : the stage attached to a finite set of units.
* `symbolStage_addGroup_fg` : **every stage is finitely generated.**
* `symbolStage_le_torsion_iff_no_int_quotient` : **a stage is torsion iff it has no `ℤ`-quotient.**
* `milnorKDegTwo_le_torsion_iff_stages` : `K₂^M(F)` is torsion iff every stage is.
* `milnorKDegTwo_le_torsion_iff_no_stage_int_quotient` : **the two combined.**
-/

namespace GaloisForLFunctions.HTGeometry

variable (F : Type*) [Field F]

/-- The stage of the symbol filtration attached to a finite set of units. -/
def symbolStage (G : Finset Fˣ) : AddSubgroup (MilnorKDeg F 2) :=
  symbolSubgroup F (Subgroup.closure (G : Set Fˣ))

theorem symbolStage_fg (G : Finset Fˣ) : (symbolStage F G).FG :=
  symbolSubgroup_fg_of_fg F ⟨G, rfl⟩

instance symbolStage_addGroup_fg (G : Finset Fˣ) : AddGroup.FG (symbolStage F G) :=
  (AddGroup.fg_iff_addSubgroup_fg _).2 (symbolStage_fg F G)

/-- **`K₂^M(F)` is torsion exactly when every stage is.** -/
theorem milnorKDegTwo_le_torsion_iff_stages :
    (∀ x : MilnorKDeg F 2, x ∈ torsionAddSubgroup (MilnorKDeg F 2))
      ↔ ∀ G : Finset Fˣ, symbolStage F G ≤ torsionAddSubgroup (MilnorKDeg F 2) := by
  constructor
  · intro h G x _
    exact h x
  · intro h x
    obtain ⟨G, hG⟩ := exists_finset_mem_symbolSubgroup F x
    exact h G hG

/-- **A stage is torsion exactly when it has no `ℤ`-quotient.**  The forward direction is that a
torsion group has no `ℤ`-quotient; the converse is the firewall-breaking lemma, available because
the stage is finitely generated. -/
theorem symbolStage_le_torsion_iff_no_int_quotient (G : Finset Fˣ) :
    symbolStage F G ≤ torsionAddSubgroup (MilnorKDeg F 2)
      ↔ ∀ φ : (symbolStage F G) →+ ℤ, ¬ Function.Surjective φ := by
  constructor
  · intro h φ hφ
    obtain ⟨y, hy⟩ := hφ 1
    obtain ⟨n, hn, hnx⟩ := h y.2
    have hz : (n : ℤ) • φ y = 0 := by
      rw [← map_zsmul]
      have : (n : ℤ) • y = 0 := Subtype.ext hnx
      rw [this, map_zero]
    rw [hy, smul_eq_mul, mul_one] at hz
    exact hn hz
  · intro h y hy
    have htor : AddMonoid.IsTorsion (symbolStage F G) :=
      isTorsion_of_fg_of_no_int_quotient h
    obtain ⟨n, hn, hnx⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).1 (htor ⟨y, hy⟩)
    refine ⟨(n : ℤ), by exact_mod_cast hn.ne', ?_⟩
    have : ((n : ℤ)) • (⟨y, hy⟩ : symbolStage F G) = 0 := by
      rw [natCast_zsmul]
      exact hnx
    exact congrArg Subtype.val this

/-- **The stage-by-stage criterion.**  `K₂^M(F)` is torsion if and only if no stage of the symbol
filtration admits a surjection onto `ℤ`.  Each stage is a finitely generated abelian group, so the
right-hand condition is a statement that finite-coefficient information decides — which is exactly
what the divisibility firewall shows is impossible for `K₂^M(F)` as a whole. -/
theorem milnorKDegTwo_le_torsion_iff_no_stage_int_quotient :
    (∀ x : MilnorKDeg F 2, x ∈ torsionAddSubgroup (MilnorKDeg F 2))
      ↔ ∀ G : Finset Fˣ, ∀ φ : (symbolStage F G) →+ ℤ, ¬ Function.Surjective φ := by
  rw [milnorKDegTwo_le_torsion_iff_stages]
  exact forall_congr' fun G => symbolStage_le_torsion_iff_no_int_quotient F G

end GaloisForLFunctions.HTGeometry
