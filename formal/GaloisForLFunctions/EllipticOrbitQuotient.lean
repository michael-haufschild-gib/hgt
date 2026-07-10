import GaloisForLFunctions.PrincipalPartDifferentialOperator

/-!
# Nested elliptic orbit quotients

This file identifies the orbit quotient of an additive quotient `G / H` under
translation by `q` with the single quotient by `H ⊔ ℤq`.  The two-class
corollary is the exact algebraic bridge between elliptic nonresonance
conditions and distinct-orbit hypotheses in orbit-residue obstructions.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A class in `(G / H) / ℤq` vanishes exactly when its representative lies in
the subgroup generated jointly by `H` and `q`. -/
theorem nested_orbit_class_eq_zero_iff
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (q x : G) :
    (((x : G ⧸ H) :
      (G ⧸ H) ⧸ AddSubgroup.zmultiples (q : G ⧸ H)) = 0) ↔
      x ∈ H ⊔ AddSubgroup.zmultiples q := by
  change (((x : G ⧸ H) :
      (G ⧸ H) ⧸ AddSubgroup.zmultiples (q : G ⧸ H)) =
    (((0 : G) : G ⧸ H) :
      (G ⧸ H) ⧸ AddSubgroup.zmultiples (q : G ⧸ H))) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simp only [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hquot : (x : G ⧸ H) = ((n • q : G) : G ⧸ H) := by
      simpa using hn.symm
    rw [QuotientAddGroup.eq_iff_sub_mem] at hquot
    have hx : x = (x - n • q) + n • q := by abel
    rw [hx]
    exact AddSubgroup.add_mem (H ⊔ AddSubgroup.zmultiples q)
      ((show H ≤ H ⊔ AddSubgroup.zmultiples q from le_sup_left) hquot)
      ((show AddSubgroup.zmultiples q ≤ H ⊔ AddSubgroup.zmultiples q from le_sup_right)
        (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples q) n))
  · intro hx
    rw [AddSubgroup.mem_sup] at hx
    rcases hx with ⟨h, hh, z, hz, rfl⟩
    rw [AddSubgroup.mem_zmultiples_iff] at hz
    rcases hz with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change ((n • q : G) : G ⧸ H) =
      ((h + n • q : G) : G ⧸ H) - 0
    simp only [sub_zero]
    rw [QuotientAddGroup.eq_iff_sub_mem]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using H.neg_mem hh

/-- Two representatives determine distinct translation orbits on `G / H`
exactly when their difference is not in `H ⊔ ℤq`. -/
theorem nested_orbit_classes_ne_iff
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (q x y : G) :
    (((x : G ⧸ H) :
      (G ⧸ H) ⧸ AddSubgroup.zmultiples (q : G ⧸ H)) ≠
      ((y : G ⧸ H) :
        (G ⧸ H) ⧸ AddSubgroup.zmultiples (q : G ⧸ H))) ↔
      x - y ∉ H ⊔ AddSubgroup.zmultiples q := by
  rw [ne_eq, ← sub_eq_zero, not_iff_not]
  simpa using nested_orbit_class_eq_zero_iff H q (x - y)

/-- The pole classes represented by `0` and `-h` are in distinct translation
orbits exactly under the standard elliptic nonresonance condition
`h ∉ H ⊔ ℤq`. -/
theorem zero_and_neg_nested_orbit_classes_ne_iff
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (q h : G) :
    ((((0 : G) : G ⧸ H) :
      (G ⧸ H) ⧸ AddSubgroup.zmultiples (q : G ⧸ H)) ≠
      (((-h : G) : G ⧸ H) :
        (G ⧸ H) ⧸ AddSubgroup.zmultiples (q : G ⧸ H))) ↔
      h ∉ H ⊔ AddSubgroup.zmultiples q := by
  simpa using nested_orbit_classes_ne_iff H q 0 (-h)

/-- **Elliptic differential orbital-residue obstruction.** Under the concrete
nonresonance condition `h ∉ H ⊔ ℤq`, applying any nonzero
constant-coefficient differential operator to two opposite nonzero simple
poles at `0` and `-h` on `G / H` cannot produce a finite `q`-coboundary. -/
theorem elliptic_nonresonance_simplePolePair_ne_coboundary
    {G C : Type*} [AddCommGroup G] [Field C] [CharZero C]
    (H : AddSubgroup G) (q h : G)
    (hnonres : h ∉ H ⊔ AddSubgroup.zmultiples q)
    {L : Polynomial C} (hL : L ≠ 0) {c : C} (hc : c ≠ 0)
    (E : (G ⧸ H) →₀ (ℕ →₀ C)) :
    simplePolePairDifferentialOperator L c
        ((0 : G) : G ⧸ H) ((-h : G) : G ⧸ H) ≠
      finiteOrbitCoboundary (q : G ⧸ H) E := by
  apply simplePolePairDifferentialOperator_ne_finiteOrbitCoboundary
    (q : G ⧸ H) ((0 : G) : G ⧸ H) ((-h : G) : G ⧸ H) hL hc
  exact (zero_and_neg_nested_orbit_classes_ne_iff H q h).2 hnonres

/-- **Simultaneous elliptic differential orbital-residue obstruction.** A
finite family of nonzero shift classes which are pairwise distinct modulo
`H ⊔ ℤq` gives pairwise distinct non-base pole orbits on `G / H`. Any
nonzero member of a differential-operator family therefore certifies that the
whole principal-part family is not a finite `q`-coboundary. -/
theorem elliptic_nonresonance_simplePolePairFamily_ne_coboundary
    {I G C : Type*} [DecidableEq I] [AddCommGroup G] [Field C] [CharZero C]
    (H : AddSubgroup G) (q : G) (s : Finset I)
    (L : I → Polynomial C) (c : I → C) (h : I → G)
    {i₀ : I} (hi₀ : i₀ ∈ s) (hL : L i₀ ≠ 0) (hc : c i₀ ≠ 0)
    (hnonres : h i₀ ∉ H ⊔ AddSubgroup.zmultiples q)
    (hsep : ∀ j ∈ s, j ≠ i₀ →
      h i₀ - h j ∉ H ⊔ AddSubgroup.zmultiples q)
    (E : (G ⧸ H) →₀ (ℕ →₀ C)) :
    simplePolePairDifferentialOperatorFamily s L c
        ((0 : G) : G ⧸ H) (fun i => ((-h i : G) : G ⧸ H)) ≠
      finiteOrbitCoboundary (q : G ⧸ H) E := by
  apply simplePolePairDifferentialOperatorFamily_ne_finiteOrbitCoboundary
    (q : G ⧸ H) ((0 : G) : G ⧸ H) s L c
    (fun i => ((-h i : G) : G ⧸ H)) hi₀ hL hc
  · exact ((zero_and_neg_nested_orbit_classes_ne_iff H q (h i₀)).2 hnonres).symm
  · intro j hjs hjne
    apply (nested_orbit_classes_ne_iff H q (-h i₀) (-h j)).2
    intro hmem
    apply hsep j hjs hjne
    have hneg := (H ⊔ AddSubgroup.zmultiples q).neg_mem hmem
    simpa [sub_eq_add_neg, add_comm, add_left_comm] using hneg

end

end GaloisForLFunctions
