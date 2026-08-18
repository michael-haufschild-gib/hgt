import GaloisForLFunctions.HTGeometry.PolynomialPlaceResidue
import GaloisForLFunctions.HTGeometry.MilnorKResidueUniformizer

/-!
# Surjectivity of the graded map of Milnor's degree filtration

Milnor's sequence for a rational function field is proved by the degree filtration `L_d` of
`K_n^M(F(t))` by symbols of polynomials of degree at most `d`.  The residues at the places of degree
`d` kill `L_{d−1}` and therefore factor through `L_d / L_{d−1}`; here we prove that the resulting
map onto `⊕_{deg π = d} K_{n−1}^M(F[X]/π)` is **onto**, one component at a time, and that a symbol
realising one component has vanishing residue at every other place of the same degree.

Both statements come from `∂{u₁, …, u_n, π} = {ū₁, …, ū_n}` with `π` used as its own uniformizer:
the entries `u_i` can be taken of degree below `deg π` by division with remainder, so the whole
symbol lies in `L_{deg π}`, and at a different irreducible of the same degree every entry is a unit
of valuation zero.

* `milnorResidue_eq_zero_of_not_dvd` : the residue kills a symbol of polynomials it does not divide.
* `exists_list_polyUnit_degree_lt` : residue classes lift to polynomials of smaller degree.
* `exists_mem_degreeFiltration_milnorResidue_eq` : **the graded map is onto its `π`-component.**
-/

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- **The residue at `π` kills a symbol whose entries are polynomials not divisible by `π`.** -/
theorem milnorResidue_eq_zero_of_not_dvd {π : Polynomial F} (hπ : Irreducible π) (n : ℕ)
    (s : MilnorSymbolDeg (RatFunc F) n)
    (hs : ∀ a ∈ s.val, ∃ (p : Polynomial F) (hp : p ≠ 0),
      p ∉ Ideal.span {π} ∧ a = polyUnit hp) :
    milnorResidue (residueDataAtPlace (RatFunc F) (polyPlace hπ)) n
        (milnorClassDeg (RatFunc F) n s) = 0 := by
  refine milnorResidue_eq_zero_of_units _ n s ?_
  intro a ha
  obtain ⟨p, hp, hpm, rfl⟩ := hs a ha
  exact residueDataAtPlace_val'_eq_zero (RatFunc F) (polyPlace hπ) hp hpm

/-- The valuation of a polynomial unit vanishes at `π` when `π` does not divide it, for the residue
data that uses `π` itself as uniformizer. -/
theorem polyResidueData_val'_eq_zero {π p : Polynomial F} (hπ : Irreducible π) (hp : p ≠ 0)
    (hpm : p ∉ Ideal.span {π}) : (polyResidueData hπ).val' (polyUnit hp) = 0 :=
  residueDataAtPlace_val'_eq_zero (RatFunc F) (polyPlace hπ) hp hpm

/-- **A list of residue classes at `π` lifts to a list of polynomial units of degree below
`deg π`.**  Division with remainder, applied entry by entry. -/
theorem exists_list_polyUnit_degree_lt {π : Polynomial F} (hπ : Irreducible π) :
    ∀ m : List (IsLocalRing.ResidueField
      (((polyPlace hπ).valuation (RatFunc F)).valuationSubring))ˣ,
      ∃ l : List (RatFunc F)ˣ,
        (∀ a ∈ l, ∃ (p : Polynomial F) (hp : p ≠ 0),
          p.natDegree < π.natDegree ∧ a = polyUnit hp)
        ∧ (∀ a ∈ l, (polyResidueData hπ).val' a = 0)
        ∧ l.map (polyResidueData hπ).residueUnit = m := by
  intro m
  induction m with
  | nil => exact ⟨[], by simp, by simp, rfl⟩
  | cons y t ih =>
      obtain ⟨l, hdeg, hval, hmap⟩ := ih
      obtain ⟨p, hp, hplt, hres⟩ := exists_polyUnit_degree_lt hπ y
      have hpm : p ∉ Ideal.span {π} := notMem_span_of_natDegree_lt hp hplt
      refine ⟨polyUnit hp :: l, ?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact ⟨p, hp, hplt, rfl⟩
        · exact hdeg b hb'
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact polyResidueData_val'_eq_zero hπ hp hpm
        · exact hval b hb'
      · rw [List.map_cons, hres, hmap]

/-- **The graded map of Milnor's filtration is onto its `π`-component.**  Every class of
`K_n^M(F[X]/π)` is the residue at `π` of a class in `L_{deg π}`. -/
theorem exists_mem_degreeFiltration_milnorResidue_eq {π : Polynomial F} (hπ : Irreducible π)
    (n : ℕ) (y : MilnorKDeg (IsLocalRing.ResidueField
      (((polyPlace hπ).valuation (RatFunc F)).valuationSubring)) n) :
    ∃ x ∈ degreeFiltration (F := F) π.natDegree (n + 1),
      milnorResidue (polyResidueData hπ) (n + 1) x = y := by
  have hmem : y ∈ AddSubgroup.map (milnorResidue (polyResidueData hπ) (n + 1))
      (degreeFiltration (F := F) π.natDegree (n + 1)) := by
    refine milnorKDeg_mem_of_gen _ (fun s => ?_) y
    obtain ⟨l, hdeg, hval, hmap⟩ := exists_list_polyUnit_degree_lt hπ s.val
    have hprop : s.val.length = n := s.property
    have hlen : l.length = n := by rw [← hprop, ← hmap, List.length_map]
    subst hlen
    refine ⟨milnorClassDeg (RatFunc F) (l.length + 1)
      ⟨l ++ [(polyResidueData hπ).unif], by simp⟩, ?_, ?_⟩
    · refine AddSubgroup.subset_closure ⟨_, ?_, rfl⟩
      intro a ha
      rcases List.mem_append.1 ha with ha' | ha'
      · obtain ⟨p, hp, hplt, hap⟩ := hdeg a ha'
        exact ⟨p, hp, le_of_lt hplt, hap⟩
      · rw [List.mem_singleton] at ha'
        exact ⟨π, hπ.ne_zero, le_rfl, by rw [ha', polyResidueData_unif]⟩
    · rw [milnorResidue_append_unif (polyResidueData hπ) l hval]
      exact congrArg (milnorClassDeg _ l.length) (Subtype.ext hmap)
  obtain ⟨x, hx, hxy⟩ := hmem
  exact ⟨x, hx, hxy⟩

end GaloisForLFunctions.HTGeometry
