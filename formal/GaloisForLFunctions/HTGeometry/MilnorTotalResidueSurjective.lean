import GaloisForLFunctions.HTGeometry.MilnorMonicPlaceFiniteness

/-!
# The total residue is onto a single place

Milnor's section at `π` lifts a class of `K_n^M(F[X]/π)` to a class of `K_{n+1}^M(F(t))` whose
residue at every *other* place of the same degree vanishes, but which may still be seen by places of
smaller degree.  Those are finitely many, and each is cleared by subtracting a lift concentrated
there — an induction on the degree.

* `exists_lift_at_place` : the section lift, with its degree bound and same-degree vanishing.
* `exists_residue_single` : **every class of `K_n^M(F[X]/π)` is the residue at `π` of a class whose
  residue vanishes at every other finite place.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

theorem not_associated_of_monicIrred {π : Polynomial F} (hmπ : π.Monic) {q : MonicIrred F}
    (hne : q.1 ≠ π) : ¬ Associated π q.1 := by
  intro hassoc
  exact hne (Polynomial.eq_of_monic_of_associated q.2.2 hmπ hassoc.symm)

/-- **The section lift at `π`**, concentrated at `π` among the places of its degree. -/
theorem exists_lift_at_place {π : Polynomial F} (hπ : Irreducible π) (hmπ : π.Monic) (n : ℕ)
    (x : MilnorKDeg (polyResidueField hπ) n) :
    ∃ y : MilnorKDeg (RatFunc F) (n + 1),
      y ∈ degreeFiltration (F := F) π.natDegree (n + 1) ∧
      milnorResidue (polyResidueData hπ) (n + 1) y = x ∧
      ∀ q : MonicIrred F, q.1 ≠ π → q.1.natDegree = π.natDegree →
        milnorResidue (polyResidueData q.2.1) (n + 1) y = 0 := by
  classical
  set S : AddSubgroup (MilnorKDeg (polyResidueField hπ) n) :=
    { carrier := {x : MilnorKDeg (polyResidueField hπ) n |
        ∃ y : MilnorKDeg (RatFunc F) (n + 1),
          y ∈ degreeFiltration (F := F) π.natDegree (n + 1) ∧
          milnorResidue (polyResidueData hπ) (n + 1) y = x ∧
          ∀ q : MonicIrred F, q.1 ≠ π → q.1.natDegree = π.natDegree →
            milnorResidue (polyResidueData q.2.1) (n + 1) y = 0}
      zero_mem' := ⟨0, AddSubgroup.zero_mem _, map_zero _, fun _ _ _ => map_zero _⟩
      add_mem' := by
        rintro a b ⟨y, hy, hya, hyq⟩ ⟨z, hz, hzb, hzq⟩
        exact ⟨y + z, AddSubgroup.add_mem _ hy hz, by rw [map_add, hya, hzb]; rfl,
          fun q h1 h2 => by rw [map_add, hyq q h1 h2, hzq q h1 h2, add_zero]⟩
      neg_mem' := by
        rintro a ⟨y, hy, hya, hyq⟩
        exact ⟨-y, AddSubgroup.neg_mem _ hy, by rw [_root_.map_neg, hya]; rfl,
          fun q h1 h2 => by rw [_root_.map_neg, hyq q h1 h2, neg_zero]⟩ } with hS
  have hmem : x ∈ S := by
    refine milnorKDeg_mem_of_gen _ (fun s => ?_) x
    refine ⟨sectionSymbol hπ s, ?_, milnorResidue_sectionSymbol hπ s, ?_⟩
    · refine AddSubgroup.subset_closure ⟨_, ?_, rfl⟩
      intro a ha
      have hmemlist : a ∈ (s.val.map (liftUnit hπ)) ++ [polyUnit hπ.ne_zero] := ha
      rcases List.mem_append.1 hmemlist with h1 | h2
      · obtain ⟨w, _, rfl⟩ := List.mem_map.1 h1
        exact ⟨liftPoly hπ w, liftPoly_ne_zero hπ w,
          le_of_lt (liftPoly_natDegree_lt hπ w), rfl⟩
      · rw [List.mem_singleton] at h2
        exact ⟨π, hπ.ne_zero, le_rfl, h2⟩
    · intro q hne hdeg
      exact milnorResidue_sectionSymbol_of_ne hπ q.2.1
        (not_associated_of_monicIrred hmπ hne) hdeg.symm s
  exact hmem

/-- **Every class is the residue at `π` of a class invisible at every other place.** -/
theorem exists_residue_single (n : ℕ) :
    ∀ d : ℕ, ∀ q : MonicIrred F, q.1.natDegree = d →
      ∀ x : MilnorKDeg (polyResidueField q.2.1) n,
      ∃ y : MilnorKDeg (RatFunc F) (n + 1),
        milnorResidue (polyResidueData q.2.1) (n + 1) y = x ∧
        ∀ q' : MonicIrred F, q' ≠ q → milnorResidue (polyResidueData q'.2.1) (n + 1) y = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro q hqd x
    classical
    obtain ⟨y₀, hy₀filt, hy₀res, hy₀same⟩ := exists_lift_at_place q.2.1 q.2.2 n x
    -- the other places seeing `y₀` have smaller degree
    have hlow : ∀ q' : MonicIrred F, q' ≠ q →
        milnorResidue (polyResidueData q'.2.1) (n + 1) y₀ ≠ 0 → q'.1.natDegree < d := by
      intro q' hne hres
      by_contra hcon
      rcases lt_trichotomy q'.1.natDegree d with h | h | h
      · exact hcon h
      · exact hres (hy₀same q' (fun hcon2 => hne (Subtype.ext hcon2)) (by rw [h, hqd]))
      · exact hres (polyResidue_degreeFiltration_eq_zero q'.2.1 (by omega) y₀ (by
          rw [hqd] at hy₀filt; exact hy₀filt))
    have hfin : {q' : MonicIrred F |
        milnorResidue (polyResidueData q'.2.1) (n + 1) y₀ ≠ 0}.Finite :=
      finite_polyResidue_ne_zero (n + 1) y₀
    set B : Finset (MonicIrred F) := hfin.toFinset.erase q with hB
    have hBmem : ∀ q' ∈ B, q' ≠ q ∧
        milnorResidue (polyResidueData q'.2.1) (n + 1) y₀ ≠ 0 := by
      intro q' hq'
      rw [hB, Finset.mem_erase, Set.Finite.mem_toFinset] at hq'
      exact hq'
    have hcorr : ∀ q' ∈ B, ∃ z : MilnorKDeg (RatFunc F) (n + 1),
        milnorResidue (polyResidueData q'.2.1) (n + 1) z
          = milnorResidue (polyResidueData q'.2.1) (n + 1) y₀ ∧
        ∀ q'' : MonicIrred F, q'' ≠ q' →
          milnorResidue (polyResidueData q''.2.1) (n + 1) z = 0 := by
      intro q' hq'
      obtain ⟨hne, hres⟩ := hBmem q' hq'
      exact ih q'.1.natDegree (hlow q' hne hres) q' rfl _
    choose z hz1 hz2 using hcorr
    refine ⟨y₀ - B.attach.sum (fun p => z p.1 p.2), ?_, ?_⟩
    · rw [map_sub, hy₀res, map_sum]
      have : ∀ p ∈ B.attach, milnorResidue (polyResidueData q.2.1) (n + 1) (z p.1 p.2) = 0 := by
        intro p _
        exact hz2 p.1 p.2 q (fun hcon => (hBmem p.1 p.2).1 hcon.symm)
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero, sub_zero]
    · intro q' hne
      rw [map_sub, map_sum]
      by_cases hq'B : q' ∈ B
      · have hsplit : B.attach.sum
            (fun p => milnorResidue (polyResidueData q'.2.1) (n + 1) (z p.1 p.2))
            = milnorResidue (polyResidueData q'.2.1) (n + 1) (z q' hq'B) := by
          refine Finset.sum_eq_single (⟨q', hq'B⟩ : {a // a ∈ B}) ?_ ?_
          · intro p _ hpne
            refine hz2 p.1 p.2 q' ?_
            intro hcon
            exact hpne (Subtype.ext hcon.symm)
          · intro hcon
            exact absurd (Finset.mem_attach _ _) hcon
        rw [hsplit, hz1 q' hq'B, sub_self]
      · have hy0 : milnorResidue (polyResidueData q'.2.1) (n + 1) y₀ = 0 := by
          by_contra hcon
          exact hq'B (by rw [hB, Finset.mem_erase, Set.Finite.mem_toFinset]; exact ⟨hne, hcon⟩)
        have hall : ∀ p ∈ B.attach,
            milnorResidue (polyResidueData q'.2.1) (n + 1) (z p.1 p.2) = 0 := by
          intro p _
          refine hz2 p.1 p.2 q' ?_
          intro hcon
          exact hq'B (hcon ▸ p.2)
        rw [hy0, Finset.sum_congr rfl hall, Finset.sum_const_zero, sub_zero]

end GaloisForLFunctions.HTGeometry
