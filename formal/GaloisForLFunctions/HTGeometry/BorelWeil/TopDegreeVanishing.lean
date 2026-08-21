import GaloisForLFunctions.HTGeometry.BorelWeil.RelativeSplitting

/-!
# Vanishing in the top Čech degree

The top Čech degree of the Bruhat cover is carried by the single full intersection of all the cells,
and the relative splitting writes any section there as a sum of one regular on all cells but the
reflected one and one regular on all cells but the identity one.  That exhibits every top cochain as
a coboundary, so the top cohomology of `L_λ` vanishes whenever the weight pairs to at least `−1`
with some simple coroot.

## Main results

* `flagCocycles_top_le_flagCoboundaries`
* `flagCohomology_top_subsingleton`
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem one_lt_card_perm {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    1 < Fintype.card (Equiv.Perm (Fin N)) := by
  classical
  rw [Fintype.one_lt_card_iff_nontrivial]
  exact ⟨⟨1, swapNext i hi, swapNext_ne_one hi⟩⟩

theorem card_erase_univ (u : Equiv.Perm (Fin N)) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).erase u).card
      = Fintype.card (Equiv.Perm (Fin N)) - 1 := by
  classical
  rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]

theorem union_pair_eq_univ {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))) \ {1, swapNext i hi})
      ∪ ({1, swapNext i hi} : Finset (Equiv.Perm (Fin N))) = Finset.univ := by
  classical
  rw [Finset.sdiff_union_self_eq_union, Finset.union_eq_left]
  exact Finset.subset_univ _

theorem sdiff_union_singleton_eq_erase {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))) \ {1, swapNext i hi})
        ∪ {(1 : Equiv.Perm (Fin N))}
      = (Finset.univ : Finset (Equiv.Perm (Fin N))).erase (swapNext i hi) := by
  classical
  ext w
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, and_true,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, not_or]
  constructor
  · rintro (⟨h1, h2⟩ | h)
    · exact h2
    · rw [h]
      exact fun hc => swapNext_ne_one hi hc
  · intro h1
    by_cases h2 : w = 1
    · exact Or.inr h2
    · exact Or.inl ⟨h2, h1⟩

theorem sdiff_union_singleton_eq_erase' {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))) \ {1, swapNext i hi}) ∪ {swapNext i hi}
      = (Finset.univ : Finset (Equiv.Perm (Fin N))).erase 1 := by
  classical
  ext w
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, and_true,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, not_or]
  constructor
  · rintro (⟨h1, h2⟩ | h)
    · exact h1
    · rw [h]
      exact fun hc => swapNext_ne_one hi hc.symm
  · intro h1
    by_cases h2 : w = swapNext i hi
    · exact Or.inr h2
    · exact Or.inl ⟨h1, h2⟩

theorem disjoint_sdiff_pair {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    Disjoint ((Finset.univ : Finset (Equiv.Perm (Fin N))) \ {1, swapNext i hi})
      ({1, swapNext i hi} : Finset (Equiv.Perm (Fin N))) :=
  Finset.sdiff_disjoint

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem erase_univ_inj {u v : Equiv.Perm (Fin N)}
    (h : (Finset.univ : Finset (Equiv.Perm (Fin N))).erase u = Finset.univ.erase v) : u = v := by
  classical
  by_contra hne
  have hv : v ∈ (Finset.univ : Finset (Equiv.Perm (Fin N))).erase u :=
    Finset.mem_erase.mpr ⟨fun hc => hne hc.symm, Finset.mem_univ v⟩
  rw [h] at hv
  exact (Finset.mem_erase.mp hv).1 rfl

/-- **Every top-degree cocycle is a coboundary**, as soon as the weight pairs to at least `−1` with
some simple coroot. -/
theorem flagCocycles_top_le_flagCoboundaries {i : Fin N} (hi : (i : ℕ) + 1 < N) {lam : Fin N → ℤ}
    (hd : -1 ≤ lam i - lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)) :
    flagCocycles N k lam (Fintype.card (Equiv.Perm (Fin N)) - 1)
      ≤ flagCoboundaries N k lam (Fintype.card (Equiv.Perm (Fin N)) - 1) := by
  classical
  intro ω hω
  have hn2 : 2 ≤ Fintype.card (Equiv.Perm (Fin N)) := one_lt_card_perm hi
  have hsupp : ∀ I : Finset (Equiv.Perm (Fin N)), I ≠ Finset.univ → ω I = 0 := by
    intro I hI
    refine hω.1.card I ?_
    intro hc
    refine hI (Finset.eq_univ_of_card I ?_)
    omega
  have hval : ω Finset.univ ∈ cellSections N k Finset.univ lam := hω.1.mem _
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin N)))
      = (Finset.univ \ {1, swapNext i hi}) ∪ {1, swapNext i hi} := (union_pair_eq_univ hi).symm
  rw [huniv] at hval
  obtain ⟨a, ha, b, hb, hsum⟩ := Submodule.mem_sup.mp
    (cellSections_pair_le_sup_relative hi (disjoint_sdiff_pair hi) hd hval)
  rw [sdiff_union_singleton_eq_erase hi] at ha
  rw [sdiff_union_singleton_eq_erase' hi] at hb
  rw [union_pair_eq_univ hi] at hsum
  have hidx : Fintype.card (Equiv.Perm (Fin N)) - 1
      = (Fintype.card (Equiv.Perm (Fin N)) - 2) + 1 := by omega
  rw [hidx, flagCoboundaries]
  have hne1s : (1 : Equiv.Perm (Fin N)) ≠ swapNext i hi := swapNext_ne_one hi
  have herase_ne : (Finset.univ : Finset (Equiv.Perm (Fin N))).erase 1
      ≠ Finset.univ.erase (swapNext i hi) := fun hc => hne1s (erase_univ_inj hc)
  have hnu : cechDModule k (fun I => if I = Finset.univ.erase (swapNext i hi) then
      (cechSign (Finset.univ : Finset (Equiv.Perm (Fin N))) (swapNext i hi) : k) • a
    else if I = Finset.univ.erase 1 then
      (cechSign (Finset.univ : Finset (Equiv.Perm (Fin N))) (1 : Equiv.Perm (Fin N)) : k) • b
    else 0) = ω := by
    funext I
    by_cases hI : I = Finset.univ
    · subst hI
      have hzero : ∀ u ∈ (Finset.univ : Finset (Equiv.Perm (Fin N))),
          u ∉ ({1, swapNext i hi} : Finset (Equiv.Perm (Fin N))) →
          (cechSign (Finset.univ : Finset (Equiv.Perm (Fin N))) u : k) •
            (if Finset.univ.erase u = Finset.univ.erase (swapNext i hi) then
              (cechSign (Finset.univ : Finset (Equiv.Perm (Fin N))) (swapNext i hi) : k) • a
            else if Finset.univ.erase u = Finset.univ.erase 1 then
              (cechSign (Finset.univ : Finset (Equiv.Perm (Fin N))) (1 : Equiv.Perm (Fin N)) : k) • b
            else 0) = 0 := by
        intro u _ hu
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
        rw [if_neg (fun hc => hu.2 (erase_univ_inj hc)), if_neg (fun hc => hu.1 (erase_univ_inj hc)),
          smul_zero]
      rw [cechDModule, ← Finset.sum_subset
        (Finset.subset_univ ({1, swapNext i hi} : Finset (Equiv.Perm (Fin N)))) hzero,
        Finset.sum_pair hne1s, if_neg herase_ne, if_pos rfl, if_pos rfl, smul_smul, smul_smul,
        cechSign_mul_self, cechSign_mul_self, one_smul, one_smul, ← hsum]
      exact add_comm b a
    · rw [hsupp I hI]
      refine Finset.sum_eq_zero fun u hu => ?_
      simp only []
      have hcard : (I.erase u).card = I.card - 1 := Finset.card_erase_of_mem hu
      have h1 : I.erase u ≠ Finset.univ.erase (swapNext i hi) := by
        intro hc
        rw [hc, card_erase_univ] at hcard
        refine hI (Finset.eq_univ_of_card I ?_)
        have hle : I.card ≤ Fintype.card (Equiv.Perm (Fin N)) := Finset.card_le_univ I
        have hpos : 0 < I.card := Finset.card_pos.mpr ⟨u, hu⟩
        omega
      have h2 : I.erase u ≠ Finset.univ.erase 1 := by
        intro hc
        rw [hc, card_erase_univ] at hcard
        refine hI (Finset.eq_univ_of_card I ?_)
        have hle : I.card ≤ Fintype.card (Equiv.Perm (Fin N)) := Finset.card_le_univ I
        have hpos : 0 < I.card := Finset.card_pos.mpr ⟨u, hu⟩
        omega
      rw [if_neg h1, if_neg h2, smul_zero]
  refine ⟨fun I => if I = Finset.univ.erase (swapNext i hi) then
      (cechSign (Finset.univ : Finset (Equiv.Perm (Fin N))) (swapNext i hi) : k) • a
    else if I = Finset.univ.erase 1 then
      (cechSign (Finset.univ : Finset (Equiv.Perm (Fin N))) (1 : Equiv.Perm (Fin N)) : k) • b
    else 0, ⟨?_, ?_⟩, hnu⟩
  · intro I hI
    have h1 : I ≠ Finset.univ.erase (swapNext i hi) := by
      intro hc
      exact hI (by rw [hc, card_erase_univ]; omega)
    have h2 : I ≠ Finset.univ.erase 1 := by
      intro hc
      exact hI (by rw [hc, card_erase_univ]; omega)
    rw [if_neg h1, if_neg h2]
  · intro I
    by_cases h1 : I = Finset.univ.erase (swapNext i hi)
    · rw [if_pos h1, h1]
      exact Submodule.smul_mem _ _ ha
    · rw [if_neg h1]
      by_cases h2 : I = Finset.univ.erase 1
      · rw [if_pos h2, h2]
        exact Submodule.smul_mem _ _ hb
      · rw [if_neg h2]
        exact Submodule.zero_mem _

/-- **Vanishing of the top cohomology of the flag variety.** -/
theorem flagCohomology_top_subsingleton {i : Fin N} (hi : (i : ℕ) + 1 < N) {lam : Fin N → ℤ}
    (hd : -1 ≤ lam i - lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)) :
    Subsingleton (flagCohomology N k lam (Fintype.card (Equiv.Perm (Fin N)) - 1)) := by
  classical
  have htop : Submodule.comap
      (flagCocycles N k lam (Fintype.card (Equiv.Perm (Fin N)) - 1)).subtype
      (flagCoboundaries N k lam (Fintype.card (Equiv.Perm (Fin N)) - 1)) = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    exact flagCocycles_top_le_flagCoboundaries hi hd z.2
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.inductionOn with
  | _ u =>
    induction y using Quotient.inductionOn with
    | _ v =>
      refine (Submodule.Quotient.eq _).mpr ?_
      rw [htop]
      trivial

end GaloisForLFunctions.HTGeometry.BorelWeil
