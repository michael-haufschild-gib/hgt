import GaloisForLFunctions.HTGeometry.MilnorSectionMap
import GaloisForLFunctions.HTGeometry.MilnorTotalResidueKernel
import GaloisForLFunctions.HTGeometry.MilnorFiltrationReduction

/-!
# A class has nonzero residue at only finitely many monic irreducibles

Milnor's residue at `π` vanishes on a symbol none of whose entries is divisible by `π`, and a
nonzero polynomial has only finitely many monic irreducible divisors.  Since every class of
`K_n^M(F(t))` is a combination of symbols of polynomials, only finitely many places can see it.

* `MonicIrred` : the monic irreducible polynomials.
* `finite_polyResidue_ne_zero` : **the residues vanish off a finite set of places.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial UniqueFactorizationMonoid

variable {F : Type*} [Field F]

/-- The monic irreducible polynomials, which index the finite places of `F(t)`. -/
abbrev MonicIrred (F : Type*) [Field F] := {q : Polynomial F // Irreducible q ∧ q.Monic}

/-- **A nonzero polynomial has only finitely many monic irreducible divisors.** -/
theorem finite_monicIrred_dvd {p : Polynomial F} (hp : p ≠ 0) :
    {q : MonicIrred F | q.1 ∣ p}.Finite := by
  classical
  have hinj : Set.InjOn (fun q : MonicIrred F => q.1) {q : MonicIrred F | q.1 ∣ p} :=
    fun a _ b _ h => Subtype.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (normalizedFactors p).toFinset.finite_toSet ?_
  rintro x ⟨q, hq, rfl⟩
  obtain ⟨c, hc, hassoc⟩ :=
    exists_mem_normalizedFactors_of_dvd hp q.2.1 hq
  have hcnorm : normalize c = c := normalize_normalized_factor c hc
  have hcmonic : c.Monic := by
    have hc0 : c ≠ 0 := (irreducible_of_normalized_factor c hc).ne_zero
    have := Polynomial.monic_normalize (p := c) hc0
    rwa [hcnorm] at this
  have : q.1 = c := Polynomial.eq_of_monic_of_associated q.2.2 hcmonic hassoc
  show (q : Polynomial F) ∈ ((normalizedFactors p).toFinset : Set (Polynomial F))
  rw [Finset.mem_coe, Multiset.mem_toFinset, this]
  exact hc

/-- **The residue vanishes off a finite set of monic irreducibles.** -/
theorem finite_polyResidue_ne_zero (n : ℕ) (x : MilnorKDeg (RatFunc F) n) :
    {q : MonicIrred F | milnorResidue (polyResidueData q.2.1) n x ≠ 0}.Finite := by
  classical
  set S : AddSubgroup (MilnorKDeg (RatFunc F) n) :=
    { carrier := {y : MilnorKDeg (RatFunc F) n |
        {q : MonicIrred F | milnorResidue (polyResidueData q.2.1) n y ≠ 0}.Finite}
      zero_mem' := by
        refine Set.Finite.subset Set.finite_empty ?_
        intro q hq
        exact absurd (map_zero (milnorResidue (polyResidueData q.2.1) n)) hq
      add_mem' := by
        intro y z hy hz
        refine Set.Finite.subset (hy.union hz) ?_
        intro q hq
        by_contra hnot
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
        exact hq (by rw [map_add, hnot.1, hnot.2, add_zero])
      neg_mem' := by
        intro y hy
        refine Set.Finite.subset hy ?_
        intro q hq
        by_contra hnot
        simp only [Set.mem_setOf_eq, not_not] at hnot
        exact hq (by rw [_root_.map_neg, hnot, neg_zero]) } with hS
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration (F := F) n x
  have hsub : degreeFiltration (F := F) d n ≤ S := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro y ⟨s, hs, rfl⟩
    obtain ⟨ps, hps, hdegs⟩ := exists_nzList (F := F) (d := d) s.val
      (fun a ha => by
        obtain ⟨p, hp, hle, hap⟩ := hs a ha
        exact ⟨p, hp, hle, hap⟩)
    show {q : MonicIrred F | milnorResidue (polyResidueData q.2.1) n
      (milnorClassDeg (RatFunc F) n s) ≠ 0}.Finite
    refine Set.Finite.subset
      (Set.Finite.biUnion ps.toFinset.finite_toSet
        (fun p _ => finite_monicIrred_dvd p.2)) ?_
    intro q hq
    by_contra hnot
    refine hq ?_
    refine milnorResidue_eq_zero_of_units (polyResidueData q.2.1) n s (fun a ha => ?_)
    rw [← hps] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    refine polyResidueData_val'_eq_zero q.2.1 p.2 ?_
    intro hmem
    exact hnot (Set.mem_biUnion (by simpa using hp) (Ideal.mem_span_singleton.1 hmem))
  exact hsub hd

end GaloisForLFunctions.HTGeometry
