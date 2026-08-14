import GaloisForLFunctions.HTGeometry.MilnorKResidueUnits
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation

/-!
# The Gersten row of Milnor `K`-theory over a Dedekind domain

At every finite place of a Dedekind domain the residue map of Milnor `K`-theory is defined in every
degree.  A symbol is a symbol of units at all but finitely many places, and the residue kills such a
symbol, so every class has only finitely many nonzero residues.  Consequently, when the residue
targets are torsion, every class has a nonzero multiple in the tame kernel, and torsion of the tame
kernel forces torsion of the whole group.

* `milnorResidueAtPlace` : **the residue at a finite place, in every degree.**
* `finite_milnorResidueAtPlace_ne_zero` : **a class has nonzero residue at only finitely many
  places.**
* `milnorTameKernel` : **the tame kernel in degree `n`.**
* `milnorKDeg_torsion_of_milnorTameKernel_torsion` : **torsion of the tame kernel forces torsion of
  `K_n^M`.**
-/

namespace GaloisForLFunctions.HTGeometry

open Valuation IsLocalRing IsDedekindDomain

section Gersten

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The residue at a finite place, in every degree.** -/
noncomputable def milnorResidueAtPlace (v : HeightOneSpectrum R) (n : ℕ) :
    MilnorKDeg K n →+ MilnorKDeg (ResidueField (v.valuation K).valuationSubring) (n - 1) :=
  milnorResidue (residueDataAtPlace K v) n

theorem residueDataAtPlace_val'_eq_zero_iff (v : HeightOneSpectrum R) (a : Kˣ) :
    (residueDataAtPlace K v).val' a = 0 ↔ v.valuation K (a : K) = 1 := by
  rw [ResidueData.val'_eq_zero_iff]
  exact tameValHom_mem_ker_iff (v.valuation K) a

/-- **A class has nonzero residue at only finitely many places.** -/
theorem finite_milnorResidueAtPlace_ne_zero_symbol (n : ℕ) (s : MilnorSymbolDeg K n) :
    {v : HeightOneSpectrum R |
      milnorResidueAtPlace K v n (milnorClassDeg K n s) ≠ 0}.Finite := by
  classical
  refine Set.Finite.subset
    (Set.Finite.biUnion (s.val.toFinset.finite_toSet)
      (fun a _ => finite_valuation_ne_one K a)) ?_
  intro v hv
  by_contra hnot
  refine hv ?_
  refine milnorResidue_eq_zero_of_units (residueDataAtPlace K v) n s (fun a ha => ?_)
  refine (residueDataAtPlace_val'_eq_zero_iff K v a).2 ?_
  by_contra hne
  exact hnot (Set.mem_biUnion (by simpa using ha) hne)

/-- **The residue at every place, in every degree, vanishing off a finite set.** -/
theorem finite_milnorResidueAtPlace_ne_zero (n : ℕ) (x : MilnorKDeg K n) :
    {v : HeightOneSpectrum R | milnorResidueAtPlace K v n x ≠ 0}.Finite := by
  classical
  refine milnorKDeg_mem_of_gen
    { carrier := {y : MilnorKDeg K n |
        {v : HeightOneSpectrum R | milnorResidueAtPlace K v n y ≠ 0}.Finite}
      zero_mem' := by
        refine Set.Finite.subset (Set.finite_empty) ?_
        intro v hv
        exact absurd (map_zero (milnorResidueAtPlace K v n)) hv
      add_mem' := by
        intro y z hy hz
        refine Set.Finite.subset (hy.union hz) ?_
        intro v hv
        by_contra hnot
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
        exact hv (by rw [map_add, hnot.1, hnot.2, add_zero])
      neg_mem' := by
        intro y hy
        refine Set.Finite.subset hy ?_
        intro v hv
        by_contra hnot
        simp only [Set.mem_setOf_eq, not_not] at hnot
        exact hv (by rw [_root_.map_neg, hnot, neg_zero]) }
    (fun s => finite_milnorResidueAtPlace_ne_zero_symbol K n s) x

variable (R)

/-- **The tame kernel in degree `n`**: the classes whose residue vanishes at every finite place. -/
noncomputable def milnorTameKernel (n : ℕ) : AddSubgroup (MilnorKDeg K n) :=
  ⨅ v : HeightOneSpectrum R, (milnorResidueAtPlace K v n).ker

theorem mem_milnorTameKernel_iff (n : ℕ) (x : MilnorKDeg K n) :
    x ∈ milnorTameKernel R K n ↔ ∀ v : HeightOneSpectrum R, milnorResidueAtPlace K v n x = 0 := by
  rw [milnorTameKernel, AddSubgroup.mem_iInf]
  exact forall_congr' fun v => AddMonoidHom.mem_ker

/-- **Every class has a nonzero multiple in the tame kernel**, as soon as its residues are torsion
and vanish off a finite set. -/
theorem exists_zsmul_mem_milnorTameKernel (n : ℕ) (x : MilnorKDeg K n)
    (hx : {v : HeightOneSpectrum R | milnorResidueAtPlace K v n x ≠ 0}.Finite)
    (htor : ∀ v : HeightOneSpectrum R,
      milnorResidueAtPlace K v n x ∈ torsionAddSubgroup
        (MilnorKDeg (ResidueField (v.valuation K).valuationSubring) (n - 1))) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ milnorTameKernel R K n := by
  classical
  choose m hm hmz using htor
  refine ⟨∏ v ∈ hx.toFinset, m v, Finset.prod_ne_zero_iff.2 (fun v _ => hm v), ?_⟩
  rw [mem_milnorTameKernel_iff]
  intro v
  rw [map_zsmul]
  by_cases hv : milnorResidueAtPlace K v n x = 0
  · rw [hv, smul_zero]
  · obtain ⟨c, hc⟩ : m v ∣ ∏ w ∈ hx.toFinset, m w :=
      Finset.dvd_prod_of_mem _ (hx.mem_toFinset.2 hv)
    rw [hc, mul_comm, mul_smul, hmz v, smul_zero]

/-- **Torsion of the tame kernel forces torsion of `K_n^M(K)`**, provided the residue targets are
torsion. -/
theorem milnorKDeg_torsion_of_milnorTameKernel_torsion (n : ℕ)
    (htar : ∀ (v : HeightOneSpectrum R)
      (y : MilnorKDeg (ResidueField (v.valuation K).valuationSubring) (n - 1)),
      y ∈ torsionAddSubgroup _)
    (hTK : ∀ y ∈ milnorTameKernel R K n, y ∈ torsionAddSubgroup (MilnorKDeg K n))
    (x : MilnorKDeg K n) : x ∈ torsionAddSubgroup (MilnorKDeg K n) := by
  obtain ⟨N, hN, hmem⟩ := exists_zsmul_mem_milnorTameKernel R K n x
    (finite_milnorResidueAtPlace_ne_zero K n x) (fun v => htar v _)
  obtain ⟨M, hM, hMz⟩ := hTK _ hmem
  exact ⟨M * N, mul_ne_zero hM hN, by rw [mul_smul]; exact hMz⟩

end Gersten

end GaloisForLFunctions.HTGeometry
