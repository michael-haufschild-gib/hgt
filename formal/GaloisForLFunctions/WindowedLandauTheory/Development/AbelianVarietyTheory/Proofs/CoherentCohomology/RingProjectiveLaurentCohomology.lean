import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.RingPolynomialCechCoefficients

/-! Negative monomials are the only top-degree obstructions over a commutative base. -/

noncomputable section

open AddMonoidAlgebra HTGeometry

namespace GlobalTheory.SchemeCohomology.RingPolynomialCech

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type*} {ι ν : Type} [CommRing K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [Fintype ν] [DecidableEq ν]

omit [Fintype ι] [LinearOrder ι] [Fintype ν] [DecidableEq ν] in
private theorem laurentCoeffs_zero {e : ℕ} (I : Finset ι) :
    laurentCoeffs (0 : (polyTwCech K ι ν e).Cochain) I = 0 := by
  change (laurentLoc K ι ν I 0).coeff = 0
  rw [map_zero, AddMonoidAlgebra.coeff_zero]

/-- In the augmented Čech complex, only monomials with full negative support
can obstruct a cocycle from being a boundary. -/
theorem polyTwCech_exists_primitive [Nonempty ι] {e p : ℕ}
    {c : (polyTwCech K ι ν e).Cochain}
    (hc : (polyTwCech K ι ν e).IsDeg c p) (hdc : (polyTwCech K ι ν e).d c = 0)
    (hfull : ∀ a : LaurentExp ι ν, negSupp a = Finset.univ → laurentCoeffs c Finset.univ a = 0) :
    ∃ b : (polyTwCech K ι ν e).Cochain,
      (∀ I : Finset ι, I.card ≠ p → b I = 0) ∧ (polyTwCech K ι ν e).d b = c := by
  classical
  have hcard (I : Finset ι) (hI : I.card ≠ p + 1) : laurentCoeffs c I = 0 := by
    change (laurentLoc K ι ν I (twVal projCoord_mem (c I))).coeff = 0
    rw [hc I hI]
    exact laurentCoeffs_zero I
  have hadm (I : Finset ι) (a : LaurentExp ι ν) (ha : a ∈ (laurentCoeffs c I).support) :
      negSupp a ⊆ I ∧ DegAdm e a :=
    laurentLoc_mem_admSubgroup (c I : twPart (projGrading K ι ν) (projCoord K ι ν) I e).2 a ha
  have hδ : monoCechD (laurentCoeffs c) = 0 := by
    funext I
    rw [← laurentCoeffs_d, hdc]
    exact laurentCoeffs_zero I
  have hne (I : Finset ι) (a : LaurentExp ι ν) (ha : a ∈ (laurentCoeffs c I).support) :
      negSupp a ≠ Finset.univ := by
    intro h
    have hI := (hadm I a ha).1
    rw [h, Finset.univ_subset_iff] at hI
    subst I
    exact (Finsupp.mem_support_iff.mp ha) (hfull a h)
  obtain ⟨η, hηcard, hηchart, hηsupp, hηd⟩ :=
    monoCech_vanishing (supp := negSupp) hcard (fun I a ha => (hadm I a ha).1) hδ hne
  have hηadm (I : Finset ι) : AddMonoidAlgebra.ofCoeff (η I) ∈ admSubgroup K I e := by
    intro a ha
    obtain ⟨J, hJ⟩ := hηsupp I a ha
    exact ⟨hηchart I a ha, (hadm J a hJ).2⟩
  choose y hy hycoeff using fun I => exists_laurentLoc_eq (hηadm I)
  let b : (polyTwCech K ι ν e).Cochain := fun I => ⟨y I, hy I⟩
  have hb : laurentCoeffs b = η := funext fun I =>
    congrArg AddMonoidAlgebra.coeff (hycoeff I)
  have hinj (I : Finset ι) : Function.Injective
      (fun z : (polyTwCech K ι ν e).obj I => (laurentLoc K ι ν I (twVal projCoord_mem z)).coeff) :=
    AddMonoidAlgebra.coeff_injective.comp ((laurentLoc_injective I).comp
      (twVal_injective projCoord_mem))
  refine ⟨b, fun I hI => hinj I ?_, funext fun I => hinj I ?_⟩
  · change laurentCoeffs b I = laurentCoeffs (0 : (polyTwCech K ι ν e).Cochain) I
    rw [hb, hηcard I hI, laurentCoeffs_zero]
  · change laurentCoeffs ((polyTwCech K ι ν e).d b) I = laurentCoeffs c I
    rw [laurentCoeffs_d, hb, hηd]

/-- A negative twist is exact in the augmented Čech complex below the projective dimension. -/
theorem polyTwCech_exactAt_of_below_top {e p : ℕ} (hp : p + 1 < Fintype.card ι) :
    (polyTwCech K ι ν e).ExactAt p := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  intro c hc hdc
  refine polyTwCech_exists_primitive hc hdc (fun a _ => ?_)
  have hcard : (Finset.univ : Finset ι).card ≠ p + 1 := by
    rw [Finset.card_univ]
    omega
  change (laurentLoc K ι ν Finset.univ (twVal projCoord_mem (c Finset.univ))).coeff a = 0
  rw [hc Finset.univ hcard]
  exact DFunLike.congr_fun (laurentCoeffs_zero (K := K) (ν := ν) (e := e) Finset.univ) a

/-- Fully negative monomials cannot occur in any boundary: each summand of the
top differential comes from an intersection missing one inverted coordinate. -/
theorem polyTwCech_boundary_full_negative_coeff {e : ℕ}
    (b : (polyTwCech K ι ν e).Cochain) (a : LaurentExp ι ν) (ha : negSupp a = Finset.univ) :
    laurentCoeffs ((polyTwCech K ι ν e).d b) Finset.univ a = 0 := by
  classical
  rw [laurentCoeffs_d, monoCechD, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finsupp.smul_apply]
  have hz : laurentCoeffs b (Finset.univ.erase i) a = 0 := by
    by_contra h
    have hmem := Finsupp.mem_support_iff.mpr h
    have hadm := laurentLoc_mem_admSubgroup
      (b (Finset.univ.erase i) : twPart (projGrading K ι ν) (projCoord K ι ν) (Finset.univ.erase i) e).2
      a hmem
    exact Finset.notMem_erase i Finset.univ (hadm.1 (ha ▸ Finset.mem_univ i))
  rw [hz, smul_zero]

/-- The degree-zero twist is exact in the augmented complex in every degree. -/
theorem polyTwCech_zero_exactAt [Nonempty ι] (p : ℕ) :
    (polyTwCech K ι ν 0).ExactAt p := by
  intro c hc hd
  refine polyTwCech_exists_primitive hc hd (fun a ha => ?_)
  by_contra h
  have hd₀ := (laurentLoc_mem_admSubgroup
    (c Finset.univ : twPart (projGrading K ι ν) (projCoord K ι ν) Finset.univ 0).2
    a (Finsupp.mem_support_iff.mpr h)).2.2
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hneg (j : ι) : a (Sum.inl j) < 0 := by
    have hj : j ∈ negSupp a := ha.symm ▸ Finset.mem_univ j
    exact (Finset.mem_filter.mp hj).2
  have hrest : ∑ j ∈ Finset.univ.erase i, a (Sum.inl j) ≤ 0 :=
    Finset.sum_nonpos fun j _ => (hneg j).le
  have hsum := Finset.sum_erase_add Finset.univ (fun j => a (Sum.inl j)) (Finset.mem_univ i)
  rw [hd₀] at hsum
  have hi := hneg i
  omega

end GlobalTheory.SchemeCohomology.RingPolynomialCech
