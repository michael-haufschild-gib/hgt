import GaloisForLFunctions.HTGeometry.PolynomialTwistedCech

/-! A Laurent cocycle for a negative twist is a boundary once its monomials with
all projective exponents negative vanish. -/

noncomputable section

open AddMonoidAlgebra HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {K ι ν : Type*} [CommRing K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [Fintype ν] [DecidableEq ν]

private theorem laurentCoeffs_zero {e : ℕ} (I : Finset ι) :
    laurentCoeffs (0 : (polyTwCech K ι ν e).Cochain) I = 0 := by
  change (laurentLoc K ι ν I 0).coeff = 0
  rw [map_zero, AddMonoidAlgebra.coeff_zero]

/-- In positive Čech degree, only monomials with full negative support can
obstruct a cocycle from being a boundary. -/
theorem polyTwCech_exists_primitive [Nonempty ι] {e p : ℕ}
    {c : (polyTwCech K ι ν e).Cochain}
    (hc : (polyTwCech K ι ν e).IsDeg c (p + 1)) (hdc : (polyTwCech K ι ν e).d c = 0)
    (hfull : ∀ a : LaurentExp ι ν, negSupp a = Finset.univ → laurentCoeffs c Finset.univ a = 0) :
    ∃ b : (polyTwCech K ι ν e).Cochain,
      (polyTwCech K ι ν e).IsDeg b p ∧ (polyTwCech K ι ν e).d b = c := by
  classical
  have hcard (I : Finset ι) (hI : I.card ≠ p + 2) : laurentCoeffs c I = 0 := by
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

/-- A negative twist is Čech-exact in positive degrees below the projective dimension. -/
theorem polyTwCech_exactAt_of_below_top {e p : ℕ} (hp : p + 2 < Fintype.card ι) :
    (polyTwCech K ι ν e).ExactAt (p + 1) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  intro c hc hdc
  refine polyTwCech_exists_primitive hc hdc (fun a _ => ?_)
  have hcard : (Finset.univ : Finset ι).card ≠ p + 2 := by
    rw [Finset.card_univ]
    omega
  change (laurentLoc K ι ν Finset.univ (twVal projCoord_mem (c Finset.univ))).coeff a = 0
  rw [hc Finset.univ hcard]
  exact DFunLike.congr_fun (laurentCoeffs_zero (K := K) (ν := ν) (e := e) Finset.univ) a

/-- On projective space the degree fixes a lower bound for each fully negative
exponent, so only finitely many monomials can survive in top degree. -/
theorem finite_full_negative_exponents [IsEmpty ν] (e : ℕ) :
    Finite {a : LaurentExp ι ν // DegAdm e a ∧ negSupp a = Finset.univ} := by
  classical
  have hneg (a : {a : LaurentExp ι ν // DegAdm e a ∧ negSupp a = Finset.univ}) (i : ι) :
      a.1 (Sum.inl i) < 0 :=
    (Finset.mem_filter.mp (a.2.2 ▸ Finset.mem_univ i : i ∈ negSupp a.1)).2
  let f (a : {a : LaurentExp ι ν // DegAdm e a ∧ negSupp a = Finset.univ}) :
      ι → Set.Icc (-(e : ℤ)) (-1) := fun i =>
    ⟨a.1 (Sum.inl i), by
      refine ⟨?_, by have := hneg a i; omega⟩
      have hrest : ∑ j ∈ Finset.univ.erase i, a.1 (Sum.inl j) ≤ 0 :=
        Finset.sum_nonpos fun j _ => (hneg a j).le
      have hsum := Finset.sum_erase_add Finset.univ (fun j => a.1 (Sum.inl j)) (Finset.mem_univ i)
      rw [a.2.1.2] at hsum
      omega⟩
  refine Finite.of_injective f fun a b h => Subtype.ext (Finsupp.ext fun v => ?_)
  rcases v with i | j
  · exact congrArg Subtype.val (congrFun h i)
  · exact isEmptyElim j

end GlobalTheory.SchemeCohomology
