import GaloisForLFunctions.HTGeometry.PencilFullOrbit

/-!
# The periodic-pencil realization: exact annihilator and exact differential matroid

One choice of facet sources realizes the complex completely.  Its annihilator among difference
operators is exactly the Stanley--Reisner ideal, and for every finite family of operators with
derivation coefficients the differential matroid of the outputs is the Stanley--Reisner
quotient-class matroid.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Bottcher
open scoped Classical Differential

noncomputable section

variable {α : Type} [Fintype α] [DecidableEq α]

local instance pencilRealizationComplexDifferential : Differential ℂ := ⟨0⟩

/-! ### The Stanley--Reisner ideal through facet restrictions -/

omit [Fintype α] in
theorem mem_stanleyReisnerIdeal_iff_pencilFacetRestrict {R : Type*} [CommRing R]
    (facets : Finset (Finset α)) (P : MvPolynomial α R) :
    P ∈ stanleyReisnerIdeal R facets ↔ ∀ A ∈ facets, pencilFacetRestrict A P = 0 := by
  rw [stanleyReisnerIdeal_eq_inf_facetIdeal, Finset.inf_eq_iInf, Ideal.mem_iInf]
  constructor
  · intro h A hA
    have hmem := h A
    rw [Ideal.mem_iInf] at hmem
    exact (pencilFacetRestrict_eq_zero_iff_mem_facetIdeal A P).mpr (hmem hA)
  · intro h A
    rw [Ideal.mem_iInf]
    intro hA
    exact (pencilFacetRestrict_eq_zero_iff_mem_facetIdeal A P).mp (h A hA)

/-- A family containing a zero element is not differentially independent. -/
theorem not_differentialIndependent_of_eq_zero {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Differential K] {ι : Type*} (x : ι → K) (i : ι) (hi : x i = 0) :
    ¬ DifferentialIndependent F x := by
  intro h
  have hinj := h.algebraMap_injective
  have hzero : MvPolynomial.aeval (fun p : ι × ℕ => differentialJet p.2 (x p.1))
      (MvPolynomial.X (i, 0) : MvPolynomial (ι × ℕ) F) = 0 := by
    rw [MvPolynomial.aeval_X]
    show differentialJet 0 (x i) = 0
    rw [differentialJet_zero, hi]
  have := (algebraicIndependent_iff.mp h) _ hzero
  exact (MvPolynomial.X_ne_zero (R := F) (i, 0)) this

theorem linearIndependent_of_subsingleton_of_torsion {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {ι : Type*} [Subsingleton ι] (v : ι → M)
    (h : ∀ (i : ι) (c : R), c • v i = 0 → c = 0) : LinearIndependent R v := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  refine h i (g i) ?_
  have hsingle : ∑ j ∈ s, g j • v j = g i • v i :=
    Finset.sum_eq_single_of_mem i hi fun j _ hji => absurd (Subsingleton.elim j i) hji
  rw [← hsingle, hsum]

omit [Fintype α] in
/-- Multiplying by a nonzero derivation polynomial does not enter the Stanley--Reisner ideal. -/
theorem mul_mapC_notMem_stanleyReisnerIdeal (facets : Finset (Finset α))
    (P : MvPolynomial α ℂ) (hP : P ∉ stanleyReisnerIdeal ℂ facets)
    (c : Polynomial ℂ) (hc : c ≠ 0) :
    MvPolynomial.C c * MvPolynomial.map (Polynomial.C) P
      ∉ stanleyReisnerIdeal (Polynomial ℂ) facets := by
  rw [mem_stanleyReisnerIdeal_iff_pencilFacetRestrict] at hP ⊢
  push Not at hP ⊢
  obtain ⟨A, hA, hAP⟩ := hP
  refine ⟨A, hA, ?_⟩
  rw [map_mul, pencilFacetRestrict_C, pencilFacetRestrict_map]
  intro hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact hc (by simpa using (MvPolynomial.C_eq_zero (σ := α)).mp h)
  · exact hAP (MvPolynomial.map_injective (Polynomial.C (R := ℂ)) Polynomial.C_injective
      (by rw [h, map_zero]))

/-! ### The realization law -/

variable {d : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The exact differential matroid of a pencil orbit, for every operator family.** -/
theorem pencilOrbit_matroid_eq {facets : Finset (Finset α)}
    (a : α → (Fin d → ℂ)) (w : Fin d → ℂ)
    (Y : facets → (Fin d → ℂ) → ℂ) (hY : ∀ A, AnalyticOnNhd ℂ (Y A) Set.univ)
    (hper : ∀ (A : facets) (v : α), v ∉ A.1 → ∀ z, Y A (z + a v) = Y A z)
    (hind : JointlyDirHypertranscendental w
      (fun p : pencilOrbitIndex facets => fun z => Y p.1.1 (z + pencilShift a p.1.2)))
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (dd : translationSubmonoid (Polynomial ℂ) α) (n : ℕ) (Q : ι → ℕ → MvPolynomial α ℂ) :
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
      isPreconnected_univ_gen Set.univ_nonempty
    haveI := meroFieldGenDirDifferentialAlgebra w
    differentialFamilyMatroid (F := ℂ)
        (fun i => entireGerm (fun z => opCarrier w a (fun y => ∑ A : facets, Y A y) n (Q i)
          (z - ∑ v, (translationDenominatorExponent dd v : ℤ) • a v))
          (analyticOnNhd_opCarrier_sub w a
            (Finset.analyticOnNhd_fun_sum _ fun A _ => hY A) n (Q i) _))
      = stanleyReisnerLaurentMatroid dd facets
        (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
          (opPoly n (Q j))) := by
  classical
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
    isPreconnected_univ_gen Set.univ_nonempty
  haveI := meroFieldGenDirDifferentialAlgebra w
  set g : pencilOrbitIndex facets → (Fin d → ℂ) → ℂ :=
    fun p => fun z => Y p.1.1 (z + pencilShift a p.1.2) with hg
  set φ := rowIndexToOrbit dd
    (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets) (opPoly n (Q j)))
    with hφdef
  have hsub := jointlyDirHypertranscendental_comp_injective w g φ
    (rowIndexToOrbit_injective dd _) hind
  have hana : ∀ q, AnalyticOnNhd ℂ ((g ∘ φ) q) Set.univ := fun q =>
    analyticOnNhd_comp_add_const _ (hY (φ q).1.1) _
  have hx := differentialIndependent_of_jointlyDirHypertranscendental w (g ∘ φ) hana hsub
  have hmat := differentialFamilyMatroid_stanleyReisnerLaurentRows_eq
    (meroFieldGenDir_deriv_complexConstant w) dd facets
    (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets) (opPoly n (Q j)))
    _ hx
  refine Eq.trans ?_ hmat
  congr 1
  funext i
  exact (differentialOperatorRowApply_eq_entireGerm_opCarrier w a Y hY
    (fun A v hv z => hper A v hv z) dd n Q i).symm

omit [Fintype α] [DecidableEq α] in
theorem opPoly_one (P : MvPolynomial α ℂ) :
    opPoly 1 (fun r => if r = 0 then P else 0)
      = MvPolynomial.map (Polynomial.C) P := by
  rw [opPoly, Finset.sum_range_one, pow_zero, map_one, one_mul, if_pos rfl]

omit [Fintype α] [DecidableEq α] in
theorem opCarrier_one (w : Fin d → ℂ) (a : α → (Fin d → ℂ)) (F : (Fin d → ℂ) → ℂ)
    (P : MvPolynomial α ℂ) :
    opCarrier w a F 1 (fun r => if r = 0 then P else 0) = seedCarrierPoly a F P := by
  funext z
  rw [opCarrier, Finset.sum_range_one, if_pos rfl, Function.iterate_zero_apply]

set_option maxHeartbeats 4000000 in
/-- **The exact annihilator of a pencil orbit source.** -/
theorem pencilOrbit_seedCarrier_eq_zero_iff {facets : Finset (Finset α)}
    (a : α → (Fin d → ℂ)) (w : Fin d → ℂ)
    (Y : facets → (Fin d → ℂ) → ℂ) (hY : ∀ A, AnalyticOnNhd ℂ (Y A) Set.univ)
    (hper : ∀ (A : facets) (v : α), v ∉ A.1 → ∀ z, Y A (z + a v) = Y A z)
    (hind : JointlyDirHypertranscendental w
      (fun p : pencilOrbitIndex facets => fun z => Y p.1.1 (z + pencilShift a p.1.2)))
    (P : MvPolynomial α ℂ) :
    seedCarrierPoly a (fun y => ∑ A : facets, Y A y) P = 0 ↔
      P ∈ stanleyReisnerIdeal ℂ facets := by
  classical
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
    isPreconnected_univ_gen Set.univ_nonempty
  haveI := meroFieldGenDirDifferentialAlgebra w
  constructor
  · intro hzero
    by_contra hP
    set Qp : Unit → ℕ → MvPolynomial α ℂ := fun _ r => if r = 0 then P else 0 with hQp
    set N : Unit → MvPolynomial α (Polynomial ℂ) ⧸ stanleyReisnerIdeal (Polynomial ℂ) facets :=
      fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
        (opPoly 1 (Qp j)) with hN
    have hmat := pencilOrbit_matroid_eq a w Y hY hper hind Unit
      (1 : translationSubmonoid (Polynomial ℂ) α) 1 Qp
    have hSRindep : (stanleyReisnerLaurentMatroid (1 : translationSubmonoid (Polynomial ℂ) α)
        facets N).Indep Set.univ := by
      rw [stanleyReisnerLaurentMatroid_indep_iff]
      haveI : Subsingleton ((Set.univ : Set Unit)) :=
        ⟨fun x y => Subtype.ext (Subsingleton.elim x.1 y.1)⟩
      refine linearIndependent_of_subsingleton_of_torsion _ fun i c hc => ?_
      by_contra hcne
      refine mul_mapC_notMem_stanleyReisnerIdeal facets P hP c hcne ?_
      have hsmul : c • N (i : Unit)
          = Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
            (MvPolynomial.C c * MvPolynomial.map (Polynomial.C) P) := by
        show c • (Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
            (opPoly 1 (fun r => if r = 0 then P else 0))) = _
        have hmk := map_smul (Ideal.Quotient.mkₐ (Polynomial ℂ)
          (stanleyReisnerIdeal (Polynomial ℂ) facets)) c
          (opPoly 1 (fun r => if r = 0 then P else 0))
        have hcx : (c • opPoly 1 (fun r => if r = 0 then P else 0)
              : MvPolynomial α (Polynomial ℂ))
            = MvPolynomial.C c * MvPolynomial.map (Polynomial.C) P := by
          rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, opPoly_one]
        rw [hcx] at hmk
        exact hmk.symm
      rw [hsmul] at hc
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hc
    rw [← hmat] at hSRindep
    rw [differentialFamilyMatroid_indep_iff] at hSRindep
    refine not_differentialIndependent_of_eq_zero (F := ℂ) _ ⟨(), Set.mem_univ _⟩ ?_ hSRindep
    have hfun : (fun z => opCarrier w a (fun y => ∑ A : facets, Y A y) 1 (Qp ())
        (z - ∑ v, (translationDenominatorExponent (1 : translationSubmonoid (Polynomial ℂ) α) v
          : ℤ) • a v)) = fun _ => (0 : ℂ) := by
      funext z
      rw [hQp, opCarrier_one, hzero]
      rfl
    rw [entireGerm_congr _ _ _ analyticOnNhd_const hfun, entireGerm_zero]
  · intro hP
    rw [mem_stanleyReisnerIdeal_iff_pencilFacetRestrict] at hP
    funext z
    rw [seedCarrierPoly_sum_pencilFacetRestrict a Y hper P z]
    have hz : ∀ A : facets, seedCarrierPoly a (Y A) (pencilFacetRestrict A.1 P) z = 0 := by
      intro A
      rw [hP A.1 A.2]
      exact congrFun (map_zero (seedCarrierPolyₗ a (Y A))) z
    rw [Finset.sum_congr rfl (fun A (_ : A ∈ Finset.univ) => hz A), Finset.sum_const_zero]
    rfl

end

end GaloisForLFunctions.HTGeometry
