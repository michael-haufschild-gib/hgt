import GaloisForLFunctions.HTGeometry.GenPeriodEscapeLaw
import GaloisForLFunctions.HTGeometry.FacetSeparatorMonomial
import GaloisForLFunctions.HTGeometry.PeriodEscapeDimension
import GaloisForLFunctions.HTGeometry.PencilRowGerm
import GaloisForLFunctions.HTGeometry.PencilHTDimension

/-!
# The period group of a facet carrier is an escape subgroup

Given, for every facet, an entire carrier that is hypertranscendental and whose translation
invariance recovers the facet incidence exactly, the period groups form a period-escape separation:
each is closed with complex-linear identity component because it is a period group of a meromorphic
germ, and each has noncompact quotient by the period-escape law.

This is the analytic half of the facet theorem; the combinatorial half chooses the carriers as the
separating monomials acting on a Stanley--Reisner seed.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher Filter Set
open scoped Differential

variable {n : ℕ}

/-- A translation is a period of an entire germ exactly when it is a period of the function. -/
theorem mem_meroPeriodSubgroupGen_entireGerm_iff {G : (Fin (n + 1) → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) (h : Fin (n + 1) → ℂ) :
    h ∈ meroPeriodSubgroupGen (E := Fin (n + 1) → ℂ) (entireGerm G hG)
      ↔ ∀ z, G (z + h) = G z := by
  have hone : (1 : analyticSubringGen (Set.univ : Set (Fin (n + 1) → ℂ))) ≠ 0 := one_ne_zero
  have hdiv : entireGerm G hG
      = algebraMap (analyticSubringGen (Set.univ : Set (Fin (n + 1) → ℂ)))
          (meroFieldGen (Set.univ : Set (Fin (n + 1) → ℂ))) (entireGermGen G hG)
        / algebraMap (analyticSubringGen (Set.univ : Set (Fin (n + 1) → ℂ)))
          (meroFieldGen (Set.univ : Set (Fin (n + 1) → ℂ))) 1 := by
    rw [map_one, div_one]
    rfl
  rw [hdiv]
  rw [mem_meroPeriodSubgroupGen_iff (A := G) (B := fun _ => 1) hone rfl rfl h]
  constructor
  · intro hz z
    have := hz z
    simpa using this
  · intro hz z
    have := hz z
    simpa using this

/-- **A facet family of hypertranscendental carriers is a period-escape separation.** -/
noncomputable def periodEscapeSeparationOfCarriers {V A : Type*}
    (faces : A → Finset V) (w : Fin (n + 1) → ℂ) (ω : V → Fin (n + 1) → ℂ)
    (hindep : LinearIndependent ℚ ω)
    (G : A → (Fin (n + 1) → ℂ) → ℂ) (hG : ∀ B, AnalyticOnNhd ℂ (G B) Set.univ)
    (hHT : ∀ B,
      letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin (n + 1) → ℂ))
        isPreconnected_univ_gen Set.univ_nonempty
      HypertranscendentalOver ℂ (entireGerm (G B) (hG B)))
    (hinc : ∀ B v, (∀ z, G B (z + ω v) = G B z) ↔ v ∉ faces B) :
    PeriodEscapeSeparation faces (n + 1) where
  a := ω
  indep := hindep
  P := fun B => meroPeriodSubgroupGen (E := Fin (n + 1) → ℂ) (entireGerm (G B) (hG B))
  escape := fun B => isEscapeSubgroup_meroPeriodSubgroupGen_of_hypertranscendental w (hHT B)
  incidence := fun B v => by
    rw [mem_meroPeriodSubgroupGen_entireGerm_iff (hG B) (ω v)]
    exact hinc B v

/-! ## Singleton independence in the Stanley--Reisner row matroid -/

theorem support_C_mul_of_ne_zero {R : Type*} [CommRing R] [IsDomain R] {α : Type*}
    {c : R} (hc : c ≠ 0) (P : MvPolynomial α R) :
    (MvPolynomial.C c * P).support = P.support := by
  ext e
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, ne_eq, mul_eq_zero,
    not_or]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hc, h⟩

theorem linearIndependent_singleton_of_notMem_stanleyReisnerIdeal
    {α : Type} [Fintype α] [DecidableEq α] {facets : Finset (Finset α)}
    {P : MvPolynomial α (Polynomial ℂ)} (hP : P ∉ stanleyReisnerIdeal (Polynomial ℂ) facets) :
    LinearIndependent (Polynomial ℂ)
      (fun _ : ↥(Set.univ : Set Unit) =>
        Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets) P) := by
  classical
  rw [_root_.linearIndependent_iff']
  intro s g hsum i hi
  by_contra hg
  have hs : s = {i} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j _ => Subsingleton.elim j i⟩
  rw [hs, Finset.sum_singleton] at hsum
  have hsm : g i • (Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets) P)
      = Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
        (MvPolynomial.C (g i) * P) := by
    rw [map_mul]
    exact Algebra.smul_def
      (A := MvPolynomial α (Polynomial ℂ) ⧸ stanleyReisnerIdeal (Polynomial ℂ) facets) (g i) _
  rw [hsm] at hsum
  have hmem : MvPolynomial.C (g i) * P ∈ stanleyReisnerIdeal (Polynomial ℂ) facets :=
    (Ideal.Quotient.eq_zero_iff_mem).mp hsum
  refine hP ?_
  rw [mem_stanleyReisnerIdeal_iff] at hmem ⊢
  intro e he
  exact hmem e (by rwa [support_C_mul_of_ne_zero hg P])

/-! ## Transferring independence along a matroid identity -/

theorem indep_of_matroid_eq {ι : Type*} {M N : Matroid ι} (h : M = N) {I : Set ι}
    (hI : N.Indep I) : M.Indep I := by
  subst h
  exact hI

/-! ## The one-term operator of a separating monomial -/

section Op

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The order-one operator family carrying only the separating monomial of a facet. -/
noncomputable def facetSepOp (facets : Finset (Finset α)) (A : Finset α) :
    ℕ → MvPolynomial α ℂ :=
  fun r => if r = 0 then facetSepMonomial facets A else 0

omit [Fintype α] in
theorem opPoly_facetSepOp (facets : Finset (Finset α)) (A : Finset α) :
    opPoly 1 (facetSepOp facets A)
      = MvPolynomial.map Polynomial.C (facetSepMonomial facets A) := by
  rw [opPoly, Finset.sum_range_one]
  simp [facetSepOp]

omit [Fintype α] in
theorem opCarrier_facetSepOp {d : ℕ} (w : Fin d → ℂ) (ω : α → (Fin d → ℂ))
    (F : (Fin d → ℂ) → ℂ) (facets : Finset (Finset α)) (A : Finset α) :
    opCarrier w ω F 1 (facetSepOp facets A)
      = seedCarrierPoly ω F (facetSepMonomial facets A) := by
  funext z
  rw [opCarrier, Finset.sum_range_one]
  simp [facetSepOp]

theorem map_facetSepMonomial_notMem {facets : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ facets) (hsep : ∀ B ∈ facets.erase A, (A \ B).Nonempty) :
    opPoly 1 (facetSepOp facets A) ∉ stanleyReisnerIdeal (Polynomial ℂ) facets := by
  intro hmem
  refine facetSepMonomial_notMem_stanleyReisnerIdeal hA hsep ?_
  rw [opPoly_facetSepOp, mem_stanleyReisnerIdeal_iff] at hmem
  rw [mem_stanleyReisnerIdeal_iff]
  intro e he
  exact hmem e (by rwa [MvPolynomial.support_map_of_injective _ Polynomial.C_injective])

end Op

/-! ## Hypertranscendence from a matroid identity -/

section HT

variable {α : Type} [Fintype α] [DecidableEq α]

theorem injective_unitUnivPair :
    Function.Injective
      (fun p : Unit × ℕ => ((⟨p.1, Set.mem_univ p.1⟩ : ↥(Set.univ : Set Unit)), p.2)) := by
  intro x y hxy
  simp only [Prod.mk.injEq] at hxy
  exact Prod.ext (Subsingleton.elim x.1 y.1) hxy.2

/-- A nonzero class is an independent singleton of the localized Stanley--Reisner row matroid. -/
theorem stanleyReisnerLaurentMatroid_indep_singleton
    {facets : Finset (Finset α)} (dd : translationSubmonoid (Polynomial ℂ) α)
    {N : MvPolynomial α (Polynomial ℂ)}
    (hN : N ∉ stanleyReisnerIdeal (Polynomial ℂ) facets) :
    (stanleyReisnerLaurentMatroid dd facets
      (fun _ : Unit => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets) N)).Indep
        Set.univ :=
  (stanleyReisnerLaurentMatroid_indep_iff _ _ _ _).mpr
    (linearIndependent_singleton_of_notMem_stanleyReisnerIdeal hN)

/-- Reindexing a one-element differential family from the universal subtype to `Unit`. -/
theorem differentialIndependent_unit_of_univ {F K : Type} [CommRing F] [CommRing K]
    [Algebra F K] [Differential K] {x : K}
    (h : DifferentialIndependent F (fun _ : ↥(Set.univ : Set Unit) => x)) :
    DifferentialIndependent F (fun _ : Unit => x) :=
  AlgebraicIndependent.comp h
    (fun p : Unit × ℕ => ((⟨p.1, Set.mem_univ p.1⟩ : ↥(Set.univ : Set Unit)), p.2))
    injective_unitUnivPair

/-- **A nonzero Stanley--Reisner class makes its carrier hypertranscendental.** -/
theorem hypertranscendentalOver_of_matroid_eq {K : Type} [Field K] [Algebra ℂ K]
    [Differential ℂ] [Differential K] [DifferentialAlgebra ℂ K] [CharZero K]
    {facets : Finset (Finset α)} (dd : translationSubmonoid (Polynomial ℂ) α)
    {N : MvPolynomial α (Polynomial ℂ)}
    (hN : N ∉ stanleyReisnerIdeal (Polynomial ℂ) facets) {x : K}
    (heq : differentialFamilyMatroid (F := ℂ) (fun _ : Unit => x)
      = stanleyReisnerLaurentMatroid dd facets
        (fun _ : Unit => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets) N)) :
    HypertranscendentalOver ℂ x := fun hDA =>
  hDA (differentialIndependent_unit_of_univ
    ((differentialFamilyMatroid_indep_iff (F := ℂ) (fun _ : Unit => x) Set.univ).mp
      (indep_of_matroid_eq heq (stanleyReisnerLaurentMatroid_indep_singleton dd hN))))

end HT

/-! ## The facet period-escape theorem -/

section Facet

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-- **The facet period-escape theorem.**  An intrinsic hypertranscendental realization of a facet
antichain in dimension `n + 1` induces a period-escape separation in the same dimension: the
separating monomial of each facet produces a hypertranscendental carrier whose periods are exactly
the translations of the vertices outside that facet. -/
theorem exists_periodEscapeSeparation_of_htRealizableDim
    (facets : Finset (Finset α))
    (hanti : ∀ B ∈ facets, ∀ C ∈ facets, B ⊆ C → B = C)
    (hd : HTRealizableDim facets (n + 1)) :
    Nonempty (PeriodEscapeSeparation (fun A : ↥facets => (A : Finset α)) (n + 1)) := by
  classical
  letI := htDimComplexDifferential
  obtain ⟨ω, w, Y, hY, hindep, hper, hann, hmat⟩ := hd
  have hFan : AnalyticOnNhd ℂ (fun y => ∑ A : facets, Y A y) Set.univ :=
    Finset.analyticOnNhd_fun_sum _ fun A _ => hY A
  have hsep : ∀ A : ↥facets, ∀ B ∈ facets.erase (A : Finset α),
      ((A : Finset α) \ B).Nonempty := fun A => sepNonempty_of_antichain A.2 hanti
  have hGan : ∀ A : ↥facets, AnalyticOnNhd ℂ
      (fun z => opCarrier w ω (fun y => ∑ A : facets, Y A y) 1
        (facetSepOp facets (A : Finset α))
        (z - ∑ v, (translationDenominatorExponent
          (1 : translationSubmonoid (Polynomial ℂ) α) v : ℤ) • ω v)) Set.univ :=
    fun A => analyticOnNhd_opCarrier_sub w ω hFan 1 (facetSepOp facets (A : Finset α)) _
  refine ⟨periodEscapeSeparationOfCarriers _ w ω hindep _ hGan ?_ ?_⟩
  · -- hypertranscendence of each carrier
    intro A
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin (n + 1) → ℂ))
      isPreconnected_univ_gen Set.univ_nonempty
    haveI := meroFieldGenDirDifferentialAlgebra w
    exact hypertranscendentalOver_of_matroid_eq
      (1 : translationSubmonoid (Polynomial ℂ) α)
      (map_facetSepMonomial_notMem A.2 (hsep A))
      (hmat Unit (1 : translationSubmonoid (Polynomial ℂ) α) 1
        (fun _ => facetSepOp facets (A : Finset α)))
  · -- the incidence
    intro A v
    have hshift : (∀ z, (fun z => opCarrier w ω (fun y => ∑ A : facets, Y A y) 1
          (facetSepOp facets (A : Finset α))
          (z - ∑ u, (translationDenominatorExponent
            (1 : translationSubmonoid (Polynomial ℂ) α) u : ℤ) • ω u)) (z + ω v)
        = (fun z => opCarrier w ω (fun y => ∑ A : facets, Y A y) 1
          (facetSepOp facets (A : Finset α))
          (z - ∑ u, (translationDenominatorExponent
            (1 : translationSubmonoid (Polynomial ℂ) α) u : ℤ) • ω u)) z)
        ↔ ∀ y, seedCarrierPoly ω (fun y => ∑ A : facets, Y A y)
            (facetSepMonomial facets (A : Finset α)) (y + ω v)
          = seedCarrierPoly ω (fun y => ∑ A : facets, Y A y)
            (facetSepMonomial facets (A : Finset α)) y := by
      simp only [opCarrier_facetSepOp]
      constructor
      · intro h y
        have hy := h (y + ∑ u, (translationDenominatorExponent
          (1 : translationSubmonoid (Polynomial ℂ) α) u : ℤ) • ω u)
        rw [show ∀ a b : Fin (n + 1) → ℂ, a + b + ω v - b = a + ω v from fun a b => by abel,
          show ∀ a b : Fin (n + 1) → ℂ, a + b - b = a from fun a b => by abel] at hy
        exact hy
      · intro h z
        rw [show z + ω v - ∑ u, (translationDenominatorExponent
            (1 : translationSubmonoid (Polynomial ℂ) α) u : ℤ) • ω u
          = (z - ∑ u, (translationDenominatorExponent
            (1 : translationSubmonoid (Polynomial ℂ) α) u : ℤ) • ω u) + ω v from by abel]
        exact h _
    rw [hshift]
    constructor
    · intro h hvA
      refine X_mul_facetSepMonomial_notMem A.2 (hsep A) hvA ((hann _).mp ?_)
      funext y
      rw [seedCarrierPoly_X_mul]
      simp only [Pi.zero_apply]
      rw [h y, sub_self]
    · intro hvA y
      have hy := congrFun ((hann _).mpr (X_mul_facetSepMonomial_mem (hsep A) hvA)) y
      rw [seedCarrierPoly_X_mul] at hy
      simp only [Pi.zero_apply] at hy
      exact sub_eq_zero.mp hy

/-- **The period-escape dimension is at most the intrinsic realization dimension.** -/
theorem peDim_le_htDim (facets : Finset (Finset α))
    (hanti : ∀ B ∈ facets, ∀ C ∈ facets, B ⊆ C → B = C) (hpos : 0 < htDim facets) :
    peDim (fun A : ↥facets => (A : Finset α)) ≤ htDim facets := by
  have hne : {d | HTRealizableDim facets d}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [htDim, hcon] at hpos
    simp at hpos
  have hmem : HTRealizableDim facets (htDim facets) := Nat.sInf_mem hne
  obtain ⟨m, hm⟩ : ∃ m, htDim facets = m + 1 := ⟨htDim facets - 1, by omega⟩
  rw [hm] at hmem ⊢
  obtain ⟨S⟩ := exists_periodEscapeSeparation_of_htRealizableDim facets hanti hmem
  exact peDim_le_of_nonempty S

end Facet

end GaloisForLFunctions.HTGeometry
