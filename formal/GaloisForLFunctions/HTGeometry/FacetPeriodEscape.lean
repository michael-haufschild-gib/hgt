import GaloisForLFunctions.HTGeometry.GenPeriodEscapeLaw
import GaloisForLFunctions.HTGeometry.FacetSeparatorMonomial
import GaloisForLFunctions.HTGeometry.PeriodEscapeDimension
import GaloisForLFunctions.HTGeometry.PencilRowGerm

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

end GaloisForLFunctions.HTGeometry
