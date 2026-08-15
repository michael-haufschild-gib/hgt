import GaloisForLFunctions.HTGeometry.PencilOrbitSeveralVariable
import GaloisForLFunctions.HTGeometry.PencilDifferentialIndependence
import GaloisForLFunctions.HTGeometry.StanleyReisnerLaurentRowSupport

/-!
# The differential matroid of a periodic-pencil source is the localized Stanley--Reisner matroid

The finite coordinate packet of a Stanley--Reisner Laurent family indexes one translate of one facet
source per Laurent exponent, and those exponents are supported on their own facet.  Integral
independence of the facet steps modulo the periods therefore separates the packet into pairwise
distinct members of the periodic-pencil orbit, and the orbit lemma produces sources for which that
packet is differentially independent over the several-variable meromorphic field with the
directional derivation.

Feeding this into the localized Stanley--Reisner rank law identifies the whole differential-family
matroid of the operator outputs with the Stanley--Reisner quotient-class matroid: rank, circuits and
every dependence relation of a periodic-pencil realization are the Stanley--Reisner ones.
-/

open MvPolynomial Set

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Classical Differential

noncomputable section

/-! ### The differential field of the direction -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

local instance pencilComplexDifferential : Differential ℂ := ⟨0⟩

instance genCharZero : CharZero (meroFieldGen (Set.univ : Set E)) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (meroFieldGen (Set.univ : Set E))).injective

/-- Complex constants are constants of the directional derivation. -/
theorem meroFieldGenDir_deriv_complexConstant (w : E) (c : ℂ) :
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
      Set.univ_nonempty
    (algebraMap ℂ (meroFieldGen (Set.univ : Set E)) c)′ = 0 := by
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
    Set.univ_nonempty
  have h1 : (algebraMap ℂ (meroFieldGen (Set.univ : Set E)) c) =
      algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
        (constToAnalyticGen (Set.univ : Set E) c) := by
    rw [IsScalarTower.algebraMap_apply ℂ (analyticSubringGen (Set.univ : Set E))
      (meroFieldGen (Set.univ : Set E))]
    rfl
  rw [h1, meroFieldGenDirDifferential_algebraMap, analyticSubringGenDirDeriv_const, map_zero]

/-- The several-variable meromorphic field with a constant directional derivation is a differential
algebra over the constants. -/
theorem meroFieldGenDirDifferentialAlgebra (w : E) :
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
      Set.univ_nonempty
    DifferentialAlgebra ℂ (meroFieldGen (Set.univ : Set E)) := by
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
    Set.univ_nonempty
  refine ⟨fun c => ?_⟩
  rw [meroFieldGenDir_deriv_complexConstant w c]
  change (0 : meroFieldGen (Set.univ : Set E)) = algebraMap ℂ (meroFieldGen (Set.univ : Set E)) 0
  rw [map_zero]

/-- Translating an entire function keeps it entire. -/
theorem analyticOnNhd_comp_add_const (f : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) (t : E) :
    AnalyticOnNhd ℂ (fun z => f (z + t)) Set.univ := by
  refine AnalyticOnNhd.comp hf (fun z _ => analyticAt_id.add analyticAt_const)
    (Set.mapsTo_univ _ _)

/-! ### The orbit of a periodic pencil -/

variable {d : ℕ} {α ι : Type}

/-- The translation attached to an integral exponent vector of vertex steps. -/
def pencilShift [Fintype α] (a : α → (Fin d → ℂ)) (g : α → ℤ) : Fin d → ℂ := ∑ v, g v • a v

theorem map_pencilShift [Fintype α] (L : (Fin d → ℂ) →ₗ[ℂ] ℂ) (a : α → (Fin d → ℂ))
    (g : α → ℤ) : L (pencilShift a g) = ∑ v, (g v : ℂ) * L (a v) := by
  rw [pencilShift, map_sum]
  exact Finset.sum_congr rfl fun v _ => by rw [map_zsmul, zsmul_eq_mul]

/-- The member of a periodic pencil attached to a facet: a source of the compact box composed with
the exponential of the facet phase. -/
def pencilFacetMember (Lf : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) {facets : Finset (Finset α)}
    (e : facets ≃ Fin facets.card) (C : Fin facets.card → sourceBox) (A : facets) :
    (Fin d → ℂ) → ℂ :=
  fun z => jetSeriesFun (boxSeq (C (e A))) 0 (Complex.exp (Lf A.1 z))

theorem analyticOnNhd_pencilFacetMember (Lf : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    {facets : Finset (Finset α)} (e : facets ≃ Fin facets.card)
    (C : Fin facets.card → sourceBox) (A : facets) :
    AnalyticOnNhd ℂ (pencilFacetMember Lf e C A) Set.univ := by
  have h1 : AnalyticOnNhd ℂ (jetSeriesFun (boxSeq (C (e A))) 0) Set.univ :=
    (differentiable_jetSeriesFun (boxSeq_bound (C (e A))) 0).differentiableOn.analyticOnNhd
      isOpen_univ
  have hexp : AnalyticOnNhd ℂ Complex.exp Set.univ :=
    Complex.differentiable_exp.differentiableOn.analyticOnNhd isOpen_univ
  have h2 : AnalyticOnNhd ℂ (fun z : Fin d → ℂ => Complex.exp (Lf A.1 z)) Set.univ :=
    AnalyticOnNhd.comp hexp ((Lf A.1).toContinuousLinearMap.analyticOnNhd Set.univ)
      (Set.mapsTo_univ _ _)
  exact AnalyticOnNhd.comp h1 h2 (Set.mapsTo_univ _ _)

/-- A step outside a facet is a period of that facet's member. -/
theorem pencilFacetMember_add_of_notMem (Lf : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    {facets : Finset (Finset α)} (e : facets ≃ Fin facets.card)
    (C : Fin facets.card → sourceBox) (a : α → (Fin d → ℂ)) (A : facets) {v : α}
    (hv : Complex.exp (Lf A.1 (a v)) = 1) (z : Fin d → ℂ) :
    pencilFacetMember Lf e C A (z + a v) = pencilFacetMember Lf e C A z := by
  rw [pencilFacetMember, pencilFacetMember, map_add, Complex.exp_add, hv, mul_one]

/-! ### The matroid of a periodic-pencil realization -/

variable [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
set_option maxHeartbeats 1000000 in
/-- **A periodic-pencil orbit is differentially independent on a Stanley--Reisner coordinate
packet.**  For facet phases whose steps outside a facet are periods and whose steps inside a facet
are integrally independent modulo the periods, there are entire facet sources whose translates along
the finite coordinate packet of any Stanley--Reisner Laurent family satisfy no algebraic differential
relation over the constants. -/
theorem exists_pencilSource_differentialIndependent
    (facets : Finset (Finset α))
    (Lf : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) (a : α → (Fin d → ℂ)) (w : Fin d → ℂ)
    (hw : ∀ A ∈ facets, Lf A w ≠ 0)
    (houtside : ∀ A ∈ facets, ∀ v ∉ A, Complex.exp (Lf A (a v)) = 1)
    (hinside : ∀ A ∈ facets, ∀ g : α → ℤ,
      Complex.exp (∑ v ∈ A, (g v : ℂ) * Lf A (a v)) = 1 → ∀ v ∈ A, g v = 0)
    (dd : translationSubmonoid (Polynomial ℂ) α)
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸ stanleyReisnerIdeal (Polynomial ℂ) facets) :
    ∃ (Y : facets → (Fin d → ℂ) → ℂ) (hY : ∀ A, AnalyticOnNhd ℂ (Y A) Set.univ),
      (∀ (A : facets) (v : α), v ∉ A.1 → ∀ z, Y A (z + a v) = Y A z) ∧
      letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
        isPreconnected_univ_gen Set.univ_nonempty
      DifferentialIndependent ℂ
        (fun q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows dd facets N) =>
          algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
            (meroFieldGen (Set.univ : Set (Fin d → ℂ)))
            (entireGermGen (fun z => Y q.1.1 (z + pencilShift a q.1.2))
              (analyticOnNhd_comp_add_const _ (hY q.1.1) _))) := by
  classical
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ)) isPreconnected_univ_gen
    Set.univ_nonempty
  haveI := meroFieldGenDirDifferentialAlgebra w
  set e := facets.equivFin with he
  have hdist : ∀ q q' : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows dd facets N),
      e q.1.1 = e q'.1.1 → q ≠ q' →
      Complex.exp (Lf (q.1.1 : Finset α) (pencilShift a q.1.2)) ≠
        Complex.exp (Lf (q'.1.1 : Finset α) (pencilShift a q'.1.2)) := by
    intro q q' hsrc hne hval
    have hfac : q.1.1 = q'.1.1 := e.injective hsrc
    rw [← hfac] at hval
    have hz : ∀ v ∉ (q.1.1 : Finset α), q.1.2 v = 0 := fun v hv =>
      finiteFinsuppRowIndex_stanleyReisnerLaurentRows_eq_zero dd facets N q hv
    have hz' : ∀ v ∉ (q.1.1 : Finset α), q'.1.2 v = 0 := by
      intro v hv
      refine finiteFinsuppRowIndex_stanleyReisnerLaurentRows_eq_zero dd facets N q' ?_
      rwa [← hfac]
    have hgout : ∀ v ∉ (q.1.1 : Finset α), q.1.2 v - q'.1.2 v = 0 := by
      intro v hv
      rw [hz v hv, hz' v hv, sub_zero]
    have hsum : ∑ v ∈ (q.1.1 : Finset α),
          ((q.1.2 v - q'.1.2 v : ℤ) : ℂ) * Lf (q.1.1 : Finset α) (a v)
        = Lf (q.1.1 : Finset α) (pencilShift a q.1.2)
          - Lf (q.1.1 : Finset α) (pencilShift a q'.1.2) := by
      rw [map_pencilShift, map_pencilShift, ← Finset.sum_sub_distrib]
      refine (Finset.sum_subset (Finset.subset_univ (q.1.1 : Finset α)) ?_).trans
        (Finset.sum_congr rfl fun v _ => ?_)
      · intro v _ hv
        rw [hgout v hv]
        simp
      · push_cast
        ring
    have hexp1 : Complex.exp (∑ v ∈ (q.1.1 : Finset α),
        ((q.1.2 v - q'.1.2 v : ℤ) : ℂ) * Lf (q.1.1 : Finset α) (a v)) = 1 := by
      rw [hsum, Complex.exp_sub, hval, div_self (Complex.exp_ne_zero _)]
    have hgin := hinside (q.1.1 : Finset α) q.1.1.2 (fun v => q.1.2 v - q'.1.2 v) hexp1
    have hgzero : q.1.2 = q'.1.2 := by
      funext v
      by_cases hv : v ∈ (q.1.1 : Finset α)
      · have h0 : q.1.2 v - q'.1.2 v = 0 := hgin v hv
        omega
      · rw [hz v hv, hz' v hv]
    exact hne (Subtype.ext (Prod.ext hfac hgzero))
  have main : ∃ C : Fin facets.card → sourceBox,
      DifferentialIndependent ℂ
        (fun q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows dd facets N) =>
          algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
            (meroFieldGen (Set.univ : Set (Fin d → ℂ)))
            (entireGermGen (fun z => pencilFacetMember Lf e C q.1.1 (z + pencilShift a q.1.2))
              (analyticOnNhd_comp_add_const _
                (analyticOnNhd_pencilFacetMember Lf e C q.1.1) _))) := by
    rcases isEmpty_or_nonempty
        (FiniteFinsuppRowIndex (stanleyReisnerLaurentRows dd facets N)) with hemp | hnon
    · refine ⟨fun _ => Classical.arbitrary sourceBox, ?_⟩
      haveI : IsEmpty
          (FiniteFinsuppRowIndex (stanleyReisnerLaurentRows dd facets N) × ℕ) :=
        ⟨fun p => hemp.elim p.1⟩
      exact algebraicIndependent_empty_type_iff.mpr
        (algebraMap ℂ (meroFieldGen (Set.univ : Set (Fin d → ℂ)))).injective
    · obtain ⟨C, hC⟩ := exists_source_pencil_jointlyDirHypertranscendental (d := d) w
        (fun j : Fin facets.card => Lf (e.symm j).1) (fun j => hw _ (e.symm j).2)
        (fun q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows dd facets N) => e q.1.1)
        (fun q => Lf (q.1.1 : Finset α) (pencilShift a q.1.2)) hdist
      refine ⟨C, ?_⟩
      have hfam : pencilFam (fun j : Fin facets.card => Lf (e.symm j).1)
            (fun q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows dd facets N) => e q.1.1)
            (fun q => Lf (q.1.1 : Finset α) (pencilShift a q.1.2)) C
          = fun q => fun z => pencilFacetMember Lf e C q.1.1 (z + pencilShift a q.1.2) := by
        funext q z
        show jetSeriesFun (boxSeq (C (e q.1.1))) 0
            (Complex.exp (Lf (e.symm (e q.1.1)).1 z + Lf (q.1.1 : Finset α)
              (pencilShift a q.1.2)))
          = jetSeriesFun (boxSeq (C (e q.1.1))) 0
            (Complex.exp (Lf (q.1.1 : Finset α) (z + pencilShift a q.1.2)))
        rw [Equiv.symm_apply_apply, map_add]
      rw [hfam] at hC
      exact differentialIndependent_of_jointlyDirHypertranscendental w _ _ hC
  obtain ⟨C, hC⟩ := main
  refine ⟨pencilFacetMember Lf e C, analyticOnNhd_pencilFacetMember Lf e C, ?_, ?_⟩
  · intro A v hv z
    exact pencilFacetMember_add_of_notMem Lf e C a A (houtside A.1 A.2 v hv) z
  · exact hC

set_option maxHeartbeats 1000000 in
/-- **The differential matroid of a periodic-pencil realization is the localized Stanley--Reisner
matroid, with the Stanley--Reisner rank.**  The whole differential-family matroid of the operator
outputs on a periodic-pencil orbit is the Stanley--Reisner quotient-class matroid, so every
dependence relation and every rank is the Stanley--Reisner one; numerically, the rank of a finite
selection is the dimension over the fraction field of the operator ring of the span of its localized
Laurent coefficient rows. -/
theorem exists_pencilSource_stanleyReisnerLaurentDifferentialFamilyMatroid_eq
    (facets : Finset (Finset α))
    (Lf : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) (a : α → (Fin d → ℂ)) (w : Fin d → ℂ)
    (hw : ∀ A ∈ facets, Lf A w ≠ 0)
    (houtside : ∀ A ∈ facets, ∀ v ∉ A, Complex.exp (Lf A (a v)) = 1)
    (hinside : ∀ A ∈ facets, ∀ g : α → ℤ,
      Complex.exp (∑ v ∈ A, (g v : ℂ) * Lf A (a v)) = 1 → ∀ v ∈ A, g v = 0)
    (dd : translationSubmonoid (Polynomial ℂ) α)
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸ stanleyReisnerIdeal (Polynomial ℂ) facets) :
    ∃ (Y : facets → (Fin d → ℂ) → ℂ) (hY : ∀ A, AnalyticOnNhd ℂ (Y A) Set.univ),
      (∀ (A : facets) (v : α), v ∉ A.1 → ∀ z, Y A (z + a v) = Y A z) ∧
      letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
        isPreconnected_univ_gen Set.univ_nonempty
      haveI := meroFieldGenDirDifferentialAlgebra w
      (differentialFamilyMatroid (F := ℂ)
          (differentialOperatorRowApply
            (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows dd facets N))
            (fun q => algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
              (meroFieldGen (Set.univ : Set (Fin d → ℂ)))
              (entireGermGen (fun z => Y q.1.1 (z + pencilShift a q.1.2))
                (analyticOnNhd_comp_add_const _ (hY q.1.1) _))))
        = stanleyReisnerLaurentMatroid dd facets N ∧
      ∀ I : Finset ι,
        (differentialFamilyMatroid (F := ℂ)
          (differentialOperatorRowApply
            (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows dd facets N))
            (fun q => algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
              (meroFieldGen (Set.univ : Set (Fin d → ℂ)))
              (entireGermGen (fun z => Y q.1.1 (z + pencilShift a q.1.2))
                (analyticOnNhd_comp_add_const _ (hY q.1.1) _))))).eRk (↑I : Set ι)
          = (Module.finrank (FractionRing (Polynomial ℂ))
              (Submodule.span (FractionRing (Polynomial ℂ))
                ((fun i => localizeOperatorRow
                  (finiteFinsuppOperatorRows
                    (stanleyReisnerLaurentRows dd facets N) i)) '' (↑I : Set ι))) : ℕ∞)) := by
  classical
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ)) isPreconnected_univ_gen
    Set.univ_nonempty
  haveI := meroFieldGenDirDifferentialAlgebra w
  obtain ⟨Y, hY, hper, hind⟩ := exists_pencilSource_differentialIndependent
    facets Lf a w hw houtside hinside dd N
  refine ⟨Y, hY, hper, ?_, ?_⟩
  · exact differentialFamilyMatroid_stanleyReisnerLaurentRows_eq
      (meroFieldGenDir_deriv_complexConstant w) dd facets N _ hind
  · intro I
    exact differentialOperatorRows_stanleyReisnerLaurent_eRk_eq_finrank_span
      (meroFieldGenDir_deriv_complexConstant w) dd facets N _ hind I

end

end GaloisForLFunctions.HTGeometry
