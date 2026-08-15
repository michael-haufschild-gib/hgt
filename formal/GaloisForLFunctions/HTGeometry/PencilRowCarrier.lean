import GaloisForLFunctions.HTGeometry.PencilOperatorCarrier
import GaloisForLFunctions.HTGeometry.StanleyReisnerLaurentRowSupport

/-!
# A Stanley--Reisner Laurent row acts as its difference operator on a pencil orbit

The finite coordinate packet of a Stanley--Reisner Laurent family indexes translates of the facet
sources, and the row entry at one coordinate is the coefficient of the corresponding translation in
the facet restriction of the operator.  Summing a row against those translates therefore reproduces
the operator applied to the sum of the facet sources, shifted by the common denominator: the part of
the denominator exponent outside a facet acts trivially on that facet's source.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open scoped Classical

noncomputable section

variable {α : Type} [Fintype α] [DecidableEq α] {E : Type*} [AddCommGroup E]

/-! ### Integral translations -/

/-- The translation attached to an integral exponent vector. -/
def intTranslation (ω : α → E) (g : α → ℤ) : E := ∑ v, g v • ω v

omit [DecidableEq α] in
theorem translationAddHom_eq_sum (ω : α → E) (e : α →₀ ℕ) :
    translationAddHom ω e = ∑ v, e v • ω v := by
  rw [translationAddHom, Finsupp.liftAddHom_apply, Finsupp.sum]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans ?_
  · intro v _ hv
    rw [Finsupp.notMem_support_iff.mp hv]
    simp
  · exact Finset.sum_congr rfl fun v _ => rfl

/-- **The translation of a Laurent-shifted exponent.** -/
theorem intTranslation_facetLaurentExponentShift (ω : α → E)
    (dd : translationSubmonoid (Polynomial ℂ) α) (A : Finset α) (e : α →₀ ℕ) :
    intTranslation ω (facetLaurentExponentShift dd A e)
      = translationAddHom ω e
        - ∑ v ∈ A, (translationDenominatorExponent dd v : ℤ) • ω v := by
  have hA : ∑ v, ((if v ∈ A then translationDenominatorExponent dd v else 0 : ℕ) : ℤ) • ω v
      = ∑ v ∈ A, (translationDenominatorExponent dd v : ℤ) • ω v := by
    rw [Finset.sum_congr rfl (g := fun v =>
      if v ∈ A then (translationDenominatorExponent dd v : ℤ) • ω v else 0)
      (fun v _ => by split <;> simp), ← Finset.sum_filter]
    congr 1
    ext v
    simp
  rw [intTranslation, translationAddHom_eq_sum, ← hA, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [facetLaurentExponentShift, sub_zsmul, natCast_zsmul, sub_eq_add_neg]

/-! ### Periods absorb the denominator outside a facet -/

omit [Fintype α] [DecidableEq α] in
theorem periodic_zsmul {ω : α → E} {G : E → ℂ} {v : α} (hG : ∀ z, G (z + ω v) = G z) :
    ∀ (k : ℤ) (z : E), G (z + k • ω v) = G z := by
  intro k
  induction k using Int.induction_on with
  | zero => intro z; simp
  | succ k ih =>
      intro z
      rw [show ((k : ℤ) + 1) • ω v = (k : ℤ) • ω v + ω v by rw [add_zsmul, one_zsmul],
        ← add_assoc, hG (z + (k : ℤ) • ω v), ih z]
  | pred k ih =>
      intro z
      rw [show (-(k : ℤ) - 1) • ω v = (-(k : ℤ)) • ω v - ω v by
          rw [sub_zsmul, one_zsmul, sub_eq_add_neg],
        ← hG (z + ((-(k : ℤ)) • ω v - ω v)),
        show z + ((-(k : ℤ)) • ω v - ω v) + ω v = z + (-(k : ℤ)) • ω v by abel]
      exact ih z

omit [Fintype α] in
theorem periodic_finset_sum {ω : α → E} {G : E → ℂ} {A : Finset α}
    (hG : ∀ v ∉ A, ∀ z, G (z + ω v) = G z) (c : α → ℤ) :
    ∀ (s : Finset α), (∀ v ∈ s, v ∉ A) → ∀ z, G (z + ∑ v ∈ s, c v • ω v) = G z := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ z; simp
  | insert a s ha ih =>
      intro hs z
      rw [Finset.sum_insert ha, ← add_assoc,
        ih (fun v hv => hs v (Finset.mem_insert_of_mem hv)) (z + c a • ω a)]
      exact periodic_zsmul (hG a (hs a (Finset.mem_insert_self a s))) (c a) z

/-- **The denominator exponent outside a facet acts trivially on that facet's source.** -/
theorem sub_facet_denominator_eq {ω : α → E} {G : E → ℂ} {A : Finset α}
    (hG : ∀ v ∉ A, ∀ z, G (z + ω v) = G z) (c : α → ℤ) (z : E) :
    G (z - ∑ v ∈ A, c v • ω v) = G (z - ∑ v, c v • ω v) := by
  have hsplit : ∑ v, c v • ω v = ∑ v ∈ A, c v • ω v + ∑ v ∈ Aᶜ, c v • ω v :=
    (Finset.sum_add_sum_compl A _).symm
  rw [hsplit, show z - (∑ v ∈ A, c v • ω v + ∑ v ∈ Aᶜ, c v • ω v)
      = (z - ∑ v ∈ A, c v • ω v) - ∑ v ∈ Aᶜ, c v • ω v by abel,
    ← periodic_finset_sum hG c Aᶜ (fun v hv => Finset.mem_compl.mp hv)
      ((z - ∑ v ∈ A, c v • ω v) - ∑ v ∈ Aᶜ, c v • ω v)]
  congr 1
  abel

/-! ### One facet: the row is the difference operator of the facet restriction -/

set_option maxHeartbeats 2000000 in
/-- **The Laurent row of one facet acts as the difference operator of the facet restriction.** -/
theorem facetRowSum_eq_seedCarrier (ω : α → E) {A : Finset α} (G : ℕ → E → ℂ)
    (hG : ∀ r, ∀ v ∉ A, ∀ z, G r (z + ω v) = G r z)
    (dd : translationSubmonoid (Polynomial ℂ) α)
    (n : ℕ) (Q : ℕ → MvPolynomial α ℂ) (z : E) :
    ∑ g ∈ (facetLaurentShift dd A (differenceToTranslationHom (opPoly n Q))).support,
        ∑ r ∈ Finset.range n,
          Polynomial.coeff
            (facetLaurentShift dd A (differenceToTranslationHom (opPoly n Q)) g) r
            * G r (z + intTranslation ω g)
      = ∑ r ∈ Finset.range n,
          seedCarrierPoly ω (G r) (Q r)
            (z - ∑ v, (translationDenominatorExponent dd v : ℤ) • ω v) := by
  classical
  have hinj : Function.Injective (facetLaurentExponentShift dd A) :=
    facetLaurentExponentShift_injective dd A
  have hval : ∀ e : α →₀ ℕ,
      facetLaurentShift dd A (differenceToTranslationHom (opPoly n Q))
          (facetLaurentExponentShift dd A e)
        = MvPolynomial.coeff e (differenceToTranslationHom (opPoly n Q)) :=
    fun e => Finsupp.mapDomain_apply hinj
      (AddMonoidAlgebra.coeff (differenceToTranslationHom (opPoly n Q))) e
  have hsupp : (facetLaurentShift dd A (differenceToTranslationHom (opPoly n Q))).support
      = Finset.image (facetLaurentExponentShift dd A)
        (differenceToTranslationHom (opPoly n Q)).support :=
    Finsupp.mapDomain_support_of_injective hinj
      (AddMonoidAlgebra.coeff (differenceToTranslationHom (opPoly n Q)))
  rw [hsupp, Finset.sum_image (fun a _ b _ h => hinj h), Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hsub : (differenceToTranslationHom (Q r)).support
      ⊆ (differenceToTranslationHom (opPoly n Q)).support := by
    intro e he
    rw [MvPolynomial.mem_support_iff] at he ⊢
    intro hzero
    apply he
    have hc := coeff_differenceToTranslationHom_opPoly n Q e r
    rw [hzero, Polynomial.coeff_zero, if_pos hr] at hc
    exact hc.symm
  rw [seedCarrierPoly_apply_translation,
    Finset.sum_subset hsub (fun e _ he => by
      rw [MvPolynomial.notMem_support_iff.mp he, zero_mul])]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [hval e, coeff_differenceToTranslationHom_opPoly n Q e r, if_pos hr,
    intTranslation_facetLaurentExponentShift]
  congr 1
  rw [show z + (translationAddHom ω e
        - ∑ v ∈ A, (translationDenominatorExponent dd v : ℤ) • ω v)
      = (z + translationAddHom ω e)
        - ∑ v ∈ A, (translationDenominatorExponent dd v : ℤ) • ω v from by abel,
    sub_facet_denominator_eq (hG r) (fun v => (translationDenominatorExponent dd v : ℤ))
      (z + translationAddHom ω e)]
  congr 1
  abel

/-! ### The whole coordinate packet reproduces the operator -/

variable {facets : Finset (Finset α)} {ι : Type} [Fintype ι]

set_option maxHeartbeats 2000000 in
/-- **The finite coordinate packet of a Stanley--Reisner Laurent family reproduces the operator.**
Summing each row against the pencil orbit gives the operator applied to the sum of the facet
sources, translated by the common denominator. -/
theorem rowSum_eq_seedCarrier_sum (ω : α → E) (H : ℕ → facets → E → ℂ)
    (hH : ∀ (r : ℕ) (A : facets), ∀ v ∉ A.1, ∀ z, H r A (z + ω v) = H r A z)
    (dd : translationSubmonoid (Polynomial ℂ) α)
    (n : ℕ) (Q : ι → ℕ → MvPolynomial α ℂ) (i : ι) (z : E) :
    ∑ q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows dd facets
        (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
          (opPoly n (Q j)))),
        ∑ r ∈ Finset.range n,
          Polynomial.coeff (stanleyReisnerLaurentRows dd facets
            (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
              (opPoly n (Q j))) i q.1.1 q.1.2) r
            * H r q.1.1 (z + intTranslation ω q.1.2)
      = ∑ r ∈ Finset.range n,
          seedCarrierPoly ω (fun y => ∑ A : facets, H r A y) (Q i r)
            (z - ∑ v, (translationDenominatorExponent dd v : ℤ) • ω v) := by
  classical
  set Rows := stanleyReisnerLaurentRows dd facets
    (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
      (opPoly n (Q j))) with hRowsdef
  set f : facets → (α → ℤ) → ℂ := fun A g => ∑ r ∈ Finset.range n,
    Polynomial.coeff (Rows i A g) r * H r A (z + intTranslation ω g) with hf
  have hrow : ∀ A : facets, Rows i A
      = facetLaurentShift dd A.1 (differenceToTranslationHom
        (opPoly n (fun r => pencilFacetRestrict A.1 (Q i r)))) := by
    intro A
    show facetLaurentShift dd A.1
      (stanleyReisnerFacetTranslationCoordinates facets
        (Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets) (opPoly n (Q i))) A) = _
    rw [stanleyReisnerFacetTranslationCoordinates_mk, pencilFacetRestrict_opPoly]
  set T : Finset (facets × (α → ℤ)) :=
    Finset.univ.biUnion (fun A : facets => (Rows i A).support.image (Prod.mk A)) with hT
  have hTS : T ⊆ finiteFinsuppRowSupport Rows := by
    intro p hp
    rw [hT, Finset.mem_biUnion] at hp
    obtain ⟨A, -, hA⟩ := hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hA
    exact mem_finiteFinsuppRowSupport_of_ne Rows (Finsupp.mem_support_iff.mp hg)
  have hvanish : ∀ p ∈ finiteFinsuppRowSupport Rows, p ∉ T → f p.1 p.2 = 0 := by
    intro p _ hp
    have hnot : p.2 ∉ (Rows i p.1).support := by
      intro hmem
      refine hp ?_
      rw [hT]
      exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨p.2, hmem, rfl⟩⟩
    have hz : Rows i p.1 p.2 = 0 := Finsupp.notMem_support_iff.mp hnot
    rw [hf]
    simp [hz]
  have hdisj : Set.PairwiseDisjoint
      ((Finset.univ : Finset facets) : Set facets)
      (fun A : facets => (Rows i A).support.image (Prod.mk A)) := by
    intro A _ B _ hAB
    refine Finset.disjoint_left.mpr fun p hpA hpB => ?_
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hpA
    obtain ⟨g', -, hg'⟩ := Finset.mem_image.mp hpB
    exact hAB (congrArg Prod.fst hg').symm
  have hstep : ∑ q : FiniteFinsuppRowIndex Rows, f q.1.1 q.1.2
      = ∑ A : facets, ∑ g ∈ (Rows i A).support, f A g := by
    rw [show (∑ q : FiniteFinsuppRowIndex Rows, f q.1.1 q.1.2)
        = ∑ p ∈ finiteFinsuppRowSupport Rows, f p.1 p.2 from
      Finset.sum_coe_sort (finiteFinsuppRowSupport Rows) (fun p => f p.1 p.2),
      ← Finset.sum_subset hTS hvanish, hT, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun A _ => ?_
    exact Finset.sum_image (fun a _ b _ h => (Prod.mk.injEq .. ▸ h : A = A ∧ a = b).2)
  have hfacet : ∀ A : facets, ∑ g ∈ (Rows i A).support, f A g
      = ∑ r ∈ Finset.range n, seedCarrierPoly ω (H r A) (pencilFacetRestrict A.1 (Q i r))
          (z - ∑ v, (translationDenominatorExponent dd v : ℤ) • ω v) := by
    intro A
    have := facetRowSum_eq_seedCarrier ω (A := A.1) (fun r => H r A)
      (fun r v hv y => hH r A v hv y) dd n (fun r => pencilFacetRestrict A.1 (Q i r)) z
    rw [hf]
    simpa only [hrow A] using this
  show ∑ q : FiniteFinsuppRowIndex Rows, f q.1.1 q.1.2 = _
  rw [hstep, Finset.sum_congr rfl (fun A (_ : A ∈ Finset.univ) => hfacet A), Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact (seedCarrierPoly_sum_pencilFacetRestrict ω (fun A => H r A)
    (fun A v hv y => hH r A v hv y) (Q i r) _).symm

end

end GaloisForLFunctions.HTGeometry
