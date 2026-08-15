import GaloisForLFunctions.HTGeometry.PencilRowGerm

/-!
# The exact differential matroid of a periodic-pencil realization

Combining the two halves — the coordinate packet of a Stanley--Reisner Laurent family reproduces the
operator applied to the source, and the pencil orbit on that packet is differentially independent —
gives the realization law in its intrinsic form: for a periodic-pencil separation there are entire
facet sources such that the differential matroid of the outputs of any finite family of operators
`∑_r δ^r Q_r` is exactly the Stanley--Reisner quotient-class matroid of those operators, and the
differential rank of a finite selection is the dimension over the fraction field of the operator
ring of the span of its localized Laurent coefficient rows.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Bottcher
open scoped Classical Differential

noncomputable section

variable {d : ℕ} {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

local instance pencilLawComplexDifferential : Differential ℂ := ⟨0⟩

omit [DecidableEq α] [Fintype ι] [DecidableEq ι] in
theorem pencilShift_eq_intTranslation (a : α → (Fin d → ℂ)) (g : α → ℤ) :
    pencilShift a g = intTranslation a g := rfl

set_option maxHeartbeats 4000000 in
/-- **The exact differential matroid of a periodic-pencil realization.**  For facet phases whose
steps outside a facet are periods and whose steps inside a facet are integrally independent modulo
the periods, there are entire facet sources, periodic under every step outside their facet, such
that for every finite family of difference operators with derivation coefficients the differential
matroid of the outputs is the Stanley--Reisner quotient-class matroid, with the corresponding
rank. -/
theorem exists_pencilSource_operatorCarrier_matroid_eq
    (facets : Finset (Finset α))
    (Lf : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) (a : α → (Fin d → ℂ)) (w : Fin d → ℂ)
    (hw : ∀ A ∈ facets, Lf A w ≠ 0)
    (houtside : ∀ A ∈ facets, ∀ v ∉ A, Complex.exp (Lf A (a v)) = 1)
    (hinside : ∀ A ∈ facets, ∀ g : α → ℤ,
      Complex.exp (∑ v ∈ A, (g v : ℂ) * Lf A (a v)) = 1 → ∀ v ∈ A, g v = 0)
    (dd : translationSubmonoid (Polynomial ℂ) α)
    (n : ℕ) (Q : ι → ℕ → MvPolynomial α ℂ) :
    ∃ (Y : facets → (Fin d → ℂ) → ℂ) (hY : ∀ A, AnalyticOnNhd ℂ (Y A) Set.univ),
      (∀ (A : facets) (v : α), v ∉ A.1 → ∀ z, Y A (z + a v) = Y A z) ∧
      letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
        isPreconnected_univ_gen Set.univ_nonempty
      haveI := meroFieldGenDirDifferentialAlgebra w
      (differentialFamilyMatroid (F := ℂ)
          (fun i => entireGerm
            (fun z => opCarrier w a (fun y => ∑ A : facets, Y A y) n (Q i)
              (z - ∑ v, (translationDenominatorExponent dd v : ℤ) • a v))
            (analyticOnNhd_opCarrier_sub w a
              (Finset.analyticOnNhd_fun_sum _ fun A _ => hY A) n (Q i) _))
        = stanleyReisnerLaurentMatroid dd facets
            (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
              (opPoly n (Q j))) ∧
      ∀ I : Finset ι,
        (differentialFamilyMatroid (F := ℂ)
          (fun i => entireGerm
            (fun z => opCarrier w a (fun y => ∑ A : facets, Y A y) n (Q i)
              (z - ∑ v, (translationDenominatorExponent dd v : ℤ) • a v))
            (analyticOnNhd_opCarrier_sub w a
              (Finset.analyticOnNhd_fun_sum _ fun A _ => hY A) n (Q i) _))).eRk (↑I : Set ι)
          = (Module.finrank (FractionRing (Polynomial ℂ))
              (Submodule.span (FractionRing (Polynomial ℂ))
                ((fun i => localizeOperatorRow
                  (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows dd facets
                    (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
                      (opPoly n (Q j)))) i)) '' (↑I : Set ι))) : ℕ∞)) := by
  classical
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
    isPreconnected_univ_gen Set.univ_nonempty
  haveI := meroFieldGenDirDifferentialAlgebra w
  obtain ⟨Y, hY, hper, hmat, hrk⟩ :=
    exists_pencilSource_stanleyReisnerLaurentDifferentialFamilyMatroid_eq
      facets Lf a w hw houtside hinside dd
      (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets) (opPoly n (Q j)))
  have hbridge : differentialOperatorRowApply
      (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows dd facets
        (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
          (opPoly n (Q j)))))
      (fun q => algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
        (meroFieldGen (Set.univ : Set (Fin d → ℂ)))
        (entireGermGen (fun z => Y q.1.1 (z + pencilShift a q.1.2))
          (analyticOnNhd_comp_add_const _ (hY q.1.1) _)))
      = fun i => entireGerm
          (fun z => opCarrier w a (fun y => ∑ A : facets, Y A y) n (Q i)
            (z - ∑ v, (translationDenominatorExponent dd v : ℤ) • a v))
          (analyticOnNhd_opCarrier_sub w a
            (Finset.analyticOnNhd_fun_sum _ fun A _ => hY A) n (Q i) _) := by
    funext i
    exact differentialOperatorRowApply_eq_entireGerm_opCarrier w a Y hY
      (fun A v hv z => hper A v hv z) dd n Q i
  refine ⟨Y, hY, hper, ?_, ?_⟩
  · rw [← hbridge]
    exact hmat
  · intro I
    rw [← hbridge]
    exact hrk I

end

end GaloisForLFunctions.HTGeometry
