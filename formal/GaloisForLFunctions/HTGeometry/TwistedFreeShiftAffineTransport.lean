import GaloisForLFunctions.HTGeometry.TwistedFreeShiftTransport
import GaloisForLFunctions.HTGeometry.TwistedFreeShiftAffineSlice

/-!
# One-slice nonsummability modulo the base, for a base-moving ambient shift

The transported form of the shifted obstruction: a bilateral palette differentially independent over
`F`, moved one slice by an ambient differential automorphism that acts on `F` by a twist, admits no
nonzero finite `F`-linear form in the jets of the zero slice as a coboundary — not even after adding
an element of `F`.

This is the form a hierarchy whose coface equation holds only modulo the base field needs.
-/

open scoped Differential

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

variable {F L α : Type*} [Field F] [Field L] [Algebra F L] [Differential L]

theorem affineSlice_ne_coboundary_of_twisted_ambient_shift
    (x : (α × ℤ) → L) (hx : DifferentialIndependent F x)
    (Ψ : L ≃+* L) (φ : F ≃+* F)
    (hderiv : ∀ y : L, Ψ (y′) = (Ψ y)′)
    (hbase : ∀ b : F, Ψ (algebraMap F L b) = algebraMap F L (φ b))
    (hshift : ∀ p : α × ℤ, Ψ (x p) = x (p.1, p.2 + 1))
    (b : F) (c : (α × ℕ) →₀ F) (hc : c ≠ 0)
    (g : differentialAdjoin F (Set.range x)) :
    Ψ (g : L) - (g : L) ≠
      ((algebraMap F (differentialAdjoin F (Set.range x)) b :
        differentialAdjoin F (Set.range x)) : L) +
      ((c.sum (fun j a =>
        algebraMap F (differentialAdjoin F (Set.range x)) a *
          ⟨differentialJet j.2 (x (j.1, 0)),
            differentialJet_mem_differentialAdjoin F
              (Set.mem_range_self (j.1, 0)) j.2⟩) :
        differentialAdjoin F (Set.range x)) : L) := by
  classical
  intro h
  have hformOne : freeShiftDifferentialAdjoinParametrization x hx
      (algebraMap (FreeShiftPolynomial F α) (FreeShiftField F α) (freeShiftOneSlice c)) =
      c.sum (fun j a => algebraMap F (differentialAdjoin F (Set.range x)) a *
        ⟨differentialJet j.2 (x (j.1, 0)),
          differentialJet_mem_differentialAdjoin F (Set.mem_range_self (j.1, 0)) j.2⟩) := by
    simp only [HTGeometry.freeShiftOneSlice, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hCcj : algebraMap (FreeShiftPolynomial F α) (FreeShiftField F α)
        (MvPolynomial.C (c j)) = algebraMap F (FreeShiftField F α) (c j) := by
      rfl
    have h1 : algebraMap (FreeShiftPolynomial F α) (FreeShiftField F α)
        ((MvPolynomial.C (c j) : FreeShiftPolynomial F α) *
          MvPolynomial.X ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α)) =
        algebraMap F (FreeShiftField F α) (c j) *
          algebraMap (FreeShiftPolynomial F α) (FreeShiftField F α)
            (MvPolynomial.X ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α)) := by
      rw [map_mul, hCcj]
    rw [h1, map_mul, AlgEquiv.commutes, freeShiftDifferentialAdjoinParametrization_X]
  have hform : freeShiftDifferentialAdjoinParametrization x hx
      (algebraMap (FreeShiftPolynomial F α) (FreeShiftField F α)
        (freeShiftAffineSlice b c)) =
      algebraMap F (differentialAdjoin F (Set.range x)) b +
        c.sum (fun j a => algebraMap F (differentialAdjoin F (Set.range x)) a *
          ⟨differentialJet j.2 (x (j.1, 0)),
            differentialJet_mem_differentialAdjoin F (Set.mem_range_self (j.1, 0)) j.2⟩) := by
    rw [freeShiftAffineSlice, map_add, map_add, hformOne]
    congr 1
    have hCb : algebraMap (FreeShiftPolynomial F α) (FreeShiftField F α) (MvPolynomial.C b)
        = algebraMap F (FreeShiftField F α) b := rfl
    rw [hCb, AlgEquiv.commutes]
  refine twistedShiftAffineSlice_ne_coboundary φ b c hc
    ((freeShiftDifferentialAdjoinParametrization x hx).symm g) ?_
  apply (freeShiftDifferentialAdjoinParametrization x hx).injective
  rw [map_sub, AlgEquiv.apply_symm_apply, hform]
  apply Subtype.ext
  rw [AddSubgroupClass.coe_sub, AddMemClass.coe_add,
    twistedShift_parametrization_coe x hx Ψ φ hderiv hbase hshift
      ((freeShiftDifferentialAdjoinParametrization x hx).symm g),
    AlgEquiv.apply_symm_apply]
  exact h

end

end GaloisForLFunctions
