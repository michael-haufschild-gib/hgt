import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Bases of the absolute differentials of localized smooth charts. -/

noncomputable section

open KaehlerDifferential TensorProduct
open scoped nonZeroDivisors

namespace GlobalTheory.PD

/-- The differentials of the coordinate polynomials give a basis after
any formally étale extension of a polynomial chart. -/
theorem exists_kaehler_basis_of_polynomial_chart
    {k A C : Type*} [CommRing k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] [Algebra A C] [IsScalarTower k A C] [Algebra.FormallyEtale A C]
    {d : ℕ} (e : MvPolynomial (Fin d) k ≃ₐ[k] A) :
    ∃ b : Module.Basis (Fin d) C Ω[C⁄k], ∀ j,
      b j = D k C (algebraMap A C (e (MvPolynomial.X j))) := by
  let P := MvPolynomial (Fin d) k
  letI : Algebra P A := e.toRingHom.toAlgebra
  letI : IsScalarTower k P A := .of_algebraMap_eq fun r => (e.commutes r).symm
  let eP : P ≃ₐ[P] A := { e with commutes' := fun _ => rfl }
  letI : Algebra.FormallyEtale P A := .of_equiv eP
  letI : Algebra P C := ((algebraMap A C).comp e.toRingHom).toAlgebra
  letI : IsScalarTower P A C := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k P C := .of_algebraMap_eq fun r => by
    change algebraMap k C r = algebraMap A C (e (algebraMap k P r))
    rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply k A C]
  letI : Algebra.FormallyEtale P C := Algebra.FormallyEtale.comp P A C
  let b := KaehlerDifferential.mvPolynomialBasis k (Fin d)
  let φ := tensorKaehlerEquivOfFormallyEtale k P C
  refine ⟨(b.baseChange C).map φ, fun j => ?_⟩
  have hD : b j = D k P (MvPolynomial.X j) := b.repr.injective (by
    rw [Module.Basis.repr_self]
    exact (KaehlerDifferential.mvPolynomialBasis_repr_D_X k (Fin d) j).symm)
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hD]
  apply φ.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = φ.symm (D k C (algebraMap P C (MvPolynomial.X j)))
  rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

variable {k B C E : Type*} [Field k] [CommRing B] [CommRing C] [Field E]
  [Algebra k B] [Algebra k C] [Algebra k E] [Algebra B C] [Algebra C E]
  [IsScalarTower k B C] [IsScalarTower k C E]
  [Algebra.Smooth k B] [Algebra.FormallyEtale B C] [IsDomain C]
  [IsLocalRing C] [IsFractionRing C E]

include B in
/-- Over a local chart ring, smooth differentials have a
basis indexed by any basis of their generic fibre of the same size. -/
theorem nonempty_kaehler_basis_of_fraction_basis {d : ℕ}
    (b : Module.Basis (Fin d) E Ω[E⁄k]) : Nonempty (Module.Basis (Fin d) C Ω[C⁄k]) := by
  letI : Algebra.FormallySmooth k C := Algebra.FormallySmooth.comp k B C
  let e := tensorKaehlerEquivOfFormallyEtale k B C
  letI : Module.Finite C Ω[C⁄k] := Module.Finite.equiv e
  letI : Module.Free C Ω[C⁄k] := Module.free_of_flat_of_isLocalRing
  letI : Algebra.FormallyEtale C E := .of_isLocalization C⁰
  let g := tensorKaehlerEquivOfFormallyEtale k C E
  have hr : Module.finrank C Ω[C⁄k] = d := by
    calc
      _ = Module.finrank E (E ⊗[C] Ω[C⁄k]) := (Module.finrank_baseChange (R := E)).symm
      _ = Module.finrank E Ω[E⁄k] := g.finrank_eq
      _ = d := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin d)
  exact ⟨Module.finBasisOfFinrankEq C Ω[C⁄k] hr⟩

end GlobalTheory.PD
