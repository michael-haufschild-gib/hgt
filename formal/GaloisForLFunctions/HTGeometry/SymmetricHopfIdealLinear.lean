import GaloisForLFunctions.HTGeometry.AdditivePolynomialHopfIdeal
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Linear relations in symmetric Hopf ideals

The polynomial presentation of a symmetric algebra transports the actual Mathlib Hopf-ideal
condition to the doubled-variable additive coproduct.  In characteristic zero, every nonzero
Hopf ideal of `Sym(V)` therefore contains a nonzero degree-one generator.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace SymmetricHopfIdealLinear

noncomputable section

variable {ι k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def tensorTransport (b : Module.Basis ι k V) :
    SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V →ₐ[k]
      MvPolynomial (Sum ι ι) k :=
  (MvPolynomial.tensorEquivSum k ι ι k).toAlgHom.comp
    (Algebra.TensorProduct.map
      (SymmetricAlgebra.equivMvPolynomial b).toAlgHom
      (SymmetricAlgebra.equivMvPolynomial b).toAlgHom)

theorem tensorTransport_comul (b : Module.Basis ι k V) :
    (tensorTransport b).comp
        (Bialgebra.comulAlgHom k (SymmetricAlgebra k V)) =
      AdditivePolynomialHopf.addComul.comp
        (SymmetricAlgebra.equivMvPolynomial b).toAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply b.ext
  intro i
  simp [tensorTransport, AdditivePolynomialHopf.addComul,
    SymmetricAlgebra.comul_ι]

theorem tensorTransport_includeLeft (b : Module.Basis ι k V) :
    (tensorTransport b).comp Algebra.TensorProduct.includeLeft =
      AdditivePolynomialHopf.left.comp
        (SymmetricAlgebra.equivMvPolynomial b).toAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply b.ext
  intro i
  simp [tensorTransport, AdditivePolynomialHopf.left]

theorem tensorTransport_includeRight (b : Module.Basis ι k V) :
    (tensorTransport b).comp Algebra.TensorProduct.includeRight =
      AdditivePolynomialHopf.right.comp
        (SymmetricAlgebra.equivMvPolynomial b).toAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply b.ext
  intro i
  simp [tensorTransport, AdditivePolynomialHopf.right]

theorem mappedIdeal_isAdditiveHopfIdeal (b : Module.Basis ι k V)
    (I : Ideal (SymmetricAlgebra k V)) [I.IsHopfIdeal k] :
    AdditivePolynomialHopf.IsAdditiveHopfIdeal
      (Ideal.map (SymmetricAlgebra.equivMvPolynomial b).toRingHom I) := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  let J : Ideal (MvPolynomial ι k) := Ideal.map e.toRingHom I
  constructor
  · intro P hPJ
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hPJ
    obtain ⟨p, hpI, rfl⟩ := hPJ
    have hpker : Coalgebra.comul (R := k) p ∈ RingHom.ker
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I)
          (Ideal.Quotient.mkₐ k I)).toRingHom := by
      change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I)
          (Ideal.Quotient.mkₐ k I) (Coalgebra.comul (R := k) p) = 0
      exact Submodule.IsCoideal.map_mkQ_comul_eq_zero
        (I := I.restrictScalars k) hpI
    change Coalgebra.comul (R := k) p ∈ RingHom.ker
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I)
        (Ideal.Quotient.mkₐ k I)) at hpker
    rw [Algebra.TensorProduct.map_ker
      (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)
      (Ideal.Quotient.mkₐ_surjective k I) (Ideal.Quotient.mkₐ_surjective k I)] at hpker
    have hmap := Ideal.mem_map_of_mem (tensorTransport b).toRingHom hpker
    have hleft : (tensorTransport b).toRingHom.comp
          (Algebra.TensorProduct.includeLeft :
            SymmetricAlgebra k V →ₐ[k]
              SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V).toRingHom =
        AdditivePolynomialHopf.left.toRingHom.comp e.toRingHom := by
      exact congrArg AlgHom.toRingHom (tensorTransport_includeLeft b)
    have hright : (tensorTransport b).toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            SymmetricAlgebra k V →ₐ[k]
              SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V).toRingHom =
        AdditivePolynomialHopf.right.toRingHom.comp e.toRingHom := by
      exact congrArg AlgHom.toRingHom (tensorTransport_includeRight b)
    change AdditivePolynomialHopf.addComul (e p) ∈
      Ideal.map AdditivePolynomialHopf.left.toRingHom J ⊔
        Ideal.map AdditivePolynomialHopf.right.toRingHom J
    have hcomul0 := DFunLike.congr_fun (tensorTransport_comul b) p
    change tensorTransport b (Coalgebra.comul (R := k) p) =
      AdditivePolynomialHopf.addComul
        (SymmetricAlgebra.equivMvPolynomial b p) at hcomul0
    have hcomul : tensorTransport b (Coalgebra.comul (R := k) p) =
        AdditivePolynomialHopf.addComul (e p) := by exact hcomul0
    rw [← hcomul]
    rw [Ideal.map_sup] at hmap
    change tensorTransport b (Coalgebra.comul (R := k) p) ∈
      Ideal.map (tensorTransport b).toRingHom
          (Ideal.map
            (Algebra.TensorProduct.includeLeft :
              SymmetricAlgebra k V →ₐ[k]
                SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V).toRingHom
            (RingHom.ker (Ideal.Quotient.mkₐ k I))) ⊔
        Ideal.map (tensorTransport b).toRingHom
          (Ideal.map
            (Algebra.TensorProduct.includeRight :
              SymmetricAlgebra k V →ₐ[k]
                SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V).toRingHom
            (RingHom.ker (Ideal.Quotient.mkₐ k I))) at hmap
    rw [Ideal.map_map
        (Algebra.TensorProduct.includeLeft :
          SymmetricAlgebra k V →ₐ[k]
            SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V).toRingHom
      (tensorTransport b).toRingHom,
      Ideal.map_map
        (Algebra.TensorProduct.includeRight :
          SymmetricAlgebra k V →ₐ[k]
            SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V).toRingHom
        (tensorTransport b).toRingHom] at hmap
    rw [← RingHom.ker_coe_toRingHom (Ideal.Quotient.mkₐ k I),
      Ideal.Quotient.mkₐ_ker, hleft, hright] at hmap
    simpa only [J, Ideal.map_map] using hmap
  · intro P hPJ
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hPJ
    obtain ⟨p, hpI, rfl⟩ := hPJ
    have hc := Submodule.IsCoideal.counit_eq_zero
      (I := I.restrictScalars k) hpI
    change MvPolynomial.constantCoeff (e p) = 0
    have haug : (MvPolynomial.aeval fun _ : ι => (0 : k)).comp e.toAlgHom =
        Bialgebra.counitAlgHom k (SymmetricAlgebra k V) := by
      apply SymmetricAlgebra.algHom_ext
      apply b.ext
      intro i
      simp [e, SymmetricAlgebra.algebraMapInv_ι]
    have hpaug := DFunLike.congr_fun haug p
    simpa using hpaug.trans hc

/-- Every nonzero Hopf ideal of a characteristic-zero symmetric Hopf algebra contains a
nonzero degree-one generator. -/
theorem nonzero_exists_nonzero_generator [CharZero k]
    (b : Module.Basis ι k V) (I : Ideal (SymmetricAlgebra k V))
    [I.IsHopfIdeal k] (hI : I ≠ ⊥) :
    ∃ v : V, v ≠ 0 ∧ SymmetricAlgebra.ι k V v ∈ I := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  let J : Ideal (MvPolynomial ι k) := Ideal.map e.toRingHom I
  have hJ : J ≠ ⊥ := by
    intro hJbot
    apply hI
    ext p
    constructor
    · intro hpI
      have hepJ : e p ∈ J := Ideal.mem_map_of_mem e.toRingHom hpI
      rw [hJbot, Ideal.mem_bot] at hepJ
      exact e.injective (hepJ.trans (map_zero e).symm)
    · rintro rfl
      exact I.zero_mem
  obtain ⟨P, hPJ, hP0, hdegree⟩ :=
    AdditivePolynomialHopf.nonzero_exists_degree_one
      (mappedIdeal_isAdditiveHopfIdeal b I) hJ
  have hscale : SymmetricPrimitive.mvScale (2 : k) P = 2 * P := by
    apply MvPolynomial.ext
    intro s
    rw [SymmetricPrimitive.coeff_mvScale]
    rw [show (2 : MvPolynomial ι k) = MvPolynomial.C (2 : k) by
      exact (map_ofNat MvPolynomial.C 2).symm]
    rw [MvPolynomial.coeff_C_mul]
    by_cases hc : MvPolynomial.coeff s P = 0
    · simp [hc]
    · have hs : s ∈ P.support := MvPolynomial.mem_support_iff.mpr hc
      rw [hdegree hs]
      simp [mul_comm]
  obtain ⟨j, hj⟩ := SymmetricPrimitive.eq_finite_linear_sum_of_scale_two hscale
  let v : V := ∑ s : ↥P.support, MvPolynomial.coeff s.1 P • b (j s)
  have hPv : P = e (SymmetricAlgebra.ι k V v) := by
    change P = SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι k V v)
    rw [hj]
    simp [v, Algebra.smul_def]
  have hv0 : v ≠ 0 := by
    intro hv
    apply hP0
    calc
      P = e (SymmetricAlgebra.ι k V v) := hPv
      _ = e (SymmetricAlgebra.ι k V 0) := by rw [hv]
      _ = 0 := by simp
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hPJ
  obtain ⟨p, hpI, hep⟩ := hPJ
  have hpv : p = SymmetricAlgebra.ι k V v := by
    apply e.injective
    calc
      e p = P := hep
      _ = e (SymmetricAlgebra.ι k V v) := hPv
  exact ⟨v, hv0, hpv ▸ hpI⟩

end
end SymmetricHopfIdealLinear
end GaloisForLFunctions.HTGeometry
