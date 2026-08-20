import GaloisForLFunctions.HTGeometry.DifferentialRelationSigmaDescent
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialBaseChange

/-!
# Differential relations of an invariant element live over the constants

A polynomial whose coefficients are all `σ`-invariant has coefficients in the field of
`σ`-constants, so the descended relation of a `σ`-invariant element is a relation over the
constants — and a relation over the constants travels along any differential map of algebras over
them.

That is what puts the value of an invariant element at a differential point inside a fixed proper
differential algebraic set: the relation is the same for every point.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

/-- A polynomial all of whose coefficients come from a subring is the image of one over it. -/
theorem exists_preimage_of_coeffs {S C K : Type*} [CommRing C] [CommRing K] (φ : C →+* K)
    (p : MvPolynomial S K) (h : ∀ u, ∃ a : C, φ a = MvPolynomial.coeff u p) :
    ∃ q : MvPolynomial S C, MvPolynomial.map φ q = p := by
  classical
  refine ⟨∑ u ∈ p.support, MvPolynomial.monomial u (h u).choose, ?_⟩
  refine MvPolynomial.ext _ _ fun v => ?_
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_sum]
  by_cases hv : v ∈ p.support
  · rw [Finset.sum_eq_single v]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
      exact (h v).choose_spec
    · intro u _ hu
      rw [MvPolynomial.coeff_monomial, if_neg hu]
    · intro hcon
      exact absurd hv hcon
  · have hzero : ∀ u ∈ p.support,
        MvPolynomial.coeff v (MvPolynomial.monomial u (h u).choose) = 0 := by
      intro u hu
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro hcon
      exact hv (hcon ▸ hu)
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, map_zero]
    exact (MvPolynomial.notMem_support_iff.mp hv).symm

variable {K C A : Type*} [Field K] [Field C] [CommRing A] [Algebra C K] [Algebra K A]
  [Algebra C A] [IsScalarTower C K A] [Differential K] [Differential C] [Differential A]

/-- **A differential relation over the base descends to the constants.**  For a `σ`-invariant
element, a nonzero differential relation with coefficients in the base field can be replaced by one
with coefficients in the field of `σ`-constants. -/
theorem exists_nonzero_constants_relation (σK : K ≃+* K) (σA : A ≃+* A)
    (hcompat : ∀ a : K, σA (algebraMap K A a) = algebraMap K A (σK a))
    (hσδ : ∀ z : A, σA (Differential.deriv z) = Differential.deriv (σA z))
    (hCfix : ∀ a : K, σK a = a → ∃ c : C, algebraMap C K c = a)
    (e : A) (heσ : σA e = e)
    {P : DifferentialPolynomial Unit K} (hP : P ≠ 0)
    (hPe : differentialPolynomialEvalOver (K := K) (fun _ : Unit => e) P = 0) :
    ∃ Q : DifferentialPolynomial Unit C, Q ≠ 0 ∧
      differentialPolynomialEvalOver (K := C) (fun _ : Unit => e) Q = 0 := by
  classical
  obtain ⟨Q', hQ'ne, hQ'fix, hQ'e⟩ :=
    exists_sigmaFixed_relation (ι := Unit) (K := K) (R := A) σK σA hcompat hσδ
      (fun _ : Unit => e) (fun _ => heσ) hP hPe
  obtain ⟨Q, hQ⟩ := exists_preimage_of_coeffs (algebraMap C K) Q'
    (fun u => hCfix _ (hQ'fix u))
  refine ⟨Q, ?_, ?_⟩
  · intro hzero
    rw [hzero, map_zero] at hQ
    exact hQ'ne hQ.symm
  · have hext : differentialCoeffExtend (ι := Unit) (F := C) (L := K) Q = Q' := hQ
    rw [← differentialPolynomialEvalOver_differentialCoeffExtend (F := C) (L := K) (M := A)
      (fun _ : Unit => e) Q, hext]
    exact hQ'e

/-- **A differential relation over the constants is inherited by every differential point.** -/
theorem eval_relation_of_differentialHom
    {C E F : Type*} [CommRing C] [Differential C] [CommRing E] [Differential E] [CommRing F]
    [Differential F] [Algebra C E] [Algebra C F]
    (χ : E →ₐ[C] F) (hχδ : ∀ z : E, χ (Differential.deriv z) = Differential.deriv (χ z))
    (e : E) {Q : DifferentialPolynomial Unit C}
    (hQ : differentialPolynomialEvalOver (K := C) (fun _ : Unit => e) Q = 0) :
    differentialPolynomialEvalOver (K := C) (fun _ : Unit => χ e) Q = 0 := by
  have hmap := map_differentialPolynomialEvalOver (F := C) (L := E) (M := F)
    ((χ : E →ₐ[C] F) : E →+* F) hχδ (fun a => χ.commutes a) (fun _ : Unit => e) Q
  rw [hQ, map_zero] at hmap
  exact hmap.symm

end

end GaloisForLFunctions.HTGeometry
