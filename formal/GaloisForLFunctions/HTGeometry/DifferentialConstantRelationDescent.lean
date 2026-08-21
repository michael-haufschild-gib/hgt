import GaloisForLFunctions.HTGeometry.DifferentialRelationSigmaDescent
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialBaseChange

/-!
# Differential relations of a shift-invariant point live over the constants

A differential relation over the base field satisfied by a `σ`-invariant point can be replaced by
one whose coefficients are `σ`-invariant, and the `σ`-invariants of the base are the constants; so
the relation descends to a relation with constant coefficients.  Evaluating it at a point of the
Galois group — an algebra map over the constants commuting with the derivation — turns it into a
relation satisfied by the coordinates of that point.

* `exists_descend_of_coeff_mem_range` — a polynomial whose coefficients come from a subring is the
  extension of a polynomial over that subring;
* `exists_constantCoeff_relation_of_sigmaFixed` — the descent;
* `differentialPolynomialEvalOver_eq_zero_of_point` — the transport to a point;
* `exists_constantCoeff_relation_eval` — the two assembled.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

section Descend

variable {ι F L : Type*} [CommRing F] [Differential F] [CommRing L] [Differential L]
  [Algebra F L]

omit [Differential F] [Differential L] in
/-- **A polynomial whose coefficients lie in the image of the base descends to the base.** -/
theorem exists_descend_of_coeff_mem_range {P : DifferentialPolynomial ι L}
    (h : ∀ u : (ι × ℕ) →₀ ℕ, ∃ c : F, algebraMap F L c = MvPolynomial.coeff u P) :
    ∃ Q : DifferentialPolynomial ι F,
      differentialCoeffExtend (ι := ι) (F := F) (L := L) Q = P := by
  classical
  refine ⟨∑ u ∈ P.support, MvPolynomial.monomial u (Classical.choose (h u)), ?_⟩
  rw [differentialCoeffExtend, map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) (MvPolynomial.as_sum P).symm
  rw [MvPolynomial.map_monomial, Classical.choose_spec (h u)]

end Descend

section Sigma

variable {ι K R C : Type*} [DecidableEq ι]
  [Field K] [CommRing R] [Algebra K R] [Differential K] [Differential R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R] [Differential C]

/-- **The descent to constant coefficients.**  A nonzero differential relation over the base
satisfied by a `σ`-invariant point can be replaced by a nonzero relation whose coefficients are
`σ`-invariant, hence — when the `σ`-invariants of the base are the constants — by one over the
constants. -/
theorem exists_constantCoeff_relation_of_sigmaFixed
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hσδ : ∀ z : R, σR (Differential.deriv z) = Differential.deriv (σR z))
    (hfix : ∀ a : K, σK a = a → ∃ c : C, algebraMap C K c = a)
    (x : ι → R) (hx : ∀ i, σR (x i) = x i)
    {P : DifferentialPolynomial ι K} (hP : P ≠ 0)
    (hPx : differentialPolynomialEvalOver (K := K) x P = 0) :
    ∃ Q : DifferentialPolynomial ι C, Q ≠ 0 ∧
      differentialPolynomialEvalOver (K := C) x Q = 0 := by
  obtain ⟨P', hP'ne, hP'fix, hP'x⟩ :=
    exists_sigmaFixed_relation (ι := ι) (K := K) (R := R) σK σR hcompat hσδ x hx hP hPx
  obtain ⟨Q, hQ⟩ :=
    exists_descend_of_coeff_mem_range (ι := ι) (F := C) (L := K) (P := P')
      (fun u => hfix _ (hP'fix u))
  refine ⟨Q, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero] at hQ
    exact hP'ne hQ.symm
  · rw [← differentialPolynomialEvalOver_differentialCoeffExtend (ι := ι) (F := C) (L := K)
      (M := R) x Q, hQ]
    exact hP'x

end Sigma

section Point

variable {ι C E : Type*} [Field C] [CommRing E] [Algebra C E] [Differential C] [Differential E]

/-- **A differential point carries a constant-coefficient relation to its coordinates.** -/
theorem differentialPolynomialEvalOver_eq_zero_of_point
    (χ : E →ₐ[C] C) (hχδ : ∀ e : E, χ (Differential.deriv e) = Differential.deriv (χ e))
    (x : ι → E) {Q : DifferentialPolynomial ι C}
    (hQ : differentialPolynomialEvalOver (K := C) x Q = 0) :
    differentialPolynomialEvalOver (K := C) (fun i => χ (x i)) Q = 0 := by
  have h := map_differentialPolynomialEvalOver (ι := ι) (F := C) (L := E) (M := C)
    (χ : E →+* C) hχδ (fun a => χ.commutes a) x Q
  rw [hQ, map_zero] at h
  exact h.symm

end Point

section Assembled

variable {ι K R C : Type*} [DecidableEq ι]
  [Field K] [CommRing R] [Algebra K R] [Differential K] [Differential R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R] [Differential C]

/-- **The descent and the transport, assembled.**  A nonzero differential relation over the base
satisfied by a `σ`-invariant point yields a nonzero relation over the constants satisfied by the
image of the point under every differential point of the ring. -/
theorem exists_constantCoeff_relation_eval
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hσδ : ∀ z : R, σR (Differential.deriv z) = Differential.deriv (σR z))
    (hfix : ∀ a : K, σK a = a → ∃ c : C, algebraMap C K c = a)
    (x : ι → R) (hx : ∀ i, σR (x i) = x i)
    {P : DifferentialPolynomial ι K} (hP : P ≠ 0)
    (hPx : differentialPolynomialEvalOver (K := K) x P = 0)
    (S : Set (R →ₐ[C] C))
    (hδ : ∀ φ ∈ S, ∀ y : R, φ (Differential.deriv y) = Differential.deriv (φ y)) :
    ∃ Q : DifferentialPolynomial ι C, Q ≠ 0 ∧
      ∀ φ ∈ S, differentialPolynomialEvalOver (K := C) (fun i => φ (x i)) Q = 0 := by
  obtain ⟨Q, hQ0, hQx⟩ :=
    exists_constantCoeff_relation_of_sigmaFixed (ι := ι) (K := K) (R := R) (C := C)
      σK σR hcompat hσδ hfix x hx hP hPx
  refine ⟨Q, hQ0, fun φ hφ => ?_⟩
  exact differentialPolynomialEvalOver_eq_zero_of_point (ι := ι) (C := C) (E := R) φ
    (hδ φ hφ) x hQx

end Assembled


end

end GaloisForLFunctions.HTGeometry
