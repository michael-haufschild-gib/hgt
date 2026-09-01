import GaloisForLFunctions.HTGeometry.DifferentialPolynomialBaseChange
import GaloisForLFunctions.HTGeometry.DifferentialPrimeIdealPoint
import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealAvoiding
import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedReduced

/-!
# Marked differential specialization after field scalar extension

A polynomial over a field extension can be expanded against a basis of that field over the
constant field.  If it lies outside the extension of a prime differential ideal, one basis
coefficient lies outside the original ideal.  A marked differential point preserving that
coefficient then preserves the whole scalar-extended polynomial by basis independence.
-/

namespace GaloisForLFunctions.HTGeometry

open TensorProduct Module
open scoped TensorProduct Differential
open GaloisForLFunctions

noncomputable section

attribute [local instance] differentialPolynomialOverDifferential

universe u v

variable {C K : Type u} [Field C] [Field K] [Algebra C K]

/-- Every differential polynomial over a field extension is a finite basis-linear combination
of coefficient-extended differential polynomials over the ground field. -/
theorem scalarExtension_eq_basis_sum {ι : Type v}
    (H : DifferentialPolynomial ι K) :
    let bs := Module.Basis.ofVectorSpace C K
    ∃ (t : Finset (Module.Basis.ofVectorSpaceIndex C K))
        (a : Module.Basis.ofVectorSpaceIndex C K → DifferentialPolynomial ι C),
      H = ∑ i ∈ t, MvPolynomial.C (bs i) *
        MvPolynomial.map (algebraMap C K) (a i) := by
  let bs := Module.Basis.ofVectorSpace C K
  let e := MvPolynomial.scalarRTensorAlgEquiv
    (R := C) (N := K) (σ := ι × ℕ)
  let z : K ⊗[C] DifferentialPolynomial ι C := e.symm H
  obtain ⟨t, a, ha⟩ := exists_basis_tmul_repr bs
    ((Algebra.TensorProduct.comm C K (DifferentialPolynomial ι C)) z)
  refine ⟨t, a, ?_⟩
  have hz : z = ∑ i ∈ t, bs i ⊗ₜ[C] a i := by
    apply (Algebra.TensorProduct.comm C K (DifferentialPolynomial ι C)).injective
    rw [ha, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Algebra.TensorProduct.comm_tmul]
  calc
    H = e z := by simp [z, e]
    _ = e (∑ i ∈ t, bs i ⊗ₜ[C] a i) := by rw [hz]
    _ = ∑ i ∈ t, MvPolynomial.C (bs i) *
        MvPolynomial.map (algebraMap C K) (a i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [e, MvPolynomial.scalarRTensorAlgEquiv,
        AddMonoidAlgebra.scalarTensorEquiv]
      ext d
      simp [MvPolynomial.coeff_map, Algebra.smul_def]
      left
      change (TensorProduct.rid C K)
        (1 ⊗ₜ[C] MvPolynomial.coeff d (a i)) = _
      simp [Algebra.smul_def]

variable [Algebra ℚ C] [Differential C] [Differential K]
  [DifferentialAlgebra C K] [IsDifferentiallyClosed C]

/-- **Marked scalar-extension specialization.**  A polynomial outside the scalar extension of a
prime differential ideal remains nonzero at some ground-field differential point annihilating
the original ideal. -/
theorem exists_point_avoiding_scalarExtended_primeDifferentialIdeal {n : ℕ}
    (I : Ideal (DifferentialPolynomial (Fin n) C))
    (hIprime : I.IsPrime)
    (hIderiv : ∀ P ∈ I, Differential.deriv P ∈ I)
    (H : DifferentialPolynomial (Fin n) K)
    (hH : H ∉ Ideal.map (MvPolynomial.map (algebraMap C K)) I) :
    ∃ y : Fin n → C,
      (∀ P ∈ I, differentialPolynomialEvalOver (K := C) y P = 0) ∧
      differentialPolynomialEvalOver (K := K)
        (fun i => algebraMap C K (y i)) H ≠ 0 := by
  classical
  let bs := Module.Basis.ofVectorSpace C K
  obtain ⟨t, a, hrepr⟩ := scalarExtension_eq_basis_sum (C := C) H
  have hexists : ∃ i ∈ t, a i ∉ I := by
    by_contra h
    push Not at h
    apply hH
    rw [hrepr]
    apply Ideal.sum_mem
    intro i hi
    exact Ideal.mul_mem_left _ _
      (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap C K)) (h i hi))
  obtain ⟨i, hi, hai⟩ := hexists
  obtain ⟨y, hyI, hyai⟩ :=
    exists_point_avoiding_primeDifferentialIdeal I hIprime hIderiv (a i) hai
  refine ⟨y, hyI, ?_⟩
  intro hzero
  have hevalExtend (Q : DifferentialPolynomial (Fin n) C) :
      differentialPolynomialEvalOver (K := K)
          (fun j => algebraMap C K (y j))
          (MvPolynomial.map (algebraMap C K) Q) =
        algebraMap C K (differentialPolynomialEvalOver (K := C) y Q) := by
    change differentialPolynomialEvalOver (K := K)
        (fun j => algebraMap C K (y j))
        (differentialCoeffExtend (F := C) (L := K) Q) = _
    rw [differentialPolynomialEvalOver_differentialCoeffExtend]
    symm
    exact map_differentialPolynomialEvalOver
      (algebraMap C K) (fun c => (DifferentialAlgebra.deriv_algebraMap c).symm)
      (fun _ => rfl) y Q
  have hsum : ∑ j ∈ t,
      differentialPolynomialEvalOver (K := C) y (a j) • bs j = 0 := by
    calc
      _ = differentialPolynomialEvalOver (K := K)
          (fun j => algebraMap C K (y j)) H := by
        rw [hrepr, map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_mul, differentialPolynomialEvalOver_C, hevalExtend]
        simp [Algebra.smul_def, bs, mul_comm]
      _ = 0 := hzero
  have hcoeff := linearIndependent_iff'.mp bs.linearIndependent t
    (fun j => differentialPolynomialEvalOver (K := C) y (a j)) hsum i hi
  exact hyai hcoeff

/-- **Marked scalar-extension specialization for radical differential ideals.**  Primality is not
needed at the source: one coefficient outside the radical ideal survives in a differential prime
above it, and the resulting ground-field point still annihilates the original ideal. -/
theorem exists_point_avoiding_scalarExtended_radicalDifferentialIdeal {n : ℕ}
    (I : Ideal (DifferentialPolynomial (Fin n) C))
    (hIrad : I.IsRadical)
    (hIderiv : ∀ P ∈ I, Differential.deriv P ∈ I)
    (H : DifferentialPolynomial (Fin n) K)
    (hH : H ∉ Ideal.map (MvPolynomial.map (algebraMap C K)) I) :
    ∃ y : Fin n → C,
      (∀ P ∈ I, differentialPolynomialEvalOver (K := C) y P = 0) ∧
      differentialPolynomialEvalOver (K := K)
        (fun i => algebraMap C K (y i)) H ≠ 0 := by
  classical
  obtain ⟨t, a, hrepr⟩ := scalarExtension_eq_basis_sum (C := C) H
  have hexists : ∃ i ∈ t, a i ∉ I := by
    by_contra h
    push Not at h
    apply hH
    rw [hrepr]
    apply Ideal.sum_mem
    intro i hi
    exact Ideal.mul_mem_left _ _
      (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap C K)) (h i hi))
  obtain ⟨i, hi, hai⟩ := hexists
  obtain ⟨P, hPprime, hPderiv, hIP, haiP⟩ :=
    exists_isPrime_avoiding_radicalDifferential hIrad hIderiv hai
  have hHP : H ∉ Ideal.map (MvPolynomial.map (algebraMap C K)) P := by
    intro hHmap
    -- Extracting one basis coefficient from membership is exactly what the direct expansion
    -- argument below supplies; derive the contradiction by evaluating a prime-avoiding point.
    obtain ⟨z, hzP, hzai⟩ :=
      exists_point_avoiding_primeDifferentialIdeal P hPprime hPderiv (a i) haiP
    have hevalMap (Q : DifferentialPolynomial (Fin n) C) :
        differentialPolynomialEvalOver (K := K)
            (fun j => algebraMap C K (z j))
            (MvPolynomial.map (algebraMap C K) Q) =
          algebraMap C K (differentialPolynomialEvalOver (K := C) z Q) := by
      change differentialPolynomialEvalOver (K := K)
          (fun j => algebraMap C K (z j))
          (differentialCoeffExtend (F := C) (L := K) Q) = _
      rw [differentialPolynomialEvalOver_differentialCoeffExtend]
      symm
      exact map_differentialPolynomialEvalOver
        (algebraMap C K) (fun c => (DifferentialAlgebra.deriv_algebraMap c).symm)
        (fun _ => rfl) z Q
    let ev : DifferentialPolynomial (Fin n) K →+* K :=
      (differentialPolynomialEvalOver (K := K)
        (fun j => algebraMap C K (z j))).toRingHom
    have hmaple : Ideal.map (MvPolynomial.map (algebraMap C K)) P ≤ RingHom.ker ev := by
      rw [Ideal.map_le_iff_le_comap]
      intro Q hQP
      change differentialPolynomialEvalOver (K := K)
          (fun j => algebraMap C K (z j))
          (MvPolynomial.map (algebraMap C K) Q) = 0
      rw [hevalMap, hzP Q hQP, map_zero]
    have hzero := hmaple hHmap
    change differentialPolynomialEvalOver (K := K)
        (fun j => algebraMap C K (z j)) H = 0 at hzero
    rw [hrepr, map_sum] at hzero
    have hsum : ∑ j ∈ t,
        differentialPolynomialEvalOver (K := C) z (a j) •
          (Module.Basis.ofVectorSpace C K) j = 0 := by
      simpa [Algebra.smul_def, mul_comm, hevalMap] using hzero
    have hcoeff := linearIndependent_iff'.mp
      (Module.Basis.ofVectorSpace C K).linearIndependent t
      (fun j => differentialPolynomialEvalOver (K := C) z (a j)) hsum i hi
    exact hzai hcoeff
  obtain ⟨y, hyP, hyai⟩ :=
    exists_point_avoiding_scalarExtended_primeDifferentialIdeal
      P hPprime hPderiv H hHP
  exact ⟨y, fun Q hQI => hyP Q (hIP hQI), hyai⟩

end

end GaloisForLFunctions.HTGeometry
