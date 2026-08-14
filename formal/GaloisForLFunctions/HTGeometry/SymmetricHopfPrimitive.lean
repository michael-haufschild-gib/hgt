import GaloisForLFunctions.HTGeometry.AffineExponentialGroupHopf

/-!
# Primitive elements of a symmetric Hopf algebra

Over a characteristic-zero field, every primitive element of `Sym(V)` is a
degree-one generator.  No finite-dimensional hypothesis on `V` is needed.

The proof folds the coproduct along multiplication.  Primitivity then says
that scaling every generator by two scales the element by two.  Transport to
a multivariable polynomial algebra forces every supported monomial to have
total degree one.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace SymmetricPrimitive

noncomputable section

variable {ι k : Type*} [Field k]

noncomputable def mvScale (a : k) : MvPolynomial ι k →ₐ[k] MvPolynomial ι k :=
  MvPolynomial.aeval fun i => MvPolynomial.C a * MvPolynomial.X i

theorem mvScale_monomial (a c : k) (s : ι →₀ ℕ) :
    mvScale a (MvPolynomial.monomial s c) =
      MvPolynomial.monomial s (c * a ^ (s.sum fun _ n => n)) := by
  rw [mvScale, MvPolynomial.aeval_monomial]
  rw [show algebraMap k (MvPolynomial ι k) c = MvPolynomial.C c by rfl]
  rw [show s.prod (fun i n => (MvPolynomial.C a * MvPolynomial.X i) ^ n) =
      MvPolynomial.C (a ^ (s.sum fun _ n => n)) *
        s.prod (fun i n => MvPolynomial.X i ^ n) by
    simp only [Finsupp.prod]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    simp_rw [← MvPolynomial.C_pow]
    rw [← map_prod, Finset.prod_pow_eq_pow_sum]
    rfl]
  rw [MvPolynomial.monomial_eq, map_mul]
  ring

theorem coeff_mvScale (a : k) (P : MvPolynomial ι k) (s : ι →₀ ℕ) :
    MvPolynomial.coeff s (mvScale a P) =
      MvPolynomial.coeff s P * a ^ (s.sum fun _ n => n) := by
  classical
  rw [P.as_sum, map_sum]
  simp_rw [mvScale_monomial]
  rw [MvPolynomial.coeff_sum]
  by_cases h : MvPolynomial.coeff s P = 0 <;> simp [h]

theorem support_degree_eq_one_of_scale_two [CharZero k] {P : MvPolynomial ι k}
    (hP : mvScale (2 : k) P = 2 * P) {s : ι →₀ ℕ} (hs : s ∈ P.support) :
    s.sum (fun _ n => n) = 1 := by
  have hc : MvPolynomial.coeff s P ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have heq := congrArg (MvPolynomial.coeff s) hP
  rw [coeff_mvScale] at heq
  rw [show (2 : MvPolynomial ι k) = MvPolynomial.C (2 : k) by
    exact (map_ofNat MvPolynomial.C 2).symm] at heq
  rw [MvPolynomial.coeff_C_mul] at heq
  have hpow : (2 : k) ^ (s.sum fun _ n => n) = 2 := by
    exact mul_left_cancel₀ hc (heq.trans (mul_comm _ _))
  have hnat : 2 ^ (s.sum fun _ n => n) = 2 ^ 1 := by
    apply Nat.cast_injective (R := k)
    simpa using hpow
  exact Nat.pow_right_injective (by omega : 1 < 2) hnat

theorem eq_finite_linear_sum_of_scale_two [CharZero k] {P : MvPolynomial ι k}
    (hP : mvScale (2 : k) P = 2 * P) :
    ∃ j : (↥P.support) → ι,
      P = ∑ s ∈ (Finset.univ : Finset ↥P.support),
        MvPolynomial.C (MvPolynomial.coeff s.1 P) * MvPolynomial.X (j s) := by
  classical
  have hdeg : ∀ s : ↥P.support, s.1.sum (fun _ n => n) = 1 :=
    fun s => support_degree_eq_one_of_scale_two hP s.2
  let j : (↥P.support) → ι := fun s =>
    Classical.choose ((Finsupp.sum_eq_one_iff s.1).mp (hdeg s))
  have hj : ∀ s : ↥P.support, s.1 = Finsupp.single (j s) 1 := fun s =>
    Classical.choose_spec ((Finsupp.sum_eq_one_iff s.1).mp (hdeg s))
  refine ⟨j, ?_⟩
  calc
    P = ∑ s ∈ P.support, MvPolynomial.monomial s (MvPolynomial.coeff s P) := P.as_sum
    _ = ∑ s ∈ P.support.attach,
        MvPolynomial.monomial s.1 (MvPolynomial.coeff s.1 P) := by
      exact (Finset.sum_attach P.support fun s =>
        MvPolynomial.monomial s (MvPolynomial.coeff s P)).symm
    _ = ∑ s ∈ (Finset.univ : Finset ↥P.support),
        MvPolynomial.C (MvPolynomial.coeff s.1 P) * MvPolynomial.X (j s) := by
      rw [Finset.univ_eq_attach]
      apply Finset.sum_congr rfl
      intro s hs
      rw [hj s]
      simp [MvPolynomial.monomial_eq]

variable (k) (V : Type*) [AddCommGroup V] [Module k V]

noncomputable def symmetricScale (a : k) :
    SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k V :=
  SymmetricAlgebra.lift (a • SymmetricAlgebra.ι k V)

@[simp] theorem symmetricScale_ι (a : k) (v : V) :
    symmetricScale k V a (SymmetricAlgebra.ι k V v) =
      a • SymmetricAlgebra.ι k V v := by
  simp [symmetricScale]

theorem symmetricScale_two_of_primitive (p : SymmetricAlgebra k V)
    (hp : Coalgebra.comul (R := k) p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p) :
    symmetricScale k V 2 p = 2 * p := by
  have hfold : (Algebra.TensorProduct.lmul' k).comp
      (Bialgebra.comulAlgHom k (SymmetricAlgebra k V)) = symmetricScale k V 2 := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro v
    simp [symmetricScale, SymmetricAlgebra.comul_ι, two_smul k]
  rw [← DFunLike.congr_fun hfold p]
  change (Algebra.TensorProduct.lmul' k)
    (Coalgebra.comul (R := k) p) = 2 * p
  rw [hp]
  simp [two_mul]

variable (b : Module.Basis ι k V)

theorem equivMvPolynomial_symmetricScale (a : k) (p : SymmetricAlgebra k V) :
    SymmetricAlgebra.equivMvPolynomial b (symmetricScale k V a p) =
      mvScale a (SymmetricAlgebra.equivMvPolynomial b p) := by
  have hmaps : (SymmetricAlgebra.equivMvPolynomial b).toAlgHom.comp
      (symmetricScale k V a) =
      (mvScale a).comp (SymmetricAlgebra.equivMvPolynomial b).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply b.ext
    intro i
    simp [mvScale, Algebra.smul_def]
  exact DFunLike.congr_fun hmaps p

/-- Primitive elements of `Sym(V)` are exactly its degree-one generators. -/
theorem primitive_eq_generator [CharZero k]
    (b : Module.Basis ι k V) (p : SymmetricAlgebra k V)
    (hp : Coalgebra.comul (R := k) p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p) :
    ∃ v : V, p = SymmetricAlgebra.ι k V v := by
  let P := SymmetricAlgebra.equivMvPolynomial b p
  have hscaleSym := symmetricScale_two_of_primitive k V p hp
  have hscale : mvScale (2 : k) P = 2 * P := by
    have h := congrArg (SymmetricAlgebra.equivMvPolynomial b) hscaleSym
    simpa only [equivMvPolynomial_symmetricScale, map_mul, map_ofNat, P] using h
  obtain ⟨j, hj⟩ := eq_finite_linear_sum_of_scale_two hscale
  let v : V := ∑ s : ↥P.support, MvPolynomial.coeff s.1 P • b (j s)
  refine ⟨v, ?_⟩
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  change P = _
  rw [hj]
  simp [v, Algebra.smul_def]

end
end SymmetricPrimitive
end GaloisForLFunctions.HTGeometry
