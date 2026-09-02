import GaloisForLFunctions.HTGeometry.AsymmetricDifferenceTensor
import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedReduced
import GaloisForLFunctions.HTGeometry.SigmaDeltaComponentQuotient

/-!
# Fixed tensors survive minimal-component reduction

For a finite automorphism-transitive family of prime components with zero intersection, a tensor
fixed by the diagonal automorphism cannot vanish after reducing only its left factor unless it was
already zero.  The proof transports vanishing around the component orbit, then expands against a
basis of the right factor and uses scalar-extension independence coefficientwise.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

universe u

variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]

/-- Reduce the left tensor factor modulo one ideal. -/
def leftComponentTensorMap (P : Ideal R) :
    R ⊗[K] R →ₐ[K] (R ⧸ P) ⊗[K] R :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P) (AlgHom.id K R)

@[simp] theorem leftComponentTensorMap_tmul (P : Ideal R) (x y : R) :
    leftComponentTensorMap (K := K) P (x ⊗ₜ[K] y) =
      Ideal.Quotient.mk P x ⊗ₜ[K] y := by
  rw [leftComponentTensorMap, Algebra.TensorProduct.map_tmul]
  rfl

/-- Vanishing after every left prime-component reduction is faithful when those components have
zero intersection. -/
theorem eq_zero_of_forall_leftComponentTensorMap_eq_zero
    (S : Finset (Ideal R)) (hSprime : ∀ P ∈ S, P.IsPrime)
    (hSbot : sInf (S : Set (Ideal R)) = ⊥)
    (e : R ⊗[K] R)
    (he : ∀ P ∈ S, leftComponentTensorMap (K := K) P e = 0) : e = 0 := by
  classical
  let bs := Module.Basis.ofVectorSpace K R
  obtain ⟨t, a, ha⟩ := exists_basis_tmul_repr bs e
  have hcoeff : ∀ i ∈ t, a i = 0 := by
    intro i hi
    have hmemAll : ∀ P ∈ S, a i ∈ P := by
      intro P hPS
      letI : P.IsPrime := hSprime P hPS
      let D := R ⧸ P
      have hli : LinearIndependent D (fun j => (1 : D) ⊗ₜ[K] bs j) := by
        exact Module.Flat.linearIndependent_one_tmul bs.linearIndependent
      have hrel : ∑ j ∈ t, (Ideal.Quotient.mk P (a j) : D) •
          ((1 : D) ⊗ₜ[K] bs j) = 0 := by
        have hzero := he P hPS
        rw [ha, map_sum] at hzero
        rw [Finset.sum_congr rfl (fun j _ => by
          change (((Ideal.Quotient.mk P (a j) : D) • (1 : D)) ⊗ₜ[K] bs j) = _
          rw [smul_eq_mul, mul_one])]
        simpa only [leftComponentTensorMap_tmul] using hzero
      have hqi : (Ideal.Quotient.mk P (a i) : D) = 0 :=
        (linearIndependent_iff'.mp hli) t
          (fun j => (Ideal.Quotient.mk P (a j) : D)) hrel i hi
      exact Ideal.Quotient.eq_zero_iff_mem.mp hqi
    have hai : a i ∈ sInf (S : Set (Ideal R)) := by
      apply (show Ideal.span {a i} ≤ sInf (S : Set (Ideal R)) from ?_)
        (Ideal.mem_span_singleton_self (a i))
      apply le_sInf
      intro P hPS
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hmemAll P hPS
    exact Ideal.mem_bot.mp (hSbot ▸ hai)
  rw [ha]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hcoeff i hi, TensorProduct.zero_tmul]

/-- Powers of the diagonal tensor automorphism act by the corresponding powers on both factors. -/
theorem differenceTensorEquiv_pow_tmul
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (n : ℕ) (x y : R) :
    (differenceTensorEquiv σK σR hcompat ^ n) (x ⊗ₜ[K] y) =
      (σR ^ n) x ⊗ₜ[K] (σR ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show differenceTensorEquiv σK σR hcompat ^ (n + 1) =
          differenceTensorEquiv σK σR hcompat *
            differenceTensorEquiv σK σR hcompat ^ n by rw [pow_succ']]
      rw [show σR ^ (n + 1) = σR * σR ^ n by rw [pow_succ']]
      change differenceTensorEquiv σK σR hcompat
          ((differenceTensorEquiv σK σR hcompat ^ n) (x ⊗ₜ[K] y)) =
        σR ((σR ^ n) x) ⊗ₜ[K] σR ((σR ^ n) y)
      rw [ih, differenceTensorEquiv_tmul]

/-- A diagonal-fixed tensor killed on one component is zero when the automorphism acts transitively
on a finite prime-component family with zero intersection. -/
theorem eq_zero_of_fixed_of_leftComponentTensorMap_eq_zero
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (S : Finset (Ideal R)) (hSprime : ∀ P ∈ S, P.IsPrime)
    (hSbot : sInf (S : Set (Ideal R)) = ⊥)
    (htrans : ∀ P ∈ S, ∀ Q ∈ S, ∃ n : ℕ,
      Ideal.map (((σR ^ n) : R ≃+* R) : R →+* R) P = Q)
    (P : Ideal R) (hPS : P ∈ S) (e : R ⊗[K] R)
    (hefixed : differenceTensorEquiv σK σR hcompat e = e)
    (heP : leftComponentTensorMap (K := K) P e = 0) : e = 0 := by
  classical
  have hcompatPow (n : ℕ) (a : K) :
      (σR ^ n) (algebraMap K R a) = algebraMap K R ((σK ^ n) a) := by
    have hsemiconj : Function.Semiconj (algebraMap K R) σK σR := by
      intro z
      exact (hcompat z).symm
    rw [ringEquiv_pow_apply, ringEquiv_pow_apply]
    exact (hsemiconj.iterate_right n a).symm
  have hfixedPow (n : ℕ) :
      (differenceTensorEquiv σK σR hcompat ^ n) e = e := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ']
        change differenceTensorEquiv σK σR hcompat
            ((differenceTensorEquiv σK σR hcompat ^ n) e) = e
        rw [ih, hefixed]
  apply eq_zero_of_forall_leftComponentTensorMap_eq_zero S hSprime hSbot e
  intro Q hQS
  obtain ⟨n, hPQ⟩ := htrans P hPS Q hQS
  let τK : K ≃+* K := σK ^ n
  let τR : R ≃+* R := σR ^ n
  let fPQ : R ⧸ P →+* R ⧸ Q :=
    Ideal.Quotient.lift P ((Ideal.Quotient.mk Q).comp (τR : R →+* R)) (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hxm := Ideal.mem_map_of_mem (τR : R →+* R) hx
      rwa [show Ideal.map (τR : R →+* R) P = Q from hPQ] at hxm)
  have hfPQ_base (a : K) :
      fPQ (algebraMap K (R ⧸ P) a) = algebraMap K (R ⧸ Q) (τK a) := by
    change Ideal.Quotient.mk Q (τR (algebraMap K R a)) =
      Ideal.Quotient.mk Q (algebraMap K R (τK a))
    rw [show τR (algebraMap K R a) = algebraMap K R (τK a) from hcompatPow n a]
  let fPQsemi : R ⧸ P →ₛₗ[(τK : K →+* K)] R ⧸ Q :=
    { toFun := fPQ
      map_add' := map_add fPQ
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hfPQ_base]
        rfl }
  let τRsemi : R →ₛₗ[(τK : K →+* K)] R :=
    { toFun := τR
      map_add' := map_add τR
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul,
          show τR (algebraMap K R a) = algebraMap K R (τK a) from hcompatPow n a]
        rfl }
  let T : (R ⧸ P) ⊗[K] R →ₛₗ[(τK : K →+* K)] (R ⧸ Q) ⊗[K] R :=
    TensorProduct.map fPQsemi τRsemi
  have hnat (z : R ⊗[K] R) :
      T (leftComponentTensorMap (K := K) P z) =
        leftComponentTensorMap (K := K) Q
          ((differenceTensorEquiv σK σR hcompat ^ n) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp [T]
    | add z w hz hw =>
        rw [map_add, map_add, map_add, hz, hw]
        exact (map_add (leftComponentTensorMap (K := K) Q) _ _).symm
    | tmul x y =>
        simp only [leftComponentTensorMap_tmul, T, TensorProduct.map_tmul,
          fPQsemi, τRsemi, τR]
        rw [differenceTensorEquiv_pow_tmul]
        rfl
  rw [← hfixedPow n, ← hnat, heP, map_zero]

end

end GaloisForLFunctions.HTGeometry
