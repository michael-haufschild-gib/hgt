import GaloisForLFunctions.HTGeometry.SigmaConstantsDomainIndependence
import GaloisForLFunctions.HTGeometry.FixedTensorComponentInjection

/-!
# Fixed tensor independence after component reduction

A family of diagonal-difference fixed tensors that is linearly independent over the constant field
remains independent over any prime-component quotient whose total fraction ring has exactly those
constants.  Independence over the constants survives the chosen quotient because fixed-tensor
vanishing propagates through the transitive family of minimal components.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

universe u

variable {C K R ι : Type u} [Field C] [Field K] [Algebra C K]
  [CommRing R] [Algebra K R] [Algebra C R] [IsScalarTower C K R]

private theorem fixed_pow {A : Type*} [CommRing A] (σ : A ≃+* A)
    {x : A} (hx : σ x = x) (n : ℕ) : (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ']; change σ ((σ ^ n) x) = x; rw [ih, hx]

/-- A basis of a constant subalgebra remains linearly independent after coercion to a tensor
product equipped with its canonical left-factor constant action. -/
theorem linearIndependent_subalgebraBasis_coe_tensorProduct
    (E : Subalgebra C (R ⊗[K] R)) (basis : Module.Basis ι C E) :
    LinearIndependent C (fun i => ((basis i : E) : R ⊗[K] R)) := by
  classical
  have coe_sum (t : Finset ι) (f : ι → E) :
      ((↑(∑ j ∈ t, f j) : E) : R ⊗[K] R) =
        ∑ j ∈ t, ((f j : E) : R ⊗[K] R) := by
    induction t using Finset.induction_on with
    | empty => rfl
    | @insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        change ((f a : E) : R ⊗[K] R) +
            ((↑(∑ j ∈ t, f j) : E) : R ⊗[K] R) = _
        rw [ih]
  rw [linearIndependent_iff']
  intro t g hsum i hi
  apply (linearIndependent_iff'.mp basis.linearIndependent) t g ?_ i hi
  apply Subtype.ext
  calc
    ((↑(∑ j ∈ t, g j • basis j) : E) : R ⊗[K] R) =
        ∑ j ∈ t, ((↑(g j • basis j) : E) : R ⊗[K] R) := by
          exact coe_sum t (fun j => g j • basis j)
    _ = ∑ j ∈ t, g j • ((basis j : E) : R ⊗[K] R) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Algebra.smul_def]
      congr 1
    _ = 0 := hsum
    _ = ((0 : E) : R ⊗[K] R) := rfl

/-- Independence on every left prime component descends to independence over the original reduced
coefficient ring when the component ideals have zero intersection. -/
theorem linearIndependent_of_leftComponentTensorMap
    (S : Finset (Ideal R)) (hSbot : sInf (S : Set (Ideal R)) = ⊥)
    (b : ι → R ⊗[K] R)
    (hcomponent : ∀ P ∈ S,
      LinearIndependent (R ⧸ P)
        (fun i => leftComponentTensorMap (K := K) P (b i))) :
    LinearIndependent R b := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum i hi
  have hmem : ∀ P ∈ S, g i ∈ P := by
    intro P hPS
    let D := R ⧸ P
    let A := D ⊗[K] R
    let bP : ι → A := fun j => leftComponentTensorMap (K := K) P (b j)
    let coeff : ι → D := fun j => Ideal.Quotient.mk P (g j)
    have smul_eq_mul (d : D) (z : A) :
        d • z = algebraMap D A d * z := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [smul_add, mul_add, hx, hy]
      | tmul x y =>
          change (d * x) ⊗ₜ[K] y = (d ⊗ₜ[K] (1 : R)) * (x ⊗ₜ[K] y)
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hcoeffMap (x : R) :
        leftComponentTensorMap (K := K) P
            (algebraMap R (R ⊗[K] R) x) =
          algebraMap D A (Ideal.Quotient.mk P x) := by
      change leftComponentTensorMap (K := K) P (x ⊗ₜ[K] (1 : R)) =
        Ideal.Quotient.mk P x ⊗ₜ[K] (1 : R)
      rw [leftComponentTensorMap_tmul]
    have hrel : ∑ j ∈ t, coeff j • bP j = 0 := by
      have hmapped := congrArg (leftComponentTensorMap (K := K) P) hsum
      rw [Finset.sum_congr rfl (fun j _ => smul_eq_mul (coeff j) (bP j))]
      simpa only [map_sum, Algebra.smul_def, map_mul, map_zero, coeff, bP,
        hcoeffMap] using hmapped
    have hqi := (linearIndependent_iff'.mp (hcomponent P hPS)) t coeff hrel i hi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hqi
  have hgi : g i ∈ sInf (S : Set (Ideal R)) := by
    apply (show Ideal.span {g i} ≤ sInf (S : Set (Ideal R)) from ?_)
      (Ideal.mem_span_singleton_self (g i))
    apply le_sInf
    intro P hPS
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmem P hPS
  exact Ideal.mem_bot.mp (hSbot ▸ hgi)

/-- Fixed constant-independent tensors remain independent over a prime-component quotient once its
total fraction ring has no new constants. -/
theorem linearIndependent_leftComponentTensorMap_of_fraction_fixed
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hconst : ∀ c : C, σR (algebraMap C R c) = algebraMap C R c)
    (S : Finset (Ideal R)) (hSprime : ∀ P ∈ S, P.IsPrime)
    (hSbot : sInf (S : Set (Ideal R)) = ⊥)
    (htrans : ∀ P ∈ S, ∀ Q ∈ S, ∃ n : ℕ,
      Ideal.map ((((σR ^ n) : R ≃+* R)) : R →+* R) P = Q)
    (P : Ideal R) (hPS : P ∈ S) (period : ℕ)
    (hPσ : IsSigmaIdeal (σR ^ period) P)
    (hPσsymm : IsSigmaIdeal (σR ^ period).symm P)
    (hfrac : ∀ x : FractionRing (R ⧸ P),
      fractionRingEquiv
          (sigmaQuotientEquiv (σR ^ period) P hPσ hPσsymm) x = x →
        ∃ c : C, x = algebraMap C (FractionRing (R ⧸ P)) c)
    (b : ι → R ⊗[K] R)
    (hb : ∀ i, differenceTensorEquiv σK σR hcompat (b i) = b i)
    (hCindep : LinearIndependent C b) :
    LinearIndependent (R ⧸ P)
      (fun i => leftComponentTensorMap (K := K) P (b i)) := by
  classical
  letI : P.IsPrime := hSprime P hPS
  let D := R ⧸ P
  let τK : K ≃+* K := σK ^ period
  let τR : R ≃+* R := σR ^ period
  let τD : D ≃+* D := sigmaQuotientEquiv τR P hPσ hPσsymm
  have hτRbase (a : K) :
      τR (algebraMap K R a) = algebraMap K R (τK a) := by
    have hsemiconj : Function.Semiconj (algebraMap K R) σK σR := by
      intro z
      exact (hcompat z).symm
    rw [ringEquiv_pow_apply, ringEquiv_pow_apply]
    exact (hsemiconj.iterate_right period a).symm
  have hτDbase (a : K) :
      τD (algebraMap K D a) = algebraMap K D (τK a) := by
    change τD (Ideal.Quotient.mk P (algebraMap K R a)) = _
    rw [sigmaQuotientEquiv_mk, hτRbase]
    rfl
  let σA : (D ⊗[K] R) ≃+* (D ⊗[K] R) :=
    asymmetricDifferenceTensorEquiv τK τD τR hτDbase hτRbase
  let qPLinear : (R ⊗[K] R) →ₗ[C] (D ⊗[K] R) :=
    (leftComponentTensorMap (K := K) P).toLinearMap.restrictScalars C
  let bP : ι → D ⊗[K] R := fun i => qPLinear (b i)
  have hCindepP : LinearIndependent C bP := by
    rw [linearIndependent_iff']
    intro t g hsum i hi
    let v : R ⊗[K] R := ∑ j ∈ t, g j • b j
    have hvP : leftComponentTensorMap (K := K) P v = 0 := by
      change qPLinear v = 0
      simpa only [v, bP, map_sum, map_smul] using hsum
    have hvfixed : differenceTensorEquiv σK σR hcompat v = v := by
      simp only [v, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Algebra.smul_def, map_mul]
      rw [hb j]
      congr 1
      rw [IsScalarTower.algebraMap_apply C R (R ⊗[K] R)]
      change differenceTensorEquiv σK σR hcompat
          (algebraMap C R (g j) ⊗ₜ[K] (1 : R)) =
        algebraMap C R (g j) ⊗ₜ[K] (1 : R)
      rw [differenceTensorEquiv_tmul, hconst, map_one]
    have hv0 := eq_zero_of_fixed_of_leftComponentTensorMap_eq_zero
      σK σR hcompat S hSprime hSbot htrans P hPS v hvfixed hvP
    exact (linearIndependent_iff'.mp hCindep) t g hv0 i hi
  have hbPfixed : ∀ i, σA (bP i) = bP i := by
    intro i
    have hnat (z : R ⊗[K] R) :
        σA (leftComponentTensorMap (K := K) P z) =
          leftComponentTensorMap (K := K) P
            ((differenceTensorEquiv σK σR hcompat ^ period) z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp [σA]
      | add x y hx hy =>
          rw [map_add, map_add, map_add, hx, hy]
          exact (map_add (leftComponentTensorMap (K := K) P) _ _).symm
      | tmul x y =>
          rw [differenceTensorEquiv_pow_tmul]
          rw [leftComponentTensorMap_tmul]
          change sigmaQuotientEquiv τR P hPσ hPσsymm
              (Ideal.Quotient.mk P x) ⊗ₜ[K] τR y =
            Ideal.Quotient.mk P (τR x) ⊗ₜ[K] τR y
          rw [sigmaQuotientEquiv_mk]
    change σA (leftComponentTensorMap (K := K) P (b i)) =
      leftComponentTensorMap (K := K) P (b i)
    rw [hnat, fixed_pow (differenceTensorEquiv σK σR hcompat) (hb i) period]
  have hσAcompat (d : D) :
      σA (algebraMap D (D ⊗[K] R) d) =
        algebraMap D (D ⊗[K] R) (τD d) := by
    change σA (d ⊗ₜ[K] (1 : R)) = τD d ⊗ₜ[K] (1 : R)
    rw [show σA = asymmetricDifferenceTensorEquiv
        τK τD τR hτDbase hτRbase from rfl,
      asymmetricDifferenceTensorEquiv_tmul, map_one]
  exact linearIndependent_of_fraction_fixed τD σA hσAcompat bP hbPfixed
    hfrac hCindepP

end

end GaloisForLFunctions.HTGeometry
