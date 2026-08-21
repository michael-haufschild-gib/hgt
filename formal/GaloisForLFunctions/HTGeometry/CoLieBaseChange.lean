import GaloisForLFunctions.HTGeometry.AffineGroupSchemeCoLie
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Base change of the co-Lie module

For an affine commutative group scheme `Spec A` over `R` and a base change `R → S`, the group
scheme `Spec (S ⊗[R] A)` over `S` has co-Lie module

`ω_{S ⊗ A} ≅ S ⊗[R] ω_A`.

The map from right to left is `s ⊗ d a ↦ s · d(1 ⊗ a)`, the map from left to right is induced by
`s ⊗ a ↦ s ⊗ d a`, which is well defined on `I/I²` because it satisfies the Leibniz rule
`φ(u v) = ε(u) · φ(v) + ε(v) · φ(u)` for the counit of `S ⊗[R] A`.
-/

namespace GaloisForLFunctions.HTGeometry.AffineGroupScheme

open Coalgebra Bialgebra Ideal
open scoped TensorProduct

variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Bialgebra R A]

/-- The base change of the universal differential at the identity, `s ⊗ a ↦ s ⊗ d a`. -/
noncomputable def baseChangeD : S ⊗[R] A →ₗ[S] S ⊗[R] coLie R A :=
  LinearMap.baseChange S (d R A)

variable {R S A}

@[simp] theorem baseChangeD_tmul (s : S) (a : A) :
    baseChangeD R S A (s ⊗ₜ[R] a) = s ⊗ₜ[R] d R A a :=
  LinearMap.baseChange_tmul _ _ _

theorem counit_baseChange_tmul (s : S) (a : A) :
    (counit (R := S) (s ⊗ₜ[R] a) : S) = (counit a : R) • s := rfl

/-- **Leibniz rule for the base-changed differential.** -/
theorem baseChangeD_mul (u v : S ⊗[R] A) :
    baseChangeD R S A (u * v)
      = (counit u : S) • baseChangeD R S A v + (counit v : S) • baseChangeD R S A u := by
  induction u with
  | zero => simp
  | add u u' hu hu' =>
      simp only [add_mul, map_add, hu, hu', add_smul, smul_add]
      abel
  | tmul s a =>
      induction v with
      | zero => simp
      | add v v' hv hv' =>
          simp only [mul_add, map_add, hv, hv', add_smul, smul_add]
          abel
      | tmul t b =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, baseChangeD_tmul, baseChangeD_tmul,
            baseChangeD_tmul, counit_baseChange_tmul, counit_baseChange_tmul, d_mul,
            TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
            TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul',
            TensorProduct.smul_tmul']
          have h1 : ((counit a : R) • s) • t = (counit a : R) • (s * t) := by
            rw [smul_eq_mul, smul_mul_assoc]
          have h2 : ((counit b : R) • t) • s = (counit b : R) • (s * t) := by
            rw [smul_eq_mul, smul_mul_assoc, mul_comm t s]
          rw [h1, h2]

theorem baseChangeD_algebraMap (s : S) :
    baseChangeD R S A (algebraMap S (S ⊗[R] A) s) = 0 := by
  show baseChangeD R S A (s ⊗ₜ[R] (1 : A)) = 0
  rw [baseChangeD_tmul, d_one, TensorProduct.tmul_zero]

/-- The base-changed differential restricted to the augmentation ideal. -/
noncomputable def augBaseChangeD :
    (augIdeal S (S ⊗[R] A)) →ₗ[S] S ⊗[R] coLie R A :=
  (baseChangeD R S A).comp (((augIdeal S (S ⊗[R] A)).subtype).restrictScalars S)

theorem augBaseChangeD_mul (x y : (augIdeal S (S ⊗[R] A))) :
    augBaseChangeD (R := R) (S := S) (A := A) (x * y) = 0 := by
  show baseChangeD R S A ((x : S ⊗[R] A) * (y : S ⊗[R] A)) = 0
  rw [baseChangeD_mul, mem_augIdeal.mp x.2, mem_augIdeal.mp y.2, zero_smul, zero_smul, add_zero]

/-- `ω_{S ⊗ A} → S ⊗ ω_A`. -/
noncomputable def coLieBaseChangeFwd :
    coLie S (S ⊗[R] A) →ₗ[S] S ⊗[R] coLie R A :=
  Ideal.Cotangent.lift (augBaseChangeD (R := R) (S := S) (A := A)) augBaseChangeD_mul

@[simp] theorem coLieBaseChangeFwd_d (u : S ⊗[R] A) :
    coLieBaseChangeFwd (R := R) (S := S) (A := A) (d S (S ⊗[R] A) u) = baseChangeD R S A u := by
  rw [d_apply, coLieBaseChangeFwd, Ideal.Cotangent.lift_toCotangent]
  show baseChangeD R S A ((toAug S (S ⊗[R] A) u : S ⊗[R] A)) = _
  rw [toAug_coe, map_sub, baseChangeD_algebraMap, sub_zero]

theorem augIdeal_le_comap_includeRight :
    augIdeal R A ≤ (augIdeal S (S ⊗[R] A)).comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom := by
  intro a ha
  rw [Ideal.mem_comap, mem_augIdeal]
  show (counit (R := S) ((1 : S) ⊗ₜ[R] a) : S) = 0
  rw [counit_baseChange_tmul, mem_augIdeal.mp ha, zero_smul]

/-- `ω_A → ω_{S ⊗ A}`, induced by `a ↦ 1 ⊗ a`. -/
noncomputable def coLieToBaseChange : coLie R A →ₗ[R] coLie S (S ⊗[R] A) :=
  Ideal.mapCotangent (augIdeal R A) (augIdeal S (S ⊗[R] A))
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) augIdeal_le_comap_includeRight

@[simp] theorem coLieToBaseChange_d (a : A) :
    coLieToBaseChange (R := R) (S := S) (A := A) (d R A a)
      = d S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) := by
  rw [d_apply, coLieToBaseChange, Ideal.mapCotangent_toCotangent, d_apply]
  congr 1
  apply Subtype.ext
  show (1 : S) ⊗ₜ[R] ((toAug R A a : A)) = ((toAug S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) : S ⊗[R] A))
  rw [toAug_coe, toAug_coe, counit_baseChange_tmul, TensorProduct.tmul_sub]
  congr 1
  show (1 : S) ⊗ₜ[R] (algebraMap R A (counit a : R)) = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

/-- `S ⊗ ω_A → ω_{S ⊗ A}`. -/
noncomputable def coLieBaseChangeBwd :
    S ⊗[R] coLie R A →ₗ[S] coLie S (S ⊗[R] A) :=
  (coLieToBaseChange (R := R) (S := S) (A := A)).liftBaseChange S

@[simp] theorem coLieBaseChangeBwd_tmul (s : S) (a : A) :
    coLieBaseChangeBwd (R := R) (S := S) (A := A) (s ⊗ₜ[R] d R A a)
      = s • d S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) := by
  rw [coLieBaseChangeBwd, LinearMap.liftBaseChange_tmul, coLieToBaseChange_d]

theorem d_baseChange_tmul (s : S) (a : A) :
    d S (S ⊗[R] A) (s ⊗ₜ[R] a) = s • d S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) := by
  have h : (s ⊗ₜ[R] a : S ⊗[R] A) = (algebraMap S (S ⊗[R] A) s) * ((1 : S) ⊗ₜ[R] a) := by
    show _ = (s ⊗ₜ[R] (1 : A)) * ((1 : S) ⊗ₜ[R] a)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, d_mul, d_algebraMap, smul_zero, add_zero]
  congr 1
  show (counit (R := S) (s ⊗ₜ[R] (1 : A)) : S) = s
  rw [counit_baseChange_tmul, Bialgebra.counit_one, one_smul]

theorem coLieBaseChangeBwd_comp_coLieBaseChangeFwd :
    (coLieBaseChangeBwd (R := R) (S := S) (A := A)).comp
        (coLieBaseChangeFwd (R := R) (S := S) (A := A)) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨u, rfl⟩ := d_surjective x
  rw [LinearMap.comp_apply, coLieBaseChangeFwd_d, LinearMap.id_apply]
  induction u with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
  | tmul s a =>
      rw [baseChangeD_tmul, coLieBaseChangeBwd_tmul]
      exact (d_baseChange_tmul s a).symm

theorem coLieBaseChangeFwd_comp_coLieBaseChangeBwd :
    (coLieBaseChangeFwd (R := R) (S := S) (A := A)).comp
        (coLieBaseChangeBwd (R := R) (S := S) (A := A)) = LinearMap.id := by
  refine LinearMap.restrictScalars_injective R ?_
  refine TensorProduct.ext' fun s m => ?_
  obtain ⟨a, rfl⟩ := d_surjective m
  show coLieBaseChangeFwd (coLieBaseChangeBwd (s ⊗ₜ[R] d R A a)) = s ⊗ₜ[R] d R A a
  rw [coLieBaseChangeBwd_tmul, map_smul, coLieBaseChangeFwd_d, baseChangeD_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- **The co-Lie module commutes with base change.** -/
noncomputable def coLieBaseChangeEquiv :
    coLie S (S ⊗[R] A) ≃ₗ[S] S ⊗[R] coLie R A :=
  LinearEquiv.ofLinear (coLieBaseChangeFwd (R := R) (S := S) (A := A))
    (coLieBaseChangeBwd (R := R) (S := S) (A := A))
    coLieBaseChangeFwd_comp_coLieBaseChangeBwd coLieBaseChangeBwd_comp_coLieBaseChangeFwd

end GaloisForLFunctions.HTGeometry.AffineGroupScheme
