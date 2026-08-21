import GaloisForLFunctions.HTGeometry.AffineGroupSchemeCoLie
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# The co-Lie module of a product of affine group schemes

For affine commutative group schemes `Spec A` and `Spec B` over `R`, the product is
`Spec (A ⊗[R] B)`, and its co-Lie module splits:

`ω_{A ⊗ B} ≅ ω_A × ω_B`.

The two projections come from the bialgebra morphisms `a ⊗ b ↦ ε(b) a` and `a ⊗ b ↦ ε(a) b`, the
two inclusions from `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`.  That they are mutually inverse is the Leibniz
rule `d(a ⊗ b) = ε(a) • d(1 ⊗ b) + ε(b) • d(a ⊗ 1)` applied to the factorisation
`a ⊗ b = (a ⊗ 1) * (1 ⊗ b)`.
-/

namespace GaloisForLFunctions.HTGeometry.AffineGroupScheme

open Coalgebra Bialgebra Ideal
open scoped TensorProduct

section Ext

variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

/-- Two `R`-linear maps out of the co-Lie module agree as soon as they agree on all `d a`. -/
theorem coLie_hom_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : coLie R A →ₗ[R] M} (h : ∀ a : A, f (d R A a) = g (d R A a)) : f = g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := d_surjective x
  exact h a

end Ext

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

/-! ### The four structural bialgebra morphisms -/

/-- The inclusion of the first factor, `a ↦ a ⊗ 1`. -/
noncomputable def inclLeft : A →ₐc[R] A ⊗[R] B :=
  (BialgHom.lTensor A (unitBialgHom R B)).comp
    (Bialgebra.TensorProduct.rid R R A).symm.toBialgHom

/-- The inclusion of the second factor, `b ↦ 1 ⊗ b`. -/
noncomputable def inclRight : B →ₐc[R] A ⊗[R] B :=
  (BialgHom.rTensor B (unitBialgHom R A)).comp
    (Bialgebra.TensorProduct.lid R B).symm.toBialgHom

/-- The projection onto the first factor, `a ⊗ b ↦ ε(b) a`. -/
noncomputable def projLeft : A ⊗[R] B →ₐc[R] A :=
  (Bialgebra.TensorProduct.rid R R A).toBialgHom.comp (BialgHom.lTensor A (counitBialgHom R B))

/-- The projection onto the second factor, `a ⊗ b ↦ ε(a) b`. -/
noncomputable def projRight : A ⊗[R] B →ₐc[R] B :=
  (Bialgebra.TensorProduct.lid R B).toBialgHom.comp (BialgHom.rTensor B (counitBialgHom R A))

variable {R A B}

@[simp] theorem inclLeft_apply (a : A) : inclLeft R A B a = a ⊗ₜ[R] (1 : B) := by
  show Bialgebra.TensorProduct.map (BialgHom.id R A) (unitBialgHom R B) (a ⊗ₜ[R] (1 : R)) = _
  rw [Bialgebra.TensorProduct.map_tmul]
  simp

@[simp] theorem inclRight_apply (b : B) : inclRight R A B b = (1 : A) ⊗ₜ[R] b := by
  show Bialgebra.TensorProduct.map (unitBialgHom R A) (BialgHom.id R B) ((1 : R) ⊗ₜ[R] b) = _
  rw [Bialgebra.TensorProduct.map_tmul]
  simp

@[simp] theorem projLeft_tmul (a : A) (b : B) :
    projLeft R A B (a ⊗ₜ[R] b) = (counit b : R) • a := by
  show Bialgebra.TensorProduct.rid R R A
      (Bialgebra.TensorProduct.map (BialgHom.id R A) (counitBialgHom R B) (a ⊗ₜ[R] b)) = _
  rw [Bialgebra.TensorProduct.map_tmul]
  simp

@[simp] theorem projRight_tmul (a : A) (b : B) :
    projRight R A B (a ⊗ₜ[R] b) = (counit a : R) • b := by
  show Bialgebra.TensorProduct.lid R B
      (Bialgebra.TensorProduct.map (counitBialgHom R A) (BialgHom.id R B) (a ⊗ₜ[R] b)) = _
  rw [Bialgebra.TensorProduct.map_tmul]
  simp

variable (R A B)

/-! ### The induced maps on co-Lie modules -/

/-- `ω_A → ω_{A ⊗ B}`. -/
noncomputable def coLieInl : coLie R A →ₗ[R] coLie R (A ⊗[R] B) := coLieMap (inclLeft R A B)

/-- `ω_B → ω_{A ⊗ B}`. -/
noncomputable def coLieInr : coLie R B →ₗ[R] coLie R (A ⊗[R] B) := coLieMap (inclRight R A B)

/-- `ω_{A ⊗ B} → ω_A`. -/
noncomputable def coLieFst : coLie R (A ⊗[R] B) →ₗ[R] coLie R A := coLieMap (projLeft R A B)

/-- `ω_{A ⊗ B} → ω_B`. -/
noncomputable def coLieSnd : coLie R (A ⊗[R] B) →ₗ[R] coLie R B := coLieMap (projRight R A B)

variable {R A B}

@[simp] theorem coLieInl_d (a : A) : coLieInl R A B (d R A a) = d R (A ⊗[R] B) (a ⊗ₜ[R] 1) := by
  rw [coLieInl, coLieMap_d, inclLeft_apply]

@[simp] theorem coLieInr_d (b : B) : coLieInr R A B (d R B b) = d R (A ⊗[R] B) (1 ⊗ₜ[R] b) := by
  rw [coLieInr, coLieMap_d, inclRight_apply]

@[simp] theorem coLieFst_d (x : A ⊗[R] B) :
    coLieFst R A B (d R (A ⊗[R] B) x) = d R A (projLeft R A B x) := coLieMap_d _ x

@[simp] theorem coLieSnd_d (x : A ⊗[R] B) :
    coLieSnd R A B (d R (A ⊗[R] B) x) = d R B (projRight R A B x) := coLieMap_d _ x

theorem coLieFst_comp_coLieInl :
    (coLieFst R A B).comp (coLieInl R A B) = LinearMap.id := by
  refine coLie_hom_ext fun a => ?_
  rw [LinearMap.comp_apply, coLieInl_d, coLieFst_d, projLeft_tmul, Bialgebra.counit_one, one_smul,
    LinearMap.id_apply]

theorem coLieSnd_comp_coLieInr :
    (coLieSnd R A B).comp (coLieInr R A B) = LinearMap.id := by
  refine coLie_hom_ext fun b => ?_
  rw [LinearMap.comp_apply, coLieInr_d, coLieSnd_d, projRight_tmul, Bialgebra.counit_one, one_smul,
    LinearMap.id_apply]

theorem coLieSnd_comp_coLieInl :
    (coLieSnd R A B).comp (coLieInl R A B) = 0 := by
  refine coLie_hom_ext fun a => ?_
  rw [LinearMap.comp_apply, coLieInl_d, coLieSnd_d, projRight_tmul, map_smul, d_one, smul_zero,
    LinearMap.zero_apply]

theorem coLieFst_comp_coLieInr :
    (coLieFst R A B).comp (coLieInr R A B) = 0 := by
  refine coLie_hom_ext fun b => ?_
  rw [LinearMap.comp_apply, coLieInr_d, coLieFst_d, projLeft_tmul, map_smul, d_one, smul_zero,
    LinearMap.zero_apply]

theorem tmul_eq_mul (a : A) (b : B) :
    (a ⊗ₜ[R] b : A ⊗[R] B) = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem d_tmul (a : A) (b : B) :
    d R (A ⊗[R] B) (a ⊗ₜ[R] b)
      = (counit a : R) • d R (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b)
        + (counit b : R) • d R (A ⊗[R] B) (a ⊗ₜ[R] (1 : B)) := by
  rw [tmul_eq_mul, d_mul]
  congr 1 <;> · congr 1; simp

/-- The two inclusions and the two projections split the co-Lie module of the product. -/
theorem coLieInl_comp_coLieFst_add_coLieInr_comp_coLieSnd :
    (coLieInl R A B).comp (coLieFst R A B) + (coLieInr R A B).comp (coLieSnd R A B)
      = LinearMap.id := by
  have key : ((coLieInl R A B).comp (coLieFst R A B)
        + (coLieInr R A B).comp (coLieSnd R A B)).comp (d R (A ⊗[R] B))
      = d R (A ⊗[R] B) := by
    refine TensorProduct.ext' fun a b => ?_
    show coLieInl R A B (coLieFst R A B (d R (A ⊗[R] B) (a ⊗ₜ[R] b)))
      + coLieInr R A B (coLieSnd R A B (d R (A ⊗[R] B) (a ⊗ₜ[R] b))) = _
    rw [coLieFst_d, coLieSnd_d, projLeft_tmul, projRight_tmul, map_smul, map_smul, map_smul,
      map_smul, coLieInl_d, coLieInr_d]
    conv_rhs => rw [d_tmul]
    abel
  refine coLie_hom_ext fun x => ?_
  simpa using LinearMap.congr_fun key x

/-- **The co-Lie module of a product of affine group schemes is the product of the co-Lie
modules.** -/
noncomputable def coLieProdEquiv :
    coLie R (A ⊗[R] B) ≃ₗ[R] coLie R A × coLie R B :=
  LinearEquiv.ofLinear ((coLieFst R A B).prod (coLieSnd R A B))
    ((coLieInl R A B).coprod (coLieInr R A B))
    (by
      refine LinearMap.ext fun x => ?_
      have h1 := LinearMap.congr_fun (coLieFst_comp_coLieInl (R := R) (A := A) (B := B)) x.1
      have h2 := LinearMap.congr_fun (coLieSnd_comp_coLieInr (R := R) (A := A) (B := B)) x.2
      have h3 := LinearMap.congr_fun (coLieSnd_comp_coLieInl (R := R) (A := A) (B := B)) x.1
      have h4 := LinearMap.congr_fun (coLieFst_comp_coLieInr (R := R) (A := A) (B := B)) x.2
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h2 h3 h4
      refine Prod.ext ?_ ?_ <;> simp [h1, h2, h3, h4])
    (by
      refine LinearMap.ext fun x => ?_
      have := LinearMap.congr_fun
        (coLieInl_comp_coLieFst_add_coLieInr_comp_coLieSnd (R := R) (A := A) (B := B)) x
      simpa using this)

@[simp] theorem coLieProdEquiv_apply (x : coLie R (A ⊗[R] B)) :
    coLieProdEquiv x = (coLieFst R A B x, coLieSnd R A B x) := rfl

@[simp] theorem coLieProdEquiv_symm_apply (x : coLie R A) (y : coLie R B) :
    (coLieProdEquiv (R := R) (A := A) (B := B)).symm (x, y)
      = coLieInl R A B x + coLieInr R A B y := rfl

end GaloisForLFunctions.HTGeometry.AffineGroupScheme
