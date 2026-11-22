import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.IsTensorProduct

/-! Exterior powers commute with extension of scalars. -/

open TensorProduct

noncomputable section

namespace GlobalTheory.SchemeCohomology

variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N]

private def restrictAlternating (n : ℕ) : N [⋀^Fin n]→ₗ[A] ⋀[B]^n N :=
  { (exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars A with
    map_eq_zero_of_eq' := fun v _ _ h hij => (exteriorPower.ιMulti B n).map_eq_zero_of_eq v h hij }

/-- A linear map over the base ring acts on wedges in the extended module. -/
def exteriorMapOver (n : ℕ) (f : M →ₗ[A] N) : ⋀[A]^n M →ₗ[A] ⋀[B]^n N :=
  exteriorPower.alternatingMapLinearEquiv ((restrictAlternating n).compLinearMap f)

@[simp] theorem exteriorMapOver_ιMulti (n : ℕ) (f : M →ₗ[A] N) (v : Fin n → M) :
    exteriorMapOver (B := B) n f (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => f (v i)) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

private def degreeProjection (n : ℕ) : ExteriorAlgebra A M →ₗ[A] ⋀[A]^n M :=
  (DirectSum.component A ℕ (fun i => ⋀[A]^i M) n).comp
    (DirectSum.decomposeLinearEquiv (fun i => ⋀[A]^i M)).toLinearMap

@[simp] private theorem degreeProjection_coe (n : ℕ) (x : ⋀[A]^n M) :
    degreeProjection n (x : ExteriorAlgebra A M) = x := by
  change (DirectSum.decompose (fun i => ⋀[A]^i M) (x : ExteriorAlgebra A M)) n = x
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same]

private theorem exteriorAlgebra_desc {f : M →ₗ[A] N} (hf : IsBaseChange B f) :
    ∃ F : ExteriorAlgebra B N →ₐ[B] B ⊗[A] ExteriorAlgebra A M,
      ∀ m, F (ExteriorAlgebra.ι B (f m)) = 1 ⊗ₜ ExteriorAlgebra.ι A m := by
  let g : N →ₗ[B] B ⊗[A] ExteriorAlgebra A M :=
    hf.lift ((TensorProduct.mk A B _ 1).comp (ExteriorAlgebra.ι A))
  have hg (m : M) : g (f m) = 1 ⊗ₜ ExteriorAlgebra.ι A m := hf.lift_eq _ m
  have anti (y z : N) : g y * g z + g z * g y = 0 := by
    induction y using hf.inductionOn with
    | zero => simp
    | smul s y hy => rw [map_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, hy, smul_zero]
    | add a b ha hb => rw [map_add, add_mul, mul_add, add_add_add_comm, ha, hb, add_zero]
    | tmul m =>
      induction z using hf.inductionOn with
      | zero => simp
      | smul s z hz => rw [map_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, hz, smul_zero]
      | add a b ha hb => rw [map_add, add_mul, mul_add, add_add_add_comm, ha, hb, add_zero]
      | tmul m' =>
        rw [hg, hg, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap, TensorProduct.tmul_zero]
  have sq (y : N) : g y * g y = 0 := by
    induction y using hf.inductionOn with
    | zero => simp
    | smul s y hy => rw [map_smul, smul_mul_assoc, mul_smul_comm, hy, smul_zero, smul_zero]
    | add a b ha hb => rw [map_add, add_mul, mul_add, mul_add, ha, hb, zero_add, add_zero, anti]
    | tmul m =>
      rw [hg, Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_sq_zero, TensorProduct.tmul_zero]
  exact ⟨ExteriorAlgebra.lift B ⟨g, sq⟩, fun m => by rw [ExteriorAlgebra.lift_ι_apply, hg]⟩

/-- The induced map on exterior powers realizes the same extension of scalars. -/
theorem exteriorMapOver_isBaseChange {f : M →ₗ[A] N} (hf : IsBaseChange B f) (n : ℕ) :
    IsBaseChange B (exteriorMapOver (B := B) n f) := by
  obtain ⟨F, hF⟩ := exteriorAlgebra_desc hf
  let G : (⋀[B]^n N) →ₗ[B] B ⊗[A] (⋀[A]^n M) :=
    ((degreeProjection n).baseChange B) ∘ₗ F.toLinearMap ∘ₗ (⋀[B]^n N).subtype
  let H : B ⊗[A] (⋀[A]^n M) →ₗ[B] ⋀[B]^n N := (exteriorMapOver n f).liftBaseChange B
  have hG (x : ⋀[A]^n M) : G (exteriorMapOver n f x) = 1 ⊗ₜ x := by
    have h : (G.restrictScalars A) ∘ₗ (exteriorMapOver n f) = TensorProduct.mk A B _ 1 := by
      apply exteriorPower.linearMap_ext
      ext1 v
      have hι : F (ExteriorAlgebra.ιMulti B n fun i => f (v i)) =
          1 ⊗ₜ ExteriorAlgebra.ιMulti A n v := by
        rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
        have h := map_list_prod (Algebra.TensorProduct.includeRight (R := A) (A := B)
          (B := ExteriorAlgebra A M)) (List.ofFn fun i => ExteriorAlgebra.ι A (v i))
        rw [Algebra.TensorProduct.includeRight_apply, List.map_ofFn] at h
        rw [h]
        congr 2
        exact funext fun i => hF (v i)
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, exteriorMapOver_ιMulti,
        LinearMap.restrictScalars_apply, G, Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe,
        AlgHom.toLinearMap_apply, hι, LinearMap.baseChange_tmul, TensorProduct.mk_apply]
      rw [← exteriorPower.ιMulti_apply_coe, degreeProjection_coe]
    exact LinearMap.congr_fun h x
  have hleft : G ∘ₗ H = LinearMap.id := by
    refine TensorProduct.AlgebraTensorModule.ext fun b x => ?_
    simp [H, hG, TensorProduct.smul_tmul']
  have hspan : Submodule.span B (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    induction y using hf.inductionOn with
    | zero => simp
    | smul s y hy => exact Submodule.smul_mem _ _ hy
    | add a b ha hb => exact add_mem ha hb
    | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
  have hsurj : Function.Surjective H := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span_of_span B n N hspan,
      Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    choose v hv using fun i => hw (Set.mem_range_self i)
    exact ⟨1 ⊗ₜ exteriorPower.ιMulti A n v, by simp [H, hv]⟩
  have hinj : Function.Injective H :=
    Function.LeftInverse.injective (g := G) fun x => LinearMap.congr_fun hleft x
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective H ⟨hinj, hsurj⟩) (by simp [H])

end GlobalTheory.SchemeCohomology
