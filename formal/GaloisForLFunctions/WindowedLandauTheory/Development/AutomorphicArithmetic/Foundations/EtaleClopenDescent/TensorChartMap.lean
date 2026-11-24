import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeCoordinates

/-! A linear map of rational coefficients commutes with the tensor
scalar action. It acts on regular tensor lattices factor by factor. -/

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

variable {k F V U W : Type*} [Field k] [Field F] [Algebra k F]
  [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V]
  [AddCommGroup U] [Module k U] [Module F U] [IsScalarTower k F U]
  [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower k F W]

/-- Change the left tensor factor by a rational linear map. -/
abbrev tensorMapLeft (f : V →ₗ[F] U) :
    V ⊗[k] W →ₗ[k] U ⊗[k] W :=
  TensorProduct.map (f.restrictScalars k) (LinearMap.id : W →ₗ[k] W)

theorem tensorMapLeft_action (f : V →ₗ[F] U) (a : F ⊗[k] F) (t : V ⊗[k] W) :
    tensorMapLeft f (tensorScalarAction a t) = tensorScalarAction a (tensorMapLeft f t) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul u v =>
      simp only [tensorScalarAction_tmul, tensorMapLeft, TensorProduct.map_tmul,
        LinearMap.restrictScalars_apply, LinearMap.id_apply, map_smul]

theorem tensorMapLeft_mem {P : Submodule k V} {Q : Submodule k U} {L : Submodule k W}
    (f : V →ₗ[F] U) (hf : P ≤ Q.comap (f.restrictScalars k)) :
    tensorChartLattice P L ≤ (tensorChartLattice Q L).comap (tensorMapLeft f) := by
  refine Submodule.map₂_le.mpr fun u hu v hv => ?_
  change tensorMapLeft f (u ⊗ₜ[k] v) ∈ tensorChartLattice Q L
  rw [tensorMapLeft, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply]
  exact Submodule.apply_mem_map₂ _ (hf hu) hv

/-- Contracting after a map of the first factor composes the functional
with that map. -/
theorem tensorContraction_tensorMapLeft (f : V →ₗ[F] U) (φ : U →ₗ[F] F) (t : V ⊗[k] W) :
    tensorContraction φ (tensorMapLeft f t) = tensorContraction (φ.comp f) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul u v =>
    simp only [tensorMapLeft, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.restrictScalars_apply, tensorContraction_tmul, LinearMap.comp_apply]

theorem tensorMapLeft_leftInverse (f : V →ₗ[F] U) (g : U →ₗ[F] V)
    (h : ∀ v, g (f v) = v) :
    Function.LeftInverse (tensorMapLeft (W := W) g) (tensorMapLeft (k := k) (W := W) f) := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v w =>
    simp only [tensorMapLeft, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.restrictScalars_apply, h]

end GlobalTheory.PD
