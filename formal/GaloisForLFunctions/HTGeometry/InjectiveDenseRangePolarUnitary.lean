import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Unitary left polar factor of an injective operator with dense range

For a bounded operator `W : E → F` between complex Hilbert spaces put `B = W W*` and let
`|W*| = B^{1/2}` be its positive square root.  Then `‖|W*| x‖ = ‖W* x‖` for every `x`.  If `W` is
injective with dense range, both `|W*|` and `W*` have dense range, so `|W*| x ↦ W* x` extends to a
unitary `F ≃ E`.  Its inverse `V` gives the left polar decomposition `W = |W*| V` with `V`
unitary, and `V` is the unique unitary with this property.
-/

open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The left modulus `|W*| = (W W*)^{1/2}`. -/
def leftModulus (W : E →L[ℂ] F) : F →L[ℂ] F := CFC.sqrt (W ∘L adjoint W)

theorem selfComp_adjoint_nonneg (W : E →L[ℂ] F) : 0 ≤ W ∘L adjoint W :=
  (nonneg_iff_isPositive _).2 (isPositive_self_comp_adjoint W)

theorem leftModulus_nonneg (W : E →L[ℂ] F) : 0 ≤ leftModulus W := CFC.sqrt_nonneg _

theorem isPositive_leftModulus (W : E →L[ℂ] F) : (leftModulus W).IsPositive :=
  (nonneg_iff_isPositive _).1 (leftModulus_nonneg W)

theorem adjoint_leftModulus (W : E →L[ℂ] F) : adjoint (leftModulus W) = leftModulus W :=
  (isPositive_leftModulus W).isSelfAdjoint.adjoint_eq

theorem leftModulus_comp_self (W : E →L[ℂ] F) :
    leftModulus W ∘L leftModulus W = W ∘L adjoint W :=
  CFC.sqrt_mul_sqrt_self _ (selfComp_adjoint_nonneg W)

/-- `‖|W*| x‖ = ‖W* x‖`. -/
theorem norm_leftModulus_apply (W : E →L[ℂ] F) (x : F) :
    ‖leftModulus W x‖ = ‖adjoint W x‖ := by
  have h : ‖leftModulus W x‖ ^ 2 = ‖adjoint W x‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
    congr 1
    rw [← adjoint_inner_left (leftModulus W), adjoint_leftModulus, ← comp_apply,
      leftModulus_comp_self, comp_apply, ← adjoint_inner_right]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The adjoint of an operator with dense range is injective. -/
theorem injective_adjoint_of_denseRange {W : E →L[ℂ] F} (hW : DenseRange W) :
    Function.Injective (adjoint W) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hmem : x ∈ (LinearMap.range (W : E →ₗ[ℂ] F))ᗮ := by
    rw [ContinuousLinearMap.orthogonal_range]
    exact hx
  have htop : (LinearMap.range (W : E →ₗ[ℂ] F)).topologicalClosure = ⊤ := by
    rw [← Submodule.dense_iff_topologicalClosure_eq_top, LinearMap.coe_range]
    exact hW
  rw [Submodule.topologicalClosure_eq_top_iff.1 htop] at hmem
  exact (Submodule.mem_bot ℂ).1 hmem

/-- The adjoint of an injective operator has dense range. -/
theorem denseRange_adjoint_of_injective {W : E →L[ℂ] F} (hW : Function.Injective W) :
    DenseRange (adjoint W) := by
  have hrange : Set.range ⇑(adjoint W) =
      (LinearMap.range ((adjoint W : F →L[ℂ] E) : F →ₗ[ℂ] E) : Set E) :=
    (LinearMap.coe_range _).symm
  rw [DenseRange, hrange, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range,
    adjoint_adjoint]
  exact LinearMap.ker_eq_bot.2 hW

theorem injective_leftModulus {W : E →L[ℂ] F} (hW : DenseRange W) :
    Function.Injective (leftModulus W) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h := norm_leftModulus_apply W x
  rw [hx, norm_zero, eq_comm, norm_eq_zero] at h
  exact (injective_iff_map_eq_zero _).1 (injective_adjoint_of_denseRange hW) x h

theorem denseRange_leftModulus {W : E →L[ℂ] F} (hW : DenseRange W) :
    DenseRange (leftModulus W) := by
  have h := denseRange_adjoint_of_injective (injective_leftModulus hW)
  rwa [adjoint_leftModulus] at h

/-- The co-polar unitary `V* : F ≃ E`, `V*(|W*| x) = W* x`. -/
def polarCoUnitary (W : E →L[ℂ] F) (hinj : Function.Injective W) (hW : DenseRange W) :
    F ≃ₗᵢ[ℂ] E :=
  (LinearEquiv.refl ℂ F).extendOfIsometry ((leftModulus W : F →L[ℂ] F) : F →ₗ[ℂ] F)
    ((adjoint W : F →L[ℂ] E) : F →ₗ[ℂ] E) (denseRange_leftModulus hW)
    (denseRange_adjoint_of_injective hinj) fun x => (norm_leftModulus_apply W x).symm

theorem polarCoUnitary_leftModulus (W : E →L[ℂ] F) (hinj : Function.Injective W)
    (hW : DenseRange W) (x : F) :
    polarCoUnitary W hinj hW (leftModulus W x) = adjoint W x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- The unitary left polar factor `V : E ≃ F`. -/
def polarUnitary (W : E →L[ℂ] F) (hinj : Function.Injective W) (hW : DenseRange W) :
    E ≃ₗᵢ[ℂ] F :=
  (polarCoUnitary W hinj hW).symm

/-- **Left polar decomposition.**  `W = |W*| V` with `V` unitary. -/
theorem leftModulus_polarUnitary (W : E →L[ℂ] F) (hinj : Function.Injective W)
    (hW : DenseRange W) (e : E) :
    leftModulus W (polarUnitary W hinj hW e) = W e := by
  refine ext_inner_left ℂ fun y => ?_
  rw [← adjoint_inner_left (leftModulus W), adjoint_leftModulus, ← adjoint_inner_left W,
    ← polarCoUnitary_leftModulus W hinj hW y, polarUnitary,
    ← LinearIsometryEquiv.inner_map_map (polarCoUnitary W hinj hW).symm,
    LinearIsometryEquiv.symm_apply_apply]

theorem leftModulus_comp_polarUnitary (W : E →L[ℂ] F) (hinj : Function.Injective W)
    (hW : DenseRange W) :
    leftModulus W ∘L (polarUnitary W hinj hW : E →L[ℂ] F) = W :=
  ContinuousLinearMap.ext fun e => leftModulus_polarUnitary W hinj hW e

/-- Uniqueness of the unitary polar factor. -/
theorem polarUnitary_unique (W : E →L[ℂ] F) (hinj : Function.Injective W) (hW : DenseRange W)
    (V : E ≃ₗᵢ[ℂ] F) (hV : ∀ e, leftModulus W (V e) = W e) : V = polarUnitary W hinj hW := by
  ext e
  exact injective_leftModulus hW ((hV e).trans (leftModulus_polarUnitary W hinj hW e).symm)

/-- `W V* = |W*|`. -/
theorem apply_polarUnitary_symm (W : E →L[ℂ] F) (hinj : Function.Injective W)
    (hW : DenseRange W) (x : F) :
    W ((polarUnitary W hinj hW).symm x) = leftModulus W x := by
  rw [← leftModulus_polarUnitary W hinj hW, LinearIsometryEquiv.apply_symm_apply]

end GaloisForLFunctions.HTGeometry
