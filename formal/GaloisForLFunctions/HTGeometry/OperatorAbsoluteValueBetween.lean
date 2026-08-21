import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The absolute value of an operator between two Hilbert spaces

For a bounded operator `T : K →L C` between complex Hilbert spaces, `|T| = √(T†T)` is the
positive square root of the energy operator on the source.  It is positive and self-adjoint,
squares to `T†T`, has the same kernel as `T`, and is a metric companion: `‖|T| x‖ = ‖T x‖`.
-/

namespace ContinuousLinearMap

variable {K C : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]

theorem adjoint_comp_self_nonneg (T : K →L[ℂ] C) : (0 : K →L[ℂ] K) ≤ (adjoint T).comp T := by
  rw [ContinuousLinearMap.le_def, sub_zero]
  exact isPositive_adjoint_comp_self T

/-- The **absolute value** `|T| = √(T†T)` of an operator between two Hilbert spaces. -/
noncomputable def absMap (T : K →L[ℂ] C) : K →L[ℂ] K := CFC.sqrt ((adjoint T).comp T)

theorem absMap_nonneg (T : K →L[ℂ] C) : (0 : K →L[ℂ] K) ≤ absMap T := CFC.sqrt_nonneg _

theorem isSelfAdjoint_absMap (T : K →L[ℂ] C) : IsSelfAdjoint (absMap T) :=
  .of_nonneg (absMap_nonneg T)

theorem absMap_mul_self (T : K →L[ℂ] C) : absMap T * absMap T = (adjoint T).comp T :=
  CFC.sqrt_mul_sqrt_self _ (adjoint_comp_self_nonneg T)

theorem absMap_comp_self (T : K →L[ℂ] C) : absMap T ∘L absMap T = (adjoint T).comp T :=
  absMap_mul_self T

/-- `|T|` is a metric companion of `T`. -/
theorem norm_absMap_apply (T : K →L[ℂ] C) (x : K) : ‖absMap T x‖ = ‖T x‖ := by
  have hsym : (absMap T).IsSymmetric :=
    isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_absMap T)
  have h1 : ‖absMap T x‖ ^ 2 = RCLike.re (inner ℂ x ((absMap T ∘L absMap T) x)) := by
    rw [comp_apply, ← inner_self_eq_norm_sq (𝕜 := ℂ) (absMap T x)]
    exact congrArg RCLike.re (hsym x (absMap T x))
  have h2 : ‖T x‖ ^ 2 = RCLike.re (inner ℂ x ((absMap T ∘L absMap T) x)) := by
    rw [absMap_comp_self, comp_apply, adjoint_inner_right, inner_self_eq_norm_sq]
  have h3 : ‖absMap T x‖ ^ 2 = ‖T x‖ ^ 2 := by rw [h1, ← h2]
  nlinarith [norm_nonneg (absMap T x), norm_nonneg (T x)]

theorem ker_absMap (T : K →L[ℂ] C) :
    LinearMap.ker (absMap T : K →ₗ[ℂ] K) = LinearMap.ker (T : K →ₗ[ℂ] C) := by
  ext x
  have hn := norm_absMap_apply T x
  constructor
  · intro hx
    have h0 : absMap T x = 0 := hx
    rw [h0, norm_zero] at hn
    exact norm_eq_zero.mp hn.symm
  · intro hx
    have h0 : T x = 0 := hx
    rw [h0, norm_zero] at hn
    exact norm_eq_zero.mp hn

end ContinuousLinearMap
