import GaloisForLFunctions.HTGeometry.FokasLenellsLeftJost
import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniqueness for the Fokas–Lenells spatial equation

The eigenfunctions constructed from the uniformized Volterra equation are the
unique global solutions of the original spatial equation (1.8) of
Yan–Zhang–Zhu, arXiv:2607.19649v1. A uniform operator bound and the real Banach
space Gronwall theorem prove uniqueness on both half-lines for every Schwartz
potential and every nonzero spectral parameter represented as `Complex.exp a`.
-/

open Complex Matrix
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def spatialOperator (q : SchwartzMap ℝ ℂ) (a : ℂ) (x : ℝ) :
    SpectralVector →L[ℝ] SpectralVector :=
  pairOperator (I*(Complex.exp a)^(2 : ℕ)) (I*Complex.exp a*reflectedDerivative q x)
    (I*Complex.exp a*deriv q x) (-I*(Complex.exp a)^(2 : ℕ))

theorem spatialOperator_eq_matrix (q : SchwartzMap ℝ ℂ) (a : ℂ) (x : ℝ) (v : SpectralVector) :
    spatialOperator q a x v =
      matrixVector (spatialLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x) (Complex.exp a)) v := by
  apply Prod.ext <;>
    simp [spatialOperator, pairOperator, matrixVector, spatialLax,
      reflectedDerivative_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def spatialOperatorBound (q : SchwartzMap ℝ ℂ) (a : ℂ) : ℝ :=
  2*‖Complex.exp a‖^(2 : ℕ) + ‖Complex.exp a‖*
    (‖(SchwartzMap.derivCLM ℂ ℂ q).toBoundedContinuousFunction‖ +
      ‖(reflectedDerivative q).toBoundedContinuousFunction‖)

theorem spatialOperator_bound (q : SchwartzMap ℝ ℂ) (a : ℂ) (x : ℝ) (v : SpectralVector) :
    ‖spatialOperator q a x v‖ ≤ spatialOperatorBound q a*‖v‖ := by
  refine ((spatialOperator q a x).le_opNorm v).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  refine (pairOperator_bound _ _ _ _).trans ?_
  simp only [norm_mul, norm_neg, norm_I, one_mul, norm_pow]
  have hq := (SchwartzMap.derivCLM ℂ ℂ q).toBoundedContinuousFunction.norm_coe_le_norm x
  have hp := (reflectedDerivative q).toBoundedContinuousFunction.norm_coe_le_norm x
  simp only [SchwartzMap.toBoundedContinuousFunction_apply, SchwartzMap.derivCLM_apply] at hq hp
  unfold spatialOperatorBound
  nlinarith [norm_nonneg (Complex.exp a)]

/-- A solution of the actual original spatial equation with prescribed initial vector. -/
def IsSpatialSolution (q : SchwartzMap ℝ ℂ) (a : ℂ) (v : SpectralVector)
    (u : ℝ → SpectralVector) : Prop :=
  u 0 = v ∧ ∀ x, HasDerivAt u (spatialOperator q a x (u x)) x

theorem spatialEigenfunction_isSpatialSolution (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v : SpectralVector) : IsSpatialSolution q a v (spatialEigenfunction q a v) := by
  refine ⟨spatialEigenfunction_initial q a v, ?_⟩
  intro x
  rw [spatialOperator_eq_matrix]
  exact spatialEigenfunction_hasDerivAt q a v x

/-- Uniqueness is proved, not assumed as part of the constructed eigenfunction. -/
theorem spatialSolution_existsUnique (q : SchwartzMap ℝ ℂ) (a : ℂ) (v : SpectralVector) :
    ∃! u : ℝ → SpectralVector, IsSpatialSolution q a v u := by
  refine ⟨spatialEigenfunction q a v, spatialEigenfunction_isSpatialSolution q a v, ?_⟩
  intro u hu
  let f := spatialEigenfunction q a v
  have hf := spatialEigenfunction_isSpatialSolution q a v
  let D : ℝ → SpectralVector := fun x => u x-f x
  let D' : ℝ → SpectralVector := fun x => spatialOperator q a x (D x)
  have hd : ∀ x, HasDerivAt D (D' x) x := by
    intro x
    have h := (hu.2 x).fun_sub (hf.2 x)
    simpa only [D, D', map_sub, f] using h
  have hc : Continuous D := (show Differentiable ℝ D from fun x => (hd x).differentiableAt).continuous
  have hz : D 0 = 0 := by simp only [D, f, hu.1, hf.1, sub_self]
  have hb : ∀ x, ‖D' x‖ ≤ spatialOperatorBound q a*‖D x‖ :=
    fun x => spatialOperator_bound q a x (D x)
  have hpos : ∀ x : ℝ, 0 ≤ x → D x = 0 := by
    intro x hx
    exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hc.continuousOn
      (fun y _ => (hd y).hasDerivWithinAt) hz (fun y _ => hb y) x ⟨hx, le_rfl⟩
  have hrev : ∀ x, HasDerivAt (fun y : ℝ => D (-y)) (-D' (-x)) x := by
    intro x
    have h := (hd (-x)).scomp x (hasDerivAt_id x).neg
    simpa only [Function.comp_def, neg_one_smul] using h
  have hneg : ∀ x : ℝ, x ≤ 0 → D x = 0 := by
    intro x hx
    have h := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      ((hc.comp (f := fun y : ℝ => -y) continuous_neg).continuousOn)
      (fun y _ => (hrev y).hasDerivWithinAt)
      (by simpa only [Function.comp_def, neg_zero] using hz)
      (fun y _ => by simpa only [Function.comp_def, norm_neg] using hb (-y)) (-x)
      (show -x ∈ Set.Icc 0 (-x) from ⟨neg_nonneg.mpr hx, le_rfl⟩)
    simpa only [Function.comp_def, neg_neg] using h
  funext x
  apply sub_eq_zero.mp
  change D x = 0
  rcases le_total 0 x with hx | hx
  · exact hpos x hx
  · exact hneg x hx

end
end GaloisForLFunctions.HTGeometry.FokasLenells
