import GaloisForLFunctions.HilbertMetric.CoherentCollisionJet
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Group.Pi.Units

/-!
# Persistence of positive Gram log-curvature

The second logarithmic derivative of an invertible Gram path is determined by its matrix
2-jet.  This module packages that jet algebraically and proves that strict positive curvature
persists under entrywise convergence of the value and first two derivatives.  It is the finite
matrix connector between coherent-collision jets and an actual non-colliding Gaussian
configuration.
-/

open Filter

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Algebraic second log-curvature associated with an invertible matrix 2-jet. -/
def gramLogCurvatureJet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (A⁻¹ * A₂ - ((A⁻¹ * A₁) * A⁻¹) * A₁)

/-- The numerator `z z₂ - z₁²` controlling the sign of a scalar logarithmic curvature. -/
def scalarLogCurvatureNumerator (z z₁ z₂ : ℝ) : ℝ := z * z₂ - z₁ ^ 2

/-- The scalar log-curvature numerator is continuous under convergence of a scalar 2-jet. -/
theorem tendsto_scalarLogCurvatureNumerator {α : Type*} {l : Filter α}
    {f f₁ f₂ : α → ℝ} {z z₁ z₂ : ℝ}
    (hf : Tendsto f l (nhds z)) (hf₁ : Tendsto f₁ l (nhds z₁))
    (hf₂ : Tendsto f₂ l (nhds z₂)) :
    Tendsto (fun x => scalarLogCurvatureNumerator (f x) (f₁ x) (f₂ x)) l
      (nhds (scalarLogCurvatureNumerator z z₁ z₂)) := by
  exact (hf.mul hf₂).sub (hf₁.pow 2)

/-- Strict positivity of a limiting scalar log-curvature numerator persists before collision. -/
theorem eventually_pos_scalarLogCurvatureNumerator {α : Type*} {l : Filter α}
    {f f₁ f₂ : α → ℝ} {z z₁ z₂ : ℝ}
    (hf : Tendsto f l (nhds z)) (hf₁ : Tendsto f₁ l (nhds z₁))
    (hf₂ : Tendsto f₂ l (nhds z₂))
    (hpos : 0 < scalarLogCurvatureNumerator z z₁ z₂) :
    ∀ᶠ x in l, 0 < scalarLogCurvatureNumerator (f x) (f₁ x) (f₂ x) := by
  exact (tendsto_scalarLogCurvatureNumerator hf hf₁ hf₂).eventually
    (eventually_gt_nhds hpos)

/-- Gram log-curvature is continuous under convergence of a matrix 2-jet at an invertible limit. -/
theorem tendsto_gramLogCurvatureJet {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} {A A₁ A₂ : α → Matrix ι ι ℝ}
    {B B₁ B₂ : Matrix ι ι ℝ}
    (hA : Tendsto A l (nhds B)) (hA₁ : Tendsto A₁ l (nhds B₁))
    (hA₂ : Tendsto A₂ l (nhds B₂)) (hdet : B.det ≠ 0) :
    Tendsto (fun x => gramLogCurvatureJet (A x) (A₁ x) (A₂ x)) l
      (nhds (gramLogCurvatureJet B B₁ B₂)) := by
  have hinvdet : ContinuousAt Ring.inverse B.det := by
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
  have hinv : Tendsto (fun x => (A x)⁻¹) l (nhds B⁻¹) :=
    (continuousAt_matrix_inv B hinvdet).tendsto.comp hA
  have hmatrix :
      Tendsto (fun x => (A x)⁻¹ * A₂ x - (((A x)⁻¹ * A₁ x) * (A x)⁻¹) * A₁ x) l
        (nhds (B⁻¹ * B₂ - ((B⁻¹ * B₁) * B⁻¹) * B₁)) :=
    (hinv.mul hA₂).sub (((hinv.mul hA₁).mul hinv).mul hA₁)
  have htrace : Continuous (fun C : Matrix ι ι ℝ => Matrix.trace C) :=
    continuous_id.matrix_trace
  exact htrace.continuousAt.tendsto.comp hmatrix

/-- Strictly positive limiting Gram log-curvature persists before the collision. -/
theorem eventually_pos_gramLogCurvatureJet {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} {A A₁ A₂ : α → Matrix ι ι ℝ}
    {B B₁ B₂ : Matrix ι ι ℝ}
    (hA : Tendsto A l (nhds B)) (hA₁ : Tendsto A₁ l (nhds B₁))
    (hA₂ : Tendsto A₂ l (nhds B₂)) (hdet : B.det ≠ 0)
    (hpos : 0 < gramLogCurvatureJet B B₁ B₂) :
    ∀ᶠ x in l, 0 < gramLogCurvatureJet (A x) (A₁ x) (A₂ x) := by
  exact (tendsto_gramLogCurvatureJet hA hA₁ hA₂ hdet).eventually
    (eventually_gt_nhds hpos)

theorem gramLogCurvatureJet_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v v₁ v₂ : ι → ℝ) :
    gramLogCurvatureJet (Matrix.diagonal v) (Matrix.diagonal v₁) (Matrix.diagonal v₂) =
      (∑ i, Ring.inverse v i * v₂ i) -
        ∑ i, Ring.inverse v i * v₁ i * Ring.inverse v i * v₁ i := by
  simp [gramLogCurvatureJet, Matrix.inv_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_sub]

theorem ringInverse_apply_eq_inv {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hv : ∀ i, v i ≠ 0) (i : ι) :
    Ring.inverse v i = (v i)⁻¹ := by
  have hu : IsUnit v := Pi.isUnit_iff.mpr fun j => (isUnit_iff_ne_zero).mpr (hv j)
  calc
    Ring.inverse v i = (((hu.unit⁻¹ : (ι → ℝ)ˣ) : (ι → ℝ)) i) := by
      rw [Ring.inverse_of_isUnit hu]
    _ = (((hu.apply i).unit⁻¹ : ℝˣ) : ℝ) := hu.val_inv_apply i
    _ = (v i)⁻¹ := by
      rw [Units.val_inv_eq_inv_val]
      rfl

/-- The log-curvature jet of diagonal data is the sum of its scalar channel curvatures. -/
theorem gramLogCurvatureJet_diagonal_of_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v v₁ v₂ : ι → ℝ) (hv : ∀ i, v i ≠ 0) :
    gramLogCurvatureJet (Matrix.diagonal v) (Matrix.diagonal v₁) (Matrix.diagonal v₂) =
      ∑ i, (v₂ i / v i - (v₁ i / v i) ^ 2) := by
  rw [gramLogCurvatureJet_diagonal]
  simp_rw [ringInverse_apply_eq_inv v hv]
  rw [Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro i hi
    rw [div_eq_mul_inv]
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    rw [div_eq_mul_inv]
    ring

/-- Simultaneous invertible congruence of a matrix 2-jet preserves its log-curvature. -/
theorem gramLogCurvatureJet_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S A A₁ A₂ : Matrix ι ι ℝ) (hS : IsUnit S.det) :
    gramLogCurvatureJet (S * A * S) (S * A₁ * S) (S * A₂ * S) =
      gramLogCurvatureJet A A₁ A₂ := by
  have hunit : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr hS
  let u : (Matrix ι ι ℝ)ˣ := hunit.unit
  have hu : (u : Matrix ι ι ℝ) = S := hunit.unit_spec
  have hSiS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS
  have hSSi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS
  have hinv : (S * A * S)⁻¹ = S⁻¹ * A⁻¹ * S⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  have htrace (N : Matrix ι ι ℝ) : Matrix.trace (S⁻¹ * N * S) = Matrix.trace N := by
    rw [← hu]
    simpa only [Matrix.coe_units_inv] using Matrix.trace_units_conj' u N
  have hfirst :
      (S * A * S)⁻¹ * (S * A₂ * S) = S⁻¹ * (A⁻¹ * A₂) * S := by
    rw [hinv]
    calc
      (S⁻¹ * A⁻¹ * S⁻¹) * (S * A₂ * S) =
          S⁻¹ * A⁻¹ * (S⁻¹ * S) * A₂ * S := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSiS]; simp [Matrix.mul_assoc]
  have hsecond :
      (((S * A * S)⁻¹ * (S * A₁ * S)) * (S * A * S)⁻¹) * (S * A₁ * S) =
        S⁻¹ * (((A⁻¹ * A₁) * A⁻¹) * A₁) * S := by
    rw [hinv]
    calc
      ((S⁻¹ * A⁻¹ * S⁻¹) * (S * A₁ * S) * (S⁻¹ * A⁻¹ * S⁻¹)) *
          (S * A₁ * S) =
        S⁻¹ * A⁻¹ * (S⁻¹ * S) * A₁ * (S * S⁻¹) * A⁻¹ *
          (S⁻¹ * S) * A₁ * S := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSiS, hSSi]; simp [Matrix.mul_assoc]
  unfold gramLogCurvatureJet
  rw [hfirst, hsecond, Matrix.trace_sub, htrace, htrace]
  exact (Matrix.trace_sub _ _).symm

/-- Arbitrary invertible left-right changes of coordinates preserve a matrix log-curvature jet. -/
theorem gramLogCurvatureJet_mul_equiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L R A A₁ A₂ : Matrix ι ι ℝ) (hL : IsUnit L.det) (hR : IsUnit R.det) :
    gramLogCurvatureJet (L * A * R) (L * A₁ * R) (L * A₂ * R) =
      gramLogCurvatureJet A A₁ A₂ := by
  have hunitR : IsUnit R := (Matrix.isUnit_iff_isUnit_det R).mpr hR
  let uR : (Matrix ι ι ℝ)ˣ := hunitR.unit
  have huR : (uR : Matrix ι ι ℝ) = R := hunitR.unit_spec
  have hLiL : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hL
  have hRRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hinv : (L * A * R)⁻¹ = R⁻¹ * A⁻¹ * L⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  have htrace (N : Matrix ι ι ℝ) : Matrix.trace (R⁻¹ * N * R) = Matrix.trace N := by
    rw [← huR]
    simpa only [Matrix.coe_units_inv] using Matrix.trace_units_conj' uR N
  have hfirst :
      (L * A * R)⁻¹ * (L * A₂ * R) = R⁻¹ * (A⁻¹ * A₂) * R := by
    rw [hinv]
    calc
      (R⁻¹ * A⁻¹ * L⁻¹) * (L * A₂ * R) =
          R⁻¹ * A⁻¹ * (L⁻¹ * L) * A₂ * R := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hLiL]; simp [Matrix.mul_assoc]
  have hsecond :
      (((L * A * R)⁻¹ * (L * A₁ * R)) * (L * A * R)⁻¹) * (L * A₁ * R) =
        R⁻¹ * (((A⁻¹ * A₁) * A⁻¹) * A₁) * R := by
    rw [hinv]
    calc
      ((R⁻¹ * A⁻¹ * L⁻¹) * (L * A₁ * R) * (R⁻¹ * A⁻¹ * L⁻¹)) *
          (L * A₁ * R) =
        R⁻¹ * A⁻¹ * (L⁻¹ * L) * A₁ * (R * R⁻¹) * A⁻¹ *
          (L⁻¹ * L) * A₁ * R := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hLiL, hRRi]; simp [Matrix.mul_assoc]
  unfold gramLogCurvatureJet
  rw [hfirst, hsecond, Matrix.trace_sub, htrace, htrace]
  exact (Matrix.trace_sub _ _).symm

end

end GaloisForLFunctions.HilbertMetric
