import GaloisForLFunctions.HTGeometry.PeriodIncidenceMultiplier

/-!
# The critical trace topology of a diagonal incidence multiplier

A diagonal incidence multiplier `x ↦ (m i • x i)` with nonvanishing symbol `m` has nonclosed range
in the uniform topology whenever `‖m i‖` has no positive lower bound.  The defect is removed by the
*critical trace topology*: weighting the target by `a i = ‖m i‖⁻¹` turns the multiplier into an
isometric bijection with the explicit pointwise inverse `y i ↦ (m i)⁻¹ • y i`.

This file proves that renorming statement, and proves that the critical weight is the **only**
diagonal weight that makes the multiplier a topological isomorphism: boundedness of the multiplier
is exactly `sup_i a i ‖m i‖ < ∞`, boundedness of its inverse is exactly `inf_i a i ‖m i‖ > 0`, and
both together say that `a` is boundedly equivalent to `‖m‖⁻¹`.  Hence the topology cannot be chosen
after seeing a desired target.

Sizes are taken in `ℝ≥0∞`, so no boundedness hypothesis is needed anywhere: a family is bounded
exactly when its size is finite.
-/

noncomputable section

open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### Diagonal sizes -/

/-- The uniform size of a family. -/
def uniformSup (x : ι → X) : ℝ≥0∞ := ⨆ i, ((‖x i‖₊ : ℝ≥0) : ℝ≥0∞)

/-- The size of a family in the diagonal trace topology with weight `a`. -/
def diagonalSup (a : ι → ℝ≥0) (y : ι → X) : ℝ≥0∞ := ⨆ i, ((a i * ‖y i‖₊ : ℝ≥0) : ℝ≥0∞)

/-- The diagonal incidence multiplier of a symbol. -/
def diagonalIncidence (m : ι → ℂ) (x : ι → X) : ι → X := fun i => m i • x i

/-- The pointwise inverse of a diagonal incidence multiplier. -/
def diagonalIncidenceInv (m : ι → ℂ) (y : ι → X) : ι → X := fun i => (m i)⁻¹ • y i

theorem diagonalIncidenceInv_diagonalIncidence {m : ι → ℂ} (hm : ∀ i, m i ≠ 0) (x : ι → X) :
    diagonalIncidenceInv m (diagonalIncidence m x) = x := by
  funext i
  rw [diagonalIncidenceInv, diagonalIncidence, smul_smul, inv_mul_cancel₀ (hm i), one_smul]

theorem diagonalIncidence_diagonalIncidenceInv {m : ι → ℂ} (hm : ∀ i, m i ≠ 0) (y : ι → X) :
    diagonalIncidence m (diagonalIncidenceInv m y) = y := by
  funext i
  rw [diagonalIncidence, diagonalIncidenceInv, smul_smul, mul_inv_cancel₀ (hm i), one_smul]

/-! ### The critical renorming -/

/-- **The critical trace topology is exact.**  Weighting the target by `‖m‖⁻¹` turns the diagonal
incidence multiplier into an isometry for the uniform size. -/
theorem diagonalSup_diagonalIncidence_critical {m : ι → ℂ} (hm : ∀ i, m i ≠ 0) (x : ι → X) :
    diagonalSup (fun i => ‖m i‖₊⁻¹) (diagonalIncidence m x) = uniformSup x := by
  rw [diagonalSup, uniformSup]
  refine iSup_congr fun i => ?_
  congr 1
  have hne : (‖m i‖₊ : ℝ≥0) ≠ 0 := by simpa using hm i
  rw [diagonalIncidence, nnnorm_smul, inv_mul_cancel_left₀ hne]

/-- The critical weight of the regularized period symbol `λ ↦ λ/(1+|λ|)` is `(1+|λ|)/|λ|`. -/
theorem nnnorm_regularizedPeriodWeight_inv_eq (z : ℂ) :
    ‖regularizedPeriodWeight z‖₊⁻¹ = (1 + ‖z‖₊) / ‖z‖₊ := by
  have hnorm : ‖regularizedPeriodWeight z‖ = ‖z‖ / (1 + ‖z‖) := norm_regularizedPeriodWeight z
  have hval : ‖regularizedPeriodWeight z‖₊ = ‖z‖₊ / (1 + ‖z‖₊) := by
    ext
    push_cast
    rw [hnorm]
  rw [hval, inv_div]

/-! ### Uniqueness of the critical weight -/

/-- **(12)** A uniform bound on `a ‖m‖` bounds the multiplier into the `a`-weighted topology. -/
theorem diagonalSup_diagonalIncidence_le {m : ι → ℂ} {a : ι → ℝ≥0} {C : ℝ≥0}
    (h : ∀ i, a i * ‖m i‖₊ ≤ C) (x : ι → X) :
    diagonalSup a (diagonalIncidence m x) ≤ (C : ℝ≥0∞) * uniformSup x := by
  rw [diagonalSup, uniformSup]
  refine iSup_le fun i => ?_
  have hterm : (a i * ‖diagonalIncidence m x i‖₊ : ℝ≥0) ≤ C * ‖x i‖₊ := by
    rw [diagonalIncidence, nnnorm_smul, ← mul_assoc]
    exact mul_le_mul' (h i) le_rfl
  calc ((a i * ‖diagonalIncidence m x i‖₊ : ℝ≥0) : ℝ≥0∞) ≤ ((C * ‖x i‖₊ : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast hterm
    _ = (C : ℝ≥0∞) * ((‖x i‖₊ : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ (C : ℝ≥0∞) * ⨆ j, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) :=
        mul_le_mul' le_rfl (le_iSup (fun j => ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞)) i)

/-- **(13)** A positive lower bound on `a ‖m‖` bounds the inverse. -/
theorem le_diagonalSup_diagonalIncidence {m : ι → ℂ} {a : ι → ℝ≥0} {c : ℝ≥0}
    (h : ∀ i, c ≤ a i * ‖m i‖₊) (x : ι → X) :
    (c : ℝ≥0∞) * uniformSup x ≤ diagonalSup a (diagonalIncidence m x) := by
  rw [diagonalSup, uniformSup, ENNReal.mul_iSup]
  refine iSup_le fun i => ?_
  have hterm : (c * ‖x i‖₊ : ℝ≥0) ≤ a i * ‖diagonalIncidence m x i‖₊ := by
    rw [diagonalIncidence, nnnorm_smul, ← mul_assoc]
    exact mul_le_mul' (h i) le_rfl
  calc (c : ℝ≥0∞) * ((‖x i‖₊ : ℝ≥0) : ℝ≥0∞) = ((c * ‖x i‖₊ : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((a i * ‖diagonalIncidence m x i‖₊ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hterm
    _ ≤ ⨆ j, ((a j * ‖diagonalIncidence m x j‖₊ : ℝ≥0) : ℝ≥0∞) :=
        le_iSup (fun j : ι => ((a j * ‖diagonalIncidence m x j‖₊ : ℝ≥0) : ℝ≥0∞)) i

/-! ### The coordinate test -/

omit [NormedSpace ℂ X] in
theorem uniformSup_single [DecidableEq ι] (i : ι) {v : X} (hv : ‖v‖₊ = 1) :
    uniformSup (fun j : ι => if j = i then v else 0) = 1 := by
  rw [uniformSup]
  refine le_antisymm (iSup_le fun j => ?_) ?_
  · by_cases hj : j = i
    · simp [hj, hv]
    · simp [hj]
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun j : ι => ((‖(if j = i then v else 0 : X)‖₊ : ℝ≥0) : ℝ≥0∞)) i)
    simp [hv]

theorem diagonalSup_diagonalIncidence_single [DecidableEq ι] (a : ι → ℝ≥0) (m : ι → ℂ) (i : ι)
    {v : X} (hv : ‖v‖₊ = 1) :
    diagonalSup a (diagonalIncidence m (fun j : ι => if j = i then v else 0))
      = ((a i * ‖m i‖₊ : ℝ≥0) : ℝ≥0∞) := by
  rw [diagonalSup]
  refine le_antisymm (iSup_le fun j => ?_) ?_
  · by_cases hj : j = i
    · subst hj
      simp [diagonalIncidence, nnnorm_smul, hv]
    · simp [diagonalIncidence, hj]
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun j : ι =>
        ((a j * ‖diagonalIncidence m (fun k : ι => if k = i then v else 0) j‖₊ : ℝ≥0) : ℝ≥0∞)) i)
    simp [diagonalIncidence, nnnorm_smul, hv]

/-- **The converse of (12).**  A bounded multiplier forces the pointwise weight bound. -/
theorem le_of_diagonalSup_diagonalIncidence_le [DecidableEq ι] {m : ι → ℂ} {a : ι → ℝ≥0} {C : ℝ≥0}
    {v : X} (hv : ‖v‖₊ = 1)
    (h : ∀ x : ι → X, diagonalSup a (diagonalIncidence m x) ≤ (C : ℝ≥0∞) * uniformSup x)
    (i : ι) : a i * ‖m i‖₊ ≤ C := by
  have hx := h (fun j : ι => if j = i then v else 0)
  rw [diagonalSup_diagonalIncidence_single a m i hv, uniformSup_single i hv, mul_one] at hx
  exact_mod_cast hx

/-- **The converse of (13).**  A bounded inverse forces the pointwise lower bound. -/
theorem le_of_le_diagonalSup_diagonalIncidence [DecidableEq ι] {m : ι → ℂ} {a : ι → ℝ≥0} {c : ℝ≥0}
    {v : X} (hv : ‖v‖₊ = 1)
    (h : ∀ x : ι → X, (c : ℝ≥0∞) * uniformSup x ≤ diagonalSup a (diagonalIncidence m x))
    (i : ι) : c ≤ a i * ‖m i‖₊ := by
  have hx := h (fun j : ι => if j = i then v else 0)
  rw [diagonalSup_diagonalIncidence_single a m i hv, uniformSup_single i hv, mul_one] at hx
  exact_mod_cast hx

/-- **(14)** A diagonal weight makes the incidence multiplier a topological isomorphism exactly
when it is boundedly equivalent to the critical weight `‖m‖⁻¹`. -/
theorem diagonalWeight_boundedly_equivalent_critical [DecidableEq ι] {m : ι → ℂ}
    (hm : ∀ i, m i ≠ 0) {a : ι → ℝ≥0} {C c : ℝ≥0} {v : X} (hv : ‖v‖₊ = 1)
    (hub : ∀ x : ι → X, diagonalSup a (diagonalIncidence m x) ≤ (C : ℝ≥0∞) * uniformSup x)
    (hlb : ∀ x : ι → X, (c : ℝ≥0∞) * uniformSup x ≤ diagonalSup a (diagonalIncidence m x))
    (i : ι) : c * ‖m i‖₊⁻¹ ≤ a i ∧ a i ≤ C * ‖m i‖₊⁻¹ := by
  have hne : (‖m i‖₊ : ℝ≥0) ≠ 0 := by simpa using hm i
  have hupper := le_of_diagonalSup_diagonalIncidence_le hv hub i
  have hlower := le_of_le_diagonalSup_diagonalIncidence hv hlb i
  have hsplit : a i = (a i * ‖m i‖₊) * ‖m i‖₊⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
  constructor
  · rw [hsplit]
    exact mul_le_mul' hlower le_rfl
  · rw [hsplit]
    exact mul_le_mul' hupper le_rfl

/-! ### Magnitude and phase -/

/-- **(15)** The regularized period symbol splits into a positive magnitude, absorbed by the
critical norm, and a unimodular phase. -/
theorem regularizedPeriodWeight_eq_magnitude_mul_phase {z : ℂ} (hz : z ≠ 0) :
    regularizedPeriodWeight z = ((‖z‖ / (1 + ‖z‖) : ℝ) : ℂ) * (z / (‖z‖ : ℂ)) := by
  have hzn : (‖z‖ : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero] using norm_ne_zero_iff.mpr hz
  have h1 : ((1 + ‖z‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    positivity
  rw [regularizedPeriodWeight]
  push_cast
  field_simp

theorem norm_phase_eq_one {z : ℂ} (hz : z ≠ 0) : ‖z / (‖z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
  exact div_self (norm_ne_zero_iff.mpr hz)

end GaloisForLFunctions.HTGeometry
