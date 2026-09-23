import GaloisForLFunctions.HTGeometry.ClockStripCauchyScale

/-!
# The tube of several transverse variables, and its Cauchy estimates

Several coupled transverse coordinates need a domain of several complex variables: the tube of
half-width `ρ`, the set of points all of whose coordinates have imaginary part smaller than `ρ`.

No several-variable complex analysis is required to estimate on it. A function holomorphic on the
tube restricts, along each coordinate through a point of the tube, to a function holomorphic on the
strip of the same half-width and bounded by the same constant; so the one-variable Cauchy estimates
apply slice by slice, and the partial derivative along a coordinate is the one-variable derivative of
that slice.

The second partial derivative along a coordinate is likewise the one-variable second derivative of
the slice — the two updates collapse — so the two estimates the clock iteration needs are the
one-variable ones, unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- The tube of half-width `ρ`: every coordinate lies in the strip. -/
def tube (k : ℕ) (ρ : ℝ) : Set (Fin k → ℂ) := {z | ∀ i, |(z i).im| < ρ}

theorem mem_tube {ρ : ℝ} {z : Fin k → ℂ} : z ∈ tube k ρ ↔ ∀ i, |(z i).im| < ρ := Iff.rfl

theorem isOpen_tube (k : ℕ) (ρ : ℝ) : IsOpen (tube k ρ) := by
  have hEq : tube k ρ = ⋂ i : Fin k, {z : Fin k → ℂ | |(z i).im| < ρ} := by
    ext z
    simp [tube, mem_iInter]
  rw [hEq]
  refine isOpen_iInter_of_finite fun i => ?_
  exact isOpen_lt ((continuous_abs.comp (Complex.continuous_im.comp (continuous_apply i))))
    continuous_const

theorem tube_mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') : tube k ρ ⊆ tube k ρ' :=
  fun _ hz i => lt_of_lt_of_le (hz i) h

/-! ## Slices -/

/-- Updating one coordinate of a point of the tube by a point of the strip stays in the tube. -/
theorem update_mem_tube {ρ : ℝ} {z : Fin k → ℂ} (hz : z ∈ tube k ρ) (i : Fin k) {ζ : ℂ}
    (hζ : ζ ∈ imStrip ρ) : Function.update z i ζ ∈ tube k ρ := by
  intro j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact mem_imStrip.mp hζ
  · rw [Function.update_of_ne hj]
    exact hz j

/-- The slice of a point along a coordinate, as an affine map of one complex variable. -/
theorem differentiable_updateSlice (z : Fin k → ℂ) (i : Fin k) :
    Differentiable ℂ fun ζ : ℂ => Function.update z i ζ := by
  have hEq : (fun ζ : ℂ => Function.update z i ζ)
      = fun ζ : ℂ => z + (ζ - z i) • (Pi.single i 1 : Fin k → ℂ) := by
    funext ζ
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [Function.update_of_ne hj]
      simp [Pi.single_eq_of_ne hj]
  rw [hEq]
  exact (differentiable_const z).add
    ((differentiable_id.sub (differentiable_const (z i))).smul_const _)

/-- A function holomorphic on the tube is holomorphic along each coordinate slice. -/
theorem differentiableOn_updateSlice {ρ : ℝ} {w : (Fin k → ℂ) → ℂ}
    (hw : DifferentiableOn ℂ w (tube k ρ)) {z : Fin k → ℂ} (hz : z ∈ tube k ρ) (i : Fin k) :
    DifferentiableOn ℂ (fun ζ : ℂ => w (Function.update z i ζ)) (imStrip ρ) := by
  intro ζ hζ
  refine (hw.differentiableAt ((isOpen_tube k ρ).mem_nhds (update_mem_tube hz i hζ))).comp
    ζ ?_ |>.differentiableWithinAt
  exact (differentiable_updateSlice z i) ζ

/-! ## Partial derivatives -/

/-- The partial derivative of a function of several complex variables along a coordinate. -/
noncomputable def cpartial (i : Fin k) (w : (Fin k → ℂ) → ℂ) (z : Fin k → ℂ) : ℂ :=
  deriv (fun ζ : ℂ => w (Function.update z i ζ)) (z i)

/-- **The partial derivative along a coordinate, restricted to that coordinate slice, is the
derivative of the slice**: the two updates collapse into one. -/
theorem cpartial_update_eq_deriv_slice (i : Fin k) (w : (Fin k → ℂ) → ℂ) (z : Fin k → ℂ) :
    (fun ζ : ℂ => cpartial i w (Function.update z i ζ))
      = deriv fun ξ : ℂ => w (Function.update z i ξ) := by
  funext ζ
  rw [cpartial, Function.update_self]
  congr 1
  funext ξ
  rw [Function.update_idem]

/-- **The second partial derivative along a coordinate is the second derivative of the slice.** -/
theorem cpartial_cpartial_eq (i : Fin k) (w : (Fin k → ℂ) → ℂ) (z : Fin k → ℂ) :
    cpartial i (cpartial i w) z
      = deriv (deriv fun ξ : ℂ => w (Function.update z i ξ)) (z i) := by
  rw [cpartial, cpartial_update_eq_deriv_slice]

/-! ## The Cauchy estimates on the tube -/

/-- **The first partial derivative of a bounded holomorphic function on a tube.** -/
theorem norm_cpartial_le_on_tube {ρ ρ' M : ℝ} (hρ : ρ < ρ') {w : (Fin k → ℂ) → ℂ}
    (hw : DifferentiableOn ℂ w (tube k ρ')) (hM : ∀ z ∈ tube k ρ', ‖w z‖ ≤ M)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ) (i : Fin k) :
    ‖cpartial i w z‖ ≤ 2 * M / (ρ' - ρ) := by
  have hzt : z ∈ tube k ρ' := tube_mono hρ.le hz
  have hslice : DifferentiableOn ℂ (fun ζ : ℂ => w (Function.update z i ζ)) (imStrip ρ') :=
    differentiableOn_updateSlice hw hzt i
  have hbound : ∀ ζ ∈ imStrip ρ', ‖w (Function.update z i ζ)‖ ≤ M :=
    fun ζ hζ => hM _ (update_mem_tube hzt i hζ)
  exact norm_deriv_le_on_imStrip hρ hslice hbound (le_of_lt (hz i))

/-- **The second partial derivative of a bounded holomorphic function on a tube.** -/
theorem norm_cpartial_cpartial_le_on_tube {ρ ρ' M : ℝ} (hρ : ρ < ρ') {w : (Fin k → ℂ) → ℂ}
    (hw : DifferentiableOn ℂ w (tube k ρ')) (hM : ∀ z ∈ tube k ρ', ‖w z‖ ≤ M)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ) (i : Fin k) :
    ‖cpartial i (cpartial i w) z‖ ≤ 16 * M / (ρ' - ρ) ^ (2 : ℕ) := by
  have hzt : z ∈ tube k ρ' := tube_mono hρ.le hz
  have hslice : DifferentiableOn ℂ (fun ζ : ℂ => w (Function.update z i ζ)) (imStrip ρ') :=
    differentiableOn_updateSlice hw hzt i
  have hbound : ∀ ζ ∈ imStrip ρ', ‖w (Function.update z i ζ)‖ ≤ M :=
    fun ζ hζ => hM _ (update_mem_tube hzt i hζ)
  rw [cpartial_cpartial_eq]
  exact norm_deriv_deriv_le_on_imStrip hρ hslice hbound (le_of_lt (hz i))

end GaloisForLFunctions.HTGeometry
