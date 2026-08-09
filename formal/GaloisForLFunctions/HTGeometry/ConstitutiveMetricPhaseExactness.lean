import GaloisForLFunctions.HTGeometry.HilbertBlockOperator

/-!
# Metric-phase exactness: cost, winding, and the Gram phase quotient

The based Hilbert complex `0 → ℂ² →(T) ℂ² → 0` with

`T(α,φ) = !![1, cos α; 0, exp(iφ) sin α]`

is acyclic for `0 < α ≤ π/2`, so its derived endpoint is zero for every parameter.  Certified here:
the determinant amplitude `exp(iφ) sin α`, the positive Gram law `TᴴT = !![1, cos α; cos α, 1]`
with its determinant `sin²α` and the eigenvectors realizing the squared singular values
`1 ± cos α`, the phase erasure of the Gram reading, the exact `2π`-periodicity of the observed law
together with the open logarithmic determinant lift, and the winding `N` after `N` observed periods.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix

section MetricPhase

variable {α φ : ℝ}

/-- The based exact law of aperture `α` and phase `φ`. -/
noncomputable def metricPhaseLaw (α φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, (Real.cos α : ℂ); 0, Complex.exp ((φ : ℂ) * Complex.I) * (Real.sin α : ℂ)]

/-- The positive Gram law `TᴴT`. -/
noncomputable def gramLaw (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, (Real.cos α : ℂ); (Real.cos α : ℂ), 1]

theorem exp_phase_norm (φ : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I)) * Complex.exp ((φ : ℂ) * Complex.I) = 1 := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

@[simp] theorem det_metricPhaseLaw (α φ : ℝ) :
    (metricPhaseLaw α φ).det = Complex.exp ((φ : ℂ) * Complex.I) * (Real.sin α : ℂ) := by
  rw [metricPhaseLaw, Matrix.det_fin_two_of]
  ring

/-- **The Gram law is the phase-blind reading.** -/
theorem conjTranspose_mul_self (α φ : ℝ) :
    (metricPhaseLaw α φ)ᴴ * metricPhaseLaw α φ = gramLaw α := by
  have hphase := exp_phase_norm φ
  have hpyth : (Real.cos α : ℂ) * (Real.cos α : ℂ) + (Real.sin α : ℂ) * (Real.sin α : ℂ) = 1 := by
    have h : Real.cos α * Real.cos α + Real.sin α * Real.sin α = 1 := by
      have hcs := Real.cos_sq_add_sin_sq α
      nlinarith [hcs]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, h, Complex.ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metricPhaseLaw, gramLaw, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.conj_ofReal, map_mul,
      -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals linear_combination (Real.sin α : ℂ) * (Real.sin α : ℂ) * hphase + hpyth

@[simp] theorem det_gramLaw (α : ℝ) : (gramLaw α).det = ((Real.sin α : ℂ)) ^ 2 := by
  rw [gramLaw, Matrix.det_fin_two_of]
  have hpyth : (Real.cos α : ℂ) * (Real.cos α : ℂ) + (Real.sin α : ℂ) * (Real.sin α : ℂ) = 1 := by
    have h : Real.cos α * Real.cos α + Real.sin α * Real.sin α = 1 := by
      have hcs := Real.cos_sq_add_sin_sq α
      nlinarith [hcs]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, h, Complex.ofReal_one]
  linear_combination -hpyth

/-- **The low singular direction.**  `(1, −1)` is a Gram eigenvector of eigenvalue `1 − cos α`. -/
theorem gramLaw_mulVec_low (α : ℝ) :
    (gramLaw α).mulVec ![1, -1] = (1 - (Real.cos α : ℂ)) • ![1, -1] := by
  funext i
  fin_cases i <;>
    simp [gramLaw, Matrix.mulVec, -Complex.ofReal_cos] <;> ring

/-- **The high singular direction.**  `(1, 1)` is a Gram eigenvector of eigenvalue `1 + cos α`. -/
theorem gramLaw_mulVec_high (α : ℝ) :
    (gramLaw α).mulVec ![1, 1] = (1 + (Real.cos α : ℂ)) • ![1, 1] := by
  funext i
  fin_cases i <;>
    simp [gramLaw, Matrix.mulVec, -Complex.ofReal_cos]
  ring

/-- **The law is acyclic**: for a positive aperture the determinant is a unit. -/
theorem det_metricPhaseLaw_ne_zero (hα : 0 < α) (hα' : α ≤ Real.pi / 2) :
    (metricPhaseLaw α φ).det ≠ 0 := by
  rw [det_metricPhaseLaw]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  have hlt : α < Real.pi := lt_of_le_of_lt hα' (by linarith [Real.pi_pos])
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα hlt
  exact_mod_cast hs.ne'

/-- **Positive Gram data erase the phase.** -/
theorem gram_phase_erasure (α φ φ' : ℝ) :
    (metricPhaseLaw α φ)ᴴ * metricPhaseLaw α φ
      = (metricPhaseLaw α φ')ᴴ * metricPhaseLaw α φ' := by
  rw [conjTranspose_mul_self, conjTranspose_mul_self]

/-- **The determinant does not.**  For a positive aperture the phases `0` and `π` are separated. -/
theorem det_phase_separates (hs : Real.sin α ≠ 0) :
    (metricPhaseLaw α 0).det ≠ (metricPhaseLaw α Real.pi).det := by
  rw [det_metricPhaseLaw, det_metricPhaseLaw]
  intro hcon
  have hs' : ((Real.sin α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have h1 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have h2 : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  rw [h1, h2, one_mul] at hcon
  have : (2 : ℂ) * (Real.sin α : ℂ) = 0 := by linear_combination hcon
  rcases mul_eq_zero.mp this with h | h
  · norm_num at h
  · exact hs' h

end MetricPhase

section Winding

variable {α : ℝ}

/-- **The observed law is exactly `2π`-periodic.** -/
theorem metricPhaseLaw_periodic (α t : ℝ) :
    metricPhaseLaw α (t + 2 * Real.pi) = metricPhaseLaw α t := by
  rw [metricPhaseLaw, metricPhaseLaw]
  congr 2
  push_cast
  rw [add_mul, Complex.exp_add]
  have : Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) = 1 := by
    simp
  rw [this, mul_one]

/-- The basepoint lift of the logarithm of the determinant. -/
noncomputable def detLogLift (α t : ℝ) : ℂ := (Real.log (Real.sin α) : ℂ) + (t : ℂ) * Complex.I

/-- **The lift really lifts the determinant.** -/
theorem exp_detLogLift (hs : 0 < Real.sin α) (t : ℝ) :
    Complex.exp (detLogLift α t) = (metricPhaseLaw α t).det := by
  rw [detLogLift, Complex.exp_add, det_metricPhaseLaw]
  have hlog : Complex.exp ((Real.log (Real.sin α) : ℂ)) = ((Real.sin α : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hs]
  rw [hlog, mul_comm]

/-- **The lifted determinant history is open**: it advances by `2πi` over each observed period. -/
theorem detLogLift_period (α t : ℝ) :
    detLogLift α (t + 2 * Real.pi) - detLogLift α t = 2 * (Real.pi : ℂ) * Complex.I := by
  rw [detLogLift, detLogLift]
  push_cast
  ring

/-- **After `N` observed periods the winding is `N`.** -/
theorem detLogLift_winding (α : ℝ) (N : ℕ) :
    detLogLift α (2 * Real.pi * N) - detLogLift α 0 = (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [detLogLift, detLogLift]
  push_cast
  ring

end Winding

section CofinalWall

open Filter Topology

/-- The squared Euclidean norm on `ℂ²`. -/
theorem euclid2_norm_sq (x : EuclideanSpace ℂ (Fin 2)) :
    ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]

theorem norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ = r := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

theorem norm_ofReal_sq (r : ℝ) : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The aperture block as a bounded operator on `ℂ²`. -/
noncomputable def apertureBlock (α : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (metricPhaseLaw α 0)

theorem apertureBlock_apply_zero (α : ℝ) (x : EuclideanSpace ℂ (Fin 2)) :
    apertureBlock α x 0 = x 0 + (Real.cos α : ℂ) * x 1 := by
  have h : apertureBlock α x 0 = ∑ j, (metricPhaseLaw α 0) 0 j * x j := Complex.ext rfl rfl
  rw [h, Fin.sum_univ_two]
  simp [metricPhaseLaw, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem apertureBlock_apply_one (α : ℝ) (x : EuclideanSpace ℂ (Fin 2)) :
    apertureBlock α x 1 = (Real.sin α : ℂ) * x 1 := by
  have h : apertureBlock α x 1 = ∑ j, (metricPhaseLaw α 0) 1 j * x j := Complex.ext rfl rfl
  rw [h, Fin.sum_univ_two]
  simp [metricPhaseLaw, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem apertureBlock_norm_sq (α : ℝ) (x : EuclideanSpace ℂ (Fin 2)) :
    ‖apertureBlock α x‖ ^ 2
      = ‖x 0 + (Real.cos α : ℂ) * x 1‖ ^ 2 + ‖(Real.sin α : ℂ) * x 1‖ ^ 2 := by
  rw [euclid2_norm_sq, apertureBlock_apply_zero, apertureBlock_apply_one]

/-- **The block is uniformly bounded**: its squared stretch never exceeds twice the input. -/
theorem apertureBlock_norm_sq_le (α : ℝ) (hc : 0 ≤ Real.cos α) (x : EuclideanSpace ℂ (Fin 2)) :
    ‖apertureBlock α x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
  have ha0 : (0 : ℝ) ≤ ‖x 0‖ := norm_nonneg _
  have hb0 : (0 : ℝ) ≤ ‖x 1‖ := norm_nonneg _
  have hc1 : Real.cos α ≤ 1 := Real.cos_le_one α
  have hupper : ‖x 0 + (Real.cos α : ℂ) * x 1‖ ≤ ‖x 0‖ + Real.cos α * ‖x 1‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_ofReal_of_nonneg hc]
  have hnn : (0 : ℝ) ≤ ‖x 0‖ + Real.cos α * ‖x 1‖ := add_nonneg ha0 (mul_nonneg hc hb0)
  have hup2 : ‖x 0 + (Real.cos α : ℂ) * x 1‖ ^ 2 ≤ (‖x 0‖ + Real.cos α * ‖x 1‖) ^ 2 := by
    nlinarith [norm_nonneg (x 0 + (Real.cos α : ℂ) * x 1)]
  have hsin : ‖(Real.sin α : ℂ) * x 1‖ ^ 2 = Real.sin α ^ 2 * ‖x 1‖ ^ 2 := by
    rw [norm_mul, mul_pow, norm_ofReal_sq]
  have hpyth : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
    have h := Real.sin_sq_add_cos_sq α
    linarith
  rw [apertureBlock_norm_sq, euclid2_norm_sq, hsin, hpyth]
  nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖), hc, hc1, ha0, hb0, hup2]

theorem norm_apertureBlock_le (α : ℝ) (hc : 0 ≤ Real.cos α) :
    ‖apertureBlock α‖ ≤ Real.sqrt 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2) fun x => ?_
  have hsq := apertureBlock_norm_sq_le α hc x
  have h2 : (Real.sqrt 2 * ‖x‖) ^ 2 = 2 * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [norm_nonneg (apertureBlock α x),
    mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg x)]

/-- **The block is bounded below by its least squared singular value `1 − cos α`.** -/
theorem apertureBlock_norm_sq_ge (α : ℝ) (hc : 0 ≤ Real.cos α) (x : EuclideanSpace ℂ (Fin 2)) :
    (1 - Real.cos α) * ‖x‖ ^ 2 ≤ ‖apertureBlock α x‖ ^ 2 := by
  have ha0 : (0 : ℝ) ≤ ‖x 0‖ := norm_nonneg _
  have hb0 : (0 : ℝ) ≤ ‖x 1‖ := norm_nonneg _
  have habs : |‖x 0‖ - Real.cos α * ‖x 1‖| ≤ ‖x 0 + (Real.cos α : ℂ) * x 1‖ := by
    have h := abs_norm_sub_norm_le (x 0) (-((Real.cos α : ℂ) * x 1))
    rw [sub_neg_eq_add, norm_neg, norm_mul, norm_ofReal_of_nonneg hc] at h
    exact h
  have hlow2 : (‖x 0‖ - Real.cos α * ‖x 1‖) ^ 2 ≤ ‖x 0 + (Real.cos α : ℂ) * x 1‖ ^ 2 := by
    have h0 : (0 : ℝ) ≤ |‖x 0‖ - Real.cos α * ‖x 1‖| := abs_nonneg _
    nlinarith [sq_abs (‖x 0‖ - Real.cos α * ‖x 1‖)]
  have hsin : ‖(Real.sin α : ℂ) * x 1‖ ^ 2 = Real.sin α ^ 2 * ‖x 1‖ ^ 2 := by
    rw [norm_mul, mul_pow, norm_ofReal_sq]
  have hpyth : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
    have h := Real.sin_sq_add_cos_sq α
    linarith
  rw [apertureBlock_norm_sq, euclid2_norm_sq, hsin, hpyth]
  nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖), hc, ha0, hb0, hlow2]

theorem one_sub_cos_pos (α : ℝ) (hs : Real.sin α ≠ 0) : 0 < 1 - Real.cos α := by
  rcases lt_or_eq_of_le (Real.cos_le_one α) with h | h
  · linarith
  · exfalso
    have hsc := Real.sin_sq_add_cos_sq α
    rw [h] at hsc
    have hz : Real.sin α ^ 2 = 0 := by nlinarith
    exact hs (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz)

theorem apertureBlock_injective (α : ℝ) (hs : Real.sin α ≠ 0) (hc : 0 ≤ Real.cos α) :
    Function.Injective (apertureBlock α) := by
  have hpos : 0 < 1 - Real.cos α := one_sub_cos_pos α hs
  intro x y hxy
  have hzero : apertureBlock α (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h := apertureBlock_norm_sq_ge α hc (x - y)
  rw [hzero, norm_zero] at h
  norm_num at h
  have hnn : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hsq : ‖x - y‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖x - y‖, hpos]
  have hz : ‖x - y‖ ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  have hzz : ‖x - y‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
  exact sub_eq_zero.mp (norm_eq_zero.mp hzz)

theorem apertureBlock_surjective (α : ℝ) (hs : Real.sin α ≠ 0) (hc : 0 ≤ Real.cos α) :
    Function.Surjective (apertureBlock α) := by
  have hinj : Function.Injective (apertureBlock α) := apertureBlock_injective α hs hc
  exact (LinearMap.injective_iff_surjective
    (f := (apertureBlock α : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)))).mp hinj

end CofinalWall

end GaloisForLFunctions.HTGeometry
