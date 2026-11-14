import GaloisForLFunctions.HTGeometry.LinearSystems.ExponentialBlockPropagation

/-!
# First-order solution operators and a rank-one boundary correction

Every continuous forcing has a unique global solution of `u' = lam u + f`
with any prescribed initial value. For negative real `lam` and positive
interval length, matching the two endpoint values also has a unique
solution. Its difference from causal convolution is one exponential times
one linear boundary state.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Variation of constants with prescribed initial value. -/
def modalInitialSolution (lam : ℂ) (f : C(ℝ, ℂ)) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (lam * (t : ℂ)) * z + exponentialBlock lam f 0 t

theorem modalInitialSolution_zero (lam : ℂ) (f : C(ℝ, ℂ)) (z : ℂ) :
    modalInitialSolution lam f z 0 = z := by
  simp [modalInitialSolution, exponentialBlock]

/-- With the same forcing, all initial-state error follows the homogeneous mode. -/
theorem modalInitialSolution_sub (lam : ℂ) (f : C(ℝ, ℂ)) (z w : ℂ) (t : ℝ) :
    modalInitialSolution lam f z t - modalInitialSolution lam f w t =
      Complex.exp (lam * (t : ℂ)) * (z - w) := by
  simp only [modalInitialSolution]
  ring

/-- Stable modes forget initial-state error at an exact exponential rate. -/
theorem norm_stableInitialSolution_sub (α : ℝ) (f : C(ℝ, ℂ)) (z w : ℂ) (t : ℝ) :
    ‖modalInitialSolution (-(Real.exp α : ℂ)) f z t -
      modalInitialSolution (-(Real.exp α : ℂ)) f w t‖ =
      Real.exp (-Real.exp α * t) * ‖z - w‖ := by
  rw [modalInitialSolution_sub, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, mul_zero, sub_zero]

/-- The constructed response solves the differential equation at every real time. -/
theorem hasDerivAt_modalInitialSolution (lam : ℂ) (f : C(ℝ, ℂ)) (z : ℂ) (t : ℝ) :
    HasDerivAt (modalInitialSolution lam f z)
      (lam * modalInitialSolution lam f z t + f t) t := by
  apply (((hasDerivAt_cexp_const_mul lam t).mul_const z).add
    (hasDerivAt_exponentialBlock lam f 0 t)).congr_deriv
  dsimp only [modalInitialSolution]
  ring

/-- Every continuous forcing and prescribed initial value determine a unique global solution. -/
theorem existsUnique_modalInitialSolution (lam : ℂ) (f : C(ℝ, ℂ)) (z : ℂ) :
    ∃! u : ℝ → ℂ, u 0 = z ∧ ∀ t, HasDerivAt u (lam * u t + f t) t := by
  refine ⟨modalInitialSolution lam f z,
    ⟨modalInitialSolution_zero lam f z, hasDerivAt_modalInitialSolution lam f z⟩, ?_⟩
  intro u hu
  let v := modalInitialSolution lam f z
  let g := fun t : ℝ => (u t - v t) * Complex.exp (-lam * (t : ℂ))
  have hd (t : ℝ) : HasDerivAt g 0 t := by
    have h := ((hu.2 t).sub (hasDerivAt_modalInitialSolution lam f z t)).mul
      (hasDerivAt_cexp_const_mul (-lam) t)
    apply h.congr_deriv
    simp only [Pi.sub_apply]
    ring
  have hg (t : ℝ) : g t = 0 := by
    have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) t 0
    simpa [g, v, hu.1, modalInitialSolution_zero] using h
  funext t
  exact sub_eq_zero.mp ((mul_eq_zero.mp (hg t)).resolve_right (Complex.exp_ne_zero _))

/-- Positive decay and positive length make the endpoint matching equation invertible. -/
theorem stableEndpoint_denominator_ne_zero (α τ : ℝ) :
    1 - Complex.exp (-(Real.exp α : ℂ) * (Real.exp τ : ℂ)) ≠ 0 := by
  have hnorm : ‖Complex.exp (-(Real.exp α : ℂ) * (Real.exp τ : ℂ))‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, neg_zero, mul_zero, sub_zero]
    simpa only [neg_mul] using
      neg_lt_zero.mpr (mul_pos (Real.exp_pos α) (Real.exp_pos τ))
  intro h
  have heq := sub_eq_zero.mp h
  rw [← heq, norm_one] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

/-- The single state needed to impose equal endpoint values. -/
def stableEndpointState (α τ : ℝ) (f : C(ℝ, ℂ)) : ℂ :=
  exponentialBlock (-(Real.exp α : ℂ)) f 0 (Real.exp τ) /
    (1 - Complex.exp (-(Real.exp α : ℂ) * (Real.exp τ : ℂ)))

/-- Causal convolution corrected by one exponential boundary mode. -/
def stableEndpointSolution (α τ : ℝ) (f : C(ℝ, ℂ)) : ℝ → ℂ :=
  modalInitialSolution (-(Real.exp α : ℂ)) f (stableEndpointState α τ f)

/-- The constructed solution has equal values at both endpoints. -/
theorem stableEndpointSolution_boundary (α τ : ℝ) (f : C(ℝ, ℂ)) :
    stableEndpointSolution α τ f (Real.exp τ) = stableEndpointSolution α τ f 0 := by
  unfold stableEndpointSolution
  rw [modalInitialSolution_zero]
  unfold modalInitialSolution stableEndpointState
  have hcancel := div_mul_cancel₀
    (exponentialBlock (-(Real.exp α : ℂ)) f 0 (Real.exp τ))
    (stableEndpoint_denominator_ne_zero α τ)
  linear_combination -hcancel

/-- The endpoint-corrected response solves the forced equation. -/
theorem hasDerivAt_stableEndpointSolution (α τ : ℝ) (f : C(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (stableEndpointSolution α τ f)
      (-(Real.exp α : ℂ) * stableEndpointSolution α τ f t + f t) t :=
  hasDerivAt_modalInitialSolution _ _ _ _

/-- The endpoint problem is well posed for every continuous forcing. -/
theorem existsUnique_stableEndpointSolution (α τ : ℝ) (f : C(ℝ, ℂ)) :
    ∃! u : ℝ → ℂ, u (Real.exp τ) = u 0 ∧
      ∀ t, HasDerivAt u (-(Real.exp α : ℂ) * u t + f t) t := by
  refine ⟨stableEndpointSolution α τ f,
    ⟨stableEndpointSolution_boundary α τ f, hasDerivAt_stableEndpointSolution α τ f⟩, ?_⟩
  intro u hu
  have hform : u = modalInitialSolution (-(Real.exp α : ℂ)) f (u 0) :=
    (existsUnique_modalInitialSolution (-(Real.exp α : ℂ)) f (u 0)).unique
      ⟨rfl, hu.2⟩ ⟨modalInitialSolution_zero _ _ _, hasDerivAt_modalInitialSolution _ _ _⟩
  have hstate : u 0 = stableEndpointState α τ f := by
    have hb := hu.1
    conv_lhs at hb => rw [hform]
    change Complex.exp (-(Real.exp α : ℂ) * (Real.exp τ : ℂ)) * u 0 +
      exponentialBlock (-(Real.exp α : ℂ)) f 0 (Real.exp τ) = u 0 at hb
    unfold stableEndpointState
    apply (eq_div_iff (stableEndpoint_denominator_ne_zero α τ)).mpr
    linear_combination -hb
  rw [hform, hstate]
  rfl

/-- Every boundary correction belongs to the same one-dimensional exponential space. -/
theorem stableEndpointSolution_sub_causal_mem_span (α τ : ℝ) (f : C(ℝ, ℂ)) :
    (fun t => stableEndpointSolution α τ f t -
      causalConv (fun s => Complex.exp (-(Real.exp α : ℂ) * (s : ℂ))) f t) ∈
      Submodule.span ℂ {fun t : ℝ => Complex.exp (-(Real.exp α : ℂ) * (t : ℂ))} := by
  have h : (fun t => stableEndpointSolution α τ f t -
      causalConv (fun s => Complex.exp (-(Real.exp α : ℂ) * (s : ℂ))) f t) =
      stableEndpointState α τ f •
        (fun t : ℝ => Complex.exp (-(Real.exp α : ℂ) * (t : ℂ))) := by
    funext t
    simp only [stableEndpointSolution, modalInitialSolution,
      exponentialBlock_zero_eq_causalConv, add_sub_cancel_right, Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- Constant forcing realizes every possible endpoint state. -/
theorem stableEndpointState_const (α τ : ℝ) (z : ℂ) :
    stableEndpointState α τ (ContinuousMap.const ℝ ((Real.exp α : ℂ) * z)) = z := by
  let f := ContinuousMap.const ℝ ((Real.exp α : ℂ) * z)
  have hc : ∀ t : ℝ, HasDerivAt (fun _ : ℝ => z)
      (-(Real.exp α : ℂ) * z + f t) t := by
    intro t
    apply (hasDerivAt_const t z).congr_deriv
    dsimp only [f, ContinuousMap.const_apply]
    ring
  have hu : stableEndpointSolution α τ f = fun _ : ℝ => z :=
    (existsUnique_stableEndpointSolution α τ f).unique
      ⟨stableEndpointSolution_boundary α τ f, hasDerivAt_stableEndpointSolution α τ f⟩
      ⟨rfl, hc⟩
  simpa only [stableEndpointSolution, modalInitialSolution_zero] using congrFun hu 0

/-- The boundary corrections fill exactly one exponential direction. -/
theorem range_stableEndpointCorrection (α τ : ℝ) :
    Set.range (fun f : C(ℝ, ℂ) => fun t => stableEndpointSolution α τ f t -
      causalConv (fun s => Complex.exp (-(Real.exp α : ℂ) * (s : ℂ))) f t) =
      (Submodule.span ℂ {fun t : ℝ => Complex.exp (-(Real.exp α : ℂ) * (t : ℂ))} :
        Set (ℝ → ℂ)) := by
  ext v
  constructor
  · rintro ⟨f, rfl⟩
    exact stableEndpointSolution_sub_causal_mem_span α τ f
  · intro hv
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨ContinuousMap.const ℝ ((Real.exp α : ℂ) * z), ?_⟩
    funext t
    simp only [stableEndpointSolution, modalInitialSolution, stableEndpointState_const,
      exponentialBlock_zero_eq_causalConv, add_sub_cancel_right, Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _

end

end GaloisForLFunctions.HTGeometry
