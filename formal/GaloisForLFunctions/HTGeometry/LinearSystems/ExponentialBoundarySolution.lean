import GaloisForLFunctions.HTGeometry.LinearSystems.ExponentialBlockPropagation

/-!
# First-order solution operators and a rank-one boundary correction

Every continuous forcing has a unique global solution of `u' = λ u + f`
with any prescribed initial value. For negative real `λ` and positive
interval length, matching the two endpoint values also has a unique
solution. Its difference from causal convolution is one exponential times
one linear boundary state.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Variation of constants with prescribed initial value. -/
def modalInitialSolution (λ : ℂ) (f : C(ℝ, ℂ)) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (λ * (t : ℂ)) * z + exponentialBlock λ f 0 t

theorem modalInitialSolution_zero (λ : ℂ) (f : C(ℝ, ℂ)) (z : ℂ) :
    modalInitialSolution λ f z 0 = z := by
  simp [modalInitialSolution, exponentialBlock]

/-- The constructed response solves the differential equation at every real time. -/
theorem hasDerivAt_modalInitialSolution (λ : ℂ) (f : C(ℝ, ℂ)) (z : ℂ) (t : ℝ) :
    HasDerivAt (modalInitialSolution λ f z)
      (λ * modalInitialSolution λ f z t + f t) t := by
  convert ((hasDerivAt_cexp_const_mul λ t).mul_const z).add
    (hasDerivAt_exponentialBlock λ f 0 t) using 1 <;>
    simp only [modalInitialSolution] <;> ring

/-- Existence and uniqueness are proved, with no spectral or solvability premise. -/
theorem existsUnique_modalInitialSolution (λ : ℂ) (f : C(ℝ, ℂ)) (z : ℂ) :
    ∃! u : ℝ → ℂ, u 0 = z ∧ ∀ t, HasDerivAt u (λ * u t + f t) t := by
  refine ⟨modalInitialSolution λ f z,
    ⟨modalInitialSolution_zero λ f z, hasDerivAt_modalInitialSolution λ f z⟩, ?_⟩
  intro u hu
  let v := modalInitialSolution λ f z
  let g := fun t : ℝ => (u t - v t) * Complex.exp (-λ * (t : ℂ))
  have hd (t : ℝ) : HasDerivAt g 0 t := by
    have h := ((hu.2 t).sub (hasDerivAt_modalInitialSolution λ f z t)).mul
      (hasDerivAt_cexp_const_mul (-λ) t)
    convert h using 1 <;> dsimp [g, v] <;> ring
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
  exact sub_ne_zero.mpr (fun h => by simpa [← h] using hnorm)

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
  field_simp [stableEndpoint_denominator_ne_zero α τ]
  ring

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

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.modalInitialSolution_zero
#print axioms GaloisForLFunctions.HTGeometry.hasDerivAt_modalInitialSolution
#print axioms GaloisForLFunctions.HTGeometry.existsUnique_modalInitialSolution
#print axioms GaloisForLFunctions.HTGeometry.stableEndpoint_denominator_ne_zero
#print axioms GaloisForLFunctions.HTGeometry.stableEndpointSolution_boundary
#print axioms GaloisForLFunctions.HTGeometry.hasDerivAt_stableEndpointSolution
#print axioms GaloisForLFunctions.HTGeometry.existsUnique_stableEndpointSolution
#print axioms GaloisForLFunctions.HTGeometry.stableEndpointSolution_sub_causal_mem_span
