import GaloisForLFunctions.RHTower.DeningerStageDeRham
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The period of the logarithmic differential

The logarithmic differential of a coordinate has period `2πi` around the unit circle, so it is not
the derivative of any holomorphic function on the punctured plane: a primitive would have constant
derivative `i` along the circle and would therefore fail to return to its value after a full turn.
Hence the first cohomology of a one-dimensional character stage does not vanish and `d log z`
represents a nonzero class, the first case of the identification of the cohomology of a character
stage with the exterior algebra on the lattice.

* `deningerCircleDeriv` : a primitive of `z⁻¹` has derivative `i` along the unit circle.
* `deningerDlog_not_exact` : no holomorphic function on `ℂ^×` has derivative `z⁻¹`.
-/

namespace RHTower

section Period

/-- The unit circle traversed once, as a curve in the punctured plane. -/
noncomputable def deningerCircle (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

theorem deningerCircle_ne_zero (θ : ℝ) : deningerCircle θ ≠ 0 := Complex.exp_ne_zero _

theorem deningerCircle_zero : deningerCircle 0 = 1 := by
  simp [deningerCircle]

theorem deningerCircle_two_pi : deningerCircle (2 * Real.pi) = 1 := by
  have h : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [deningerCircle, h, Complex.exp_two_pi_mul_I]

/-- The derivative of the coordinate embedding of the reals in the complex numbers. -/
theorem deningerOfReal_hasDerivAt (t : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
  have h := Complex.ofRealCLM.hasDerivAt (x := t)
  rw [Complex.ofRealCLM_apply, Complex.ofReal_one] at h
  exact h

/-- **The unit circle is a holomorphic curve** with derivative `i` times the point. -/
theorem deningerCircle_hasDerivAt (θ : ℝ) :
    HasDerivAt deningerCircle (deningerCircle θ * Complex.I) θ := by
  have h1 := deningerOfReal_hasDerivAt θ
  have h2 : HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.I) Complex.I θ := by
    have h := h1.mul_const Complex.I
    rw [one_mul] at h
    exact h
  exact HasDerivAt.cexp h2

/-- **A primitive of the logarithmic differential has constant derivative `i` along the unit
circle.** -/
theorem deningerCircleDeriv {f : ℂ → ℂ} (hf : ∀ z : ℂ, z ≠ 0 → HasDerivAt f z⁻¹ z) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => f (deningerCircle t)) Complex.I θ := by
  have hcurve := deningerCircle_hasDerivAt θ
  have hfd : HasFDerivAt f
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deningerCircle θ)⁻¹) (deningerCircle θ) :=
    (hf _ (deningerCircle_ne_zero θ)).hasFDerivAt
  have hcomp := (hfd.restrictScalars ℝ).comp_hasDerivAt θ hcurve
  have hval : (ContinuousLinearMap.restrictScalars ℝ
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deningerCircle θ)⁻¹))
        (deningerCircle θ * Complex.I) = Complex.I := by
    show (deningerCircle θ * Complex.I) * (deningerCircle θ)⁻¹ = Complex.I
    field_simp
    exact div_self (deningerCircle_ne_zero θ)
  rw [hval] at hcomp
  exact hcomp

/-- The derivative of the linear function `t ↦ i t` on the reals. -/
theorem deningerLinearI_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ)) Complex.I t := by
  have h := Complex.ofRealCLM.hasDerivAt (x := t)
  rw [Complex.ofRealCLM_apply, Complex.ofReal_one] at h
  have h2 := h.const_mul Complex.I
  rw [mul_one] at h2
  exact h2

/-- **The logarithmic differential is not exact**: no holomorphic function on the punctured plane
has derivative `z⁻¹`, because a primitive would grow by the period `2πi` along the unit circle. -/
theorem deningerDlog_not_exact : ¬ ∃ f : ℂ → ℂ, ∀ z : ℂ, z ≠ 0 → HasDerivAt f z⁻¹ z := by
  rintro ⟨f, hf⟩
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => f (deningerCircle t) - Complex.I * (t : ℂ)) 0 t := by
    intro t
    have h := (deningerCircleDeriv hf t).sub (deningerLinearI_hasDerivAt t)
    rw [sub_self] at h
    exact h
  have hconst := is_const_of_deriv_eq_zero (f := fun t : ℝ =>
      f (deningerCircle t) - Complex.I * (t : ℂ))
    (fun t => (hderiv t).differentiableAt) (fun t => (hderiv t).deriv) (2 * Real.pi) 0
  have hper : deningerCircle (2 * Real.pi) = deningerCircle 0 := by
    rw [deningerCircle_two_pi, deningerCircle_zero]
  rw [hper] at hconst
  simp only [Complex.ofReal_zero, mul_zero, sub_zero] at hconst
  have hzero : Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 0 := sub_eq_self.mp hconst
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  exact (mul_ne_zero Complex.I_ne_zero hpi) hzero

end Period

end RHTower

namespace RHTower

section FormPeriod

/-- **The logarithmic differential is not an exterior derivative on the stage**: on the
one-dimensional character stage `ℂ^×` the closed form `d log z` is not exact, so the first
cohomology of a character stage does not vanish and `d log P(a)` carries a nonzero class. -/
theorem deningerDlogForm_not_exact :
    ¬ ∃ h : DeningerStageForm 1 0, DeningerIsHolomorphicForm h ∧
      ∀ z ∈ deningerStageTorus 1, extDeriv h z = deningerDlogForm 1 0 z := by
  rintro ⟨h, hholo, hd⟩
  refine deningerDlog_not_exact ⟨fun w => h (fun _ => w) (fun i : Fin 0 => i.elim0), ?_⟩
  intro w hw
  have hz : (fun _ : Fin 1 => w) ∈ deningerStageTorus 1 := fun _ => hw
  have hdiff : DifferentiableAt ℂ h (fun _ : Fin 1 => w) := (hholo _ hz).differentiableAt
  have hempty : ∀ w₀ w₁ : Fin 0 → (Fin 1 → ℂ), w₀ = w₁ := fun _ _ => funext fun i => i.elim0
  have hval : extDeriv h (fun _ : Fin 1 => w) (fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℂ)) =
      fderiv ℂ (fun y => h y (fun i : Fin 0 => i.elim0)) (fun _ : Fin 1 => w)
        (fun _ : Fin 1 => (1 : ℂ)) := by
    rw [extDeriv_apply hdiff]
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · rw [hempty (Fin.removeNth 0 fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℂ))
        (fun i : Fin 0 => i.elim0)]
      simp
    · intro b _ hb
      exact absurd (Subsingleton.elim b 0) hb
    · intro hb
      exact absurd (Finset.mem_univ (0 : Fin 1)) hb
  have hinv : fderiv ℂ (fun y => h y (fun i : Fin 0 => i.elim0)) (fun _ : Fin 1 => w)
      (fun _ : Fin 1 => (1 : ℂ)) = w⁻¹ := by
    rw [← hval, hd _ hz]
    simp [deningerDlogForm_apply]
  set ι : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℂ ℂ
    with hι
  have hHdiff : DifferentiableAt ℂ (fun y => h y (fun i : Fin 0 => i.elim0))
      (fun _ : Fin 1 => w) :=
    hdiff.continuousAlternatingMap_apply fun i : Fin 0 => i.elim0
  have hH : HasFDerivAt (fun y => h y (fun i : Fin 0 => i.elim0))
      (fderiv ℂ (fun y => h y (fun i : Fin 0 => i.elim0)) (fun _ : Fin 1 => w))
      (fun _ : Fin 1 => w) := hHdiff.hasFDerivAt
  have hcomp := HasFDerivAt.comp w hH ι.hasFDerivAt
  have hres := hcomp.hasDerivAt
  rw [show ((fderiv ℂ (fun y => h y (fun i : Fin 0 => i.elim0)) (fun _ : Fin 1 => w)).comp ι) 1
      = w⁻¹ from hinv] at hres
  exact hres

end FormPeriod

end RHTower
