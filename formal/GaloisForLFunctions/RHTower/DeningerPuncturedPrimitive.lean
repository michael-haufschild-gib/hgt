import GaloisForLFunctions.RHTower.DeningerDlogPeriod
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Primitives on the punctured plane

A holomorphic function on the punctured plane whose period around the unit circle vanishes has a
primitive.  The construction pulls the function back along the exponential, where the plane is
convex and Morera's theorem gives a primitive; the period is exactly the increment of that primitive
over one period of the exponential, so it vanishes precisely when the primitive descends.  Every
holomorphic function on the punctured plane therefore differs from a multiple of `z⁻¹` by a
derivative, and the multiple is its period divided by `2πi`.

* `deningerPuncturedPeriod` : the period around the unit circle.
* `deningerExists_primitive_of_period_zero` : vanishing period gives a primitive.
* `deningerPuncturedDecomposition` : every holomorphic function on `ℂ^×` is `c z⁻¹` plus an exact
  one.
-/

namespace RHTower

open Complex Filter Topology intervalIntegral

section PuncturedPrimitive

/-- **The period of a function on the punctured plane** around the unit circle. -/
noncomputable def deningerPuncturedPeriod (g : ℂ → ℂ) : ℂ := ∮ z in C(0, 1), g z

variable {g : ℂ → ℂ}

/-- The exponential pullback of a function on the punctured plane, weighted by the exponential, is
entire. -/
theorem deningerExpPullback_differentiable (hg : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z) :
    Differentiable ℂ fun w : ℂ => g (Complex.exp w) * Complex.exp w := by
  intro w
  exact ((hg _ (Complex.exp_ne_zero w)).comp w (Complex.differentiable_exp w)).mul
    (Complex.differentiable_exp w)

/-- The period is the increment of a primitive of the exponential pullback over one period of the
exponential. -/
theorem deningerPeriod_eq_increment (hg : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z)
    {G : ℂ → ℂ} (hG : ∀ w : ℂ, HasDerivAt G (g (Complex.exp w) * Complex.exp w) w) :
    deningerPuncturedPeriod g = G (2 * Real.pi * Complex.I) - G 0 := by
  have hcurve : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I t := by
    intro t
    have h := deningerOfReal_hasDerivAt t
    have h2 := h.mul_const Complex.I
    rw [one_mul] at h2
    exact h2
  have hcomp : ∀ t : ℝ, HasDerivAt (fun t : ℝ => G ((t : ℂ) * Complex.I))
      (Complex.I * (g (Complex.exp ((t : ℂ) * Complex.I)) *
        Complex.exp ((t : ℂ) * Complex.I))) t := by
    intro t
    have h := (hG ((t : ℂ) * Complex.I)).scomp t (hcurve t)
    rw [smul_eq_mul] at h
    exact h
  have hcont : Continuous fun t : ℝ => Complex.I * (g (Complex.exp ((t : ℂ) * Complex.I)) *
      Complex.exp ((t : ℂ) * Complex.I)) := by
    have hdiff := deningerExpPullback_differentiable hg
    have : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
    exact continuous_const.mul (hdiff.continuous.comp this)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => G ((t : ℂ) * Complex.I))
    (f' := fun t : ℝ => Complex.I * (g (Complex.exp ((t : ℂ) * Complex.I)) *
      Complex.exp ((t : ℂ) * Complex.I)))
    (fun t _ => hcomp t) (hcont.intervalIntegrable 0 (2 * Real.pi))
  rw [deningerPuncturedPeriod, circleIntegral]
  have hint : ∀ t : ℝ, deriv (circleMap 0 1) t • g (circleMap 0 1 t) =
      Complex.I * (g (Complex.exp ((t : ℂ) * Complex.I)) * Complex.exp ((t : ℂ) * Complex.I)) := by
    intro t
    have hcm : circleMap 0 1 t = Complex.exp ((t : ℂ) * Complex.I) := by
      simp [circleMap]
    rw [deriv_circleMap, hcm, smul_eq_mul]
    ring
  simp only [hint]
  rw [hFTC]
  norm_num

/-- **A vanishing period gives a primitive on the punctured plane.** -/
theorem deningerExists_primitive_of_period_zero (hg : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z)
    (hper : deningerPuncturedPeriod g = 0) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ, z ≠ 0 → HasDerivAt h (g z) z := by
  obtain ⟨G, hG'⟩ := (deningerExpPullback_differentiable hg).isExactOn_univ
  have hG : ∀ w : ℂ, HasDerivAt G (g (Complex.exp w) * Complex.exp w) w :=
    fun w => hG' w (Set.mem_univ w)
  -- the primitive of the pullback is periodic
  have hFper : ∀ w : ℂ, g (Complex.exp (w + 2 * Real.pi * Complex.I)) *
      Complex.exp (w + 2 * Real.pi * Complex.I) = g (Complex.exp w) * Complex.exp w := by
    intro w
    rw [Complex.exp_periodic w]
  have hdiff : ∀ w : ℂ, HasDerivAt (fun w : ℂ => G (w + 2 * Real.pi * Complex.I) - G w) 0 w := by
    intro w
    have h1 : HasDerivAt (fun w : ℂ => G (w + 2 * Real.pi * Complex.I))
        (g (Complex.exp w) * Complex.exp w) w := by
      have h := (hG (w + 2 * Real.pi * Complex.I)).comp w
        ((hasDerivAt_id w).add_const (2 * Real.pi * Complex.I))
      rw [mul_one, hFper w] at h
      exact h
    have h := h1.sub (hG w)
    rw [sub_self] at h
    exact h
  have hconst : ∀ w : ℂ, G (w + 2 * Real.pi * Complex.I) - G w =
      G (0 + 2 * Real.pi * Complex.I) - G 0 := by
    intro w
    exact is_const_of_deriv_eq_zero (f := fun w : ℂ => G (w + 2 * Real.pi * Complex.I) - G w)
      (fun w => (hdiff w).differentiableAt) (fun w => (hdiff w).deriv) w 0
  have hzero : G (0 + 2 * Real.pi * Complex.I) - G 0 = 0 := by
    rw [zero_add, ← deningerPeriod_eq_increment hg hG, hper]
  have hper' : Function.Periodic G (2 * Real.pi * Complex.I) := by
    intro w
    have := hconst w
    rw [hzero] at this
    exact sub_eq_zero.1 this
  -- functions with the same exponential get the same value
  have hkey : ∀ w₁ w₂ : ℂ, Complex.exp w₁ = Complex.exp w₂ → G w₁ = G w₂ := by
    intro w₁ w₂ h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    rw [hn]
    exact (hper'.int_mul n) w₂
  refine ⟨fun z => G (Complex.log z), fun z₀ hz₀ => ?_⟩
  -- a local branch of the logarithm at `z₀`
  set L : ℂ → ℂ := fun z => Complex.log z₀ + Complex.log (z / z₀) with hL
  have hone : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    norm_num
  have hLderiv : HasDerivAt L z₀⁻¹ z₀ := by
    have hdiv : HasDerivAt (fun z : ℂ => z / z₀) z₀⁻¹ z₀ := by
      have h := (hasDerivAt_id z₀).div_const z₀
      rw [one_div] at h
      exact h
    have hz : z₀ / z₀ = 1 := div_self hz₀
    have hlog : HasDerivAt Complex.log (z₀ / z₀)⁻¹ (z₀ / z₀) := by
      rw [hz]
      exact Complex.hasDerivAt_log hone
    have h : HasDerivAt (Complex.log ∘ fun z : ℂ => z / z₀) ((z₀ / z₀)⁻¹ * z₀⁻¹) z₀ :=
      HasDerivAt.comp z₀ hlog hdiv
    rw [hz, inv_one, one_mul] at h
    exact h.const_add _
  have hLz₀ : L z₀ = Complex.log z₀ := by
    rw [hL]
    simp [div_self hz₀]
  have hGL : HasDerivAt (fun z => G (L z)) (g z₀) z₀ := by
    have h := (hG (L z₀)).comp z₀ hLderiv
    rw [hLz₀, Complex.exp_log hz₀] at h
    rw [show g z₀ * z₀ * z₀⁻¹ = g z₀ by field_simp] at h
    exact h
  refine hGL.congr_of_eventuallyEq ?_
  have hopen : ∀ᶠ z in 𝓝 z₀, z ≠ 0 ∧ z / z₀ ∈ Complex.slitPlane := by
    refine Filter.Eventually.and (eventually_ne_nhds hz₀) ?_
    have hcont : ContinuousAt (fun z : ℂ => z / z₀) z₀ := by fun_prop
    have hval : (fun z : ℂ => z / z₀) z₀ ∈ Complex.slitPlane := by
      show z₀ / z₀ ∈ Complex.slitPlane
      rw [div_self hz₀]
      exact hone
    exact hcont (Complex.isOpen_slitPlane.mem_nhds hval)
  filter_upwards [hopen] with z hz
  refine hkey (Complex.log z) (L z) ?_
  rw [Complex.exp_log hz.1, hL, Complex.exp_add, Complex.exp_log hz₀,
    Complex.exp_log (div_ne_zero hz.1 hz₀)]
  field_simp

/-- **Every holomorphic function on the punctured plane is a multiple of `z⁻¹` plus a
derivative**, the multiple being its period divided by `2πi`.  This is the surjectivity half of the
identification of the first cohomology of a one-dimensional character stage. -/
theorem deningerPuncturedDecomposition (f : ℂ → ℂ)
    (hf : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ f z) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ, z ≠ 0 →
      HasDerivAt h (f z - ((2 * Real.pi * Complex.I)⁻¹ * deningerPuncturedPeriod f) * z⁻¹) z := by
  set c : ℂ := (2 * Real.pi * Complex.I)⁻¹ * deningerPuncturedPeriod f with hc
  have hg : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ (fun z => f z - c * z⁻¹) z := by
    intro z hz
    exact (hf z hz).sub ((differentiableAt_const c).mul (differentiableAt_inv hz))
  have htwopi : (2 * Real.pi * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hinv : deningerPuncturedPeriod (fun z : ℂ => z⁻¹) = 2 * Real.pi * Complex.I := by
    rw [deningerPuncturedPeriod]
    have h := circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (R := (1 : ℝ))
      (w := (0 : ℂ)) (by simp)
    simpa using h
  have hsub : deningerPuncturedPeriod (fun z => f z - c * z⁻¹) = 0 := by
    have hfint : CircleIntegrable f 0 1 := by
      refine ContinuousOn.circleIntegrable (by norm_num) ?_
      intro z hz
      have hz0 : z ≠ 0 := by
        intro h
        rw [h] at hz
        simp at hz
      exact ((hf z hz0).continuousAt).continuousWithinAt
    have hiint : CircleIntegrable (fun z : ℂ => c * z⁻¹) 0 1 := by
      refine ContinuousOn.circleIntegrable (by norm_num) ?_
      intro z hz
      have hz0 : z ≠ 0 := by
        intro h
        rw [h] at hz
        simp at hz
      exact (continuousAt_const.mul (continuousAt_inv₀ hz0)).continuousWithinAt
    have hsmul : (∮ z in C(0, 1), c * z⁻¹) = c * ∮ z in C(0, 1), z⁻¹ := by
      simp
    rw [deningerPuncturedPeriod, circleIntegral.integral_sub hfint hiint, hsmul,
      show (∮ z in C(0, 1), z⁻¹) = deningerPuncturedPeriod (fun z : ℂ => z⁻¹) from rfl, hinv, hc]
    field_simp
    exact sub_self _
  exact deningerExists_primitive_of_period_zero hg hsub

end PuncturedPrimitive

end RHTower
