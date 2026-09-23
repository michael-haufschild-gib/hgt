import GaloisForLFunctions.HTGeometry.NevBDWronskianLimit
import GaloisForLFunctions.HTGeometry.EntryUniformLimit

/-!
# Continuity of the kernel with one argument fixed

With one argument held fixed the kernel series is a bilinear series of the kind the uniform estimate
covers directly, so its partial sums — polynomials — converge to it uniformly on balls and the limit
is continuous.  This is the easy case; the diagonal needed the tunable estimate.
-/

open scoped BigOperators
open Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

theorem kernelInf_comm (s : ℕ → ℝ) (x y : ℝ) : kernelInf s x y = kernelInf s y x := by
  rw [kernelInf, kernelInf]
  exact tsum_congr fun k => by ring

/-- The complex bilinear kernel with the first argument fixed at a real point. -/
theorem ofReal_kernelInf (s : ℕ → ℝ) (ξ x : ℝ) :
    ((kernelInf s ξ x : ℝ) : ℂ)
      = ∑' k, monicOrthoC s k ((ξ : ℝ) : ℂ) * monicOrthoC s k ((x : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
  rw [kernelInf, ofReal_bilinear_tsum]
  exact tsum_congr fun k => by rw [monicOrthoC_ofReal, monicOrthoC_ofReal]

/-- **The kernel with one argument fixed is continuous.** -/
theorem continuousOn_kernelC (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (ξ : ℂ)
    (r : ℝ) :
    ContinuousOn (fun z => ∑' k, monicOrthoC s k ξ * monicOrthoC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) (Metric.ball 0 r) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  have hf : ∀ N, kernelRoot s (fun j => monicOrthoC s j ξ) N ≤ ballBoundQ s S P ‖ξ‖ :=
    fun N => kernelRoot_le_ballBoundQ h hS hP le_rfl N
  have hG : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ N,
      kernelRoot s (fun j => monicOrthoC s j z) N ≤ ballBoundQ s S P r := by
    intro z hz N
    have hnorm : ‖z‖ ≤ r := by
      have := Metric.mem_ball.mp hz
      rw [dist_zero_right] at this
      exact this.le
    exact kernelRoot_le_ballBoundQ h hS hP hnorm N
  have huni := tendstoUniformlyOn_bilinearLimit (Kg := ballBoundQ s S P r) h
    (fun k => monicOrthoC s k ξ) hf (fun z k => monicOrthoC s k z) (Metric.ball 0 r) hG
  refine huni.continuousOn ((Filter.Eventually.of_forall fun N => ?_).frequently)
  exact (differentiableOn_bilinearPartialSum s _ _
    (fun k => differentiable_monicOrthoC s k) N (Metric.ball 0 r)).continuousOn

/-- **The real kernel with one argument fixed is continuous.** -/
theorem continuousAt_kernelInf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (ξ x₀ : ℝ) : ContinuousAt (fun x : ℝ => kernelInf s x ξ) x₀ := by
  set r : ℝ := |x₀| + 1 with hrdef
  have hmem : ((x₀ : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, hrdef]
    linarith
  have hcont := continuousOn_kernelC h h0b ((ξ : ℝ) : ℂ) r
  have hat := hcont.continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  have hcomp : ContinuousAt (fun x : ℝ =>
      ((∑' k, monicOrthoC s k ((ξ : ℝ) : ℂ) * monicOrthoC s k ((x : ℝ) : ℂ) /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)).re)) x₀ :=
    Complex.continuous_re.continuousAt.comp (hat.comp Complex.continuous_ofReal.continuousAt)
  have hfun : (fun x : ℝ =>
      ((∑' k, monicOrthoC s k ((ξ : ℝ) : ℂ) * monicOrthoC s k ((x : ℝ) : ℂ) /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)).re))
      = fun x : ℝ => kernelInf s x ξ := by
    funext x
    rw [← ofReal_kernelInf, Complex.ofReal_re, kernelInf_comm]
  rwa [hfun] at hcomp

/-- The kernel with one argument fixed is positive near that argument. -/
theorem eventually_kernelInf_pos (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (ξ : ℝ) :
    ∃ η > 0, ∀ x : ℝ, |x - ξ| < η → 0 < kernelInf s x ξ := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  have hb : BoundedKernel s 0 := ⟨S, P, hSpos, hPpos, hS, hP⟩
  have hdiag : 0 < kernelInf s ξ ξ := by
    have hbnd : ∀ N, kernelRoot s (fun j => monicOrthoC s j ((ξ : ℝ) : ℂ)) N
        ≤ ballBoundQ s S P ‖((ξ : ℝ) : ℂ)‖ := fun N => kernelRoot_le_ballBoundQ h hS hP le_rfl N
    have hpos := kernelSum_pos h hbnd
    rw [kernelSum_ofReal] at hpos
    have heq : kernelInf s ξ ξ = ∑' k, ((monicOrtho s k).eval ξ) ^ (2 : ℕ) /
        momentInner s (monicOrtho s k) (monicOrtho s k) := by
      rw [kernelInf]
      exact tsum_congr fun k => by rw [sq]
    rw [heq]
    exact hpos
  have hcont := continuousAt_kernelInf h hb ξ ξ
  have hev : ∀ᶠ x in nhds ξ, 0 < kernelInf s x ξ :=
    hcont.eventually_const_lt hdiag
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hall⟩ := hev
  refine ⟨η, hη, fun x hx => ?_⟩
  exact hall (by rwa [Real.dist_eq])

/-- **The denominator changes sign at every fiber point.**  It is `(x − ξ)` times a factor of
constant sign nearby, so the values at `ξ ± δ` have opposite signs. -/
theorem nevDenominator_opposite_signs (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    {t ξ : ℝ} (hξ : nevBrealInf s ξ * t - nevDrealInf s ξ = 0) :
    ∃ η > 0, ∀ δ : ℝ, 0 < δ → δ < η →
      (nevBrealInf s (ξ - δ) * t - nevDrealInf s (ξ - δ)) *
        (nevBrealInf s (ξ + δ) * t - nevDrealInf s (ξ + δ)) < 0 := by
  obtain ⟨η, hη, hpos⟩ := eventually_kernelInf_pos h h0b ξ
  have hB : nevBrealInf s ξ ≠ 0 := nevBrealInf_ne_zero_of_mem_fiber h h0b hξ
  have hB2 : 0 < nevBrealInf s ξ ^ (2 : ℕ) := by positivity
  have h0v : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  refine ⟨η, hη, fun δ hδ hδη => ?_⟩
  have hplus := nevDenominator_factor_at_fiber h h0b hξ (ξ + δ)
  have hminus := nevDenominator_factor_at_fiber h h0b hξ (ξ - δ)
  have hKp : 0 < kernelInf s (ξ + δ) ξ := hpos _ (by rw [add_sub_cancel_left]; rwa [abs_of_pos hδ])
  have hKm : 0 < kernelInf s (ξ - δ) ξ := by
    refine hpos _ ?_
    have : ξ - δ - ξ = -δ := by ring
    rw [this, abs_neg, abs_of_pos hδ]
    exact hδη
  have hp : 0 < (nevBrealInf s (ξ + δ) * t - nevDrealInf s (ξ + δ)) * nevBrealInf s ξ := by
    rw [hplus, add_sub_cancel_left]
    positivity
  have hm : (nevBrealInf s (ξ - δ) * t - nevDrealInf s (ξ - δ)) * nevBrealInf s ξ < 0 := by
    rw [hminus]
    have hsub : ξ - δ - ξ = -δ := by ring
    rw [hsub]
    nlinarith [hKm, h0v, hδ]
  nlinarith [hp, hm, hB2]

end HTGeometry
