import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Even holomorphic functions of the square root

Let `h` be even and holomorphic on the strip `|Im z| < B`.  Then `w ↦ h(w^{1/2})`, with the
principal square root, is holomorphic at every `w` with `|Im w^{1/2}| < B`
(`differentiableAt_comp_sqrtPrincipal`).

Proof.  Off the cut this is the chain rule.  On the negative axis `w < 0` use the other branch
`b(v) = i (−v)^{1/2}`, which is holomorphic at `w` and squares to `v`: then `b(v) = ±v^{1/2}`, and
evenness of `h` gives `h(b(v)) = h(v^{1/2})`.  At `w = 0` the function is continuous and holomorphic
on a punctured disc, so the singularity is removable.
-/

open Complex Set Filter Topology Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The principal square root `w^{1/2}`. -/
def sqrtPrincipal (w : ℂ) : ℂ := w ^ (1 / 2 : ℂ)

theorem sqrtPrincipal_sq (w : ℂ) : sqrtPrincipal w ^ 2 = w := by
  unfold sqrtPrincipal; rw [one_div]; exact Complex.cpow_ofNat_inv_pow w 2

theorem norm_sqrtPrincipal (w : ℂ) : ‖sqrtPrincipal w‖ = Real.sqrt ‖w‖ := by
  have h := congrArg norm (sqrtPrincipal_sq w)
  rw [norm_pow] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem sqrtPrincipal_zero : sqrtPrincipal 0 = 0 := by
  unfold sqrtPrincipal; exact Complex.zero_cpow (by norm_num)

/-- `h(v^{1/2}) = h(i (−v)^{1/2})` for even `h`. -/
theorem comp_sqrtPrincipal_eq_comp_otherBranch {h : ℂ → ℂ} (heven : ∀ z, h (-z) = h z) (v : ℂ) :
    h (sqrtPrincipal v) = h (I * sqrtPrincipal (-v)) := by
  have h1 : (I * sqrtPrincipal (-v)) ^ 2 = sqrtPrincipal v ^ 2 := by
    rw [mul_pow, sqrtPrincipal_sq, sqrtPrincipal_sq, Complex.I_sq]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
  · rw [h2]
  · rw [h2, heven]

theorem abs_im_otherBranch (v : ℂ) : |(I * sqrtPrincipal (-v)).im| = |(sqrtPrincipal v).im| := by
  have h1 : (I * sqrtPrincipal (-v)) ^ 2 = sqrtPrincipal v ^ 2 := by
    rw [mul_pow, sqrtPrincipal_sq, sqrtPrincipal_sq, Complex.I_sq]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
  · rw [h2]
  · rw [h2, Complex.neg_im, abs_neg]

theorem differentiableAt_comp_sqrtPrincipal_of_ne {h : ℂ → ℂ} {B : ℝ} (heven : ∀ z, h (-z) = h z)
    (hh : ∀ z : ℂ, |z.im| < B → DifferentiableAt ℂ h z) {w : ℂ} (hw0 : w ≠ 0)
    (hw : |(sqrtPrincipal w).im| < B) : DifferentiableAt ℂ (fun v => h (sqrtPrincipal v)) w := by
  by_cases hs : w ∈ slitPlane
  · exact (hh _ hw).comp w (differentiableAt_id.cpow_const hs)
  · have hneg : -w ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hs ⊢
      push Not at hs
      obtain ⟨hre, him⟩ := hs
      left
      rw [Complex.neg_re]
      rcases lt_or_eq_of_le hre with hlt | heq
      · linarith
      · exact absurd (Complex.ext (by simpa using heq) (by simpa using him)) hw0
    have hfun : (fun v => h (sqrtPrincipal v)) = fun v => h (I * sqrtPrincipal (-v)) :=
      funext (comp_sqrtPrincipal_eq_comp_otherBranch heven)
    rw [hfun]
    have hd : DifferentiableAt ℂ (fun v => I * sqrtPrincipal (-v)) w := by
      unfold sqrtPrincipal
      exact (differentiableAt_neg_iff.mpr differentiableAt_id |>.cpow_const hneg).const_mul I
    have him : |(I * sqrtPrincipal (-w)).im| < B := by rw [abs_im_otherBranch]; exact hw
    exact (hh _ him).comp w hd

/-- **Even holomorphic functions are holomorphic in `z²`.** -/
theorem differentiableAt_comp_sqrtPrincipal {h : ℂ → ℂ} {B : ℝ} (heven : ∀ z, h (-z) = h z)
    (hh : ∀ z : ℂ, |z.im| < B → DifferentiableAt ℂ h z) {w : ℂ} (hw : |(sqrtPrincipal w).im| < B) :
    DifferentiableAt ℂ (fun v => h (sqrtPrincipal v)) w := by
  by_cases hw0 : w = 0
  · subst hw0
    have hB : 0 < B := by rw [sqrtPrincipal_zero, Complex.zero_im, abs_zero] at hw; exact hw
    have hball : ball (0 : ℂ) (B ^ 2) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ (by positivity)
    have hon : DifferentiableOn ℂ (fun v => h (sqrtPrincipal v)) (ball (0 : ℂ) (B ^ 2) \ {0}) := by
      intro v hv
      refine (differentiableAt_comp_sqrtPrincipal_of_ne heven hh hv.2 ?_).differentiableWithinAt
      have hv1 : ‖v‖ < B ^ 2 := by simpa using hv.1
      calc |(sqrtPrincipal v).im| ≤ ‖sqrtPrincipal v‖ := Complex.abs_im_le_norm _
        _ = Real.sqrt ‖v‖ := norm_sqrtPrincipal v
        _ < B := by
            rw [Real.sqrt_lt' hB]; exact hv1
    have hcont : ContinuousAt (fun v => h (sqrtPrincipal v)) 0 := by
      have h1 : ContinuousAt sqrtPrincipal 0 := by
        have := (Complex.continuousAt_cpow_zero_of_re_pos (z := (1 / 2 : ℂ)) (by norm_num)).comp
          (f := fun v : ℂ => (v, (1 / 2 : ℂ))) (by fun_prop)
        have e : sqrtPrincipal = fun x : ℂ => x ^ (2 : ℂ)⁻¹ := by
          funext x; unfold sqrtPrincipal; rw [one_div]
        rw [e]
        simpa [Function.comp_def] using this
      have h2 : ContinuousAt h (sqrtPrincipal 0) := (hh _ hw).continuousAt
      exact h2.comp h1
    exact ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff hball).mp
      ⟨hon, hcont⟩).differentiableAt hball
  · exact differentiableAt_comp_sqrtPrincipal_of_ne heven hh hw0 hw

end GaloisForLFunctions.HTGeometry
