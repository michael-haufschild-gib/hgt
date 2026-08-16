import GaloisForLFunctions.RHTower.ProlateTailIntegralBound

/-!
# The Gaussian target and the two transfer inputs for the profile integral

The growing-window transfer needs three inputs at the prolate family: convergence of the integral
over every fixed window, convergence of the window values to the target, and smallness of the tails.
This file supplies the first two in the form the family provides them, plus the reflection that
turns the right tail bound into the left one.

* `integral_gaussianProfile` : `∫_ℝ e^{−x²/2} = √(2π)`, the target value.
* `tendsto_intervalIntegral_gaussianProfile` : the window values converge to it.
* `tendsto_intervalIntegral_of_window_dist` : uniform closeness on a window transfers to the
  integrals over that window.
* `intervalIntegral_neg_of_even` : for an even integrand the left tail equals the right tail.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The Gaussian target -/

theorem gaussianProfile_eq (x : ℝ) : gaussianProfile x = Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  rw [gaussianProfile]
  ring_nf

theorem integrable_gaussianProfile : Integrable gaussianProfile volume := by
  have h := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  refine h.congr ?_
  filter_upwards with x
  exact (gaussianProfile_eq x).symm

/-- **The total mass of the Gaussian profile.** -/
theorem integral_gaussianProfile : (∫ x : ℝ, gaussianProfile x) = Real.sqrt (2 * Real.pi) := by
  have hfun : (fun x : ℝ => gaussianProfile x) = fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    funext x
    exact gaussianProfile_eq x
  rw [hfun, integral_gaussian]
  congr 1
  ring

/-- **The symmetric windows exhaust the Gaussian mass.** -/
theorem tendsto_intervalIntegral_gaussianProfile :
    Tendsto (fun K : ℝ => ∫ x in (-K)..K, gaussianProfile x) atTop
      (𝓝 (Real.sqrt (2 * Real.pi))) := by
  have h := intervalIntegral_tendsto_integral (μ := volume) (l := (atTop : Filter ℝ))
    (a := fun K : ℝ => -K) (b := fun K : ℝ => K) integrable_gaussianProfile
    tendsto_neg_atTop_atBot tendsto_id
  rwa [integral_gaussianProfile] at h

/-! ## Uniform closeness on a window transfers to the integrals -/

/-- **Window transfer.**  A family that is uniformly close to a fixed continuous function on a
symmetric window has integrals over that window converging to the integral of the limit. -/
theorem tendsto_intervalIntegral_of_window_dist {ι : Type*} {L : Filter ι}
    {u : ι → ℝ → ℝ} {v : ℝ → ℝ} {K : ℝ} {E : ι → ℝ} (hK : 0 ≤ K)
    (hcont : ∀ i, Continuous (u i)) (hvc : Continuous v)
    (hdist : ∀ i, ∀ x ∈ uIoc (-K) K, |u i x - v x| ≤ E i)
    (hE : Tendsto E L (𝓝 0)) :
    Tendsto (fun i => ∫ x in (-K)..K, u i x) L (𝓝 (∫ x in (-K)..K, v x)) := by
  have hbound : ∀ i, ‖(∫ x in (-K)..K, u i x) - ∫ x in (-K)..K, v x‖ ≤ E i * (2 * K) := by
    intro i
    have hsub : (∫ x in (-K)..K, u i x) - ∫ x in (-K)..K, v x
        = ∫ x in (-K)..K, (u i x - v x) := by
      rw [intervalIntegral.integral_sub ((hcont i).intervalIntegrable _ _)
        (hvc.intervalIntegrable _ _)]
    rw [hsub]
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => u i x - v x) (a := -K) (b := K) (C := E i)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hdist i x hx)
    have habs : |K - -K| = 2 * K := by
      rw [show K - -K = 2 * K by ring, abs_of_nonneg (by linarith)]
    rwa [habs] at hle
  have hzero : Tendsto (fun i => E i * (2 * K)) L (𝓝 0) := by
    have := hE.mul_const (2 * K)
    simpa using this
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  refine squeeze_zero_norm (fun i => ?_) hzero
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, dist_eq_norm]
  exact hbound i

/-! ## Reflection -/

/-- For an even integrand the left tail equals the right tail. -/
theorem intervalIntegral_neg_of_even {f : ℝ → ℝ} (hf : Function.Even f) (K R : ℝ) :
    (∫ x in (-R)..(-K), f x) = ∫ x in K..R, f x := by
  have h := intervalIntegral.integral_comp_neg (a := K) (b := R) f
  rw [show (fun x : ℝ => f (-x)) = f from funext fun x => hf x] at h
  exact h.symm

end GaloisForLFunctions.RHTower

end
