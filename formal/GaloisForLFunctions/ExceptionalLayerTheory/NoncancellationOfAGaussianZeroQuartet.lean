import GaloisForLFunctions.ExceptionalLayerTheory.SeparationOfTwoGaussianModesAtHighObservationHeight

/-!
# Noncancellation of a Gaussian zero quartet

The effective horizontal observation height is L(t) + log(t/2).
At any finite limiting height all fixed modes remain comparable. At
height tending to infinity only the maximal abscissa contributes to
the relative magnitude. An off-line functional-equation quartet then
retains at least the fraction 1 − exp(−π Im ρ/2) in the limit, even if
each term is allowed an independent phase.
-/

noncomputable section
open Complex Filter Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Relative multiplicative calibration also works when the norm ratio
tends to zero, tends to infinity, or oscillates. -/
theorem gaussian_pair_relative_calibration (ρ η : ℂ) (σ : ℝ) (L : ℝ → ℝ) :
    Tendsto (fun t => (gaussianModeNorm ρ σ (L t) t/gaussianModeNorm η σ (L t) t) /
      Real.exp (gaussianPairLogRatio ρ η (L t) t)) atTop (𝓝 1) := by
  have h := (gaussian_pair_log_asymptotic ρ η σ L).rexp
  rw [Real.exp_zero] at h
  apply h.congr'
  filter_upwards [gaussian_mode_eventually_positive ρ σ L,gaussian_mode_eventually_positive η σ L] with t hρ hη
  change Real.exp (_ - _ - _) = _
  rw [Real.exp_sub,Real.exp_sub,Real.exp_log hρ,Real.exp_log hη]

/-- A finite effective height retains both modes, even at different
abscissae. It sets their relative magnitude explicitly. -/
theorem gaussian_pair_at_finite_shifted_height (ρ η : ℂ) (σ : ℝ) (L : ℝ → ℝ) {b : ℝ}
    (hb : Tendsto (fun t => L t+Real.log (t/2)) atTop (𝓝 b)) :
    Tendsto (fun t => gaussianModeNorm ρ σ (L t) t/gaussianModeNorm η σ (L t) t) atTop
      (𝓝 (Real.exp ((ρ.re-η.re)*b/2+Real.pi*(ρ.im-η.im)/4))) := by
  have hp := (((hb.const_mul (ρ.re-η.re)).div_const 2).add_const (Real.pi*(ρ.im-η.im)/4)).rexp
  have h := (gaussian_pair_relative_calibration ρ η σ L).mul hp
  rw [one_mul] at h
  exact h.congr fun t => div_mul_cancel₀ _ (Real.exp_ne_zero _)

/-- Any diverging effective height suppresses every mode strictly to the
left of the reference, including schedules with L(t) tending to −∞. -/
theorem lower_gaussian_mode_disappears {ρ η : ℂ} (hl : ρ.re<η.re) (σ : ℝ) (L : ℝ → ℝ)
    (hL : Tendsto (fun t => L t+Real.log (t/2)) atTop atTop) :
    Tendsto (fun t => gaussianModeNorm ρ σ (L t) t/gaussianModeNorm η σ (L t) t) atTop (𝓝 0) := by
  have hlog : Tendsto (fun t => gaussianPairLogRatio ρ η (L t) t) atTop atBot :=
    tendsto_atBot_add_const_right _ _ (Filter.Tendsto.atBot_div_const (by norm_num : (0:ℝ)<2)
      (hL.const_mul_atTop_of_neg (sub_neg.mpr hl)))
  have h := (gaussian_pair_relative_calibration ρ η σ L).mul (Real.tendsto_exp_atBot.comp hlog)
  rw [mul_zero] at h
  exact h.congr fun t => div_mul_cancel₀ _ (Real.exp_ne_zero _)

/-- Complex Gaussian Mellin reading at the marked point and observation height. -/
abbrev gaussianKernelAtHeight (ρ : ℂ) (σ L t : ℝ) :=
  gaussianMBKernel (Real.exp (-L)) (ρ-((σ:ℂ)+(t:ℂ)*I))

/-- The uppermost observed abscissa has a uniform lower bound against
all phases if the other modes on that abscissa have insufficient total
magnitude. Indices can repeat a site to account for multiplicity. -/
theorem finite_gaussian_modes_survive {ι : Type*} (S : Finset ι) (z : ι → ℂ) (ρ : ℂ)
    (hmax : ∀ i ∈ S, (z i).re≤ρ.re) (σ : ℝ) (L : ℝ → ℝ)
    (hL : Tendsto (fun t => L t+Real.log (t/2)) atTop atTop) {k : ℝ}
    (hk : k < 1-∑ i ∈ S, if (z i).re=ρ.re then Real.exp (Real.pi*((z i).im-ρ.im)/4) else 0) :
    ∀ᶠ t : ℝ in atTop, ∀ q : ι → ℂ, (∀ i ∈ S, ‖q i‖=1) →
      k*gaussianModeNorm ρ σ (L t) t <
        ‖gaussianKernelAtHeight ρ σ (L t) t + ∑ i ∈ S, q i*gaussianKernelAtHeight (z i) σ (L t) t‖ := by
  classical
  have hi (i : ι) (h : i∈S) :
      Tendsto (fun t => gaussianModeNorm (z i) σ (L t) t/gaussianModeNorm ρ σ (L t) t)
        atTop (𝓝 (if (z i).re=ρ.re then Real.exp (Real.pi*((z i).im-ρ.im)/4) else 0)) := by
    by_cases he : (z i).re=ρ.re
    · simpa only [if_pos he] using equal_real_gaussian_ratio_limit he σ L
    · simpa only [if_neg he] using lower_gaussian_mode_disappears (lt_of_le_of_ne (hmax i h) he) σ L hL
  have hs := (tendsto_finsetSum S hi).eventually_lt_const (by linarith only [hk] : _ < 1-k)
  filter_upwards [hs,gaussian_mode_eventually_positive ρ σ L] with t ht hp q hq
  let F (i : ι) := q i*gaussianKernelAtHeight (z i) σ (L t) t
  have hnorm : ‖∑ i ∈ S, F i‖ ≤ ∑ i ∈ S, gaussianModeNorm (z i) σ (L t) t :=
    (norm_sum_le ..).trans_eq (Finset.sum_congr rfl fun i h => by
      change ‖q i*gaussianKernelAtHeight (z i) σ (L t) t‖ = ‖gaussianKernelAtHeight (z i) σ (L t) t‖
      rw [norm_mul,hq i h,one_mul])
  have htri := norm_sub_le (gaussianKernelAtHeight ρ σ (L t) t+∑ i ∈ S, F i) (∑ i ∈ S, F i)
  rw [add_sub_cancel_right] at htri
  change gaussianModeNorm ρ σ (L t) t ≤ _ at htri
  have hsmall := (div_lt_iff₀ hp).mp (by simpa only [Finset.sum_div] using ht :
    (∑ i ∈ S, gaussianModeNorm (z i) σ (L t) t)/gaussianModeNorm ρ σ (L t) t < 1-k)
  change _ < ‖gaussianKernelAtHeight ρ σ (L t) t+∑ i ∈ S, F i‖
  linarith only [hnorm,htri,hsmall]

/-- For the four points ρ, conjugate ρ, 1−ρ and 1−conjugate ρ, a
positive fraction survives every set of phases whenever Re ρ > 1/2
and Im ρ > 0. The fraction depends only on the ordinate. -/
theorem gaussian_functional_equation_quartet {ρ : ℂ} (hβ : 1/2<ρ.re) (σ : ℝ) (L : ℝ → ℝ)
    (hL : Tendsto (fun t => L t+Real.log (t/2)) atTop atTop) {k : ℝ}
    (hk : k<1-Real.exp (-(Real.pi*ρ.im/2))) :
    ∀ᶠ t : ℝ in atTop, ∀ q : Fin 3 → ℂ, (∀ i, ‖q i‖=1) →
      k*gaussianModeNorm ρ σ (L t) t <
      ‖gaussianKernelAtHeight ρ σ (L t) t + ∑ i : Fin 3, q i*gaussianKernelAtHeight
        (![ (starRingEnd ℂ) ρ, 1-ρ, 1-(starRingEnd ℂ) ρ ] i) σ (L t) t‖ := by
  let z : Fin 3 → ℂ := ![(starRingEnd ℂ) ρ,1-ρ,1-(starRingEnd ℂ) ρ]
  have hleft : 1-ρ.re<ρ.re := by linarith only [hβ]
  have hm (i : Fin 3) (_ : i∈Finset.univ) : (z i).re≤ρ.re := by
    fin_cases i <;> simp [z,Complex.sub_re,hleft.le]
  have hconst : -ρ.im-ρ.im= -(2*ρ.im) := by ring
  have hb : k<1-∑ i : Fin 3, if (z i).re=ρ.re then Real.exp (Real.pi*((z i).im-ρ.im)/4) else 0 := by
    simpa [Fin.sum_univ_succ,z,Complex.sub_re,hleft.ne,hconst,
      show Real.pi * -(2*ρ.im)/4= -(Real.pi*ρ.im/2) by ring,
      show -(Real.pi*(2*ρ.im))/4 = -(Real.pi*ρ.im/2) by ring] using hk
  filter_upwards [finite_gaussian_modes_survive Finset.univ z ρ hm σ L hL hb] with t ht q hq
  exact ht q (fun i _ => hq i)

#print axioms gaussian_pair_at_finite_shifted_height
#print axioms lower_gaussian_mode_disappears
#print axioms finite_gaussian_modes_survive
#print axioms gaussian_functional_equation_quartet
end GaloisForLFunctions.ExceptionalLayerTheory
