import GaloisForLFunctions.RHTower.SuzukiDslopeLineMass
import GaloisForLFunctions.RHTower.HalfPlaneHardyBoundary

noncomputable section

/-!
# `F_γ` attains its boundary values in `L²`

The restrictions of `F_γ` to the horizontal lines converge, in `L²(ℝ)` and along any sequence of
heights tending to zero, to the restriction to the real axis itself.

Dominated convergence supplies this: the integrands tend to zero pointwise because `F_γ` is
holomorphic — hence continuous — at every point of the *closed* half-plane, and the uniform Cauchy
profile dominates the differences, with the constant `4` absorbing the triangle inequality.

Together with the Paley--Wiener datum of the rotated `F_γ`, this identifies the boundary values as
the Fourier transform of a datum on the positive ray, which is what places `F_γ` in the Hardy
space.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- **The line restrictions of `F_γ` converge to its boundary values in `L²`.** -/
theorem tendsto_dslope_lineLp (hRH : RiemannHypothesis) {γ : ℂ} (hγ : XiC γ = 0) {C : ℝ}
    (hC1 : 1 ≤ C) (hCb : ∀ z : ℂ, 0 ≤ z.im → ‖dslope suzukiHalfInner γ z‖ ≤ C)
    (σ : ℕ → ℝ) (hσnn : ∀ n, 0 ≤ σ n) (hσ0 : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun n => (memLp_dslope_line hRH hγ hC1 hCb (hσnn n)).toLp _) atTop
      (𝓝 ((memLp_dslope_line hRH hγ hC1 hCb (le_refl (0 : ℝ))).toLp _)) := by
  have hmaj : Integrable (fun x : ℝ => 8 * C ^ 2 / (1 + (x - γ.re) ^ 2)) volume :=
    integrable_lineMajorant γ.re (8 * C ^ 2)
  have hdiff : ∀ n : ℕ, ∀ᵐ x : ℝ,
      ‖(((memLp_dslope_line hRH hγ hC1 hCb (hσnn n)).toLp _
          - (memLp_dslope_line hRH hγ hC1 hCb (le_refl (0 : ℝ))).toLp _
            : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ ^ 2
        = ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ n : ℝ) : ℂ) * I)
            - dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ^ 2 := by
    intro n
    filter_upwards [MeasureTheory.Lp.coeFn_sub
        ((memLp_dslope_line hRH hγ hC1 hCb (hσnn n)).toLp _)
        ((memLp_dslope_line hRH hγ hC1 hCb (le_refl (0 : ℝ))).toLp _),
      (memLp_dslope_line hRH hγ hC1 hCb (hσnn n)).coeFn_toLp,
      (memLp_dslope_line hRH hγ hC1 hCb (le_refl (0 : ℝ))).coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hbnd : ∀ n : ℕ, ∀ x : ℝ,
      ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ n : ℝ) : ℂ) * I)
          - dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ^ 2
        ≤ 8 * C ^ 2 / (1 + (x - γ.re) ^ 2) := by
    intro n x
    have hz1 : (0 : ℝ) ≤ (((x : ℂ) + ((σ n : ℝ) : ℂ) * I)).im := by simpa using hσnn n
    have hz2 : (0 : ℝ) ≤ (((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im := by simp
    have hb1 := norm_sq_dslope_le_lineMajorant hRH hγ hC1 hCb hz1
    have hb2 := norm_sq_dslope_le_lineMajorant hRH hγ hC1 hCb hz2
    have hre1 : (((x : ℂ) + ((σ n : ℝ) : ℂ) * I)).re = x := by simp
    have hre2 : (((x : ℂ) + ((0 : ℝ) : ℂ) * I)).re = x := by simp
    rw [hre1] at hb1
    rw [hre2] at hb2
    have hsub := norm_sub_le (dslope suzukiHalfInner γ ((x : ℂ) + ((σ n : ℝ) : ℂ) * I))
      (dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I))
    have hden : (0 : ℝ) < 1 + (x - γ.re) ^ 2 := by positivity
    have hd : (8 : ℝ) * C ^ 2 / (1 + (x - γ.re) ^ 2)
        = 4 * (2 * C ^ 2 / (1 + (x - γ.re) ^ 2)) := by ring
    rw [hd]
    set a := ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ n : ℝ) : ℂ) * I)‖ with ha
    set b := ‖dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ with hb
    set d := ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ n : ℝ) : ℂ) * I)
      - dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ with hdd
    have hdnn : 0 ≤ d := norm_nonneg _
    have hann : 0 ≤ a := norm_nonneg _
    have hbnn : 0 ≤ b := norm_nonneg _
    have hd2 : d ^ 2 ≤ (a + b) ^ 2 := by nlinarith [hsub]
    nlinarith [hb1, hb2, hd2, sq_nonneg (a - b)]
  have hptw : ∀ᵐ x : ℝ, Tendsto (fun n =>
      ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ n : ℝ) : ℂ) * I)
        - dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards with x
    have hz : (0 : ℝ) ≤ (((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im := by simp
    have hcont := (differentiableAt_dslope_suzukiHalfInner_of_rh hRH hγ hz).continuousAt
    have hin : Tendsto (fun n => ((x : ℂ) + ((σ n : ℝ) : ℂ) * I)) atTop
        (𝓝 ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) := by
      have h' : Tendsto (fun n => ((σ n : ℝ) : ℂ)) atTop (𝓝 (((0 : ℝ) : ℂ))) :=
        (Complex.continuous_ofReal.tendsto 0).comp hσ0
      exact tendsto_const_nhds.add (h'.mul_const I)
    have hcomp := hcont.tendsto.comp hin
    have hconst : Tendsto
        (fun _ : ℕ => dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) atTop
        (𝓝 (dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I))) := tendsto_const_nhds
    have h2 := ((hcomp.sub hconst).norm).pow 2
    simpa using h2
  have hintTo : Tendsto (fun n => ∫ x : ℝ,
      ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ n : ℝ) : ℂ) * I)
        - dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ^ 2) atTop (𝓝 0) := by
    have hmeasn : ∀ n : ℕ, AEStronglyMeasurable (fun x : ℝ =>
        ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ n : ℝ) : ℂ) * I)
          - dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ^ 2) volume := by
      intro n
      exact (((continuous_dslope_line hRH hγ (hσnn n)).sub
        (continuous_dslope_line hRH hγ (le_refl (0 : ℝ)))).norm.pow 2).aestronglyMeasurable
    have := MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x : ℝ => 8 * C ^ 2 / (1 + (x - γ.re) ^ 2)) hmeasn hmaj
      (fun n => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hbnd n x) hptw
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n : ℕ,
      ‖(memLp_dslope_line hRH hγ hC1 hCb (hσnn n)).toLp _
          - (memLp_dslope_line hRH hγ hC1 hCb (le_refl (0 : ℝ))).toLp _‖ ^ 2
        = ∫ x : ℝ, ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ n : ℝ) : ℂ) * I)
            - dslope suzukiHalfInner γ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ^ 2 := by
    intro n
    rw [norm_sq_lp_eq_integral]
    exact MeasureTheory.integral_congr_ae (hdiff n)
  have hsqTo : Tendsto (fun n =>
      ‖(memLp_dslope_line hRH hγ hC1 hCb (hσnn n)).toLp _
        - (memLp_dslope_line hRH hγ hC1 hCb (le_refl (0 : ℝ))).toLp _‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hintTo
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsqTo
  simp only [Real.sqrt_zero] at hroot
  refine hroot.congr fun n => ?_
  exact Real.sqrt_sq (norm_nonneg _)

end RHTower
