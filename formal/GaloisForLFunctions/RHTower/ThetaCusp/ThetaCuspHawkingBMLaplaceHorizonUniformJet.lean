import GaloisForLFunctions.HTGeometry.HypergeometricTaylorEndpointBounds
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceGaussFactors
import GaloisForLFunctions.HTGeometry.UniformThirdOrderJet

/-! The literal Gauss horizon factor as a closed-ball uniform cubic jet. -/

namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

private theorem local_horizonGauss_parameter_neighborhood (w chi : ℂ) (hw : w.im ≠ 0) :
    ∃ R B δ : ℝ, 0 < R ∧ R ≤ 1 ∧ 0 < B ∧ 0 < δ ∧
      ∀ u ∈ ball w R, ‖gaussA u chi‖ ≤ B ∧ ‖gaussB u chi‖ ≤ B ∧ ‖gaussC u‖ ≤ B ∧
        δ ≤ |u.im| := by
  let B := ‖gaussA w chi‖ + ‖gaussB w chi‖ + ‖gaussC w‖ + 1
  let δ := |w.im| / 2
  have hδ : 0 < δ := div_pos (abs_pos.mpr hw) (by norm_num)
  have hA : ∀ᶠ u in 𝓝 w, ‖gaussA u chi‖ < B :=
    (show ContinuousAt (fun u => ‖gaussA u chi‖) w by unfold gaussA; fun_prop).eventually_lt
      continuousAt_const (by
        dsimp [B]
        linarith [norm_nonneg (gaussB w chi), norm_nonneg (gaussC w)])
  have hB : ∀ᶠ u in 𝓝 w, ‖gaussB u chi‖ < B :=
    (show ContinuousAt (fun u => ‖gaussB u chi‖) w by unfold gaussB; fun_prop).eventually_lt
      continuousAt_const (by
        dsimp [B]
        linarith [norm_nonneg (gaussA w chi), norm_nonneg (gaussC w)])
  have hC : ∀ᶠ u in 𝓝 w, ‖gaussC u‖ < B :=
    (show ContinuousAt (fun u => ‖gaussC u‖) w by unfold gaussC; fun_prop).eventually_lt
      continuousAt_const (by
        dsimp [B]
        linarith [norm_nonneg (gaussA w chi), norm_nonneg (gaussB w chi)])
  have hi : ∀ᶠ u : ℂ in 𝓝 w, δ < |u.im| := continuousAt_const.eventually_lt
    (by fun_prop) (by
      dsimp [δ]
      linarith [abs_pos.mpr hw])
  obtain ⟨R, hR, hall⟩ := Metric.eventually_nhds_iff.mp (hA.and (hB.and (hC.and hi)))
  refine ⟨min R 1, B, δ, lt_min hR (by norm_num), min_le_right _ _, by dsimp [B]; positivity,
    hδ, ?_⟩
  intro u hu
  obtain ⟨ha, hb, hc, hd⟩ := hall ((mem_ball.mp hu).trans_le (min_le_left _ _))
  exact ⟨ha.le, hb.le, hc.le, hd.le⟩

/-- The literal Gauss factor has its three actual hypergeometric coefficients
and a cubic remainder uniformly on a closed nonreal-frequency ball. -/
theorem exists_horizonGauss_uniformJet3 (w chi : ℂ) (hw : w.im ≠ 0) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      HasUniformJet3 (closedBall w R) (1 / 2)
        (fun u z => gaussFactor u chi false (z : ℂ))
        (fun u => ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) 0)
        (fun u => ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) 1)
        (fun u => ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) 2) C := by
  obtain ⟨R₀, B, δ, hR₀, _, hB, hδ, hp⟩ := local_horizonGauss_parameter_neighborhood w chi hw
  obtain ⟨N, hN⟩ := exists_nat_ge (B + 1)
  have hsep (u : ℂ) (hu : u ∈ ball w R₀) (j : ℕ) : δ ≤ ‖gaussC u + j‖ := by
    have hh := Complex.abs_im_le_norm (gaussC u + j)
    simp only [gaussC, Complex.add_im, Complex.one_im, Complex.natCast_im, zero_add, add_zero] at hh
    exact (hp u hu).2.2.2.trans hh
  have hcoef (u : ℂ) (hu : u ∈ ball w R₀) := gaussParameterMajorant_bound hB hδ
    (hp u hu).1 (hp u hu).2.1 (hp u hu).2.2.1 (hsep u hu) N hN
  have hnonneg (n : ℕ) : 0 ≤ gaussParameterMajorant B δ N n :=
    (norm_nonneg _).trans (hcoef w (mem_ball_self hR₀) n)
  let C : ℝ := ∑' n, gaussParameterMajorant B δ N (n + 3) * (1 / 2 : ℝ) ^ n
  have hC0 : 0 ≤ C := tsum_nonneg (fun n => mul_nonneg (hnonneg _) (pow_nonneg (by norm_num) _))
  refine ⟨R₀ / 2, C, half_pos hR₀, hC0, ?_⟩
  intro u hu z hz
  have hu' : u ∈ ball w R₀ := by
    rw [mem_ball]
    calc
      dist u w ≤ R₀ / 2 := by simpa only [mem_closedBall] using hu
      _ < R₀ := half_lt_self hR₀
  have hz' : z ∈ Icc (0 : ℝ) (1 / 2) := ⟨hz.1.le, hz.2⟩
  have hn : ‖(z : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz'.1] using hz'.2
  have h := hypergeometric_taylor_remainder_bound hB hδ
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (hp u hu').1 (hp u hu').2.1 (hp u hu').2.2.1 (hsep u hu') N hN hn 3
  have htail : ‖gaussFactor u chi false (z : ℂ) -
      ∑ n ∈ Finset.range 3,
        ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) n *
          (z : ℂ) ^ n‖ ≤ C * z ^ 3 := by
    simpa only [ordinaryHypergeometric, gaussFactor, radialSeries, Bool.false_eq_true, ↓reduceIte,
      horizonSeries, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz'.1] using h
  have hsum : ∑ n ∈ Finset.range 3,
      ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) n *
        (z : ℂ) ^ n =
      ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) 0 +
        ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) 1 * z +
          ordinaryHypergeometricCoefficient (gaussA u chi) (gaussB u chi) (gaussC u) 2 * z ^ 2 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_range_succ,
      show (2 : ℕ) = 1 + 1 by norm_num, Finset.sum_range_succ,
      show (1 : ℕ) = 0 + 1 by norm_num, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
  rw [hsum] at htail
  simpa only [sub_add_eq_sub_sub] using htail

end
end RHTower.D4BMLaplaceRadial
