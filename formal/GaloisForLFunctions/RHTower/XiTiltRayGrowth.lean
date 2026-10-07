import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing

/-!
# Superlinear Xi growth beyond every real threshold

The existing Archimedean ray-growth theorem and compact boundedness remove
any finite initial segment. Every fixed real exponential tilt retains this
obstruction to an exponential ray bound.
-/

open Complex Set

namespace RHTower

/-- Xi's logarithmic growth beats every slope beyond every prescribed real threshold. -/
theorem xi_superlinear_ray_above (A R : ℝ) :
    ∃ σ : ℝ, R < σ ∧ 1 ≤ σ ∧ A * σ < Real.log ‖xi (σ : ℂ)‖ := by
  have hc : Continuous (fun x : ℝ => riemannXi (x : ℂ)) :=
    differentiable_riemannXi.continuous.comp Complex.continuous_ofReal
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := max 1 R)).exists_bound_of_continuousOn
    hc.continuousOn
  let B := max A (|M| + 1)
  have hAB : A ≤ B := le_max_left _ _
  have hMB : |M| + 1 ≤ B := le_max_right _ _
  have hB : 0 < B := by have := abs_nonneg M; linarith
  obtain ⟨σ, hσ, hg⟩ := riemannXi_ray_growth B
  have hR : R < σ := by
    by_contra hn
    have hσR : σ ≤ R := le_of_not_gt hn
    have hb := hM σ ⟨hσ, hσR.trans (le_max_right 1 R)⟩
    have hnorm : 0 < ‖riemannXi (σ : ℂ)‖ :=
      norm_pos_iff.mpr (riemannXi_ne_zero_of_ofReal σ)
    have hl := Real.log_le_sub_one_of_pos hnorm
    have hm := mul_le_mul_of_nonneg_left hσ hB.le
    have habs := le_abs_self M
    nlinarith
  refine ⟨σ, hR, hσ, ?_⟩
  rw [xi_eq_riemannXi]
  exact (mul_le_mul_of_nonneg_right hAB (by linarith)).trans_lt hg

/-- No fixed exponential tilt of Xi has an exponential bound on any shifted real ray. -/
theorem xi_tilt_not_exp_ray_bound (a R : ℝ) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖xi ((R + t : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((R + t : ℝ) : ℂ))‖ ≤
        Real.exp (C * t) := by
  rintro ⟨C, hC, hb⟩
  obtain ⟨σ, hσR, hσ, hg⟩ := xi_superlinear_ray_above
    (C + |a| + |C * R| + 1) (R + 1)
  have ht : 1 ≤ σ - R := by linarith
  have hd : ‖xi (σ : ℂ)‖ * Real.exp (-a * σ) ≤ Real.exp (C * (σ - R)) := by
    have hh := hb (σ - R) ht
    rw [show R + (σ - R) = σ by ring] at hh
    simpa [norm_mul, Complex.norm_exp] using hh
  have hp : 0 < ‖xi (σ : ℂ)‖ := norm_pos_iff.mpr (xi_ne_zero_of_ofReal σ)
  have hl := Real.log_le_log (mul_pos hp (Real.exp_pos (-a * σ))) hd
  rw [Real.log_mul hp.ne' (Real.exp_pos (-a * σ)).ne', Real.log_exp, Real.log_exp] at hl
  have hax := mul_le_mul_of_nonneg_right (le_abs_self a) (by linarith : 0 ≤ σ)
  have hcr : -(C * R) ≤ |C * R| := neg_le_abs _
  have hcrx : |C * R| ≤ |C * R| * σ := by nlinarith [abs_nonneg (C * R)]
  nlinarith

end RHTower
