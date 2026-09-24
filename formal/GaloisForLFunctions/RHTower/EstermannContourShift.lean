import GaloisForLFunctions.RHTower.EstermannVerticalIntegrable

/-!
# The contour shift for Estermann's zeta

Letting the height of the rectangle tend to infinity in the exact rectangle identity: the two
horizontal edges vanish and the two vertical edges converge to the full line integrals, so the
difference of the two vertical integrals is `2π` times the residue at `s = 1`.
-/

open Complex Filter MeasureTheory

namespace RHTower

noncomputable section

/-- **The contour shift.**  The vertical integrals at `Re s = 2` and `Re s = ½` differ by `2π`
times the residue of the smoothed Perron integrand at `s = 1`. -/
theorem estermannMellin_vertical_difference (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) :
    (∫ v : ℝ, estermannMellinIntegrand q ((a : ZMod q)) x (((2 : ℝ) : ℂ) + (v : ℂ) * I))
        - ∫ v : ℝ,
            estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)
      = 2 * Real.pi * deriv (estermannMellinNumerator q ((a : ZMod q)) x) 1 := by
  have hint2 : Integrable (fun v : ℝ =>
      estermannMellinIntegrand q ((a : ZMod q)) x (((2 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    integrable_estermannMellinIntegrand_vertical q a hx (by norm_num) (by norm_num) (by norm_num)
  have hinth : Integrable (fun v : ℝ =>
      estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    integrable_estermannMellinIntegrand_vertical q a hx (by norm_num) (by norm_num) (by norm_num)
  have hrect : ∀ T : ℝ, 0 < T →
      (((∫ u in (1 / 2 : ℝ)..2,
            estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
          - ∫ u in (1 / 2 : ℝ)..2,
              estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + ((T : ℝ) : ℂ) * I))
        + I * ∫ v in (-T : ℝ)..T,
            estermannMellinIntegrand q ((a : ZMod q)) x (((2 : ℝ) : ℂ) + (v : ℂ) * I))
        - I * ∫ v in (-T : ℝ)..T,
            estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)
      = 2 * Real.pi * I * deriv (estermannMellinNumerator q ((a : ZMod q)) x) 1 := by
    intro T hT
    have h := rectIntegral_estermannMellinIntegrand q a hx hT
    rw [rectIntegral] at h
    have hz₁re : ((1 / 2 : ℂ) - (T : ℂ) * I).re = 1 / 2 := by simp
    have hz₁im : ((1 / 2 : ℂ) - (T : ℂ) * I).im = -T := by simp
    have hz₂re : ((2 : ℂ) + (T : ℂ) * I).re = 2 := by simp
    have hz₂im : ((2 : ℂ) + (T : ℂ) * I).im = T := by simp
    rw [hz₁re, hz₁im, hz₂re, hz₂im] at h
    simpa only [smul_eq_mul] using h
  have hbot : Tendsto (fun T : ℝ => ∫ u in (1 / 2 : ℝ)..2,
      estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
      atTop (nhds 0) := by
    have h := tendsto_horizontal_estermannMellin q a hx (-1) (Or.inr rfl)
    refine h.congr (fun T => ?_)
    norm_num
  have htop : Tendsto (fun T : ℝ => ∫ u in (1 / 2 : ℝ)..2,
      estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + ((T : ℝ) : ℂ) * I))
      atTop (nhds 0) := by
    have h := tendsto_horizontal_estermannMellin q a hx 1 (Or.inl rfl)
    refine h.congr (fun T => ?_)
    norm_num
  have hright : Tendsto (fun T : ℝ => ∫ v in (-T : ℝ)..T,
      estermannMellinIntegrand q ((a : ZMod q)) x (((2 : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (nhds (∫ v : ℝ,
        estermannMellinIntegrand q ((a : ZMod q)) x (((2 : ℝ) : ℂ) + (v : ℂ) * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hint2 tendsto_neg_atTop_atBot tendsto_id
  have hleft : Tendsto (fun T : ℝ => ∫ v in (-T : ℝ)..T,
      estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (nhds (∫ v : ℝ,
        estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hinth tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbot.sub htop).add (hright.const_mul I)).sub (hleft.const_mul I)
  have hconst : Tendsto (fun T : ℝ =>
      (((∫ u in (1 / 2 : ℝ)..2,
            estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
          - ∫ u in (1 / 2 : ℝ)..2,
              estermannMellinIntegrand q ((a : ZMod q)) x ((u : ℂ) + ((T : ℝ) : ℂ) * I))
        + I * ∫ v in (-T : ℝ)..T,
            estermannMellinIntegrand q ((a : ZMod q)) x (((2 : ℝ) : ℂ) + (v : ℂ) * I))
        - I * ∫ v in (-T : ℝ)..T,
            estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I))
      atTop (nhds (2 * Real.pi * I *
        deriv (estermannMellinNumerator q ((a : ZMod q)) x) 1)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (hrect T hT).symm
  have huniq := tendsto_nhds_unique hlim hconst
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  apply mul_left_cancel₀ hI
  rw [mul_sub]
  linear_combination huniq

end

end RHTower
