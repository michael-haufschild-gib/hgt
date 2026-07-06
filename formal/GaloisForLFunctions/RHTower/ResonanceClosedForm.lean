/-
Closed form for the resonance moment of the completed carrier.

The Euler integral bounds the Gamma modulus by its value on the real axis,
`‖Γ(z)‖ ≤ Γ(Re z)`, which makes the envelope sup on the critical line explicit:
`‖archFactor(linePt u)‖ ≤ (¼+u²)/2 · π^{−1/4} · Γ(¼)`.  Conjugation symmetry identifies the
reflected resonance integral with the conjugate of the direct one, so the full resonance
moment `‖∫ arch(linePt) + ∫ arch(1−linePt)‖` is bounded by twice the all-explicit van der
Corput bound — a closed-form function of the segment endpoints alone.  The `Cmain` face of
the completed carrier's first moment is a theorem: no analytic data remains open in Hardy's
resonance cancellation.
-/
import GaloisForLFunctions.RHTower.WindingCurvature

open Complex Metric

namespace RHTower

/-- **Euler-integral modulus bound**: `‖Γ(z)‖ ≤ Γ(Re z)` on the right half plane. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,
    show Complex.GammaIntegral z =
      ∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1) from rfl]
  calc ‖∫ x in Set.Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0 : ℝ), ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
    _ = Real.Gamma z.re := (Real.Gamma_eq_integral hz).symm

/-- **Explicit envelope sup on the critical line**:
`‖archFactor(linePt u)‖ ≤ (¼+u²)/2 · π^{−1/4} · Γ(¼)`. -/
theorem norm_archFactor_line_le (u : ℝ) :
    ‖archFactor (linePt u)‖ ≤
      (1 / 4 + u ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) := by
  have h2 : linePt u * (linePt u - 1) = ((-(1 / 4 + u ^ 2) : ℝ) : ℂ) := by
    unfold linePt
    push_cast
    linear_combination ((u : ℂ)) ^ 2 * Complex.I_sq
  have hGRnorm : ‖Complex.Gammaℝ (linePt u)‖ ≤
      Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) := by
    rw [Complex.Gammaℝ_def, norm_mul]
    have hpow : ‖((Real.pi : ℝ) : ℂ) ^ (-(linePt u) / 2)‖ = Real.pi ^ (-(1 / 4 : ℝ)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      congr 1
      rw [show (-(linePt u) / 2 : ℂ) = -(linePt u / 2) from by ring, Complex.neg_re,
        re_div_two, linePt_re]
      norm_num
    have hre : ((linePt u) / 2).re = 1 / 4 := by
      rw [re_div_two, linePt_re]
      norm_num
    have hGnorm : ‖Complex.Gamma ((linePt u) / 2)‖ ≤ Real.Gamma (1 / 4) := by
      have h := norm_Gamma_le_Gamma_re (z := (linePt u) / 2) (by rw [hre]; norm_num)
      rwa [hre] at h
    rw [hpow]
    exact mul_le_mul_of_nonneg_left hGnorm (Real.rpow_nonneg Real.pi_pos.le _)
  have hpoly : ‖linePt u * (linePt u - 1) / 2‖ = (1 / 4 + u ^ 2) / 2 := by
    rw [norm_div, h2, Complex.norm_real, Real.norm_eq_abs,
      show |(-(1 / 4 + u ^ 2) : ℝ)| = 1 / 4 + u ^ 2 from by
        rw [abs_neg]; exact abs_of_pos (by positivity)]
    norm_num
  calc ‖archFactor (linePt u)‖
      = ‖linePt u * (linePt u - 1) / 2‖ * ‖Complex.Gammaℝ (linePt u)‖ := by
        unfold archFactor
        rw [norm_mul]
    _ ≤ (1 / 4 + u ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) := by
        rw [hpoly]
        exact mul_le_mul_of_nonneg_left hGRnorm (by positivity)

/-- The envelope is conjugation-equivariant. -/
theorem archFactor_conj (s : ℂ) :
    archFactor ((starRingEnd ℂ) s) = (starRingEnd ℂ) (archFactor s) := by
  unfold archFactor
  rw [Gammaℝ_conj, map_mul, map_div₀, map_mul, map_sub, map_one, map_ofNat]

/-- **The reflected resonance integral is the conjugate of the direct one.** -/
theorem integral_archFactor_reflected_eq_conj (α β : ℝ) :
    (∫ u in α..β, archFactor (1 - linePt u)) =
      (starRingEnd ℂ) (∫ u in α..β, archFactor (linePt u)) := by
  have h1 : ∀ u : ℝ, archFactor (1 - linePt u) =
      (starRingEnd ℂ) (archFactor (linePt u)) := by
    intro u
    rw [← conj_linePt]
    exact archFactor_conj (linePt u)
  rw [intervalIntegral.integral_congr
    (g := fun u : ℝ => (starRingEnd ℂ) (archFactor (linePt u))) (fun u _ => h1 u)]
  have hcont : Continuous fun u : ℝ => archFactor (linePt u) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hasDerivAt_archFactor_line u).continuousAt
  have hInt : IntervalIntegrable (fun u : ℝ => archFactor (linePt u))
      MeasureTheory.volume α β := hcont.intervalIntegrable α β
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap hInt
  simpa using hcomm

/-- **Closed form for the resonance moment.**  Above the explicit winding threshold, the
full resonance moment of the completed carrier is bounded by twice the all-explicit van der
Corput bound with the Euler-integral envelope sup: a function of the segment endpoints alone.
Every analytic face of Hardy's resonance cancellation is a theorem. -/
theorem resonance_moment_le_closed_form {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hm : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2) :
    ‖(∫ u in α..β, archFactor (linePt u)) +
        ∫ u in α..β, archFactor (1 - linePt u)‖ ≤
      2 * (2 * ((1 / 4 + β ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) /
          ((Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)) +
        (β - α) * ((1 / 4 + β ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) *
            (3 / α + Real.pi / 4) /
            ((Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2) +
          (1 / 4 + β ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) *
            (3 / α ^ 2 + Real.pi / (4 * α)) /
            ((Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2) ^ 2)) := by
  have hM₀seg : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ ≤
      (1 / 4 + β ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) := by
    intro u hu
    refine le_trans (norm_archFactor_line_le u) ?_
    have hu2 : u ^ 2 ≤ β ^ 2 := by
      nlinarith [hu.1, hu.2, hα]
    have hC : (0 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) :=
      mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
        (Real.Gamma_pos_of_pos (by norm_num)).le
    have hquad : (1 / 4 + u ^ 2) / 2 ≤ (1 / 4 + β ^ 2) / 2 := by
      linarith
    exact mul_le_mul_of_nonneg_right hquad hC
  have hmain := norm_integral_archFactor_line_le_all_explicit hα hαβ hm hM₀seg
  rw [integral_archFactor_reflected_eq_conj]
  calc ‖(∫ u in α..β, archFactor (linePt u)) +
        (starRingEnd ℂ) (∫ u in α..β, archFactor (linePt u))‖
      ≤ ‖∫ u in α..β, archFactor (linePt u)‖ +
        ‖(starRingEnd ℂ) (∫ u in α..β, archFactor (linePt u))‖ := norm_add_le _ _
    _ = 2 * ‖∫ u in α..β, archFactor (linePt u)‖ := by
        rw [Complex.norm_conj]
        ring
    _ ≤ _ := by
        have h2 : (0 : ℝ) ≤ 2 := by norm_num
        exact mul_le_mul_of_nonneg_left hmain h2

end RHTower
