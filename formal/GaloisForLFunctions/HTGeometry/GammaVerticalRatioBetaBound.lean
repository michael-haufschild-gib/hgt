import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# A sharp uniform bound for the vertical Gamma ratio

The Beta integral bounds the modulus of a vertical Gamma quotient by its value on the real axis:
for `a, d > 0` and every real `x`,

`‖Γ(a+ix)‖ / ‖Γ(a+d+ix)‖ ≤ Γ(a) / Γ(a+d)`.

The proof is one line of mathematics — `Γ(u)Γ(v)/Γ(u+v)` is the Beta integral, whose modulus is at
most the Beta integral of the real parts — but it is exactly the uniform-in-height bound that a
contour shift on a strip needs, and it needs no Stirling asymptotics.
-/

open Complex MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- On the open unit interval the Beta integrand of complex parameters has the modulus of the
Beta integrand of the real parts. -/
theorem norm_betaIntegrand {u v : ℂ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖
      = x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
  have hx0 : (0 : ℝ) < x := hx.1
  have hx1 : (0 : ℝ) < 1 - x := by linarith [hx.2]
  have h1 : ‖(x : ℂ) ^ (u - 1)‖ = x ^ (u - 1).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
  have hcast : (1 : ℂ) - (x : ℂ) = (((1 - x : ℝ)) : ℂ) := by push_cast; ring
  have h2 : ‖(1 - (x : ℂ)) ^ (v - 1)‖ = (1 - x) ^ (v - 1).re := by
    rw [hcast]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hx1 _
  rw [norm_mul, h1, h2]
  simp

/-- The real-parameter Beta integrand is the cast of a real integrand. -/
theorem betaIntegrand_ofReal {a b : ℝ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ((x : ℂ)) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)
      = (((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ)) : ℂ) := by
  have hx0 : (0 : ℝ) ≤ x := le_of_lt hx.1
  have hx1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
  have hcast : (1 : ℂ) - (x : ℂ) = (((1 - x : ℝ)) : ℂ) := by push_cast; ring
  have he1 : ((a : ℂ) - 1) = (((a - 1 : ℝ)) : ℂ) := by push_cast; ring
  have he2 : ((b : ℂ) - 1) = (((b - 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, he1, he2, ← Complex.ofReal_cpow hx0, ← Complex.ofReal_cpow hx1,
    ← Complex.ofReal_mul]

/-- **The Beta bound.**  The modulus of the Beta integral is at most its value on the real
parts. -/
theorem norm_betaIntegral_le {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖Complex.betaIntegral u v‖
      ≤ Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) := by
  have hzero : (0 : ℝ) ≤ 1 := by norm_num
  have hae : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖
        = ‖((x : ℂ)) ^ ((u.re : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v.re : ℂ) - 1)‖ := by
    have hmeas : (volume.restrict (Ioc (0 : ℝ) 1)) {(1 : ℝ)} = 0 := by
      simp
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
      MeasureTheory.compl_mem_ae_iff.mpr hmeas] with x hx hx1
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩
      simpa using hx1
    rw [norm_betaIntegrand hxIoo, norm_betaIntegrand (u := (u.re : ℂ)) (v := (v.re : ℂ)) hxIoo]
    simp
  have hstep1 : ‖Complex.betaIntegral u v‖
      ≤ ∫ x in (0 : ℝ)..1, ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hzero
  have hstep2 : (∫ x in (0 : ℝ)..1, ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖)
      = ∫ x in (0 : ℝ)..1, ‖((x : ℂ)) ^ ((u.re : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v.re : ℂ) - 1)‖ := by
    rw [intervalIntegral.integral_of_le hzero, intervalIntegral.integral_of_le hzero]
    exact MeasureTheory.integral_congr_ae hae
  have hreal : (∫ x in (0 : ℝ)..1, ‖((x : ℂ)) ^ ((u.re : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v.re : ℂ) - 1)‖)
      = ‖Complex.betaIntegral (u.re : ℂ) (v.re : ℂ)‖ := by
    have hcast : Complex.betaIntegral (u.re : ℂ) (v.re : ℂ)
        = (((∫ x in (0 : ℝ)..1, x ^ (u.re - 1) * (1 - x) ^ (v.re - 1)) : ℝ) : ℂ) := by
      rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal,
        intervalIntegral.integral_of_le hzero, intervalIntegral.integral_of_le hzero]
      refine MeasureTheory.integral_congr_ae ?_
      have hmeas : (volume.restrict (Ioc (0 : ℝ) 1)) {(1 : ℝ)} = 0 := by
        simp
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.compl_mem_ae_iff.mpr hmeas] with x hx hx1
      have hxIoo : x ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩
        simpa using hx1
      exact betaIntegrand_ofReal hxIoo
    have hnn : ∀ x ∈ Ioo (0 : ℝ) 1, (0 : ℝ) ≤ x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := le_of_lt hx.1
      have hx1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
      positivity
    have hnormcast : (∫ x in (0 : ℝ)..1,
        ‖((x : ℂ)) ^ ((u.re : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v.re : ℂ) - 1)‖)
        = ∫ x in (0 : ℝ)..1, x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
      rw [intervalIntegral.integral_of_le hzero, intervalIntegral.integral_of_le hzero]
      refine MeasureTheory.integral_congr_ae ?_
      have hmeas : (volume.restrict (Ioc (0 : ℝ) 1)) {(1 : ℝ)} = 0 := by
        simp
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.compl_mem_ae_iff.mpr hmeas] with x hx hx1
      have hxIoo : x ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩
        simpa using hx1
      rw [norm_betaIntegrand (u := (u.re : ℂ)) (v := (v.re : ℂ)) hxIoo]
      simp
    rw [hnormcast, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    refine intervalIntegral.integral_nonneg hzero fun x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hx1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
    positivity
  have hbeta : Complex.betaIntegral (u.re : ℂ) (v.re : ℂ)
      = (((Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) : ℝ)) : ℂ) := by
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (u.re : ℂ)) (t := (v.re : ℂ))
      (by simpa using hu) (by simpa using hv)
    have hcast : ((u.re : ℂ)) + (v.re : ℂ) = (((u.re + v.re : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
    have hGne : ((Real.Gamma (u.re + v.re) : ℝ) : ℂ) ≠ 0 := by
      simpa using ne_of_gt (Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < u.re + v.re))
    rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff hGne, mul_comm]
    exact h.symm
  have hGpos : (0 : ℝ) ≤ Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) := by
    have h1 : 0 < Real.Gamma u.re := Real.Gamma_pos_of_pos hu
    have h2 : 0 < Real.Gamma v.re := Real.Gamma_pos_of_pos hv
    have h3 : 0 < Real.Gamma (u.re + v.re) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  calc ‖Complex.betaIntegral u v‖
      ≤ ∫ x in (0 : ℝ)..1, ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ := hstep1
    _ = ‖Complex.betaIntegral (u.re : ℂ) (v.re : ℂ)‖ := by rw [hstep2, hreal]
    _ = Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) := by
        rw [hbeta, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hGpos]

/-- **The uniform vertical Gamma-ratio bound.**  Shifting the abscissa to the right by `d` costs at
most the real ratio, uniformly in the height. -/
theorem norm_Gamma_vertical_le {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (x : ℝ) :
    ‖Complex.Gamma ((a : ℂ) + (x : ℂ) * I)‖
      ≤ (Real.Gamma a / Real.Gamma (a + d))
        * ‖Complex.Gamma (((a + d : ℝ) : ℂ) + (x : ℂ) * I)‖ := by
  set u : ℂ := (a : ℂ) + (x : ℂ) * I with hu
  have hure : u.re = a := by rw [hu]; simp
  have hdre : ((d : ℂ)).re = d := by simp
  have hsum : u + (d : ℂ) = ((a + d : ℝ) : ℂ) + (x : ℂ) * I := by
    rw [hu]; push_cast; ring
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := u) (t := (d : ℂ))
    (by rw [hure]; exact ha) (by rw [hdre]; exact hd)
  have hbound := norm_betaIntegral_le (u := u) (v := (d : ℂ))
    (by rw [hure]; exact ha) (by rw [hdre]; exact hd)
  rw [hure, hdre] at hbound
  have hGd : (0 : ℝ) < Real.Gamma d := Real.Gamma_pos_of_pos hd
  have hGa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hGsum : (0 : ℝ) < Real.Gamma (a + d) := Real.Gamma_pos_of_pos (by linarith)
  have hnorm : ‖Complex.Gamma u‖ * Real.Gamma d
      = ‖Complex.Gamma (((a + d : ℝ) : ℂ) + (x : ℂ) * I)‖
        * ‖Complex.betaIntegral u (d : ℂ)‖ := by
    have hn := congrArg norm hbeta
    rw [norm_mul, norm_mul, hsum, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hGd] at hn
    exact hn
  have hle : ‖Complex.Gamma u‖ * Real.Gamma d
      ≤ ‖Complex.Gamma (((a + d : ℝ) : ℂ) + (x : ℂ) * I)‖
        * (Real.Gamma a * Real.Gamma d / Real.Gamma (a + d)) := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  have hfinal : ‖Complex.Gamma u‖ * Real.Gamma d
      ≤ ((Real.Gamma a / Real.Gamma (a + d))
        * ‖Complex.Gamma (((a + d : ℝ) : ℂ) + (x : ℂ) * I)‖) * Real.Gamma d := by
    refine le_trans hle (le_of_eq ?_)
    field_simp
  exact le_of_mul_le_mul_right hfinal hGd

end

end GaloisForLFunctions.HTGeometry
