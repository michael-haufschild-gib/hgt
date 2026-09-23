import GaloisForLFunctions.HTGeometry.GammaShiftRatioAsymptotic
import GaloisForLFunctions.HTGeometry.GammaShiftTubeDatum

/-!
# Equation (14), uniformly on a tube

The comparison of two translates is uniform in the abscissa.  The digamma against the vertical
logarithm is uniform already in the corpus; the complex logarithm of `σ+it` differs from
`log t + iπ/2` by `O(1/t)` with a constant depending only on the tube — the real part because
`‖σ+it‖ ≤ t + M²`, the imaginary part by Jordan's inequality applied to `cos (arg s) = σ/‖s‖`.

Exponentiating a uniform `O(1/t)` gives `1 + O(1/t)`, so the ratio of two translates is the real
power of the argument uniformly on the tube — eq. (14) in the form eq. (4) asks for.
-/

open Filter Set Topology Function intervalIntegral

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The vertical argument is a right angle up to `O(1/t)`, uniformly on a tube.**  Jordan's
inequality turns `cos (arg s) = σ/‖s‖` into a bound on `π/2 − arg s`. -/
theorem abs_arg_vertical_sub_le {M : ℝ} {σ t : ℝ} (hσ : 0 < σ) (hσM : σ ≤ M) (ht : 1 ≤ t) :
    |Real.pi / 2 - Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I)| ≤ (Real.pi / 2) * (M / t) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos (σ := σ) htpos
  have hsnorm : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := norm_pos_iff.mpr hs
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have hcos : Real.cos (Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I))
      = σ / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    rw [Complex.cos_arg hs, hre]
  have hargnonneg : 0 ≤ Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [Complex.arg_nonneg_iff, him]
    exact le_of_lt htpos
  have hargle : Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I) ≤ Real.pi / 2 := by
    by_contra hcon
    have hcon' : Real.pi / 2 < Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I) := not_le.mp hcon
    have hpi0 : 0 < Real.pi := Real.pi_pos
    have hnonpos : Real.cos (Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I)) ≤ 0 := by
      refine Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_lt hcon') ?_
      have hpi : Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I) ≤ Real.pi := Complex.arg_le_pi _
      linarith
    rw [hcos] at hnonpos
    have hpos : 0 < σ / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := div_pos hσ hsnorm
    linarith
  set x : ℝ := Real.pi / 2 - Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I) with hx
  have hx0 : 0 ≤ x := by
    rw [hx]
    linarith
  have hxle : x ≤ Real.pi / 2 := by
    rw [hx]
    linarith
  have hsin : Real.sin x = σ / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    rw [hx, Real.sin_pi_div_two_sub, hcos]
  have hjordan : 2 / Real.pi * x ≤ Real.sin x := Real.mul_le_sin hx0 hxle
  have hM0 : 0 ≤ M := le_trans (le_of_lt hσ) hσM
  have hbound : Real.sin x ≤ M / t := by
    rw [hsin]
    have hts : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := norm_vertical_ge_height σ t
    calc σ / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ M / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
          gcongr
      _ ≤ M / t := by gcongr
  have hpi : 0 < Real.pi := Real.pi_pos
  have hkey : 2 / Real.pi * x ≤ M / t := le_trans hjordan hbound
  have hxid : x = (Real.pi / 2) * (2 / Real.pi * x) := by
    field_simp
  rw [abs_of_nonneg hx0, hxid]
  exact mul_le_mul_of_nonneg_left hkey (by linarith)

/-- **The modulus of the vertical argument is its height up to `O(1/t)`, uniformly on a tube.** -/
theorem abs_log_norm_vertical_sub_le {M : ℝ} {σ t : ℝ} (hσ : 0 < σ) (hσM : σ ≤ M) (ht : 1 ≤ t) :
    |Real.log ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ - Real.log t| ≤ M ^ (2 : ℕ) / t := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hts : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := norm_vertical_ge_height σ t
  have hsnorm : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := lt_of_lt_of_le htpos hts
  have hsq : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (2 : ℕ) = σ ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  have hM0 : 0 ≤ M := le_trans (le_of_lt hσ) hσM
  have hle : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ t + M ^ (2 : ℕ) := by
    nlinarith [hsq, hsnorm, hσ, hσM, ht, hM0]
  have hratio : 1 ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / t := (one_le_div htpos).mpr hts
  have hlogdiv : Real.log ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ - Real.log t
      = Real.log (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / t) :=
    (Real.log_div (ne_of_gt hsnorm) (ne_of_gt htpos)).symm
  rw [hlogdiv, abs_of_nonneg (Real.log_nonneg hratio)]
  have hstep : Real.log (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / t)
      ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / t - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hfrac : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / t - 1 ≤ M ^ (2 : ℕ) / t := by
    have heq : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / t - 1
        = (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ - t) / t := by
      field_simp
    rw [heq]
    gcongr
    linarith
  linarith

/-- **The complex logarithm on a vertical line is the vertical logarithm up to `O(1/t)`, uniformly
on a tube.** -/
theorem norm_log_vertical_sub_vertLog_le {M : ℝ} {σ t : ℝ} (hσ : 0 < σ) (hσM : σ ≤ M)
    (ht : 1 ≤ t) :
    ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖
      ≤ (M ^ (2 : ℕ) + (Real.pi / 2) * M) / t := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  set z : ℂ := Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t with hz
  have hre : z.re = Real.log ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ - Real.log t := by
    rw [hz, vertLog]
    simp [Complex.log_re]
  have him : z.im = Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I) - Real.pi / 2 := by
    rw [hz, vertLog]
    simp [Complex.log_im]
  have h1 : |z.re| ≤ M ^ (2 : ℕ) / t := by
    rw [hre]
    exact abs_log_norm_vertical_sub_le hσ hσM ht
  have h2 : |z.im| ≤ (Real.pi / 2) * (M / t) := by
    rw [him, abs_sub_comm]
    exact abs_arg_vertical_sub_le hσ hσM ht
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ M ^ (2 : ℕ) / t + (Real.pi / 2) * (M / t) := by linarith
    _ = (M ^ (2 : ℕ) + (Real.pi / 2) * M) / t := by ring

/-- The ratio of two translates is the exponential of the integrated digamma against the
logarithm. -/
theorem gammaShift_ratio_eq_exp {σ lam t : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam) (ht : 0 < t) :
    gammaLine (σ + lam) t / (gammaLine σ t * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ))
      = Complex.exp ((∫ u in (0 : ℝ)..lam,
          Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
        - (lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hzre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [hval]
    exact hσ
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos (σ := σ) ht
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  have hcpow : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ)
      = Complex.exp ((lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [Complex.cpow_def_of_ne_zero hs]
    ring_nf
  have hshift : gammaLine (σ + lam) t
      = gammaLine σ t
        * Complex.exp (∫ u in (0 : ℝ)..lam,
          Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ))) := by
    have h := gamma_shift_exp_integral (z := (σ : ℂ) + (t : ℂ) * Complex.I) hzre hlam
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)
        = ((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hval] at h
    exact h
  rw [hshift, hcpow, Complex.exp_sub]
  have hexpne : Complex.exp ((lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp

/-- **Equation (14) on a tube.**  The ratio of two Gamma translates is the real power of the
argument, uniformly for `0 < σ ≤ M`. -/
theorem tubeLimit_gammaShift_ratio {M lam : ℝ} (hM : 0 < M) (hlam : 0 ≤ lam) :
    TubeLimit M (fun σ t => gammaLine (σ + lam) t
      / (gammaLine σ t * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ))) 1 := by
  classical
  obtain ⟨C₁, hC₁, hdig⟩ := exists_uniform_bound_digamma_sub_vertLog (M := M + lam) (by linarith)
  set C₂ : ℝ := M ^ (2 : ℕ) + (Real.pi / 2) * M with hC₂def
  have hC₂ : 0 ≤ C₂ := by
    have : 0 ≤ M := le_of_lt hM
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  set C : ℝ := lam * C₁ + lam * C₂ with hCdef
  have hC : 0 ≤ C := by positivity
  -- the exponent is uniformly small
  have hexp : ∀ σ t : ℝ, 0 < σ → σ ≤ M → 1 ≤ t →
      ‖(∫ u in (0 : ℝ)..lam,
          Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
        - (lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / t := by
    intro σ t hσ hσM ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
    have hcont : ContinuousOn (fun u : ℝ =>
        Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ))) (Set.uIcc 0 lam) := by
      refine (continuousOn_digamma_shift ((σ : ℂ) + (t : ℂ) * Complex.I)).mono ?_
      intro v hv
      rw [Set.uIcc_of_le hlam] at hv
      have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      show -((σ : ℂ) + (t : ℂ) * Complex.I).re < v
      rw [hre]
      have hv0 : (0 : ℝ) ≤ v := hv.1
      linarith
    have hint : IntervalIntegrable (fun u : ℝ =>
        Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
        MeasureTheory.volume 0 lam := hcont.intervalIntegrable
    have hsplit : (∫ u in (0 : ℝ)..lam,
          Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
        - (lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)
        = (∫ u in (0 : ℝ)..lam,
            (Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)) - vertLog t))
          + (lam : ℂ) * (vertLog t - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [intervalIntegral.integral_sub hint (intervalIntegrable_const),
        intervalIntegral.integral_const]
      simp only [Complex.real_smul, sub_zero]
      ring
    rw [hsplit]
    have hbound1 : ‖(∫ u in (0 : ℝ)..lam,
        (Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)) - vertLog t))‖
        ≤ (C₁ / t) * |lam - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro u hu
      rw [Set.uIoc_of_le hlam] at hu
      have hu0 : (0 : ℝ) ≤ u := le_of_lt hu.1
      have huM : σ + u ≤ M + lam := by linarith [hu.2]
      have hval : ((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)
          = ((σ + u : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hval]
      exact hdig (σ + u) t (by linarith) huM ht
    have hbound2 : ‖(lam : ℂ) * (vertLog t - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ lam * (C₂ / t) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam, ← norm_neg]
      have hneg : -(vertLog t - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I))
          = Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t := by ring
      rw [hneg]
      refine mul_le_mul_of_nonneg_left ?_ hlam
      exact norm_log_vertical_sub_vertLog_le hσ hσM ht
    have habs : |lam - 0| = lam := by
      rw [sub_zero, abs_of_nonneg hlam]
    calc ‖(∫ u in (0 : ℝ)..lam,
          (Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)) - vertLog t))
        + (lam : ℂ) * (vertLog t - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ ‖(∫ u in (0 : ℝ)..lam,
            (Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)) - vertLog t))‖
          + ‖(lam : ℂ) * (vertLog t - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I))‖ :=
          norm_add_le _ _
      _ ≤ (C₁ / t) * |lam - 0| + lam * (C₂ / t) := by linarith
      _ = C / t := by
          rw [habs, hCdef]
          field_simp
  -- exponentiate
  intro ε hε
  refine ⟨max 1 (max (C + 1) (2 * C / ε + 1)), fun σ t hσ hσM ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have htC : C + 1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htCε : 2 * C / ε + 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hw := hexp σ t hσ hσM ht1
  have hsmall : C / t ≤ 1 := by
    rw [div_le_one htpos]
    linarith
  have hwle : ‖(∫ u in (0 : ℝ)..lam,
      Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
      - (lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 := le_trans hw hsmall
  have hratio := gammaShift_ratio_eq_exp (σ := σ) (lam := lam) hσ hlam htpos
  show ‖gammaLine (σ + lam) t
      / (gammaLine σ t * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ)) - 1‖ ≤ ε
  rw [hratio]
  have hexp1 := Complex.norm_exp_sub_one_le hwle
  refine le_trans hexp1 ?_
  have h2w : 2 * ‖(∫ u in (0 : ℝ)..lam,
      Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
      - (lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * (C / t) := by
    linarith
  refine le_trans h2w ?_
  have h1 : 2 * C / ε ≤ t := by linarith
  rw [div_le_iff₀ hε] at h1
  rw [← mul_div_assoc, div_le_iff₀ htpos]
  linarith

end

end GaloisForLFunctions.HTGeometry
