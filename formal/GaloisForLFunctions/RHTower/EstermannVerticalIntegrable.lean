import GaloisForLFunctions.RHTower.EstermannHorizontalDecay
import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversion
import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversionGeneralLine

/-!
# Vertical integrability of the Estermann Mellin integrand

On a line `Re s = σ` with `0 < σ ≤ 2` and `σ ≠ 1` the integrand `x^{-s} Γ(s) D(s, a/q)` is
continuous, and above unit height it is bounded by `C(1+|t|)^N e^{-π|t|/2}`.  Raising the constant
absorbs the compact part `|t| ≤ 1`, so a single majorant of that shape dominates the whole line and
the integrand is integrable.
-/

open Complex Filter MeasureTheory

namespace RHTower

noncomputable section

/-- **Vertical integrability.** -/
theorem integrable_estermannMellinIntegrand_vertical (q : ℕ) [NeZero q] (a : (ZMod q)ˣ)
    {x σ : ℝ} (hx : 0 < x) (hσ0 : 0 < σ) (hσ2 : σ ≤ 2) (hσ1 : σ ≠ 1) :
    Integrable (fun v : ℝ =>
      estermannMellinIntegrand q ((a : ZMod q)) x ((σ : ℂ) + (v : ℂ) * I)) := by
  classical
  set f : ℝ → ℂ := fun v =>
    estermannMellinIntegrand q ((a : ZMod q)) x ((σ : ℂ) + (v : ℂ) * I) with hf
  -- continuity
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hcont : Continuous f := by
    rw [hf]
    refine Continuous.mul (Continuous.mul ?_ ?_) ?_
    · exact (Continuous.const_cpow (by fun_prop) (Or.inl hx0))
    · exact GaloisForLFunctions.SelbergClass.continuous_Gamma_line_of_pos hσ0
    · rw [continuous_iff_continuousAt]
      intro v
      have hne : ((σ : ℂ) + (v : ℂ) * I) ≠ 1 := by
        intro hcon
        have hre := congrArg Complex.re hcon
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, Complex.one_re] at hre
        exact hσ1 (by linarith)
      have hinner : ContinuousAt (fun v : ℝ => (σ : ℂ) + (v : ℂ) * I) v := by fun_prop
      have hg : ContinuousAt (estermannZeta q ((a : ZMod q))) ((σ : ℂ) + (v : ℂ) * I) :=
        (differentiableAt_estermannZeta a hne).continuousAt
      exact ContinuousAt.comp (g := estermannZeta q ((a : ZMod q)))
        (f := fun v : ℝ => (σ : ℂ) + (v : ℂ) * I) hg hinner
  -- the tail bound
  obtain ⟨CΓ, NΓ, hCΓ0, hCΓ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip hσ0 σ
  obtain ⟨CD, ND, hCD0, hCD⟩ := exists_bound_norm_estermannZeta_strip q a
  set Mx : ℝ := x ^ (-σ) with hMx
  have hMx0 : 0 < Mx := Real.rpow_pos_of_pos hx _
  set K₀ : ℝ := Mx * CΓ * CD with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  set N : ℕ := NΓ + ND with hN
  have htail : ∀ v : ℝ, 1 ≤ |v| →
      ‖f v‖ ≤ K₀ * ((1 + |v|) ^ N * Real.exp (-(Real.pi / 2) * |v|)) := by
    intro v hv
    have hre : ((σ : ℂ) + (v : ℂ) * I).re = σ := by simp
    have him : ((σ : ℂ) + (v : ℂ) * I).im = v := by simp
    have hxb : ‖((x : ℝ) : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * I))‖ = Mx := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.neg_re, hre, hMx]
    have hΓb := hCΓ σ v le_rfl le_rfl hv
    have hDb : ‖estermannZeta q ((a : ZMod q)) ((σ : ℂ) + (v : ℂ) * I)‖ ≤ CD * (1 + |v|) ^ ND := by
      have h := hCD ((σ : ℂ) + (v : ℂ) * I) (by rw [hre]; linarith) (by rw [hre]; exact hσ2)
        (by rw [him]; exact hv)
      rw [him] at h
      exact h
    have hpow : |v| ^ NΓ ≤ (1 + |v|) ^ NΓ :=
      pow_le_pow_left₀ (abs_nonneg v) (by linarith [abs_nonneg v]) NΓ
    have hΓb' : ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * I)‖
        ≤ CΓ * (1 + |v|) ^ NΓ * Real.exp (-(Real.pi * |v| / 2)) :=
      hΓb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCΓ0)
        (Real.exp_pos _).le)
    show ‖((x : ℝ) : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * I)) * Complex.Gamma ((σ : ℂ) + (v : ℂ) * I) *
        estermannZeta q ((a : ZMod q)) ((σ : ℂ) + (v : ℂ) * I)‖ ≤ _
    rw [norm_mul, norm_mul, hxb]
    calc Mx * ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * I)‖
            * ‖estermannZeta q ((a : ZMod q)) ((σ : ℂ) + (v : ℂ) * I)‖
        ≤ Mx * (CΓ * (1 + |v|) ^ NΓ * Real.exp (-(Real.pi * |v| / 2))) * (CD * (1 + |v|) ^ ND) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hΓb' hMx0.le) hDb (norm_nonneg _) ?_
          positivity
      _ = K₀ * ((1 + |v|) ^ N * Real.exp (-(Real.pi / 2) * |v|)) := by
          rw [hK₀, hN, pow_add, show -(Real.pi * |v| / 2) = -(Real.pi / 2) * |v| by ring]
          ring
  -- the compact part
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  set K : ℝ := K₀ + (max C₁ 0) * Real.exp (Real.pi / 2) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hmaj : Integrable (fun v : ℝ => K * ((1 + |v|) ^ N * Real.exp (-(Real.pi / 2) * |v|))) :=
    (GaloisForLFunctions.SelbergClass.integrable_one_add_abs_pow_mul_exp_neg_abs N
      (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul K
  refine Integrable.mono' hmaj hcont.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro v
  have hbase : (0 : ℝ) ≤ (1 + |v|) ^ N * Real.exp (-(Real.pi / 2) * |v|) := by positivity
  have hexpid : Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  rcases le_or_gt 1 |v| with hbig | hsmall
  · refine (htail v hbig).trans ?_
    have hKK : K₀ ≤ K := by
      rw [hK]
      nlinarith [le_max_right C₁ 0, Real.exp_pos (Real.pi / 2)]
    exact mul_le_mul_of_nonneg_right hKK hbase
  · have hmem : v ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc, ← abs_le]
      exact le_of_lt hsmall
    have h := le_trans (hC₁ v hmem) (le_max_left C₁ 0)
    have hlow : Real.exp (-(Real.pi / 2)) ≤ Real.exp (-(Real.pi / 2) * |v|) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [abs_nonneg v, le_of_lt hsmall, Real.pi_pos]
    have hone : (1 : ℝ) ≤ (1 + |v|) ^ N := one_le_pow₀ (by linarith [abs_nonneg v])
    have hprod : Real.exp (-(Real.pi / 2)) ≤ (1 + |v|) ^ N * Real.exp (-(Real.pi / 2) * |v|) := by
      nlinarith [hone, hlow, Real.exp_pos (-(Real.pi / 2))]
    have hstep : max C₁ 0 ≤ K * Real.exp (-(Real.pi / 2)) := by
      rw [hK]
      nlinarith [hK₀0, hexpid, le_max_right C₁ 0, Real.exp_pos (-(Real.pi / 2))]
    calc ‖f v‖ ≤ max C₁ 0 := h
      _ ≤ K * Real.exp (-(Real.pi / 2)) := hstep
      _ ≤ K * ((1 + |v|) ^ N * Real.exp (-(Real.pi / 2) * |v|)) :=
          mul_le_mul_of_nonneg_left hprod hK0

end

end RHTower
