import GaloisForLFunctions.HTGeometry.CarlemanOperatorBound

/-!
# The conductor Hankel kernel is bounded on the half line

The real-place conductor commutator has, in the Fourier picture, the Hankel kernel

`k(u + v) = 2π e^{-2(u+v)} / (u+v)`,

obtained by integrating the rank-one Hankel kernels of the resolvents `1/(λ + 2 + iξ)` over
`λ ∈ (0, ∞)`.  The exponential factor is harmless: pointwise `k(r) ≤ 2π/r`, so the Carleman
(Hilbert) kernel dominates and Schur's test for that kernel gives the bound directly.

This is what replaces the Coifman–Rochberg–Weiss commutator theorem for this symbol.  On the
physical side the row integrals of `(b(x) − b(y))/(x − y)` diverge, which is the `BMO` borderline;
on the Fourier side the exponential factor puts the kernel under the Carleman kernel and an
elementary test closes it.
-/

open MeasureTheory Set Filter Topology ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The conductor Hankel kernel `2π e^{-2r}/r` on the half line. -/
def conductorHankelKernel (r : ℝ) : ℝ := 2 * Real.pi * Real.exp (-2 * r) / r

theorem conductorHankelKernel_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ conductorHankelKernel r := by
  rw [conductorHankelKernel]
  positivity

/-- The exponential factor puts the conductor kernel under the Carleman kernel. -/
theorem conductorHankelKernel_le {r : ℝ} (hr : 0 < r) :
    conductorHankelKernel r ≤ 2 * Real.pi * (1 / r) := by
  rw [conductorHankelKernel, div_le_iff₀ hr]
  have hexp : Real.exp (-2 * r) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    linarith
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  calc 2 * Real.pi * Real.exp (-2 * r) ≤ 2 * Real.pi * 1 :=
        mul_le_mul_of_nonneg_left hexp hpi.le
    _ = 2 * Real.pi * (1 / r) * r := by field_simp

/-- **The conductor Hankel bound.**  Schur's test for the Carleman kernel transfers verbatim to
the conductor kernel, with the constant `(2π)² π²`. -/
theorem lintegral_conductorHankel_sq_le {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ s in Ioi (0:ℝ),
        (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t) ^ 2)
      ≤ ENNReal.ofReal (4 * Real.pi ^ 4) * ∫⁻ t in Ioi (0:ℝ), F t ^ 2 := by
  have hstep : ∀ s ∈ Ioi (0:ℝ),
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t) ^ 2
        ≤ ENNReal.ofReal (2 * Real.pi) ^ 2
          * (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hinner : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t)
        ≤ ENNReal.ofReal (2 * Real.pi)
          * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t := by
      rw [← lintegral_const_mul']
      · refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
        have ht0 : (0 : ℝ) < t := ht
        have hst : (0 : ℝ) < s + t := by linarith
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (conductorHankelKernel_le hst)) le_rfl
      · exact ENNReal.ofReal_ne_top
    calc (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t) ^ 2
        ≤ (ENNReal.ofReal (2 * Real.pi)
            * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
          exact pow_le_pow_left' hinner 2
      _ = ENNReal.ofReal (2 * Real.pi) ^ 2
            * (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
          rw [mul_pow]
  have houter : (∫⁻ s in Ioi (0:ℝ),
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t) ^ 2)
      ≤ ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (2 * Real.pi) ^ 2
        * (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 :=
    setLIntegral_mono' measurableSet_Ioi hstep
  have hconst : (∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (2 * Real.pi) ^ 2
        * (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2)
      = ENNReal.ofReal (2 * Real.pi) ^ 2
        * ∫⁻ s in Ioi (0:ℝ), (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
    rw [← lintegral_const_mul']
    exact pow_ne_top ENNReal.ofReal_ne_top
  refine le_trans houter ?_
  rw [hconst]
  refine le_trans (mul_le_mul' le_rfl (lintegral_carleman_sq_le hF)) ?_
  rw [← mul_assoc]
  refine mul_le_mul' ?_ le_rfl
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

/-! ## The kernel is the resolvent family integrated -/

/-- The Hankel kernel of the resolvent `1/(λ + 2 + iξ)` is the rank-one kernel
`2π e^{-(λ+2)(u+v)}`; integrating over `λ` produces the conductor kernel. -/
theorem integral_resolventHankel {r : ℝ} (hr : 0 < r) :
    (∫ lam in Ioi (0:ℝ), 2 * Real.pi * Real.exp (-(lam + 2) * r)) = conductorHankelKernel r := by
  have hderiv : ∀ lam ∈ Ioi (0:ℝ),
      HasDerivAt (fun m : ℝ => -(2 * Real.pi / r) * Real.exp (-(m + 2) * r))
        (2 * Real.pi * Real.exp (-(lam + 2) * r)) lam := by
    intro lam _
    have hinner : HasDerivAt (fun m : ℝ => -(m + 2) * r) (-r) lam := by
      have h := ((hasDerivAt_id lam).add_const (2 : ℝ)).neg.mul_const r
      refine h.congr_deriv ?_
      ring
    have h := (Real.hasDerivAt_exp (-(lam + 2) * r)).comp lam hinner
    have h2 := h.const_mul (-(2 * Real.pi / r))
    refine h2.congr_deriv ?_
    field_simp
  have hlim : Tendsto (fun m : ℝ => -(2 * Real.pi / r) * Real.exp (-(m + 2) * r)) atTop (𝓝 0) := by
    have hexp : Tendsto (fun m : ℝ => Real.exp (-(m + 2) * r)) atTop (𝓝 0) := by
      have harg : Tendsto (fun m : ℝ => -(m + 2) * r) atTop atBot := by
        have hb : Tendsto (fun m : ℝ => -(m + 2)) atTop atBot := by
          have := tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_id)
          simpa [Function.comp_def] using this
        exact hb.atBot_mul_const hr
      simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp harg
    simpa using hexp.const_mul (-(2 * Real.pi / r))
  have hint : IntegrableOn (fun lam : ℝ => 2 * Real.pi * Real.exp (-(lam + 2) * r))
      (Ioi 0) volume := by
    refine integrableOn_Ioi_deriv_of_nonneg
      (g := fun m : ℝ => -(2 * Real.pi / r) * Real.exp (-(m + 2) * r))
      (l := 0) ?_ hderiv ?_ hlim
    · refine ContinuousAt.continuousWithinAt ?_
      exact (Real.continuous_exp.continuousAt.comp
        (((continuous_id.add continuous_const).neg.mul continuous_const).continuousAt)).const_mul _
    · intro lam _
      positivity
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun m : ℝ => -(2 * Real.pi / r) * Real.exp (-(m + 2) * r))
    (f' := fun lam : ℝ => 2 * Real.pi * Real.exp (-(lam + 2) * r))
    (by
      refine ContinuousAt.continuousWithinAt ?_
      exact (Real.continuous_exp.continuousAt.comp
        (((continuous_id.add continuous_const).neg.mul continuous_const).continuousAt)).const_mul _)
    hderiv hint hlim
  rw [hval, conductorHankelKernel]
  have hexp0 : Real.exp (-((0 : ℝ) + 2) * r) = Real.exp (-2 * r) := by
    congr 1
    ring
  rw [hexp0]
  field_simp
  ring

/-! ## The bilinear form -/

theorem measurable_conductorHankelTransform {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun u : ℝ =>
      ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (u + v)) * F v := by
  refine Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ =>
    ENNReal.ofReal (conductorHankelKernel (p.1 + p.2)) * F p.2) ?_
  refine Measurable.mul ?_ (hF.comp measurable_snd)
  refine ENNReal.measurable_ofReal.comp ?_
  refine Measurable.div ?_ (measurable_fst.add measurable_snd)
  exact measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (measurable_fst.add measurable_snd)))

/-- **The conductor Hankel form is bounded.**  Cauchy–Schwarz against the operator bound. -/
theorem lintegral_conductorHankel_form_le {F G : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ u in Ioi (0:ℝ),
        G u * ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (u + v)) * F v)
      ≤ ENNReal.ofReal (2 * Real.pi ^ 2)
        * ((∫⁻ u in Ioi (0:ℝ), G u ^ 2) ^ ((1 : ℝ) / 2)
          * (∫⁻ v in Ioi (0:ℝ), F v ^ 2) ^ ((1 : ℝ) / 2)) := by
  set T : ℝ → ℝ≥0∞ := fun u =>
    ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (u + v)) * F v with hT
  have hTmeas : Measurable T := measurable_conductorHankelTransform hF
  have hcs : (∫⁻ u in Ioi (0:ℝ), G u * T u)
      ≤ (∫⁻ u in Ioi (0:ℝ), G u ^ (2:ℝ)) ^ ((1:ℝ)/2)
        * (∫⁻ u in Ioi (0:ℝ), T u ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioi (0:ℝ)))
      Real.HolderConjugate.two_two hG.aemeasurable hTmeas.aemeasurable
    simpa [Pi.mul_apply] using this
  have hrw2 : ∀ x : ℝ≥0∞, x ^ (2:ℝ) = x ^ (2:ℕ) := fun x => ENNReal.rpow_two x
  simp only [hrw2] at hcs
  have hTsq : (∫⁻ u in Ioi (0:ℝ), T u ^ (2:ℕ))
      ≤ ENNReal.ofReal (4 * Real.pi ^ 4) * ∫⁻ v in Ioi (0:ℝ), F v ^ (2:ℕ) :=
    lintegral_conductorHankel_sq_le hF
  have hpow : ((∫⁻ u in Ioi (0:ℝ), T u ^ (2:ℕ)) ^ ((1:ℝ)/2))
      ≤ ENNReal.ofReal (2 * Real.pi ^ 2)
        * (∫⁻ v in Ioi (0:ℝ), F v ^ (2:ℕ)) ^ ((1:ℝ)/2) := by
    refine le_trans (ENNReal.rpow_le_rpow hTsq (by norm_num)) ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
    refine mul_le_mul' ?_ le_rfl
    have heq : ENNReal.ofReal (4 * Real.pi ^ 4) = ENNReal.ofReal (2 * Real.pi ^ 2) ^ (2:ℕ) := by
      rw [← ENNReal.ofReal_pow (by positivity)]
      congr 1
      ring
    rw [heq, ← ENNReal.rpow_natCast (ENNReal.ofReal (2 * Real.pi ^ 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ u in Ioi (0:ℝ), G u * T u)
      ≤ (∫⁻ u in Ioi (0:ℝ), G u ^ (2:ℕ)) ^ ((1:ℝ)/2)
        * (∫⁻ u in Ioi (0:ℝ), T u ^ (2:ℕ)) ^ ((1:ℝ)/2) := hcs
    _ ≤ (∫⁻ u in Ioi (0:ℝ), G u ^ (2:ℕ)) ^ ((1:ℝ)/2)
        * (ENNReal.ofReal (2 * Real.pi ^ 2)
          * (∫⁻ v in Ioi (0:ℝ), F v ^ (2:ℕ)) ^ ((1:ℝ)/2)) := mul_le_mul' le_rfl hpow
    _ = ENNReal.ofReal (2 * Real.pi ^ 2)
        * ((∫⁻ u in Ioi (0:ℝ), G u ^ (2:ℕ)) ^ ((1:ℝ)/2)
          * (∫⁻ v in Ioi (0:ℝ), F v ^ (2:ℕ)) ^ ((1:ℝ)/2)) := by ring

end

end GaloisForLFunctions.HTGeometry
