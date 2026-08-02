import GaloisForLFunctions.HTGeometry.GammaShiftExpIntegral
import GaloisForLFunctions.HTGeometry.DigammaVerticalUniformLog
import GaloisForLFunctions.HTGeometry.GammaShiftDatumAlgebra

/-!
# Equation (14): the ratio of two Gamma translates is a real power

`Γ(z+λ) = Γ(z)·exp(∫₀^λ ψ(z+u) du)` turns the comparison of two translates into the asymptotics of
the integrated digamma.  On a vertical line the digamma is `log s + O(1/t)` uniformly in the
abscissa, and the complex logarithm of `σ+it` differs from `log t + iπ/2` by `o(1)`, so the integral
is
`λ·log s + o(1)` and

`Γ((σ+λ)+it) / (Γ(σ+it)·(σ+it)^λ) → 1`.

That is eq. (14) with the error term in the form the boundary datum consumes: the shifted Gamma has
datum `(1, λ, 0)` with residue `1` against the unshifted reference shape.
-/

open Filter Set Topology Function intervalIntegral

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The modulus of the vertical argument is asymptotically its height. -/
theorem tendsto_norm_vertical_div (σ : ℝ) :
    Tendsto (fun t : ℝ => ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / t) atTop (nhds 1) := by
  have hsq : Tendsto (fun t : ℝ => σ ^ 2 / t ^ 2 + 1) atTop (nhds (0 + 1)) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_pow_atTop (n := 2) (by norm_num)
  rw [zero_add] at hsq
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (σ ^ 2 / t ^ 2 + 1)) atTop (nhds 1) := by
    have := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hsq
    rwa [Real.sqrt_one] at this
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Complex.norm_add_mul_I,
    show σ ^ 2 + t ^ 2 = t ^ 2 * (σ ^ 2 / t ^ 2 + 1) by field_simp,
    Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]
  field_simp

/-- The logarithm of the modulus is asymptotically the logarithm of the height. -/
theorem tendsto_log_norm_vertical_sub (σ : ℝ) :
    Tendsto (fun t : ℝ => Real.log ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ - Real.log t) atTop
      (nhds 0) := by
  have hlog : Tendsto (fun t : ℝ => Real.log (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / t)) atTop
      (nhds 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      (tendsto_norm_vertical_div σ)
    rwa [Real.log_one] at this
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hs : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    refine norm_pos_iff.mpr ?_
    exact vertical_ne_zero_of_pos (σ := σ) ht
  rw [Real.log_div (ne_of_gt hs) (ne_of_gt ht)]

/-- The argument of the vertical line tends to a right angle. -/
theorem tendsto_arg_vertical (σ : ℝ) :
    Tendsto (fun t : ℝ => Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop
      (nhds (Real.pi / 2)) := by
  have hcont : ContinuousAt Complex.arg Complex.I := by
    refine Complex.continuousAt_arg ?_
    right
    simp
  have hinner : Tendsto (fun t : ℝ => ((σ / t : ℝ) : ℂ) + Complex.I) atTop
      (nhds ((0 : ℂ) + Complex.I)) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    have hreal : Tendsto (fun t : ℝ => σ / t) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact (Complex.continuous_ofReal.tendsto 0).comp hreal
  rw [zero_add] at hinner
  have hcomp := hcont.tendsto.comp hinner
  rw [Complex.arg_I] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt ht
  have hval : (σ : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * (((σ / t : ℝ) : ℂ) + Complex.I) := by
    push_cast
    field_simp
  show Complex.arg (((σ / t : ℝ) : ℂ) + Complex.I) = Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I)
  rw [hval, Complex.arg_real_mul _ ht]

/-- **The complex logarithm on a vertical line is the vertical logarithm up to `o(1)`.** -/
theorem tendsto_log_vertical_sub_vertLog (σ : ℝ) :
    Tendsto (fun t : ℝ => Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t) atTop
      (nhds 0) := by
  have hre : Tendsto (fun t : ℝ =>
      ((Real.log ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ - Real.log t : ℝ) : ℂ)) atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp (tendsto_log_norm_vertical_sub σ)
    rw [Complex.ofReal_zero] at h
    refine h.congr fun t => ?_
    simp [Function.comp_apply, Complex.ofReal_sub]
  have him : Tendsto (fun t : ℝ =>
      ((Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I) - Real.pi / 2 : ℝ) : ℂ) * Complex.I) atTop
      (nhds 0) := by
    have hsub : Tendsto (fun t : ℝ =>
        Complex.arg ((σ : ℂ) + (t : ℂ) * Complex.I) - Real.pi / 2) atTop (nhds 0) := by
      have := (tendsto_arg_vertical σ).sub (tendsto_const_nhds (x := Real.pi / 2))
      simpa using this
    have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hsub
    have := hc.mul (tendsto_const_nhds (x := Complex.I))
    simpa using this
  have hsum := hre.add him
  rw [add_zero] at hsum
  refine hsum.congr fun t => ?_
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, vertLog]
  · simp [Complex.log_im, vertLog]

/-- **Equation (14).**  The ratio of two Gamma translates on a vertical line is the corresponding
real power of the argument, up to `1 + o(1)`. -/
theorem tendsto_gammaShift_ratio {σ : ℝ} (hσ : 0 < σ) {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun t : ℝ => gammaLine (σ + lam) t
      / (gammaLine σ t * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ))) atTop (nhds 1) := by
  classical
  -- the integrated digamma against the logarithm
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bound_digamma_sub_vertLog (M := σ + lam)
    (by linarith)
  have hkey : Tendsto (fun t : ℝ =>
      (∫ u in (0 : ℝ)..lam, Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
        - (lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
    have hsplit : ∀ t : ℝ, 1 ≤ t →
        (∫ u in (0 : ℝ)..lam, Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
          - (lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)
        = (∫ u in (0 : ℝ)..lam,
            (Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)) - vertLog t))
          + (lam : ℂ) * (vertLog t - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      intro t ht
      have hcont : ContinuousOn (fun u : ℝ =>
          Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ))) (Set.uIcc 0 lam) := by
        refine (continuousOn_digamma_shift ((σ : ℂ) + (t : ℂ) * Complex.I)).mono ?_
        intro v hv
        rw [Set.uIcc_of_le hlam] at hv
        have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
        show -((σ : ℂ) + (t : ℂ) * Complex.I).re < v
        rw [hre]
        have : (0 : ℝ) ≤ v := hv.1
        linarith
      have hint : IntervalIntegrable (fun u : ℝ =>
          Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
          MeasureTheory.volume 0 lam := hcont.intervalIntegrable
      rw [intervalIntegral.integral_sub hint (intervalIntegrable_const),
        intervalIntegral.integral_const]
      simp only [Complex.real_smul, sub_zero]
      ring
    have hbnd : Tendsto (fun t : ℝ =>
        (∫ u in (0 : ℝ)..lam,
          (Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)) - vertLog t))) atTop
        (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hsq : Tendsto (fun t : ℝ => C / t * |lam - 0|) atTop (nhds 0) := by
        have hCt : Tendsto (fun t : ℝ => C / t) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        simpa using hCt.mul_const (|lam - 0|)
      refine squeeze_zero' (by filter_upwards with t using norm_nonneg _) ?_ hsq
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro u hu
      rw [Set.uIoc_of_le hlam] at hu
      have hu0 : 0 ≤ u := le_of_lt hu.1
      have huM : σ + u ≤ σ + lam := by linarith [hu.2]
      have hval : ((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)
          = ((σ + u : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hval]
      exact hbound (σ + u) t (by linarith) huM ht
    have hneg : Tendsto (fun t : ℝ =>
        vertLog t - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
      have h := (tendsto_log_vertical_sub_vertLog σ).neg
      rw [neg_zero] at h
      refine h.congr fun t => ?_
      ring
    have hlog := (tendsto_const_nhds (x := (lam : ℂ))).mul hneg
    rw [mul_zero] at hlog
    have hsum := hbnd.add hlog
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact (hsplit t ht).symm
  -- exponentiate
  have hexp := (Complex.continuous_exp.tendsto (0 : ℂ)).comp hkey
  rw [Complex.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hzre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
    have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [this]
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
  show Complex.exp ((∫ u in (0 : ℝ)..lam,
        Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (u : ℂ)))
      - (lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I))
    = gammaLine (σ + lam) t / (gammaLine σ t * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ))
  rw [hshift, hcpow, Complex.exp_sub]
  have hexpne : Complex.exp ((lam : ℂ) * Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp

/-- **The shifted Gamma has datum `(1, λ, 0)` with residue `1`** against the unshifted reference
shape: this is eq. (14) in the form the boundary datum consumes. -/
theorem hasShiftDatum_gammaShift {σ : ℝ} (hσ : 0 < σ) {lam : ℝ} (hlam : 0 ≤ lam) :
    HasShiftDatum 0 σ (fun t => gammaLine (σ + lam) t) 1 lam 0 1 := by
  refine ⟨one_ne_zero, ?_⟩
  refine (tendsto_gammaShift_ratio hσ hlam).congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  have htpos : (0 : ℝ) < t := by linarith
  refine congrArg (fun w => gammaLine (σ + lam) t / w) ?_
  rw [gammaShiftShape, add_zero, zpow_one, zpow_zero, mul_one]

end

end GaloisForLFunctions.HTGeometry
