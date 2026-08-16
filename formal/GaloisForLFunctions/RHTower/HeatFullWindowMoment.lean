import GaloisForLFunctions.RHTower.HeatMomentAsymptotic
import GaloisForLFunctions.RHTower.HeatMultiplierFourier
import GaloisForLFunctions.RHTower.BoundaryGermL2

/-!
# The full-window Gaussian moment of the heat multiplier

The heat multiplier is even, so the moment of `|θ|^λ` over the full window `(-π, π]` is twice the
half-window moment.  Combined with the half-window asymptotic this gives equation `(6)` in the
card's normalisation.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-- The heat multiplier is even. -/
theorem heatMultiplier_even (x θ : ℝ) : heatMultiplier x (-θ) = heatMultiplier x θ := by
  have h := (Equiv.neg ℤ).tsum_eq
    (fun k : ℤ => Complex.exp (-(Real.pi : ℂ) * x * (k : ℂ) ^ 2 + I * (k : ℂ) * (-θ : ℝ)))
  rw [heatMultiplier, heatMultiplier, ← h]
  refine tsum_congr fun k => ?_
  congr 1
  simp only [Equiv.neg_apply]
  push_cast
  ring

/-- Reflecting the window. -/
theorem setIntegral_reflect_window {x : ℝ} {lam : ℂ} :
    (∫ θ in Ioc (-Real.pi) 0, ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
      = ∫ θ in Ioc (0 : ℝ) Real.pi, ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : (∫ θ in Ioc (-Real.pi) 0, ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
      = ∫ θ in (-Real.pi)..(0 : ℝ), ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ := by
    rw [intervalIntegral.integral_of_le (by linarith)]
  have h2 : (∫ θ in (0 : ℝ)..Real.pi,
      ((|(-θ)| : ℝ) : ℂ) ^ lam * heatMultiplier x (-θ))
      = ∫ θ in (-Real.pi)..(0 : ℝ), ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ := by
    have := intervalIntegral.integral_comp_neg
      (f := fun θ : ℝ => ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ) (a := (0 : ℝ)) (b := Real.pi)
    simpa using this
  rw [h1, ← h2, intervalIntegral.integral_of_le hpi.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
  have hθ0 : (0 : ℝ) < θ := hθ.1
  rw [abs_neg, abs_of_pos hθ0, heatMultiplier_even]

/-- The `|θ|`-weighted integrand is integrable on the negative half window. -/
theorem integrableOn_abs_cpow_mul_heatMultiplier_neg {lam : ℂ} (hlam : -1 < lam.re) {x : ℝ}
    (hx : 0 < x) :
    IntegrableOn (fun θ : ℝ => ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
      (Ioc (-Real.pi) 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-Real.pi)) (b := Real.pi)).exists_bound_of_continuousOn
    ((continuous_heatMultiplier hx).continuousOn)
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
      (volume.restrict (Ioc (-Real.pi) 0)) := by
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Ioc (a := (-Real.pi)) (b := (0 : ℝ))).symm]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ContinuousOn.mul ?_ ((continuous_heatMultiplier hx).continuousOn)
    intro θ hθ
    have hθ0 : θ < 0 := hθ.2
    have hpos : (0 : ℝ) < |θ| := abs_pos.mpr (ne_of_lt hθ0)
    have hslit : (((|θ| : ℝ)) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by simpa using hpos)
    have h1 : ContinuousAt (fun t : ℝ => (((|t| : ℝ)) : ℂ)) θ := by fun_prop
    exact (ContinuousAt.comp (g := fun z : ℂ => z ^ lam)
      (f := fun t : ℝ => (((|t| : ℝ)) : ℂ)) (x := θ)
      (continuousAt_cpow_const hslit) h1).continuousWithinAt
  have hmaj : IntegrableOn (fun θ : ℝ => M * |θ| ^ lam.re) (Ioc (-Real.pi) 0) := by
    refine (Integrable.const_mul ((integrableOn_abs_rpow_window hlam).mono_set ?_) M)
    intro y hy
    exact ⟨hy.1, by linarith [hy.2, hpi]⟩
  have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae hne0] with θ hθ hne
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have hmem : θ ∈ Icc (-Real.pi) Real.pi := ⟨hθ.1.le, by linarith [hθ.2, hpi]⟩
  have hθle : θ ≤ 0 := hθ.2
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have := hM θ hmem
  have hnn : (0 : ℝ) ≤ |θ| ^ lam.re := Real.rpow_nonneg (abs_nonneg θ) _
  calc |θ| ^ lam.re * ‖heatMultiplier x θ‖ ≤ |θ| ^ lam.re * M :=
        mul_le_mul_of_nonneg_left this hnn
    _ = M * |θ| ^ lam.re := by ring

/-- **The full-window moment is twice the half-window moment.** -/
theorem integral_abs_cpow_mul_heatMultiplier_window {lam : ℂ} (hlam : -1 < lam.re) {x : ℝ}
    (hx : 0 < x) :
    (∫ θ in Ioc (-Real.pi) Real.pi, ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
      = 2 * ∫ θ in Ioc (0 : ℝ) Real.pi, ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : IntegrableOn (fun θ : ℝ => ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
      (Ioc (0 : ℝ) Real.pi) := by
    refine (integrableOn_cpow_mul_heatMultiplier hlam hx).congr_fun (fun θ hθ => ?_)
      measurableSet_Ioc
    have hθ0 : (0 : ℝ) < θ := hθ.1
    rw [abs_of_pos hθ0]
  have hdisj : Disjoint (Ioc (-Real.pi) 0) (Ioc (0 : ℝ) Real.pi) := by
    rw [Set.disjoint_left]
    intro a ha ha'
    exact absurd ha'.1 (by simpa using ha.2)
  have hsplit := MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
    (integrableOn_abs_cpow_mul_heatMultiplier_neg hlam hx) hpos
  rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) hpi.le] at hsplit
  rw [hsplit, setIntegral_reflect_window]
  have hcongr : (∫ θ in Ioc (0 : ℝ) Real.pi, ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
      = ∫ θ in Ioc (0 : ℝ) Real.pi, ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    have hθ0 : (0 : ℝ) < θ := hθ.1
    rw [abs_of_pos hθ0]
  rw [hcongr]
  ring

/-- The normalised full-window moment: the card's `(1/2π) ∫_{-π}^{π} W_x |θ|^λ dθ`. -/
noncomputable def heatMoment (x : ℝ) (lam : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ)))
    * ∫ θ in Ioc (-Real.pi) Real.pi, ((|θ| : ℝ) : ℂ) ^ lam * heatMultiplier x θ

/-- The card's main term `(4πx)^{λ/2} Γ((λ+1)/2) / √π`. -/
noncomputable def heatMomentTerm (x : ℝ) (lam : ℂ) : ℂ :=
  (((4 * Real.pi * x : ℝ)) : ℂ) ^ (lam / 2) * Complex.Gamma ((lam + 1) / 2)
    / ((Real.sqrt Real.pi : ℝ) : ℂ)

/-- **Equation `(6)`.**  The normalised window moment is the Gaussian absolute moment up to an
exponentially small error. -/
theorem norm_heatMoment_sub_term_le {lam : ℂ} (hlam : -1 < lam.re) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖heatMoment x lam - heatMomentTerm x lam‖
      ≤ (1 / Real.pi) * (x ^ (-(1 : ℝ) / 2)
        * (Real.exp (-(Real.pi / (4 * x))) * heatTailConst
              * (Real.pi ^ (lam.re + 1) / (lam.re + 1))
          + Real.exp (-(Real.pi / (8 * x)))
              * (1 / 2 * (8 * Real.pi * x) ^ ((lam.re + 1) / 2)
                  * Real.Gamma ((lam.re + 1) / 2)))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpine : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
  have hfull := integral_abs_cpow_mul_heatMultiplier_window hlam hx
  have hmain := heatMomentMain_eq lam hx
  have hkey : heatMoment x lam - heatMomentTerm x lam
      = (1 / ((Real.pi : ℝ) : ℂ))
        * ((∫ θ in Ioc (0 : ℝ) Real.pi, ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
          - ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
            * (1 / 2 * (((4 * Real.pi * x : ℝ)) : ℂ) ^ ((lam + 1) / 2)
                * Complex.Gamma ((lam + 1) / 2))) := by
    rw [heatMoment, heatMomentTerm, hfull, ← hmain]
    field_simp
  rw [hkey, norm_mul]
  have hnorm : ‖(1 : ℂ) / ((Real.pi : ℝ) : ℂ)‖ = 1 / Real.pi := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hpi.le]
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left (norm_heatWindowMoment_sub_main_le hlam hx hx1)
    (by positivity)

/-- The window multiplier has total mass one. -/
theorem heatMoment_zero {x : ℝ} (hx : 0 < x) : heatMoment x 0 = 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpine : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
  have hcongr : (∫ θ in Ioc (-Real.pi) Real.pi, ((|θ| : ℝ) : ℂ) ^ (0 : ℂ) * heatMultiplier x θ)
      = ∫ θ in Ioc (-Real.pi) Real.pi,
          heatMultiplier x θ * Complex.exp (I * ((0 : ℤ) : ℂ) * (θ : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    rw [Complex.cpow_zero, one_mul]
    simp
  rw [heatMoment, hcongr, integral_heatMultiplier_mul_exp hx]
  have hz : heatCoeff x 0 = 1 := by
    rw [heatCoeff]
    norm_num
  rw [hz]
  push_cast
  field_simp

/-! ## Vanishing of the positive moments -/

/-- `exp(-a/x) → 0` as `x` decreases to zero. -/
theorem tendsto_exp_neg_div_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.exp (-(a / x))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have hdiv : Tendsto (fun x : ℝ => a / x) (𝓝[>] (0 : ℝ)) atTop := by
    have := hinv.const_mul_atTop ha
    refine this.congr fun x => ?_
    rw [div_eq_mul_inv]
  have hneg : Tendsto (fun x : ℝ => -(a / x)) (𝓝[>] (0 : ℝ)) atBot :=
    tendsto_neg_atTop_atBot.comp hdiv
  exact Real.tendsto_exp_atBot.comp hneg

/-- `x^{-1/2} exp(-a/x) → 0` as `x` decreases to zero. -/
theorem tendsto_rpow_neg_half_mul_exp {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => x ^ (-(1 : ℝ) / 2) * Real.exp (-(a / x))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hmaj : Tendsto (fun x : ℝ => (2 / a) * Real.exp (-(a / (2 * x)))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hbase : Tendsto (fun x : ℝ => Real.exp (-(a / 2 / x))) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_exp_neg_div_nhdsGT_zero (by positivity)
    have := hbase.const_mul (2 / a)
    rw [mul_zero] at this
    refine this.congr fun x => ?_
    congr 2
    rw [div_div]
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    positivity
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with x hx hx1
    have hx0 : (0 : ℝ) < x := hx
    have hxle : x ≤ 1 := hx1.2.le
    have hstep := rpow_neg_half_le_exp ha hx0 hxle
    have hexp : (0 : ℝ) < Real.exp (-(a / x)) := Real.exp_pos _
    have hchain : x ^ (-(1 : ℝ) / 2) * Real.exp (-(a / x))
        ≤ (2 / a) * Real.exp (a / (2 * x)) * Real.exp (-(a / x)) :=
      mul_le_mul_of_nonneg_right hstep hexp.le
    refine hchain.trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring

/-- **The positive moments of the heat multiplier vanish in the small-aperture limit.** -/
theorem tendsto_heatMoment_of_pos_re {lam : ℂ} (hlam : 0 < lam.re) :
    Tendsto (fun x : ℝ => heatMoment x lam) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlam' : -1 < lam.re := by linarith
  -- the main term tends to zero
  have hterm : Tendsto (fun x : ℝ => heatMomentTerm x lam) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ x : ℝ, 0 < x → ‖heatMomentTerm x lam‖
        = (4 * Real.pi * x) ^ (lam.re / 2)
          * (‖Complex.Gamma ((lam + 1) / 2)‖ / Real.sqrt Real.pi) := by
      intro x hx
      have h4 : (0 : ℝ) < 4 * Real.pi * x := by positivity
      rw [heatMomentTerm, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h4,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_div_assoc]
      congr 2
      simp
    have hbase : Tendsto (fun x : ℝ => (4 * Real.pi * x) ^ (lam.re / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcont : Continuous (fun x : ℝ => 4 * Real.pi * x) := by fun_prop
      have hlin : Tendsto (fun x : ℝ => 4 * Real.pi * x) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        have := hcont.tendsto (0 : ℝ)
        simpa using this
      have hrpow : Tendsto (fun y : ℝ => y ^ (lam.re / 2)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hc := Real.continuousAt_rpow_const (0 : ℝ) (lam.re / 2)
          (Or.inr (by linarith))
        have hz : (0 : ℝ) ^ (lam.re / 2) = 0 := Real.zero_rpow (by linarith)
        have := hc.tendsto
        rwa [hz] at this
      exact (hrpow.comp hlin).mono_left nhdsWithin_le_nhds
    have := hbase.mul_const (‖Complex.Gamma ((lam + 1) / 2)‖ / Real.sqrt Real.pi)
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hnorm x hx).symm
  -- the error tends to zero
  set C₁ : ℝ := heatTailConst * (Real.pi ^ (lam.re + 1) / (lam.re + 1)) with hC₁
  set C₂ : ℝ := 1 / 2 * (8 * Real.pi) ^ ((lam.re + 1) / 2) * Real.Gamma ((lam.re + 1) / 2)
    with hC₂
  have hC₁nn : 0 ≤ C₁ := by
    rw [hC₁]
    have := heatTailConst_nonneg
    have hp : (0 : ℝ) < Real.pi ^ (lam.re + 1) := Real.rpow_pos_of_pos hpi _
    positivity
  have hC₂nn : 0 ≤ C₂ := by
    rw [hC₂]
    have hg : 0 ≤ Real.Gamma ((lam.re + 1) / 2) :=
      Real.Gamma_nonneg_of_nonneg (by linarith)
    have hp : (0 : ℝ) < (8 * Real.pi) ^ ((lam.re + 1) / 2) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hmaj : Tendsto (fun x : ℝ => (1 / Real.pi)
      * (C₁ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-((Real.pi / 4) / x)))
        + C₂ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-((Real.pi / 8) / x)))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_half_mul_exp (a := Real.pi / 4) (by positivity)).const_mul C₁
    have h2 := (tendsto_rpow_neg_half_mul_exp (a := Real.pi / 8) (by positivity)).const_mul C₂
    rw [mul_zero] at h1 h2
    have := (h1.add h2).const_mul (1 / Real.pi)
    rw [add_zero, mul_zero] at this
    exact this
  have hdiff : Tendsto (fun x : ℝ => heatMoment x lam - heatMomentTerm x lam)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with x hx hx1
    have hx0 : (0 : ℝ) < x := hx
    have hxle : x ≤ 1 := hx1.2.le
    refine (norm_heatMoment_sub_term_le hlam' hx0 hxle).trans ?_
    have hpow : (0 : ℝ) ≤ x ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
    have harg1 : Real.pi / (4 * x) = (Real.pi / 4) / x := by
      rw [div_div]
    have harg2 : Real.pi / (8 * x) = (Real.pi / 8) / x := by
      rw [div_div]
    rw [harg1, harg2]
    have hscale : (8 * Real.pi * x) ^ ((lam.re + 1) / 2)
        ≤ (8 * Real.pi) ^ ((lam.re + 1) / 2) := by
      have hb : (0 : ℝ) < 8 * Real.pi := by positivity
      have : (8 * Real.pi * x) ^ ((lam.re + 1) / 2)
          = (8 * Real.pi) ^ ((lam.re + 1) / 2) * x ^ ((lam.re + 1) / 2) := by
        rw [Real.mul_rpow hb.le hx0.le]
      rw [this]
      have hx1' : x ^ ((lam.re + 1) / 2) ≤ 1 := by
        exact Real.rpow_le_one hx0.le hxle (by linarith : (0:ℝ) ≤ (lam.re + 1) / 2)
      nlinarith [Real.rpow_pos_of_pos hb ((lam.re + 1) / 2),
        Real.rpow_nonneg hx0.le ((lam.re + 1) / 2)]
    have hg : 0 ≤ Real.Gamma ((lam.re + 1) / 2) := Real.Gamma_nonneg_of_nonneg (by linarith)
    have hstep : x ^ (-(1 : ℝ) / 2)
        * (Real.exp (-(Real.pi / 4 / x)) * heatTailConst
              * (Real.pi ^ (lam.re + 1) / (lam.re + 1))
          + Real.exp (-(Real.pi / 8 / x))
              * (1 / 2 * (8 * Real.pi * x) ^ ((lam.re + 1) / 2)
                  * Real.Gamma ((lam.re + 1) / 2)))
        ≤ C₁ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(Real.pi / 4 / x)))
          + C₂ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(Real.pi / 8 / x))) := by
      rw [hC₁, hC₂]
      have he1 : (0 : ℝ) < Real.exp (-(Real.pi / 4 / x)) := Real.exp_pos _
      have he2 : (0 : ℝ) < Real.exp (-(Real.pi / 8 / x)) := Real.exp_pos _
      nlinarith [mul_nonneg hpow he2.le, mul_nonneg (mul_nonneg hpow he2.le) hg,
        mul_le_mul_of_nonneg_right hscale hg,
        mul_nonneg (mul_nonneg hpow he2.le) (mul_nonneg hg (le_of_lt
          (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 8 * Real.pi) ((lam.re + 1) / 2))))]
    have hfin : (1 / Real.pi) * (x ^ (-(1 : ℝ) / 2)
        * (Real.exp (-(Real.pi / 4 / x)) * heatTailConst
              * (Real.pi ^ (lam.re + 1) / (lam.re + 1))
          + Real.exp (-(Real.pi / 8 / x))
              * (1 / 2 * (8 * Real.pi * x) ^ ((lam.re + 1) / 2)
                  * Real.Gamma ((lam.re + 1) / 2))))
        ≤ (1 / Real.pi) * (C₁ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(Real.pi / 4 / x)))
          + C₂ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(Real.pi / 8 / x)))) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    exact hfin
  have := hdiff.add hterm
  rw [zero_add] at this
  refine this.congr fun x => ?_
  ring

end RHTower
