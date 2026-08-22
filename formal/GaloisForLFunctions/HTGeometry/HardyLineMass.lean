import GaloisForLFunctions.HTGeometry.HalfPlaneHardy
import GaloisForLFunctions.HTGeometry.LineScalingL2

/-!
# The mass of a Hardy function on vertical and horizontal segments

Two elementary consequences of the uniform `L²` bound on vertical lines.  First, the bound transfers
between the two parametrisations `w = σ + 2πiξ` and `w = σ + iy` of a line, at the cost of a factor
`2π`.  Second, Tonelli turns the bound into finiteness of the total mass over a vertical strip, so
the mass carried by the horizontal segment at height `T` is integrable in `T` and therefore vanishes
along a sequence of heights tending to infinity.  That sequence is what makes a contour shift across
the strip legitimate for a datum which is only square-integrable.

## Main results

* `memLp_two_hardyLine`
* `integral_norm_sq_hardyLine_le`
* `exists_seq_stripMass_tendsto_zero`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology

noncomputable section

theorem rayLine_inv_two_pi (σ y : ℝ) :
    rayLine σ ((2 * Real.pi)⁻¹ * y) = (σ : ℂ) + (y : ℝ) * Complex.I := by
  rw [rayLine]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  congr 2
  push_cast
  field_simp

/-- The `L²` bound on a vertical line, in the `w = σ + iy` parametrisation. -/
theorem memLp_two_hardyLine {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {σ : ℝ} (hσ : 0 < σ) :
    MemLp (fun y : ℝ => F ((σ : ℂ) + (y : ℝ) * Complex.I)) 2 volume := by
  have hne : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have h := memLp_two_comp_const_mul (hF.memLp σ hσ) hne
  refine h.ae_eq (Filter.Eventually.of_forall fun y => ?_)
  show F (rayLine σ ((2 * Real.pi)⁻¹ * y)) = F ((σ : ℂ) + (y : ℝ) * Complex.I)
  rw [rayLine_inv_two_pi]

/-- The mass on a vertical line, in the `w = σ + iy` parametrisation. -/
theorem integral_norm_sq_hardyLine_le {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {σ : ℝ}
    (hσ : 0 < σ) :
    (∫ y : ℝ, ‖F ((σ : ℂ) + (y : ℝ) * Complex.I)‖ ^ 2) ≤ 2 * Real.pi * M := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h := integral_norm_sq_comp_const_mul (fun ξ : ℝ => F (rayLine σ ξ)) (2 * Real.pi)⁻¹
  have heq : (∫ y : ℝ, ‖F ((σ : ℂ) + (y : ℝ) * Complex.I)‖ ^ 2)
      = |(2 * Real.pi)⁻¹|⁻¹ * ∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ 2 := by
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ‖F ((σ : ℂ) + (y : ℝ) * Complex.I)‖ ^ 2
      = ‖F (rayLine σ ((2 * Real.pi)⁻¹ * y))‖ ^ 2
    rw [rayLine_inv_two_pi]
  rw [heq, abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹), inv_inv]
  exact mul_le_mul_of_nonneg_left (hF.bound σ hσ) hpi.le

/-! ### The mass on the horizontal segments -/

/-- The mass of `F` on the horizontal segment `[c,d] × {T}`. -/
def stripMass (F : ℂ → ℂ) (c d T : ℝ) : ℝ :=
  ∫ σ in Icc c d, ‖F ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2

/-- `F` clamped into the closed vertical strip; globally continuous when `F` is holomorphic on the
half-plane and the strip lies inside it. -/
def stripClamp (F : ℂ → ℂ) (c d : ℝ) : ℂ → ℂ :=
  fun w => F (((max c (min w.re d) : ℝ) : ℂ) + (w.im : ℝ) * Complex.I)

theorem continuous_stripClamp {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {c d : ℝ}
    (hc : 0 < c) : Continuous (stripClamp F c d) := by
  have hq : Continuous fun w : ℂ => ((max c (min w.re d) : ℝ) : ℂ) + (w.im : ℝ) * Complex.I := by
    fun_prop
  have hmem : ∀ w : ℂ,
      (((max c (min w.re d) : ℝ) : ℂ) + (w.im : ℝ) * Complex.I) ∈ {v : ℂ | 0 < v.re} := by
    intro w
    have hre : (((max c (min w.re d) : ℝ) : ℂ) + (w.im : ℝ) * Complex.I).re
        = max c (min w.re d) := by simp
    simp only [Set.mem_setOf_eq, hre]
    exact lt_of_lt_of_le hc (le_max_left _ _)
  exact hF.holo.continuousOn.comp_continuous hq hmem

theorem stripClamp_eq {F : ℂ → ℂ} {c d : ℝ} {σ : ℝ} (hσ : σ ∈ Icc c d) (T : ℝ) :
    stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I) = F ((σ : ℂ) + (T : ℝ) * Complex.I) := by
  have hre : ((σ : ℂ) + (T : ℝ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (T : ℝ) * Complex.I).im = T := by simp
  rw [stripClamp, hre, him, min_eq_left hσ.2, max_eq_right hσ.1]

theorem measurable_stripMassIntegrand {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {c d : ℝ}
    (hc : 0 < c) :
    Measurable (Function.uncurry fun T σ : ℝ =>
      ENNReal.ofReal (‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2)) := by
  have hcont : Continuous (Function.uncurry fun T σ : ℝ =>
      ‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2) := by
    have h1 : Continuous fun p : ℝ × ℝ => ((p.2 : ℂ) + (p.1 : ℝ) * Complex.I) := by fun_prop
    exact ((continuous_stripClamp hF hc).comp h1).norm.pow 2
  exact hcont.measurable.ennreal_ofReal

theorem integrableOn_stripMassIntegrand {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {c d : ℝ}
    (hc : 0 < c) (T : ℝ) :
    IntegrableOn (fun σ : ℝ => ‖F ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2) (Icc c d) := by
  have hcont : Continuous fun σ : ℝ => ‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2 := by
    have h1 : Continuous fun σ : ℝ => ((σ : ℂ) + (T : ℝ) * Complex.I) := by fun_prop
    exact ((continuous_stripClamp hF hc).comp h1).norm.pow 2
  refine (hcont.integrableOn_Icc).congr_fun (fun σ hσ => ?_) measurableSet_Icc
  show ‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2
    = ‖F ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2
  rw [stripClamp_eq hσ T]

/-- **The total mass over a vertical strip is finite.** -/
theorem lintegral_stripMass_lt_top {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {c d : ℝ}
    (hc : 0 < c) :
    (∫⁻ T : ℝ, ENNReal.ofReal (stripMass F c d T)) < ⊤ := by
  have hM0 : 0 ≤ 2 * Real.pi * M := by
    have h := integral_norm_sq_hardyLine_le hF hc
    have hnn : (0 : ℝ) ≤ ∫ y : ℝ, ‖F ((c : ℂ) + (y : ℝ) * Complex.I)‖ ^ 2 :=
      integral_nonneg fun y => by positivity
    linarith
  -- rewrite the outer integrand as an inner lower integral
  have hstep : ∀ T : ℝ, ENNReal.ofReal (stripMass F c d T)
      = ∫⁻ σ in Icc c d, ENNReal.ofReal
          (‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2) := by
    intro T
    have hint := integrableOn_stripMassIntegrand (d := d) hF hc T
    have hcongr : (∫⁻ σ in Icc c d, ENNReal.ofReal
        (‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2))
        = ∫⁻ σ in Icc c d, ENNReal.ofReal (‖F ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_)
      rw [stripClamp_eq hσ T]
    rw [hcongr, stripMass]
    exact ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun σ => by positivity)
  simp only [hstep]
  rw [lintegral_lintegral_swap (measurable_stripMassIntegrand hF hc).aemeasurable]
  have hinner : ∀ σ ∈ Icc c d,
      (∫⁻ T : ℝ, ENNReal.ofReal (‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2))
        ≤ ENNReal.ofReal (2 * Real.pi * M) := by
    intro σ hσ
    have hσ0 : 0 < σ := lt_of_lt_of_le hc hσ.1
    have hcongr : (∫⁻ T : ℝ, ENNReal.ofReal
        (‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2))
        = ∫⁻ T : ℝ, ENNReal.ofReal (‖F ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2) := by
      refine lintegral_congr fun T => ?_
      rw [stripClamp_eq hσ T]
    rw [hcongr]
    have hint : Integrable (fun T : ℝ => ‖F ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm (memLp_two_hardyLine hF hσ0).aestronglyMeasurable).1
        (memLp_two_hardyLine hF hσ0)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun T => by positivity)]
    exact ENNReal.ofReal_le_ofReal (integral_norm_sq_hardyLine_le hF hσ0)
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Icc hinner) ?_
  rw [setLIntegral_const, Real.volume_Icc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-! ### A sequence of good heights -/

/-- A measurable nonnegative function with finite total mass on the line becomes small at
arbitrarily large heights, in both directions at once. -/
theorem exists_seq_tendsto_zero_of_lintegral_lt_top {h : ℝ → ENNReal} (hmeas : Measurable h)
    (hfin : (∫⁻ t : ℝ, h t) < ⊤) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      Tendsto (fun n : ℕ => h (T n) + h (-(T n))) atTop (𝓝 0) := by
  classical
  set K : ℝ → ENNReal := fun t => h t + h (-t) with hK
  have hKmeas : Measurable K := hmeas.add (hmeas.comp measurable_neg)
  have hrefl : (∫⁻ t : ℝ, h (-t)) = ∫⁻ t : ℝ, h t :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp hmeas
  have hKfin : (∫⁻ t : ℝ, K t) < ⊤ := by
    rw [hK, lintegral_add_left hmeas, hrefl]
    exact ENNReal.add_lt_top.2 ⟨hfin, hfin⟩
  have hsmall : ∀ n : ℕ, ∃ t : ℝ, (n : ℝ) < t ∧ K t < ((n : ENNReal) + 1)⁻¹ := by
    intro n
    by_contra hcon
    have hle : ∀ t ∈ Ioi ((n : ℝ)), ((n : ENNReal) + 1)⁻¹ ≤ K t := by
      intro t ht
      by_contra hlt
      exact hcon ⟨t, ht, not_le.1 hlt⟩
    have hbig : (∫⁻ t in Ioi ((n : ℝ)), K t) = ⊤ := by
      have h1 : (∫⁻ _t in Ioi ((n : ℝ)), ((n : ENNReal) + 1)⁻¹) ≤ ∫⁻ t in Ioi ((n : ℝ)), K t :=
        setLIntegral_mono' measurableSet_Ioi hle
      rw [setLIntegral_const, Real.volume_Ioi] at h1
      have hne : ((n : ENNReal) + 1)⁻¹ ≠ 0 := by
        refine ENNReal.inv_ne_zero.2 ?_
        exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩
      rw [ENNReal.mul_top hne] at h1
      exact top_le_iff.1 h1
    have hmono : (∫⁻ t in Ioi ((n : ℝ)), K t) ≤ ∫⁻ t : ℝ, K t :=
      setLIntegral_le_lintegral _ _
    rw [hbig] at hmono
    exact absurd (top_le_iff.1 hmono) (ne_of_lt hKfin)
  choose T hT1 hT2 using hsmall
  refine ⟨T, ?_, ?_⟩
  · refine tendsto_atTop_mono (fun n => (hT1 n).le) ?_
    exact tendsto_natCast_atTop_atTop
  · have hub : Tendsto (fun n : ℕ => ((n : ENNReal) + 1)⁻¹) atTop (𝓝 0) := by
      have h0 := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine h0.congr fun n => ?_
      simp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
      (fun n => _root_.zero_le) (fun n => (hT2 n).le)

/-- **A sequence of heights along which both horizontal edges of the strip lose their mass.** -/
theorem exists_seq_stripMass_tendsto_zero {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {c d : ℝ} (hc : 0 < c) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      Tendsto (fun n : ℕ => stripMass F c d (T n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => stripMass F c d (-(T n))) atTop (𝓝 0) := by
  set h : ℝ → ENNReal := fun T => ENNReal.ofReal (stripMass F c d T) with hh
  have hstep : ∀ T : ℝ, h T
      = ∫⁻ σ in Icc c d, ENNReal.ofReal
          (‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2) := by
    intro T
    have hint := integrableOn_stripMassIntegrand (d := d) hF hc T
    have hcongr : (∫⁻ σ in Icc c d, ENNReal.ofReal
        (‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2))
        = ∫⁻ σ in Icc c d, ENNReal.ofReal (‖F ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_)
      rw [stripClamp_eq hσ T]
    show ENNReal.ofReal (stripMass F c d T) = _
    rw [hcongr]
    exact ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun σ => by positivity)
  have hmeas : Measurable h := by
    have hm := (measurable_stripMassIntegrand hF (d := d) hc).lintegral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Icc c d))
    simp only [Function.uncurry_apply_pair] at hm
    have hfun : h = fun T : ℝ => ∫⁻ σ in Icc c d, ENNReal.ofReal
        (‖stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2) := funext hstep
    rw [hfun]
    exact hm
  have hfin : (∫⁻ T : ℝ, h T) < ⊤ := lintegral_stripMass_lt_top hF hc
  obtain ⟨T, hT, hzero⟩ := exists_seq_tendsto_zero_of_lintegral_lt_top hmeas hfin
  have hmass0 : ∀ x : ℝ, 0 ≤ stripMass F c d x := by
    intro x
    exact integral_nonneg fun σ => by positivity
  refine ⟨T, hT, ?_, ?_⟩
  · have hle : ∀ n : ℕ, h (T n) ≤ h (T n) + h (-(T n)) := fun n => le_self_add
    have hsq : Tendsto (fun n : ℕ => h (T n)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
        (fun n => _root_.zero_le) hle
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq
    simpa [Function.comp_def, hh, ENNReal.toReal_ofReal (hmass0 _)] using this
  · have hle : ∀ n : ℕ, h (-(T n)) ≤ h (T n) + h (-(T n)) := fun n => le_add_self
    have hsq : Tendsto (fun n : ℕ => h (-(T n))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
        (fun n => _root_.zero_le) hle
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq
    simpa [Function.comp_def, hh, ENNReal.toReal_ofReal (hmass0 _)] using this

end

end GaloisForLFunctions.HTGeometry
