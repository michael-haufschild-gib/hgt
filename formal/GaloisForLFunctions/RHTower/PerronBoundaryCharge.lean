import GaloisForLFunctions.RHTower.VariablePerronKink

/-!
# Perron boundary charge

Quiet-crossing arguments do not intrinsically consume a uniform supremum bound on an entire
rectangle.  They consume four boundary constraints: convergence of the truncated right edge,
vanishing top and bottom charges, and a bounded left charge.  Moreover, the exhausting height
sequence may depend on the contour depth and the Perron knot width.

This module packages that boundary-only constraint and composes it with the variable Perron
coefficient identity and the exact flank-growth support theorem.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set
open scoped Topology Interval

/-- The entire contour integrand formed from a carrier and the variable Perron regularization. -/
def perronContourIntegrand (F : ℂ → ℂ) (n : ℕ) (δ : ℝ) (s : ℂ) : ℂ :=
  F s * perronEAt n δ s

/-- **Boundary charge at one depth and knot width.**  A height exhaustion makes the truncated right
edge converge to the full vertical integral, makes the top and bottom edge integrals vanish, and
bounds every truncated left edge by `L`.  The exhaustion may depend on `M` and `δ`. -/
def HasPerronBoundaryChargeAt (F : ℂ → ℂ) (c : ℝ) (n : ℕ) (δ : ℝ)
    (M : ℕ) (L : ℝ) : Prop :=
  ∃ T : ℕ → ℝ,
    Tendsto T atTop atTop ∧
    Tendsto (fun k => ∫ y in (-(T k))..(T k),
      perronContourIntegrand F n δ (↑c + ↑y * I)) atTop
      (𝓝 (∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I))) ∧
    Tendsto (fun k => ∫ x in (-(M : ℝ))..c,
      perronContourIntegrand F n δ (↑x + ↑(T k) * I)) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ x in (-(M : ℝ))..c,
      perronContourIntegrand F n δ (↑x + ↑(-(T k)) * I)) atTop (𝓝 0) ∧
    ∀ k, ‖∫ y in (-(T k))..(T k),
      perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖ ≤ L

/-- Cauchy's rectangle identity turns the three non-right boundary constraints into the full
right-edge norm bound `≤ L`.  No interior rectangle supremum is used. -/
theorem perron_right_integral_norm_le_of_boundaryChargeAt
    {F : ℂ → ℂ} {c : ℝ} {n M : ℕ} {δ L : ℝ}
    (hF : Differentiable ℂ F)
    (hE : Differentiable ℂ (perronEAt n δ))
    (hcharge : HasPerronBoundaryChargeAt F c n δ M L) :
    ‖∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I)‖ ≤ L := by
  rcases hcharge with ⟨T, _hT, hright, htop, hbot, hleft⟩
  have hGdiff : Differentiable ℂ (perronContourIntegrand F n δ) := by
    unfold perronContourIntegrand
    exact hF.mul hE
  have hrectbd : ∀ k,
      ‖∫ y in (-(T k))..(T k), perronContourIntegrand F n δ (↑c + ↑y * I)‖
        ≤ ‖∫ x in (-(M : ℝ))..c,
              perronContourIntegrand F n δ (↑x + ↑(T k) * I)‖
          + ‖∫ x in (-(M : ℝ))..c,
              perronContourIntegrand F n δ (↑x + ↑(-(T k)) * I)‖ + L := by
    intro k
    set z : ℂ := ⟨-(M : ℝ), -(T k)⟩ with hz
    set w : ℂ := ⟨c, T k⟩ with hw
    have hrect := integral_boundary_rect_eq_zero_of_differentiableOn
      (perronContourIntegrand F n δ) z w hGdiff.differentiableOn
    have hzre : z.re = -(M : ℝ) := rfl
    have hzim : z.im = -(T k) := rfl
    have hwre : w.re = c := rfl
    have hwim : w.im = T k := rfl
    rw [hzre, hzim, hwre, hwim] at hrect
    simp only [smul_eq_mul] at hrect
    set Itop := ∫ x in (-(M : ℝ))..c,
      perronContourIntegrand F n δ (↑x + ↑(T k) * I) with hItop
    set Ibot := ∫ x in (-(M : ℝ))..c,
      perronContourIntegrand F n δ (↑x + ↑(-(T k)) * I) with hIbot
    set Ilft := ∫ y in (-(T k))..(T k),
      perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I) with hIlft
    have heqI : I * (∫ y in (-(T k))..(T k),
        perronContourIntegrand F n δ (↑c + ↑y * I)) =
        Itop - Ibot + I * Ilft := by
      linear_combination hrect
    have hInorm : ‖∫ y in (-(T k))..(T k),
        perronContourIntegrand F n δ (↑c + ↑y * I)‖ =
        ‖Itop - Ibot + I * Ilft‖ := by
      rw [← heqI, norm_mul, Complex.norm_I, one_mul]
    rw [hInorm]
    calc
      ‖Itop - Ibot + I * Ilft‖ ≤ ‖Itop - Ibot‖ + ‖I * Ilft‖ := norm_add_le _ _
      _ ≤ (‖Itop‖ + ‖Ibot‖) + ‖Ilft‖ := by
        gcongr
        · exact norm_sub_le _ _
        · rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖Itop‖ + ‖Ibot‖ + L := by
        gcongr
        exact hleft k
  have hrightnorm : Tendsto (fun k => ‖∫ y in (-(T k))..(T k),
      perronContourIntegrand F n δ (↑c + ↑y * I)‖) atTop
      (𝓝 ‖∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I)‖) := hright.norm
  have hupp : Tendsto (fun k =>
      ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(T k) * I)‖
      + ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(-(T k)) * I)‖ + L)
      atTop (𝓝 L) := by
    simpa using (htop.norm.add hbot.norm).add_const L
  exact le_of_tendsto_of_tendsto' hrightnorm hupp hrectbd

/-- **Normalized variable Perron boundary charge.**  At every admissible knot width and eventually
at every depth, the left charge is normalized so division by `2π` yields precisely the coefficient
majorant `H(M)(n-δ)^(1-M)`. -/
def HasVariablePerronBoundaryCharge (F : ℂ → ℂ) (c : ℝ)
    (H : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → δ < (n : ℝ) →
    ∀ᶠ M : ℕ in atTop,
      HasPerronBoundaryChargeAt F c n δ M
        (2 * Real.pi * H M * perronSupportScaleAt n δ ^ (1 - (M : ℝ)))

/-- Boundary charge discharges the variable quiet-flank coefficient Prop using the exact variable
Perron integral representation. -/
theorem HasVariablePerronBoundaryCharge.hasVariableQuietFlankCoefficientBound
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ}
    (hcharge : HasVariablePerronBoundaryCharge F c H n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) :
    HasVariableQuietFlankCoefficientBound a H n := by
  intro δ hδ0 hδ1 hδn
  filter_upwards [hcharge δ hδ0 hδ1 hδn] with M hM
  have hI := perron_right_integral_norm_le_of_boundaryChargeAt hF
    (perronEAt_differentiable hn hδ0 hδn) hM
  have hrepr := perronSecondDiffAt_integral hc0 hsum hF hFeq hn hδ0 hδ1
  have hnorm := congrArg norm hrepr
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))] at hnorm
  rw [hnorm]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I)‖
        ≤ (1 / (2 * Real.pi)) *
          (2 * Real.pi * H M * perronSupportScaleAt n δ ^ (1 - (M : ℝ))) :=
            mul_le_mul_of_nonneg_left hI (by positivity)
    _ = H M * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) := by
      field_simp [Real.pi_ne_zero]

/-- **Boundary-charge support theorem.**  A geometric envelope `H(M) ≤ C R^M` for the normalized
boundary charge forces every nonzero coefficient index to satisfy the exact inequality `n ≤ R`. -/
theorem coefficient_index_le_exact_flank_radius_of_boundaryCharge
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hcharge : HasVariablePerronBoundaryCharge F c H n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R := by
  exact coefficient_index_le_exact_flank_radius hn hR hH0 hH
    (hcharge.hasVariableQuietFlankCoefficientBound hc0 hsum hF hFeq hn) han

/-- **Integrable continuous charge admits quiet heights.**  A continuous real function integrable
on `(0,∞)` has a nonnegative sequence of arguments tending to infinity along which its values tend
to zero.  Choose each argument by the integral mean-value theorem on `[k,k+1]`; those unit-interval
averages tend to zero because the improper integral converges. -/
theorem exists_seq_atTop_tendsto_zero_of_continuous_integrableOn_Ioi
    {u : ℝ → ℝ} (hu : Continuous u) (huint : IntegrableOn u (Ioi 0)) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧ (∀ k, 0 ≤ T k) ∧
      Tendsto (fun k => u (T k)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcum : Tendsto (fun k : ℕ => ∫ x in (0 : ℝ)..(k : ℝ), u x) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), u x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 huint hnat
  have hcumsucc : Tendsto (fun k : ℕ => ∫ x in (0 : ℝ)..((k : ℝ) + 1), u x) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), u x)) := by
    have hs : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 hnat
    exact intervalIntegral_tendsto_integral_Ioi 0 huint hs
  have hunit : Tendsto (fun k : ℕ => ∫ x in (k : ℝ)..((k : ℝ) + 1), u x)
      atTop (𝓝 0) := by
    have heq : (fun k : ℕ => ∫ x in (k : ℝ)..((k : ℝ) + 1), u x) =
        fun k : ℕ => (∫ x in (0 : ℝ)..((k : ℝ) + 1), u x) -
          ∫ x in (0 : ℝ)..(k : ℝ), u x := by
      funext k
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hu.intervalIntegrable (μ := volume) (0 : ℝ) (k : ℝ))
        (hu.intervalIntegrable (μ := volume) (k : ℝ) ((k : ℝ) + 1))
      linear_combination hadd
    rw [heq]
    simpa using hcumsucc.sub hcum
  choose T hTmem hTavg using fun k : ℕ =>
    exists_eq_interval_average (by norm_num : (k : ℝ) ≠ (k : ℝ) + 1) hu.continuousOn
  refine ⟨T, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono' atTop (Eventually.of_forall fun k => by
      have hk := hTmem k
      rw [uIoo_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at hk
      exact hk.1.le) hnat
  · intro k
    have hk := hTmem k
    rw [uIoo_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at hk
    exact le_trans (Nat.cast_nonneg k) hk.1.le
  · have hval : (fun k : ℕ => u (T k)) =
        fun k : ℕ => ∫ x in (k : ℝ)..((k : ℝ) + 1), u x := by
      funext k
      rw [hTavg k, interval_average_eq_div]
      ring
    rw [hval]
    exact hunit

/-- **Strip-mass producer data.**  The right edge is integrable, the sum of horizontal edge norms is
integrable over positive heights, and the full left `L¹` charge is bounded by `L`. -/
def HasPerronStripMassAt (F : ℂ → ℂ) (c : ℝ) (n : ℕ) (δ : ℝ)
    (M : ℕ) (L : ℝ) : Prop :=
  Integrable (fun y : ℝ => perronContourIntegrand F n δ (↑c + ↑y * I)) ∧
  IntegrableOn (fun T : ℝ =>
    ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑T * I)‖ +
    ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(-T) * I)‖) (Ioi 0) ∧
  Integrable (fun y : ℝ => ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖) ∧
  (∫ y : ℝ, ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖) ≤ L

/-- Strip mass constructs boundary charge.  Integrability of the continuous horizontal charge
selects a depth-dependent quiet exhaustion; right integrability gives truncation convergence, and
the full left `L¹` mass bounds every truncated left edge. -/
theorem HasPerronStripMassAt.hasPerronBoundaryChargeAt
    {F : ℂ → ℂ} {c : ℝ} {n M : ℕ} {δ L : ℝ}
    (hF : Differentiable ℂ F) (hE : Differentiable ℂ (perronEAt n δ))
    (hmass : HasPerronStripMassAt F c n δ M L) :
    HasPerronBoundaryChargeAt F c n δ M L := by
  rcases hmass with ⟨hrightInt, hhorizontalInt, hleftInt, hleftBound⟩
  let u : ℝ → ℝ := fun T =>
    ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑T * I)‖ +
    ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(-T) * I)‖
  have hGcont : Continuous (perronContourIntegrand F n δ) := by
    exact (hF.mul hE).continuous
  have htopcont : Continuous (fun T : ℝ =>
      ∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑T * I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hGcont.comp (by fun_prop)
  have hbotcont : Continuous (fun T : ℝ =>
      ∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(-T) * I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hGcont.comp (by fun_prop)
  have hucont : Continuous u := htopcont.norm.add hbotcont.norm
  obtain ⟨T, hTtop, hTnonneg, huT⟩ :=
    exists_seq_atTop_tendsto_zero_of_continuous_integrableOn_Ioi hucont hhorizontalInt
  refine ⟨T, hTtop, ?_, ?_, ?_, ?_⟩
  · exact intervalIntegral_tendsto_integral hrightInt (tendsto_neg_atBot_iff.mpr hTtop) hTtop
  · apply squeeze_zero_norm (fun k => ?_) huT
    exact le_add_of_nonneg_right (norm_nonneg _)
  · apply squeeze_zero_norm (fun k => ?_) huT
    exact le_add_of_nonneg_left (norm_nonneg _)
  · intro k
    have hTk0 : 0 ≤ T k := hTnonneg k
    calc
      ‖∫ y in (-(T k))..(T k),
          perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖
          ≤ ∫ y in (-(T k))..(T k),
              ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = ∫ y in Ioc (-(T k)) (T k),
              ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖ :=
            intervalIntegral.integral_of_le (by linarith)
      _ ≤ ∫ y : ℝ, ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖ :=
            setIntegral_le_integral hleftInt (Eventually.of_forall fun _ => norm_nonneg _)
      _ ≤ L := hleftBound


end RHTower
