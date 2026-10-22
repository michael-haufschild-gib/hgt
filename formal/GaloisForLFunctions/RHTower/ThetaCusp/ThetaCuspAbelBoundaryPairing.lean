import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOneSidedConnection

/-!
# The global Abel pairing of the Ward integral at the rational boundary

Rotating `M_z = ∫₁^∞ y^α (ϑ(y) - 1) dy` (`α = iz/2 - 3/4`) through rectangles in the logarithmic
clock gives, for every `0 < φ < π/2`,
`M_z = i ∫₀^φ e^{i(α+1)θ}(ϑ(e^{iθ}) - 1) dθ + e^{i(α+1)φ} ∫₁^∞ r^α (ϑ(r e^{iφ}) - 1) dr`,
and the ray integral is `2 Σ_{n ≥ 1} J_α(π n² e^{iφ})` with
`J_α(c) = e^{-c}/c + (α/c) ∫₁^∞ r^{α-1} e^{-cr} dr` (integration by parts).  For `Re α < 0`
the uniform bound `|J_α(c)| ≤ (1/|c|)(1 + |α|/(-Re α))` on `Re c ≥ 0`, continuity of the tail
integral, and boundedness of `ϑ(e^{iθ})` near `θ = π/2` (the `(p, q) = (1, 2)` cusp, where the
Gauss sum vanishes; also `ϑ(i + w) = w^{-1/2} Σ_m e^{-π(m+1/2)²/w}`) let `φ ↑ π/2`:

`M_z = A(α) + 2 e^{iπ(α+1)/2} Σ_{n ≥ 1} I_n(α)`,
`I_n(α) = (-1)^n/(iπn²) + (α/(iπn²)) ∫₁^∞ r^{α-1} e^{-iπn² r} dr`,

each `I_n` being the improper oscillatory integral `∫₁^∞ r^α e^{-iπn² r} dr`.  The square-phase
potential `Q(r) = Σ_{n ≥ 1} e^{-iπn² r}/n²` is continuous, bounded by `π²/6`, two-periodic with
mean zero, `Q(1) = -π²/12`, obeys `Q(r+1) + Q(r) = ½ Q(4r)`, and
`M_z = A(α) + 2 e^{iπ(α+1)/2}[iπ/12 + (α/(iπ)) ∫₁^∞ r^{α-1} Q(r) dr]`.
The two-ended source modes satisfy `U_z(x) - V_z(x) = -i e^{-izx} Ξ(z)`.
-/
open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower.HalfWeight

/-! ## Rotation of the Ward Mellin integral -/

/-- The log-clock Mellin integrand `Φ_α(w) = e^{(α+1)w} (ϑ(e^w) - 1)`. -/
def wardLogIntegrand (α w : ℂ) : ℂ := cexp ((α + 1) * w) * (jacobiThetaSum (cexp w) - 1)

theorem norm_jacobiThetaSum_cexp_sub_one_le {φ : ℝ} (hφ : φ < Real.pi / 2) {w : ℂ}
    (hre : 0 ≤ w.re) (him0 : 0 ≤ w.im) (him : w.im ≤ φ) :
    ‖jacobiThetaSum (cexp w) - 1‖ ≤ 2 / (1 - Real.exp (-(Real.pi * Real.cos φ))) *
      Real.exp (-(Real.pi * Real.cos φ * Real.exp w.re)) := by
  obtain ⟨h1, h2⟩ := re_cexp_ge hφ hre him0 him
  have hcpos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ⟩
  have hpos : 0 < (cexp w).re := lt_of_lt_of_le hcpos h1
  have h := norm_jacobiThetaSum_sub_one_le hpos
  set r := Real.exp (-(Real.pi * (cexp w).re))
  set r₀ := Real.exp (-(Real.pi * Real.cos φ))
  have hr : r ≤ r₀ := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hr₀ : r₀ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hr' : r ≤ Real.exp (-(Real.pi * Real.cos φ * Real.exp w.re)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hrpos : 0 < r := Real.exp_pos _
  calc ‖jacobiThetaSum (cexp w) - 1‖ ≤ 2 * (r / (1 - r)) := h
    _ ≤ 2 * (r / (1 - r₀)) := by gcongr
    _ = 2 / (1 - r₀) * r := by ring
    _ ≤ 2 / (1 - r₀) * Real.exp (-(Real.pi * Real.cos φ * Real.exp w.re)) := by
        gcongr

theorem exists_norm_wardLogIntegrand_le (α : ℂ) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → 0 ≤ w.im → w.im ≤ φ →
      ‖wardLogIntegrand α w‖ ≤ C * Real.exp (-w.re) := by
  have hcpos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ⟩
  obtain ⟨C₁, hC₁, hb⟩ := exists_exp_mul_exp_neg_exp_le |(α + 1).re|
    (by positivity : 0 < Real.pi * Real.cos φ)
  have hr₀ : Real.exp (-(Real.pi * Real.cos φ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  set D := 2 / (1 - Real.exp (-(Real.pi * Real.cos φ)))
  have hD : 0 ≤ D := div_nonneg (by norm_num) (by linarith)
  refine ⟨Real.exp (|(α + 1).im| * φ) * D * C₁, by positivity, fun w hre him0 him => ?_⟩
  have hθ := norm_jacobiThetaSum_cexp_sub_one_le hφ hre him0 him
  have hphase : ‖cexp ((α + 1) * w)‖ ≤ Real.exp (|(α + 1).im| * φ) *
      Real.exp (|(α + 1).re| * w.re) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [Complex.mul_re]
    have h1 : -((α + 1).im * w.im) ≤ |(α + 1).im| * φ := by
      have := neg_abs_le (α + 1).im; nlinarith [abs_nonneg (α + 1).im]
    have h2 : (α + 1).re * w.re ≤ |(α + 1).re| * w.re :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hre
    linarith
  unfold wardLogIntegrand
  rw [norm_mul]
  calc ‖cexp ((α + 1) * w)‖ * ‖jacobiThetaSum (cexp w) - 1‖
      ≤ (Real.exp (|(α + 1).im| * φ) * Real.exp (|(α + 1).re| * w.re)) *
          (D * Real.exp (-(Real.pi * Real.cos φ * Real.exp w.re))) :=
        mul_le_mul hphase hθ (norm_nonneg _) (by positivity)
    _ = Real.exp (|(α + 1).im| * φ) * D * (Real.exp (|(α + 1).re| * w.re) *
          Real.exp (-(Real.pi * Real.cos φ * Real.exp w.re))) := by ring
    _ ≤ Real.exp (|(α + 1).im| * φ) * D * (C₁ * Real.exp (-w.re)) :=
        mul_le_mul_of_nonneg_left (hb w.re hre) (by positivity)
    _ = _ := by ring

theorem differentiableAt_wardLogIntegrand (α : ℂ) {φ : ℝ} (hφ : φ < Real.pi / 2) {w : ℂ}
    (hre : 0 ≤ w.re) (him0 : 0 ≤ w.im) (him : w.im ≤ φ) :
    DifferentiableAt ℂ (wardLogIntegrand α) w := by
  have hcpos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ⟩
  have hpos : 0 < (cexp w).re := lt_of_lt_of_le hcpos (re_cexp_ge hφ hre him0 him).1
  have h := (hasDerivAt_jacobiThetaSum hpos).differentiableAt.comp w Complex.differentiableAt_exp
  unfold wardLogIntegrand
  exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp ((α + 1) * w)) w).mul (h.sub_const 1)

theorem integrableOn_wardLogIntegrand (α : ℂ) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ < Real.pi / 2)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ φ) :
    IntegrableOn (fun t : ℝ => wardLogIntegrand α (t + s * I)) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_wardLogIntegrand_le α hφ0 hφ
  refine ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul C).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hd := differentiableAt_wardLogIntegrand α hφ (w := (t : ℂ) + s * I) (by simp [ht0])
      (by simp [hs0]) (by simp [hs])
    exact (ContinuousAt.comp (g := wardLogIntegrand α) (f := fun t : ℝ => (t : ℂ) + s * I)
      hd.continuousAt (by fun_prop)).continuousWithinAt
  · have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have := hb ((t : ℂ) + s * I) (by simp [ht0]) (by simp [hs0]) (by simp [hs])
    simpa [neg_mul, one_mul] using this

/-- **Rotated Ward integral.** For `0 < φ < π/2`, with `α = α_z`,
`M_z = i ∫₀^φ e^{i(α+1)θ}(ϑ(e^{iθ}) - 1) dθ + e^{i(α+1)φ} ∫₁^∞ r^α (ϑ(r e^{iφ}) - 1) dr`. -/
theorem wardMellin_eq_rotated (z : ℂ) {φ : ℝ} (hφ0 : 0 < φ) (hφ : φ < Real.pi / 2) :
    wardMellin z =
      I * (∫ θ in (0 : ℝ)..φ, cexp ((wardExponent z + 1) * (θ * I)) *
          (jacobiThetaSum (cexp (θ * I)) - 1)) +
        cexp ((wardExponent z + 1) * (φ * I)) *
          ∫ r in Ioi (1 : ℝ), (r : ℂ) ^ wardExponent z *
            (jacobiThetaSum (r * cexp (φ * I)) - 1) := by
  set α := wardExponent z
  obtain ⟨C, hC, hb⟩ := exists_norm_wardLogIntegrand_le α hφ0.le hφ
  have hi0 : IntegrableOn (fun t : ℝ => wardLogIntegrand α t) (Ioi 0) := by
    simpa using integrableOn_wardLogIntegrand α hφ0.le hφ le_rfl hφ0.le (s := 0)
  have hiφ := integrableOn_wardLogIntegrand α hφ0.le hφ hφ0.le le_rfl
  have hdecay : Tendsto (fun L : ℝ => ∫ s in (0 : ℝ)..φ, wardLogIntegrand α (L + s * I))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun L : ℝ => C * Real.exp (-L) * |φ - 0|) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).mul_const |φ - 0|
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with L hL
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [Set.uIoc_of_le hφ0.le] at hs
    simpa using hb ((L : ℂ) + s * I) (by simp [hL]) (by simp [hs.1.le]) (by simp [hs.2])
  have hrot := integral_Ioi_eq_rotated (f := wardLogIntegrand α) hφ0.le
    (fun w hre him0 him => differentiableAt_wardLogIntegrand α hφ hre him0 him) hi0 hiφ hdecay
  have hcp : ∀ t : ℝ, cexp (t : ℂ) ^ α = cexp (t * α) := fun t =>
    cpow_cexp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]) α
  have hreal : (∫ t in Ioi (0 : ℝ), wardLogIntegrand α t) = wardMellin z := by
    unfold wardMellin
    rw [← integral_Ioi_exp_smul_comp (fun r : ℝ => (r : ℂ) ^ α * (jacobiThetaSum r - 1))]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [wardLogIntegrand, Complex.real_smul, Complex.ofReal_exp, hcp]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2; ring
  have hray : (∫ t in Ioi (0 : ℝ), wardLogIntegrand α (t + φ * I)) =
      cexp ((α + 1) * (φ * I)) * ∫ r in Ioi (1 : ℝ), (r : ℂ) ^ α *
        (jacobiThetaSum (r * cexp (φ * I)) - 1) := by
    rw [← integral_Ioi_exp_smul_comp (fun r : ℝ => (r : ℂ) ^ α *
      (jacobiThetaSum (r * cexp (φ * I)) - 1)), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [wardLogIntegrand, Complex.real_smul, Complex.ofReal_exp, hcp]
    rw [Complex.exp_add (t : ℂ)]
    have e : cexp ((α + 1) * (t + φ * I)) =
        cexp ((α + 1) * (φ * I)) * (cexp t * cexp (t * α)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    rw [e]; ring
  have harc : (∫ s in (0 : ℝ)..φ, wardLogIntegrand α (s * I)) =
      ∫ θ in (0 : ℝ)..φ, cexp ((α + 1) * (θ * I)) * (jacobiThetaSum (cexp (θ * I)) - 1) := rfl
  rw [hreal, hray, harc] at hrot
  rw [hrot]; ring

/-! ## The square-phase integrals `I_n(α)` -/

/-- `K_α(c) = ∫₁^∞ r^{α-1} e^{-cr} dr`, absolutely convergent for `Re α < 0`, `Re c ≥ 0`. -/
def abelTailIntegral (α c : ℂ) : ℂ := ∫ r in Ioi (1 : ℝ), (r : ℂ) ^ (α - 1) * cexp (-c * r)

/-- The integrated-by-parts square-phase term `e^{-c}/c + (α/c) K_α(c)`. -/
def abelRayTerm (α c : ℂ) : ℂ := cexp (-c) / c + α / c * abelTailIntegral α c

theorem norm_ofReal_cpow_of_pos {r : ℝ} (hr : 0 < r) (a : ℂ) : ‖(r : ℂ) ^ a‖ = r ^ a.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hr a

theorem norm_abelTail_integrand_le {α c : ℂ} (hc : 0 ≤ c.re) {r : ℝ} (hr : 1 ≤ r) :
    ‖(r : ℂ) ^ (α - 1) * cexp (-c * r)‖ ≤ r ^ (α.re - 1) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  rw [norm_mul, norm_ofReal_cpow_of_pos hr0, Complex.norm_exp]
  have : (-c * (r : ℂ)).re = -(c.re * r) := by simp [Complex.mul_re]
  rw [this, Complex.sub_re, Complex.one_re]
  have hexp : Real.exp (-(c.re * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc r ^ (α.re - 1) * Real.exp (-(c.re * r)) ≤ r ^ (α.re - 1) * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = r ^ (α.re - 1) := mul_one _

theorem continuous_abelTail_integrand (α c : ℂ) :
    ContinuousOn (fun r : ℝ => (r : ℂ) ^ (α - 1) * cexp (-c * r)) (Ioi 0) := by
  intro r hr
  have hslit : (r : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hr)
  exact (((continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt).mul
    (by fun_prop : Continuous fun r : ℝ => cexp (-c * r)).continuousAt).continuousWithinAt

theorem integrableOn_abelTail {α c : ℂ} (hα : α.re < 0) (hc : 0 ≤ c.re) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ (α - 1) * cexp (-c * r)) (Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (by linarith : α.re - 1 < -1) one_pos).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr =>
      norm_abelTail_integrand_le hc (le_of_lt hr)))
  exact ((continuous_abelTail_integrand α c).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
    measurableSet_Ioi

theorem norm_abelTailIntegral_le {α c : ℂ} (hα : α.re < 0) (hc : 0 ≤ c.re) :
    ‖abelTailIntegral α c‖ ≤ 1 / (-α.re) := by
  have hint := integral_Ioi_rpow_of_lt (by linarith : α.re - 1 < -1) one_pos
  simp only [Real.one_rpow, sub_add_cancel] at hint
  unfold abelTailIntegral
  calc ‖∫ r in Ioi (1 : ℝ), (r : ℂ) ^ (α - 1) * cexp (-c * r)‖
      ≤ ∫ r in Ioi (1 : ℝ), r ^ (α.re - 1) :=
        norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr =>
            norm_abelTail_integrand_le hc (le_of_lt hr)))
    _ = 1 / (-α.re) := by rw [hint]; ring

theorem continuousOn_abelTailIntegral {α : ℂ} (hα : α.re < 0) :
    ContinuousOn (abelTailIntegral α) {c : ℂ | 0 ≤ c.re} := by
  refine continuousOn_of_dominated (bound := fun r : ℝ => r ^ (α.re - 1)) (fun c _ => ?_)
    (fun c hc => (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr =>
      norm_abelTail_integrand_le hc (le_of_lt hr)))
    (integrableOn_Ioi_rpow_of_lt (by linarith : α.re - 1 < -1) one_pos)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_))
  · exact ((continuous_abelTail_integrand α c).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi
  · exact (by fun_prop : Continuous fun c : ℂ => (r : ℂ) ^ (α - 1) * cexp (-c * r)).continuousOn

/-- **Uniform square-phase bound** `|J(c)| ≤ (1/|c|)(1 + |α|/(-Re α))` on `Re c ≥ 0`. -/
theorem norm_abelRayTerm_le {α c : ℂ} (hα : α.re < 0) (hc : 0 ≤ c.re) (hc0 : c ≠ 0) :
    ‖abelRayTerm α c‖ ≤ 1 / ‖c‖ * (1 + ‖α‖ / (-α.re)) := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have he : ‖cexp (-c)‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.neg_re]; exact Real.exp_le_one_iff.mpr (by linarith)
  unfold abelRayTerm
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_mul, norm_div]
  have hK := norm_abelTailIntegral_le hα hc
  calc ‖cexp (-c)‖ / ‖c‖ + ‖α‖ / ‖c‖ * ‖abelTailIntegral α c‖
      ≤ 1 / ‖c‖ + ‖α‖ / ‖c‖ * (1 / (-α.re)) := by gcongr
    _ = 1 / ‖c‖ * (1 + ‖α‖ / (-α.re)) := by ring

/-- **Integration by parts.** For `Re c > 0`, `∫₁^∞ r^α e^{-cr} dr = e^{-c}/c + (α/c) K_α(c)`. -/
theorem integral_cpow_mul_cexp_eq_abelRayTerm {α c : ℂ} (hα : α.re < 0) (hc : 0 < c.re) :
    (∫ r in Ioi (1 : ℝ), (r : ℂ) ^ α * cexp (-c * r)) = abelRayTerm α c := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hu : ∀ r ∈ Ioi (1 : ℝ), HasDerivAt (fun r : ℝ => (r : ℂ) ^ α) (α * (r : ℂ) ^ (α - 1)) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
    exact (Complex.hasStrictDerivAt_cpow_const (Or.inl (by simpa using hr0))).hasDerivAt.comp_ofReal
  have hv : ∀ r ∈ Ioi (1 : ℝ), HasDerivAt (fun r : ℝ => -cexp (-c * r) / c) (cexp (-c * r)) r := by
    intro r _
    have h := (((Complex.hasDerivAt_exp _).comp (r : ℂ) ((hasDerivAt_id (r : ℂ)).const_mul (-c))).neg.div_const c).comp_ofReal
    exact h.congr_deriv (by field_simp; simp only [id])
  have hbound : ∀ r : ℝ, 1 ≤ r → ‖(r : ℂ) ^ α‖ ≤ 1 := by
    intro r hr
    rw [norm_ofReal_cpow_of_pos (lt_of_lt_of_le one_pos hr)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hr hα.le
  have hint1 : IntegrableOn ((fun r : ℝ => (r : ℂ) ^ α) * fun r : ℝ => cexp (-c * r)) (Ioi 1) := by
    refine ((integrableOn_exp_mul_Ioi (by linarith : -c.re < 0) 1)).mono' ?_
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun r hr => ?_) measurableSet_Ioi
      have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
      have hslit : (r : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hr0)
      exact (((continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt).mul
        (by fun_prop : Continuous fun r : ℝ => cexp (-c * r)).continuousAt).continuousWithinAt
    · simp only [Pi.mul_apply, norm_mul, Complex.norm_exp]
      have : (-c * (r : ℂ)).re = -c.re * r := by simp [Complex.mul_re]
      rw [this]
      calc ‖(r : ℂ) ^ α‖ * Real.exp (-c.re * r) ≤ 1 * Real.exp (-c.re * r) :=
            mul_le_mul_of_nonneg_right (hbound r (le_of_lt hr)) (Real.exp_pos _).le
        _ = Real.exp (-c.re * r) := one_mul _
  have hint2 : IntegrableOn ((fun r : ℝ => α * (r : ℂ) ^ (α - 1)) * fun r : ℝ => -cexp (-c * r) / c)
      (Ioi 1) := by
    refine IntegrableOn.congr_fun ((integrableOn_abelTail hα hc.le).const_mul (-α / c))
      (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; field_simp
  have hzero : Tendsto ((fun r : ℝ => (r : ℂ) ^ α) * fun r : ℝ => -cexp (-c * r) / c) (𝓝[>] 1)
      (𝓝 (-cexp (-c) / c)) := by
    have hslit : ((1 : ℝ) : ℂ) ∈ Complex.slitPlane := Or.inl (by simp)
    have hcont : ContinuousAt ((fun r : ℝ => (r : ℂ) ^ α) * fun r : ℝ => -cexp (-c * r) / c) 1 :=
      ((continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt).mul
        (by fun_prop : Continuous fun r : ℝ => -cexp (-c * r) / c).continuousAt
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    simpa using this
  have hinf : Tendsto ((fun r : ℝ => (r : ℂ) ^ α) * fun r : ℝ => -cexp (-c * r) / c) atTop (𝓝 0) := by
    have hlim : Tendsto (fun r : ℝ => Real.exp (-c.re * r) / ‖c‖) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (by linarith : -c.re < 0))).div_const ‖c‖
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with r hr
    simp only [Pi.mul_apply, norm_mul, norm_div, norm_neg, Complex.norm_exp]
    have : (-c * (r : ℂ)).re = -c.re * r := by simp [Complex.mul_re]
    rw [this]
    calc ‖(r : ℂ) ^ α‖ * (Real.exp (-c.re * r) / ‖c‖) ≤ 1 * (Real.exp (-c.re * r) / ‖c‖) :=
          mul_le_mul_of_nonneg_right (hbound r hr) (by positivity)
      _ = _ := one_mul _
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hint1 hint2 hzero hinf
  rw [h]
  unfold abelRayTerm abelTailIntegral
  rw [← integral_const_mul, zero_sub, sub_eq_add_neg, ← integral_neg]
  congr 1
  · ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    field_simp

theorem integrableOn_cpow_mul_cexp_Ioi_one {α c : ℂ} (hα : α.re < 0) (hc : 0 < c.re) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ α * cexp (-c * r)) (Ioi 1) := by
  refine ((integrableOn_exp_mul_Ioi (by linarith : -c.re < 0) 1)).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun r hr => ?_) measurableSet_Ioi
    have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
    have hslit : (r : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hr0)
    exact (((continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt).mul
      (by fun_prop : Continuous fun r : ℝ => cexp (-c * r)).continuousAt).continuousWithinAt
  · have hr1 : (1 : ℝ) ≤ r := le_of_lt hr
    rw [norm_mul, norm_ofReal_cpow_of_pos (lt_of_lt_of_le one_pos hr1), Complex.norm_exp]
    have : (-c * (r : ℂ)).re = -c.re * r := by simp [Complex.mul_re]
    rw [this]
    calc r ^ α.re * Real.exp (-c.re * r) ≤ 1 * Real.exp (-c.re * r) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hr1 hα.le)
            (Real.exp_pos _).le
      _ = Real.exp (-c.re * r) := one_mul _

/-- The damped square-phase exponent `c_n(φ) = π (n+1)² e^{iφ}`. -/
def abelRate (n : ℕ) (φ : ℝ) : ℂ := (Real.pi : ℂ) * ((n + 1 : ℕ) : ℂ) ^ 2 * cexp (φ * I)

theorem abelRate_re (n : ℕ) (φ : ℝ) :
    (abelRate n φ).re = Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.cos φ := by
  unfold abelRate
  rw [show (Real.pi : ℂ) * ((n + 1 : ℕ) : ℂ) ^ 2 = ((Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) by
    push_cast; ring, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem norm_abelRate (n : ℕ) (φ : ℝ) : ‖abelRate n φ‖ = Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  unfold abelRate
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, norm_pow,
    Complex.norm_natCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]

/-- **Series of the rotated ray.** For `0 ≤ φ < π/2` and `Re α < 0`,
`∫₁^∞ r^α (ϑ(r e^{iφ}) - 1) dr = 2 Σ_{n ≥ 1} J_α(π n² e^{iφ})`. -/
theorem integral_ray_eq_tsum {α : ℂ} (hα : α.re < 0) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ < Real.pi / 2) :
    (∫ r in Ioi (1 : ℝ), (r : ℂ) ^ α * (jacobiThetaSum (r * cexp (φ * I)) - 1)) =
      2 * ∑' n : ℕ, abelRayTerm α (abelRate n φ) := by
  have hcos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ⟩
  have hrate : ∀ n : ℕ, 0 < (abelRate n φ).re := fun n => by rw [abelRate_re]; positivity
  set F : ℕ → ℝ → ℂ := fun n r => 2 * ((r : ℂ) ^ α * cexp (-abelRate n φ * r))
  have hpt : ∀ r ∈ Ioi (1 : ℝ), (r : ℂ) ^ α * (jacobiThetaSum (r * cexp (φ * I)) - 1) =
      ∑' n : ℕ, F n r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
    have hre : 0 < ((r : ℂ) * cexp (φ * I)).re := by
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]; positivity
    rw [(hasSum_jacobiThetaSum_sub_one hre).tsum_eq.symm, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [F, abelRate]
    rw [show -(Real.pi : ℂ) * ((n + 1 : ℕ) : ℂ) ^ 2 * ((r : ℂ) * cexp (φ * I)) =
      -((Real.pi : ℂ) * ((n + 1 : ℕ) : ℂ) ^ 2 * cexp (φ * I)) * r by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 1)) := fun n =>
    (integrableOn_cpow_mul_cexp_Ioi_one hα (hrate n)).const_mul 2
  have hnorm : ∀ n, (∫ r in Ioi (1 : ℝ), ‖F n r‖) ≤
      2 / (Real.pi * Real.cos φ) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have hc := hrate n
    have h1 : (∫ r in Ioi (1 : ℝ), ‖F n r‖) ≤ ∫ r in Ioi (1 : ℝ), 2 * Real.exp (-(abelRate n φ).re * r) := by
      refine setIntegral_mono_on (hint n).norm ((integrableOn_exp_mul_Ioi (by linarith) 1).const_mul 2)
        measurableSet_Ioi fun r hr => ?_
      have hr1 : (1 : ℝ) ≤ r := le_of_lt hr
      simp only [F, norm_mul, Complex.norm_ofNat, norm_ofReal_cpow_of_pos (lt_of_lt_of_le one_pos hr1),
        Complex.norm_exp]
      have : (-abelRate n φ * (r : ℂ)).re = -(abelRate n φ).re * r := by simp [Complex.mul_re]
      rw [this]
      have hp := Real.rpow_le_one_of_one_le_of_nonpos hr1 hα.le
      have := Real.exp_pos (-(abelRate n φ).re * r)
      nlinarith
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 1] at h1
    refine h1.trans ?_
    rw [abelRate_re] at *
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hexp : Real.exp (-(Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.cos φ) * 1) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    rw [show 2 * (-Real.exp (-(Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.cos φ) * 1) /
        -(Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.cos φ)) = 2 * Real.exp (-(Real.pi *
          ((n + 1 : ℕ) : ℝ) ^ 2 * Real.cos φ) * 1) / (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.cos φ) by
        field_simp]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    simpa using hexp
  have hsum : Summable (fun n => ∫ r in Ioi (1 : ℝ), ‖F n r‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun r => norm_nonneg _) hnorm ?_
    refine Summable.mul_left _ ?_
    exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  rw [← integral_tsum_of_summable_integral_norm hint hsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [F]
  rw [integral_const_mul, integral_cpow_mul_cexp_eq_abelRayTerm hα (hrate n)]

/-! ## The boundary arc -/

theorem cuspRemainder_one_two (η : ℂ) : cuspRemainder 1 2 η = jacobiThetaSum (I + η) := by
  have hG : gaussQ (-((1 : ℕ) : ℤ)) 2 = 0 := gaussQ_two (by decide)
  have hP : cuspPoint 1 2 = I := by unfold cuspPoint; push_cast; ring
  unfold cuspRemainder
  rw [hP, hG]; ring

theorem cexp_I_sub_I_mem_closedBall {θ : ℝ} (h1 : Real.pi / 3 ≤ θ) (h2 : θ < Real.pi / 2) :
    cexp (θ * I) - I ∈ Metric.closedBall ((Real.cos θ : ℝ) : ℂ) (Real.cos θ / 2) := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
  have hcos2 : Real.cos θ ≤ 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) h1
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hpyth := Real.sin_sq_add_cos_sq θ
  rw [Metric.mem_closedBall, Complex.dist_eq]
  have e : cexp (θ * I) - I - (Real.cos θ : ℂ) = ((Real.sin θ - 1 : ℝ) : ℂ) * I := by
    rw [← Complex.cos_add_sin_I]; push_cast; ring
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  nlinarith

/-- `ϑ(e^{iθ})` is bounded on `[0, π/2)` and tends to `0` at `θ = π/2`. -/
theorem exists_norm_jacobiThetaSum_arc_le :
    ∃ B : ℝ, ∀ θ ∈ Ico (0 : ℝ) (Real.pi / 2), ‖jacobiThetaSum (cexp (θ * I))‖ ≤ B := by
  obtain ⟨K, c, hK, hc, hb⟩ := exists_norm_cuspRemainder_le 1 2 (by norm_num)
  refine ⟨max 3 (K / c), fun θ hθ => ?_⟩
  obtain ⟨hθ0, hθ1⟩ := hθ
  by_cases hθ3 : θ ≤ Real.pi / 3
  · refine le_trans ?_ (le_max_left _ _)
    have hre : (1 : ℝ) / 2 ≤ (cexp (θ * I)).re := by
      rw [Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos]) hθ3
    have h := norm_jacobiThetaSum_sub_one_le (by linarith : 0 < (cexp (θ * I)).re)
    set r := Real.exp (-(Real.pi * (cexp (θ * I)).re))
    have hr : r ≤ 1 / 2 := by
      calc r ≤ Real.exp (-(Real.pi * (1 / 2))) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
        _ ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          have := Real.add_one_le_exp (Real.pi * (1 / 2)); linarith [Real.pi_gt_three]
    have hr0 : 0 < r := Real.exp_pos _
    have h2 : 2 * (r / (1 - r)) ≤ 2 := by
      rw [mul_div_assoc']; rw [div_le_iff₀ (by linarith)]; linarith
    calc ‖jacobiThetaSum (cexp (θ * I))‖ = ‖(jacobiThetaSum (cexp (θ * I)) - 1) + 1‖ := by ring_nf
      _ ≤ ‖jacobiThetaSum (cexp (θ * I)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 + 1 := by rw [norm_one]; linarith
      _ = 3 := by norm_num
  · push Not at hθ3
    refine le_trans ?_ (le_max_right _ _)
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hmem := cexp_I_sub_I_mem_closedBall hθ3.le hθ1
    have h := hb (Real.cos θ) hcos hcos1 _ hmem
    rw [cuspRemainder_one_two, show I + (cexp (θ * I) - I) = cexp (θ * I) by ring] at h
    refine h.trans ?_
    set ε := Real.cos θ
    have ht := pow_mul_exp_neg_mul_le_factorial hc (by positivity : (0 : ℝ) ≤ 1 / ε) 1
    simp only [pow_one, Nat.factorial_one, Nat.cast_one] at ht
    have hsq : (Real.sqrt ε)⁻¹ ≤ 1 / ε := by
      rw [inv_eq_one_div]
      refine one_div_le_one_div_of_le hcos ?_
      calc ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hcos.le).symm
        _ ≤ Real.sqrt ε * 1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hcos1)
            (Real.sqrt_nonneg _)
        _ = Real.sqrt ε := mul_one _
    have he : Real.exp (-(c / ε)) = Real.exp (-(c * (1 / ε))) := by ring_nf
    calc K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) ≤ K * (1 / ε) * Real.exp (-(c * (1 / ε))) := by
          rw [he]; gcongr
      _ = K * (1 / ε * Real.exp (-(c * (1 / ε)))) := by ring
      _ ≤ K * (1 / c) := by gcongr
      _ = K / c := by ring

theorem tendsto_jacobiThetaSum_arc :
    Tendsto (fun θ : ℝ => jacobiThetaSum (cexp (θ * I))) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  obtain ⟨K, c, hK, hc, hb⟩ := exists_norm_cuspRemainder_le 1 2 (by norm_num)
  have hcos : Tendsto (fun θ : ℝ => Real.cos θ) (𝓝[<] (Real.pi / 2)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (Real.continuous_cos.tendsto (Real.pi / 2)).mono_left
        (nhdsWithin_le_nhds (s := Iio (Real.pi / 2)))
      rwa [Real.cos_pi_div_two] at this
    · filter_upwards [Ioo_mem_nhdsLT (show 0 < Real.pi / 2 by positivity)] with θ hθ
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hinv : Tendsto (fun θ : ℝ => c * (1 / Real.cos θ)) (𝓝[<] (Real.pi / 2)) atTop := by
    have := tendsto_inv_nhdsGT_zero.comp hcos
    exact (this.const_mul_atTop hc).congr fun θ => by simp [Function.comp]
  have hlim : Tendsto (fun θ : ℝ => K * ((c * (1 / Real.cos θ)) ^ 1 *
      Real.exp (-(c * (1 / Real.cos θ)))) / c) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hinv).const_mul K
    simpa using this.div_const c
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 3 < Real.pi / 2 by linarith [Real.pi_pos])]
    with θ hθ
  obtain ⟨hθ3, hθ1⟩ := hθ
  have hcos0 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have h := hb (Real.cos θ) hcos0 hcos1 _ (cexp_I_sub_I_mem_closedBall hθ3.le hθ1)
  rw [cuspRemainder_one_two, show I + (cexp (θ * I) - I) = cexp (θ * I) by ring] at h
  refine h.trans ?_
  set ε := Real.cos θ
  have hsq : (Real.sqrt ε)⁻¹ ≤ 1 / ε := by
    rw [inv_eq_one_div]
    refine one_div_le_one_div_of_le hcos0 ?_
    calc ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hcos0.le).symm
      _ ≤ Real.sqrt ε * 1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hcos1)
          (Real.sqrt_nonneg _)
      _ = Real.sqrt ε := mul_one _
  calc K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) ≤ K * (1 / ε) * Real.exp (-(c / ε)) := by gcongr
    _ = K * ((c * (1 / ε)) ^ 1 * Real.exp (-(c * (1 / ε)))) / c := by
        field_simp

/-- The boundary-arc integrand `e^{i(α+1)θ} (ϑ(e^{iθ}) - 1)`. -/
def abelArcIntegrand (α : ℂ) (θ : ℝ) : ℂ :=
  cexp ((α + 1) * (θ * I)) * (jacobiThetaSum (cexp (θ * I)) - 1)

/-- The arc term `A(α) = i ∫₀^{π/2} e^{i(α+1)θ}(ϑ(e^{iθ}) - 1) dθ`. -/
def abelArcTerm (α : ℂ) : ℂ := I * ∫ θ in (0 : ℝ)..(Real.pi / 2), abelArcIntegrand α θ

theorem continuousOn_abelArcIntegrand (α : ℂ) :
    ContinuousOn (abelArcIntegrand α) (Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hre : 0 < (cexp (θ * I)).re := by
    rw [Complex.exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hθc : ContinuousAt (fun θ : ℝ => jacobiThetaSum (cexp (θ * I))) θ :=
    ContinuousAt.comp (g := jacobiThetaSum) (f := fun θ : ℝ => cexp (θ * I))
      (hasDerivAt_jacobiThetaSum hre).continuousAt (by fun_prop)
  exact ((by fun_prop : Continuous fun θ : ℝ => cexp ((α + 1) * (θ * I))).continuousAt.mul
    (hθc.sub continuousAt_const)).continuousWithinAt

theorem intervalIntegrable_abelArcIntegrand (α : ℂ) :
    IntervalIntegrable (abelArcIntegrand α) volume 0 (Real.pi / 2) := by
  obtain ⟨B, hB⟩ := exists_norm_jacobiThetaSum_arc_le
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)]
  refine (integrableOn_const (C := Real.exp (|(α + 1).im| * (Real.pi / 2)) * (B + 1))
    (by simp)).mono' ((continuousOn_abelArcIntegrand α).aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_))
  have hθ' : θ ∈ Ico (0 : ℝ) (Real.pi / 2) := ⟨hθ.1.le, hθ.2⟩
  unfold abelArcIntegrand
  rw [norm_mul]
  refine mul_le_mul ?_ ((norm_sub_le _ _).trans ?_) (norm_nonneg _) (Real.exp_pos _).le
  · rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : ((α + 1) * (θ * I)).re = -((α + 1).im * θ) := by simp [Complex.mul_re]
    rw [this]
    have := neg_abs_le (α + 1).im
    nlinarith [hθ.1, hθ.2, abs_nonneg (α + 1).im]
  · rw [norm_one]; linarith [hB θ hθ']

theorem abelRate_pi_div_two (n : ℕ) : abelRate n (Real.pi / 2) = I * Real.pi * ((n + 1 : ℕ) : ℂ) ^ 2 := by
  unfold abelRate
  rw [show ((Real.pi / 2 : ℝ) : ℂ) * I = (Real.pi / 2 : ℂ) * I by push_cast; ring,
    Complex.exp_pi_div_two_mul_I]
  ring

/-- **Global Abel pairing (Ward integral through the rational boundary).** For `Im z > -3/2`,
`M_z = A(α_z) + 2 e^{iπ(α_z+1)/2} Σ_{n ≥ 1} I_n(α_z)`. -/
theorem wardMellin_eq_abelPairing (z : ℂ) (hz : -(3 / 2) < z.im) :
    wardMellin z = abelArcTerm (wardExponent z) +
      2 * cexp ((wardExponent z + 1) * ((Real.pi / 2 : ℝ) * I)) *
        ∑' n : ℕ, abelRayTerm (wardExponent z) (abelRate n (Real.pi / 2)) := by
  set α := wardExponent z
  have hα : α.re < 0 := by
    simp only [α, wardExponent, Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.I_re,
      Complex.I_im]
    norm_num; linarith
  have hπ : (0 : ℝ) < Real.pi / 2 := by positivity
  -- the rotated representation holds on the left neighbourhood of `π/2`
  have hrep : ∀ φ ∈ Ioo (0 : ℝ) (Real.pi / 2), wardMellin z =
      I * (∫ θ in (0 : ℝ)..φ, abelArcIntegrand α θ) +
        2 * cexp ((α + 1) * (φ * I)) * ∑' n : ℕ, abelRayTerm α (abelRate n φ) := by
    intro φ hφ
    rw [wardMellin_eq_rotated z hφ.1 hφ.2, integral_ray_eq_tsum hα hφ.1.le hφ.2]
    unfold abelArcIntegrand
    ring
  have hIoo : Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := Ioo_mem_nhdsLT hπ
  -- limit of the arc primitive
  have harc : Tendsto (fun φ : ℝ => ∫ θ in (0 : ℝ)..φ, abelArcIntegrand α θ) (𝓝[<] (Real.pi / 2))
      (𝓝 (∫ θ in (0 : ℝ)..(Real.pi / 2), abelArcIntegrand α θ)) := by
    have hc := intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_abelArcIntegrand α) (a := 0) (by simp [hπ.le])
    rw [Set.uIcc_of_le hπ.le] at hc
    have := (hc (Real.pi / 2) ⟨hπ.le, le_rfl⟩).mono (Ioo_subset_Icc_self)
    rw [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hπ] at this
    exact this
  -- limit of the phase
  have hphase : Tendsto (fun φ : ℝ => cexp ((α + 1) * (φ * I))) (𝓝[<] (Real.pi / 2))
      (𝓝 (cexp ((α + 1) * ((Real.pi / 2 : ℝ) * I)))) :=
    ((by fun_prop : Continuous fun φ : ℝ => cexp ((α + 1) * (φ * I))).tendsto _).mono_left
      nhdsWithin_le_nhds
  -- Tannery for the square-phase series
  have hseries : Tendsto (fun φ : ℝ => ∑' n : ℕ, abelRayTerm α (abelRate n φ)) (𝓝[<] (Real.pi / 2))
      (𝓝 (∑' n : ℕ, abelRayTerm α (abelRate n (Real.pi / 2)))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n => 1 / (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) * (1 + ‖α‖ / (-α.re))) ?_ ?_ ?_
    · have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      refine (this.mul_left (1 / Real.pi * (1 + ‖α‖ / (-α.re)))).congr fun n => ?_
      field_simp
    · intro n
      have hne : abelRate n (Real.pi / 2) ≠ 0 := by
        intro h; have := norm_abelRate n (Real.pi / 2); rw [h, norm_zero] at this
        have : (0 : ℝ) < Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
        linarith
      have hK := continuousOn_abelTailIntegral hα _ (show 0 ≤ (abelRate n (Real.pi / 2)).re by
        rw [abelRate_re, Real.cos_pi_div_two, mul_zero])
      have hJ : ContinuousWithinAt (abelRayTerm α) {c : ℂ | 0 ≤ c.re} (abelRate n (Real.pi / 2)) := by
        unfold abelRayTerm
        exact ((Complex.continuous_exp.comp continuous_neg).continuousAt.continuousWithinAt.div
          continuousWithinAt_id hne).add ((continuousWithinAt_const.div continuousWithinAt_id hne).mul hK)
      have hrate : Tendsto (fun φ : ℝ => abelRate n φ) (𝓝[<] (Real.pi / 2))
          (𝓝[{c : ℂ | 0 ≤ c.re}] (abelRate n (Real.pi / 2))) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · exact ((by unfold abelRate; fun_prop : Continuous fun φ : ℝ => abelRate n φ).tendsto _).mono_left
            nhdsWithin_le_nhds
        · filter_upwards [hIoo] with φ hφ
          show 0 ≤ (abelRate n φ).re
          rw [abelRate_re]
          have := Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
          positivity
      exact hJ.tendsto.comp hrate
    · filter_upwards [hIoo] with φ hφ n
      have hre : 0 ≤ (abelRate n φ).re := by
        rw [abelRate_re]
        have := Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
        positivity
      have hne : abelRate n φ ≠ 0 := by
        intro h; have := norm_abelRate n φ; rw [h, norm_zero] at this
        have : (0 : ℝ) < Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
        linarith
      have := norm_abelRayTerm_le hα hre hne
      rwa [norm_abelRate] at this
  have hlim := ((harc.const_mul I).add ((hphase.const_mul 2).mul hseries))
  have hconst : Tendsto (fun _ : ℝ => wardMellin z) (𝓝[<] (Real.pi / 2)) (𝓝 (wardMellin z)) :=
    tendsto_const_nhds
  have heq := tendsto_nhds_unique hconst (hlim.congr' (by
    filter_upwards [hIoo] with φ hφ
    rw [hrep φ hφ]))
  rw [heq]
  unfold abelArcTerm
  ring

theorem cexp_neg_I_pi_sq (m : ℕ) : cexp (-(I * Real.pi * (m : ℂ) ^ 2)) = (-1) ^ m := by
  have h : -(I * Real.pi * (m : ℂ) ^ 2) = ((m ^ 2 : ℕ) : ℂ) * (-(Real.pi * I)) := by
    push_cast; ring
  rw [h, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  obtain he | ho := Nat.even_or_odd m
  · rw [Even.neg_one_pow (Nat.even_pow.mpr ⟨he, two_ne_zero⟩), Even.neg_one_pow he]
  · rw [Odd.neg_one_pow (Odd.pow ho), Odd.neg_one_pow ho]

/-- **The square-phase integrals** `I_n(α) = (-1)^n/(iπn²) + (α/(iπn²)) ∫₁^∞ r^{α-1} e^{-iπn² r} dr`. -/
theorem abelRayTerm_square (α : ℂ) (m : ℕ) :
    abelRayTerm α (I * Real.pi * (m : ℂ) ^ 2) =
      (-1) ^ m / (I * Real.pi * (m : ℂ) ^ 2) + α / (I * Real.pi * (m : ℂ) ^ 2) *
        ∫ r in Ioi (1 : ℝ), (r : ℂ) ^ (α - 1) * cexp (-(I * Real.pi * (m : ℂ) ^ 2) * r) := by
  unfold abelRayTerm abelTailIntegral
  rw [cexp_neg_I_pi_sq]

/-- **Bound (6):** `|I_n(α)| ≤ (1/(πn²))(1 + |α|/(-Re α))`. -/
theorem norm_abelRayTerm_square_le {α : ℂ} (hα : α.re < 0) {m : ℕ} (hm : 0 < m) :
    ‖abelRayTerm α (I * Real.pi * (m : ℂ) ^ 2)‖ ≤
      1 / (Real.pi * (m : ℝ) ^ 2) * (1 + ‖α‖ / (-α.re)) := by
  have hc : 0 ≤ (I * Real.pi * (m : ℂ) ^ 2).re := by
    simp [Complex.mul_re, ← Complex.ofReal_natCast, ← Complex.ofReal_pow]
  have hne : I * Real.pi * (m : ℂ) ^ 2 ≠ 0 := by
    have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    exact mul_ne_zero (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (pow_ne_zero 2 this)
  have h := norm_abelRayTerm_le hα hc hne
  have hn : ‖I * Real.pi * (m : ℂ) ^ 2‖ = Real.pi * (m : ℝ) ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, norm_pow,
      Complex.norm_natCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rwa [hn] at h

/-- `I_n(α)` is the improper oscillatory integral `lim_{R→∞} ∫₁^R r^α e^{-iπn² r} dr`. -/
theorem tendsto_integral_abelRayTerm_square {α : ℂ} (hα : α.re < 0) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun R : ℝ => ∫ r in (1 : ℝ)..R, (r : ℂ) ^ α * cexp (-(I * Real.pi * (m : ℂ) ^ 2) * r))
      atTop (𝓝 (abelRayTerm α (I * Real.pi * (m : ℂ) ^ 2))) := by
  set c : ℂ := I * Real.pi * (m : ℂ) ^ 2
  have hc : 0 ≤ c.re := by
    simp [c, Complex.mul_re, ← Complex.ofReal_natCast, ← Complex.ofReal_pow]
  have hcre : c.re = 0 := by
    simp [c, Complex.mul_re, ← Complex.ofReal_natCast, ← Complex.ofReal_pow]
  have hne : c ≠ 0 := by
    have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    exact mul_ne_zero (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (pow_ne_zero 2 this)
  have hIBP : ∀ R : ℝ, 1 ≤ R → (∫ r in (1 : ℝ)..R, (r : ℂ) ^ α * cexp (-c * r)) =
      (R : ℂ) ^ α * (-cexp (-c * R) / c) - ((1 : ℝ) : ℂ) ^ α * (-cexp (-c * ((1 : ℝ) : ℂ)) / c) -
        ∫ r in (1 : ℝ)..R, (α * (r : ℂ) ^ (α - 1)) * (-cexp (-c * r) / c) := by
    intro R hR
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun r : ℝ => (r : ℂ) ^ α)
      (v := fun r : ℝ => -cexp (-c * r) / c) (u' := fun r : ℝ => α * (r : ℂ) ^ (α - 1))
      (v' := fun r : ℝ => cexp (-c * r)) (fun r hr => ?_) (fun r _ => ?_) ?_ ?_
    · have hr1 : 1 ≤ r := by
        rw [Set.uIcc_of_le hR] at hr; exact hr.1
      have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
      exact (Complex.hasStrictDerivAt_cpow_const (Or.inl (by simpa using hr0))).hasDerivAt.comp_ofReal
    · have h := (((Complex.hasDerivAt_exp _).comp (r : ℂ) ((hasDerivAt_id (r : ℂ)).const_mul
        (-c))).neg.div_const c).comp_ofReal
      exact h.congr_deriv (by field_simp; simp only [id])
    · refine ContinuousOn.intervalIntegrable fun r hr => ?_
      rw [Set.uIcc_of_le hR] at hr
      have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr.1
      have hslit : (r : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hr0)
      exact ((continuousAt_const.mul ((continuousAt_cpow_const hslit).comp
        Complex.continuous_ofReal.continuousAt))).continuousWithinAt
    · exact (by fun_prop : Continuous fun r : ℝ => cexp (-c * r)).intervalIntegrable _ _
  have hK := intervalIntegral_tendsto_integral_Ioi
    (f := fun r : ℝ => (r : ℂ) ^ (α - 1) * cexp (-c * r)) 1 (integrableOn_abelTail hα hc) tendsto_id
  have hbd : Tendsto (fun R : ℝ => (R : ℂ) ^ α * (-cexp (-c * R) / c)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun R : ℝ => R ^ α.re / ‖c‖) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (y := -α.re) (by linarith)).div_const ‖c‖ |>.congr
        (fun R => by rw [neg_neg])
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [norm_mul, norm_div, norm_neg, Complex.norm_exp, norm_ofReal_cpow_of_pos hR]
    have : (-c * (R : ℂ)).re = 0 := by simp [Complex.mul_re, hcre]
    rw [this, Real.exp_zero]
    ring_nf; rfl
  have hlim := ((hbd.sub (tendsto_const_nhds (x := ((1 : ℝ) : ℂ) ^ α *
    (-cexp (-c * ((1 : ℝ) : ℂ)) / c)))).sub
    ((hK.const_mul (-α / c))))
  refine (hlim.congr' ?_).trans_eq ?_  -- placeholder combination
  · filter_upwards [eventually_ge_atTop 1] with R hR
    rw [hIBP R hR, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun r _ => ?_
    field_simp
  · unfold abelRayTerm abelTailIntegral
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul, mul_one, zero_sub]
    field_simp
    ring_nf

/-! ## The square-phase potential -/

/-- The square-phase term `e^{-iπm²r}/m²` (zero at `m = 0`). -/
def squarePhaseTerm (m : ℕ) (r : ℝ) : ℂ := cexp (-(I * Real.pi * (m : ℂ) ^ 2 * r)) / (m : ℂ) ^ 2

/-- The square-phase potential `Q(r) = Σ_{n ≥ 1} e^{-iπn²r}/n²`. -/
def squarePhasePotential (r : ℝ) : ℂ := ∑' m : ℕ, squarePhaseTerm m r

theorem norm_squarePhaseTerm (m : ℕ) (r : ℝ) : ‖squarePhaseTerm m r‖ = 1 / (m : ℝ) ^ 2 := by
  unfold squarePhaseTerm
  rw [norm_div, Complex.norm_exp, norm_pow, Complex.norm_natCast]
  have : (-(I * Real.pi * (m : ℂ) ^ 2 * r)).re = 0 := by
    simp [Complex.mul_re, ← Complex.ofReal_natCast, ← Complex.ofReal_pow]
  rw [this, Real.exp_zero]

theorem summable_squarePhaseTerm (r : ℝ) : Summable (fun m => squarePhaseTerm m r) :=
  Summable.of_norm_bounded hasSum_zeta_two.summable fun m => (norm_squarePhaseTerm m r).le

theorem squarePhaseTerm_zero (r : ℝ) : squarePhaseTerm 0 r = 0 := by simp [squarePhaseTerm]

/-- `Q` is the Dirichlet series over `n ≥ 1`. -/
theorem squarePhasePotential_eq (r : ℝ) :
    squarePhasePotential r =
      ∑' n : ℕ, cexp (-(I * Real.pi * ((n + 1 : ℕ) : ℂ) ^ 2 * r)) / ((n + 1 : ℕ) : ℂ) ^ 2 := by
  unfold squarePhasePotential
  rw [(summable_squarePhaseTerm r).tsum_eq_zero_add, squarePhaseTerm_zero, zero_add]
  rfl

theorem norm_squarePhasePotential_le (r : ℝ) : ‖squarePhasePotential r‖ ≤ Real.pi ^ 2 / 6 := by
  unfold squarePhasePotential
  refine (norm_tsum_le_tsum_norm (summable_squarePhaseTerm r).norm).trans ?_
  simp_rw [norm_squarePhaseTerm]
  rw [hasSum_zeta_two.tsum_eq]

theorem continuous_squarePhasePotential : Continuous squarePhasePotential :=
  continuous_tsum (fun m => by unfold squarePhaseTerm; fun_prop) hasSum_zeta_two.summable
    fun m r => (norm_squarePhaseTerm m r).le

theorem squarePhaseTerm_add_two (m : ℕ) (r : ℝ) : squarePhaseTerm m (r + 2) = squarePhaseTerm m r := by
  unfold squarePhaseTerm
  congr 1
  rw [show -(I * Real.pi * (m : ℂ) ^ 2 * ((r + 2 : ℝ) : ℂ)) =
    -(I * Real.pi * (m : ℂ) ^ 2 * r) + ((-(m ^ 2 : ℕ) : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `Q` has period two. -/
theorem squarePhasePotential_add_two (r : ℝ) : squarePhasePotential (r + 2) = squarePhasePotential r := by
  unfold squarePhasePotential; simp_rw [squarePhaseTerm_add_two]

theorem integral_squarePhaseTerm (m : ℕ) : ∫ r in (0 : ℝ)..2, squarePhaseTerm m r = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [squarePhaseTerm_zero]
  unfold squarePhaseTerm
  have hc : -(I * Real.pi * (m : ℂ) ^ 2) ≠ 0 := by
    have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero I_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (pow_ne_zero 2 this))
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  have h := integral_exp_mul_complex (a := 0) (b := 2) hc
  simp only [neg_mul] at h ⊢
  rw [show (fun x : ℝ => cexp (-(I * Real.pi * (m : ℂ) ^ 2 * x))) =
    fun x : ℝ => cexp (-(I * Real.pi * (m : ℂ) ^ 2) * x) by funext x; ring_nf]
  rw [integral_exp_mul_complex hc]
  have h2 : cexp (-(I * Real.pi * (m : ℂ) ^ 2) * ((2 : ℝ) : ℂ)) = 1 := by
    rw [show -(I * Real.pi * (m : ℂ) ^ 2) * ((2 : ℝ) : ℂ) = ((-(m ^ 2 : ℕ) : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_int_mul_two_pi_mul_I]
  rw [h2]; simp

/-- `Q` has period mean zero. -/
theorem integral_squarePhasePotential : ∫ r in (0 : ℝ)..2, squarePhasePotential r = 0 := by
  unfold squarePhasePotential
  have hint : ∀ m : ℕ, Integrable (fun r => squarePhaseTerm m r) (volume.restrict (Ioc (0 : ℝ) 2)) :=
    fun m => (by unfold squarePhaseTerm; fun_prop : Continuous fun r => squarePhaseTerm m r)
      |>.integrableOn_Ioc
  have hnorm : ∀ m : ℕ, (∫ r in Ioc (0 : ℝ) 2, ‖squarePhaseTerm m r‖) = 2 * (1 / (m : ℝ) ^ 2) := by
    intro m
    simp_rw [norm_squarePhaseTerm]
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
    norm_num
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← integral_tsum_of_summable_integral_norm hint (by
      simp_rw [hnorm]; exact hasSum_zeta_two.summable.mul_left 2)]
  simp_rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 by norm_num),
    integral_squarePhaseTerm, tsum_zero]

/-- The alternating Basel sum `Σ_{n ≥ 1} (-1)^n/n² = -π²/12`. -/
theorem tsum_neg_one_pow_div_sq : ∑' m : ℕ, (-1 : ℝ) ^ m / (m : ℝ) ^ 2 = -(Real.pi ^ 2 / 12) := by
  set g : ℕ → ℝ := fun m => 1 / (m : ℝ) ^ 2
  set f : ℕ → ℝ := fun m => (-1 : ℝ) ^ m / (m : ℝ) ^ 2
  have hg : Summable g := hasSum_zeta_two.summable
  have hf : Summable f := Summable.of_norm_bounded hg fun m => by
    simp [f, g]
  have hg2 : Summable fun k => g (2 * k) := hg.comp_injective (fun a b h => by omega)
  have hg21 : Summable fun k => g (2 * k + 1) := hg.comp_injective (fun a b h => by omega)
  have hf2 : Summable fun k => f (2 * k) := hf.comp_injective (fun a b h => by omega)
  have hf21 : Summable fun k => f (2 * k + 1) := hf.comp_injective (fun a b h => by omega)
  have heven : ∑' k, g (2 * k) = (Real.pi ^ 2 / 6) / 4 := by
    rw [← hasSum_zeta_two.tsum_eq, ← tsum_div_const]
    refine tsum_congr fun k => ?_
    simp only [g]; push_cast; ring
  have hodd : ∑' k, g (2 * k + 1) = Real.pi ^ 2 / 8 := by
    have h := tsum_even_add_odd hg2 hg21
    rw [heven, hasSum_zeta_two.tsum_eq] at h
    linarith
  have hfe : ∑' k, f (2 * k) = ∑' k, g (2 * k) := tsum_congr fun k => by
    simp only [f, g, pow_mul]; norm_num
  have hfo : ∑' k, f (2 * k + 1) = -∑' k, g (2 * k + 1) := by
    rw [← tsum_neg]; refine tsum_congr fun k => ?_
    simp only [f, g]
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_div]
  rw [← tsum_even_add_odd hf2 hf21, hfe, hfo, heven, hodd]
  ring

/-- **`Q(1) = -π²/12`.** -/
theorem squarePhasePotential_one : squarePhasePotential 1 = -((Real.pi : ℂ) ^ 2 / 12) := by
  unfold squarePhasePotential
  have h : ∀ m : ℕ, squarePhaseTerm m 1 = (((-1 : ℝ) ^ m / (m : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro m
    unfold squarePhaseTerm
    rw [Complex.ofReal_one, mul_one, cexp_neg_I_pi_sq]
    push_cast; ring
  simp_rw [h]
  rw [← Complex.ofReal_tsum, tsum_neg_one_pow_div_sq]
  push_cast; ring

theorem squarePhaseTerm_add_one (m : ℕ) (r : ℝ) :
    squarePhaseTerm m (r + 1) = (-1) ^ m * squarePhaseTerm m r := by
  unfold squarePhaseTerm
  rw [show -(I * Real.pi * (m : ℂ) ^ 2 * ((r + 1 : ℝ) : ℂ)) =
    -(I * Real.pi * (m : ℂ) ^ 2 * r) + -(I * Real.pi * (m : ℂ) ^ 2) by push_cast; ring,
    Complex.exp_add, cexp_neg_I_pi_sq]
  ring

theorem squarePhaseTerm_two_mul (k : ℕ) (r : ℝ) :
    squarePhaseTerm (2 * k) r = (1 / 4) * squarePhaseTerm k (4 * r) := by
  unfold squarePhaseTerm
  push_cast
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp
  ring_nf

/-- **Square-frequency parity law** `Q(r+1) + Q(r) = ½ Q(4r)`. -/
theorem squarePhasePotential_parity (r : ℝ) :
    squarePhasePotential (r + 1) + squarePhasePotential r = (1 / 2) * squarePhasePotential (4 * r) := by
  unfold squarePhasePotential
  have hs := summable_squarePhaseTerm r
  have hs1 := summable_squarePhaseTerm (r + 1)
  rw [← hs1.tsum_add hs]
  set h : ℕ → ℂ := fun m => squarePhaseTerm m (r + 1) + squarePhaseTerm m r
  have hh : Summable h := hs1.add hs
  have he : Summable fun k => h (2 * k) := hh.comp_injective (fun a b hab => by omega)
  have ho : Summable fun k => h (2 * k + 1) := hh.comp_injective (fun a b hab => by omega)
  rw [← tsum_even_add_odd he ho]
  have hodd : ∀ k, h (2 * k + 1) = 0 := by
    intro k; simp only [h, squarePhaseTerm_add_one, pow_succ, pow_mul]; norm_num
  have heven : ∀ k, h (2 * k) = (1 / 2) * squarePhaseTerm k (4 * r) := by
    intro k; simp only [h, squarePhaseTerm_add_one, pow_mul, squarePhaseTerm_two_mul]; norm_num; ring
  simp_rw [hodd, heven, tsum_zero, add_zero]
  rw [tsum_mul_left]

theorem re_I_mul_pi_natSq (m : ℕ) : (I * Real.pi * (m : ℂ) ^ 2).re = 0 := by
  rw [show I * (Real.pi : ℂ) * (m : ℂ) ^ 2 = ((Real.pi * (m : ℝ) ^ 2 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.mul_I_re, Complex.ofReal_im, neg_zero]

theorem re_neg_I_mul_pi_natSq_mul (m : ℕ) (r : ℝ) :
    (-(I * Real.pi * (m : ℂ) ^ 2 * r)).re = 0 := by
  rw [show -(I * (Real.pi : ℂ) * (m : ℂ) ^ 2 * r) = ((-(Real.pi * (m : ℝ) ^ 2 * r) : ℝ) : ℂ) * I by
    push_cast; ring, Complex.mul_I_re, Complex.ofReal_im, neg_zero]

/-- **Boundary formula through the square-phase potential (8).** For `Im z > -3/2`,
`M_z = A(α) + 2 e^{iπ(α+1)/2} [iπ/12 + (α/(iπ)) ∫₁^∞ r^{α-1} Q(r) dr]`. -/
theorem wardMellin_eq_squarePhasePotential (z : ℂ) (hz : -(3 / 2) < z.im) :
    wardMellin z = abelArcTerm (wardExponent z) +
      2 * cexp ((wardExponent z + 1) * ((Real.pi / 2 : ℝ) * I)) *
        (I * Real.pi / 12 + wardExponent z / (I * Real.pi) *
          ∫ r in Ioi (1 : ℝ), (r : ℂ) ^ (wardExponent z - 1) * squarePhasePotential r) := by
  rw [wardMellin_eq_abelPairing z hz]
  set α := wardExponent z
  have hα : α.re < 0 := by
    simp only [α, wardExponent, Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.I_re,
      Complex.I_im]
    norm_num; linarith
  congr 2
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- split each square-phase term
  have hterm : ∀ n : ℕ, abelRayTerm α (abelRate n (Real.pi / 2)) =
      (1 / (I * Real.pi)) * (((-1 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) +
        α / (I * Real.pi) * ∫ r in Ioi (1 : ℝ), (r : ℂ) ^ (α - 1) *
          (cexp (-(I * Real.pi * ((n + 1 : ℕ) : ℂ) ^ 2 * r)) / ((n + 1 : ℕ) : ℂ) ^ 2) := by
    intro n
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    rw [abelRate_pi_div_two, abelRayTerm_square]
    have hint : (∫ r in Ioi (1 : ℝ), (r : ℂ) ^ (α - 1) *
        (cexp (-(I * Real.pi * ((n + 1 : ℕ) : ℂ) ^ 2 * r)) / ((n + 1 : ℕ) : ℂ) ^ 2)) =
        (∫ r in Ioi (1 : ℝ), (r : ℂ) ^ (α - 1) *
          cexp (-(I * Real.pi * ((n + 1 : ℕ) : ℂ) ^ 2) * r)) / ((n + 1 : ℕ) : ℂ) ^ 2 := by
      rw [← integral_div]
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      ring_nf
    rw [hint]
    push_cast
    field_simp
  have hA0 : Summable fun n : ℕ => (-1 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2 :=
    Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hasSum_zeta_two.summable)
      fun n => by rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow, Real.norm_natCast]
  have hA : Summable fun n : ℕ => (1 / (I * Real.pi)) *
      (((-1 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) :=
    (Complex.summable_ofReal.mpr hA0).mul_left _
  set F : ℕ → ℝ → ℂ := fun n r => (r : ℂ) ^ (α - 1) *
    (cexp (-(I * Real.pi * ((n + 1 : ℕ) : ℂ) ^ 2 * r)) / ((n + 1 : ℕ) : ℂ) ^ 2)
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi 1)) := by
    intro n
    refine IntegrableOn.congr_fun ((integrableOn_abelTail hα (c := I * Real.pi * ((n + 1 : ℕ) : ℂ) ^ 2)
      (re_I_mul_pi_natSq (n + 1)).ge).div_const
      (((n + 1 : ℕ) : ℂ) ^ 2)) (fun r _ => ?_) measurableSet_Ioi
    simp only [F]; ring_nf
  have hFnorm : ∀ n, (∫ r in Ioi (1 : ℝ), ‖F n r‖) ≤ 1 / (-α.re) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have hbd : ∀ r ∈ Ioi (1 : ℝ), ‖F n r‖ ≤ r ^ (α.re - 1) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      intro r hr
      have hr1 : (1 : ℝ) ≤ r := le_of_lt hr
      simp only [F, norm_mul, norm_div, Complex.norm_exp, norm_pow, Complex.norm_natCast,
        norm_ofReal_cpow_of_pos (lt_of_lt_of_le one_pos hr1)]
      rw [re_neg_I_mul_pi_natSq_mul, Real.exp_zero, Complex.sub_re, Complex.one_re]
    have hint := integral_Ioi_rpow_of_lt (by linarith : α.re - 1 < -1) one_pos
    simp only [Real.one_rpow, sub_add_cancel] at hint
    calc (∫ r in Ioi (1 : ℝ), ‖F n r‖) ≤ ∫ r in Ioi (1 : ℝ), r ^ (α.re - 1) *
          (1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
          setIntegral_mono_on (hFint n).norm
            ((integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).mul_const _) measurableSet_Ioi hbd
      _ = 1 / (-α.re) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
          rw [integral_mul_const, hint]; ring
  have hFsum : Summable fun n => ∫ r in Ioi (1 : ℝ), ‖F n r‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun r => norm_nonneg _) hFnorm
      (((summable_nat_add_iff 1).mpr hasSum_zeta_two.summable).mul_left _)
  have hB : Summable fun n : ℕ => α / (I * Real.pi) * ∫ r in Ioi (1 : ℝ), F n r :=
    Summable.mul_left _ (Summable.of_norm_bounded hFsum fun n => norm_integral_le_integral_norm _)
  simp_rw [hterm]
  rw [hA.tsum_add hB, tsum_mul_left, tsum_mul_left, integral_tsum_of_summable_integral_norm hFint hFsum]
  have halt : ∑' n : ℕ, (((-1 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) =
      -((Real.pi : ℂ) ^ 2 / 12) := by
    rw [← Complex.ofReal_tsum]
    have hsum : Summable (fun m : ℕ => (-1 : ℝ) ^ m / (m : ℝ) ^ 2) :=
      Summable.of_norm_bounded hasSum_zeta_two.summable fun m => by
        rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow, Real.norm_natCast]
    have h : (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2) =
        ∑' m : ℕ, (-1 : ℝ) ^ m / (m : ℝ) ^ 2 := by
      rw [hsum.tsum_eq_zero_add]; simp
    rw [h, tsum_neg_one_pow_div_sq]
    push_cast; ring
  rw [halt]
  have hQ : (∫ r in Ioi (1 : ℝ), ∑' n : ℕ, F n r) =
      ∫ r in Ioi (1 : ℝ), (r : ℂ) ^ (α - 1) * squarePhasePotential r := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [F]
    rw [tsum_mul_left, squarePhasePotential_eq]
  rw [hQ]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## The twisted Poisson identity at `y = i` and the two-ended modes -/

theorem rationalCuspCoeff_one_two (ℓ : ℤ) : rationalCuspCoeff 1 2 ℓ = 1 - (-1) ^ ℓ := by
  unfold rationalCuspCoeff
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_pow two_ne_zero,
    mul_zero, zero_div, Complex.exp_zero, one_mul, Nat.cast_ofNat, one_pow]
  have h1 : cexp (2 * Real.pi * I * (-((1 : ℕ) : ℂ) * 1 / 2)) = -1 := by
    rw [show 2 * (Real.pi : ℂ) * I * (-((1 : ℕ) : ℂ) * 1 / 2) = -(Real.pi * I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have h2 : cexp (2 * Real.pi * I * ((((1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) * ℓ) = (-1) ^ ℓ := by
    rw [show 2 * (Real.pi : ℂ) * I * ((((1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) * ℓ = ℓ * (Real.pi * I) by
      push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  simp only [Nat.cast_one] at h1 h2
  rw [h1, h2]
  simp [sub_eq_add_neg]

/-- **Twisted Poisson identity at `i`**: `ϑ(i + w) = w^{-1/2} Σ_{m ∈ ℤ} e^{-π(m+1/2)²/w}`. -/
theorem jacobiThetaSum_I_add {w : ℂ} (hw : 0 < w.re) :
    jacobiThetaSum (I + w) =
      w ^ (-(1 / 2) : ℂ) * ∑' m : ℤ, cexp (-(Real.pi : ℂ) * ((m : ℂ) + 1 / 2) ^ 2 / w) := by
  have hP : cuspPoint 1 2 = I := by unfold cuspPoint; push_cast; ring
  have h := jacobiThetaSum_cusp 1 2 (by norm_num) hw
  rw [show 2 * I * ((1 : ℕ) : ℂ) / ((2 : ℕ) : ℂ) = I by push_cast; ring] at h
  rw [h]
  unfold cuspPoissonSeries
  simp_rw [rationalCuspCoeff_one_two]
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw
  set f : ℤ → ℂ := fun ℓ => (1 - (-1) ^ ℓ) * cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 /
    (((2 : ℕ) : ℂ) ^ 2 * w))
  have hsupp : Function.support f ⊆ Set.range (fun m : ℤ => 2 * m + 1) := by
    intro ℓ hℓ
    by_contra hnot
    apply hℓ
    obtain ⟨k, hk⟩ : Even ℓ := by
      rcases Int.even_or_odd ℓ with he | ⟨k, hk⟩
      · exact he
      · exact absurd ⟨k, hk.symm⟩ hnot
    simp only [f, hk, ← two_mul, zpow_mul]
    norm_num
  have hinj : Function.Injective (fun m : ℤ => 2 * m + 1) := fun a b hab => by
    simp only at hab; omega
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [f]
  have hodd : ((-1 : ℂ)) ^ (2 * m + 1) = -1 := by
    rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num
  rw [hodd]
  have e : cexp (-(Real.pi : ℂ) * (((2 * m + 1 : ℤ)) : ℂ) ^ 2 / (((2 : ℕ) : ℂ) ^ 2 * w)) =
      cexp (-(Real.pi : ℂ) * ((m : ℂ) + 1 / 2) ^ 2 / w) := by
    congr 1; push_cast; field_simp
  rw [e]
  push_cast
  ring

/-- The left-decaying source mode `U_z(x) = -i e^{-izx} ∫_{-∞}^x e^{izy} k(y) dy`. -/
def thetaLeftSourceMode (z : ℂ) (x : ℝ) : ℂ :=
  -I * cexp (-(I * z * x)) * ∫ y in Iic x, cexp (I * z * y) * (thetaCuspFullSource y : ℂ)

/-- The right-decaying source mode `V_z(x) = i e^{-izx} ∫_x^∞ e^{izy} k(y) dy`. -/
def thetaRightSourceMode (z : ℂ) (x : ℝ) : ℂ :=
  I * cexp (-(I * z * x)) * ∫ y in Ioi x, cexp (I * z * y) * (thetaCuspFullSource y : ℂ)

/-- **Connection of the two-ended modes**: `U_z(x) - V_z(x) = -i e^{-izx} Ξ(z)`. -/
theorem thetaLeftSourceMode_sub_right (z : ℂ) (x : ℝ) :
    thetaLeftSourceMode z x - thetaRightSourceMode z x = -I * cexp (-(I * z * x)) * XiC z := by
  have hint : Integrable (fun y : ℝ => cexp (I * z * y) * (thetaCuspFullSource y : ℂ)) := by
    refine (expMomentSource_thetaSourceC.integrable_cexp (-z)).congr
      (Eventually.of_forall fun y => ?_)
    simp only [thetaSourceC]; ring_nf
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (f := fun y : ℝ => cexp (I * z * y) *
    (thetaCuspFullSource y : ℂ)) (b := x) hint.integrableOn hint.integrableOn
  have hXi : XiC z = ∫ y : ℝ, cexp (I * z * y) * (thetaCuspFullSource y : ℂ) := by
    have h1 := expMomentSource_thetaSourceC.sourceTransform_eq_integral_cos thetaSourceC_neg z
    have h2 := expMomentSource_thetaSourceC.sourceTransform_eq_integral_cos thetaSourceC_neg (-z)
    have hcos : ∀ t : ℝ, Complex.cos (-z * t) = Complex.cos (z * t) := fun t => by
      rw [neg_mul, Complex.cos_neg]
    simp_rw [hcos] at h2
    rw [← sourceTransform_thetaSourceC, h1, ← h2]
    unfold sourceTransform
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [thetaSourceC]; ring_nf
  unfold thetaLeftSourceMode thetaRightSourceMode
  rw [hXi, ← hsplit]
  ring

end RHTower
