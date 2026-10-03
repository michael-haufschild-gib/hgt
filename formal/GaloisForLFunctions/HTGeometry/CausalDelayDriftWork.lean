import GaloisForLFunctions.HTGeometry.EulerShellHardyTraceFormation
import GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift

/-!
# Causal-delay radial-drift work

The delayed, width-`T` smoothed radial multiplier
`Φ_{δ,b,T}(z) = e^{-bz}(e^{δz} - 1)(1 - e^{-Tz})/(Tz)` (**(CDW.3)**) is the Laplace transform of the
signed window difference `h_{δ,b,T} = T^{-1}(1_{(b-δ,b-δ+T]} - 1_{(b,b+T]})` (**(CDW.7)**,
**(CDW.9)**).  For `δ ≠ 0`:

* the packet `Φ_{δ,b,T}(L)v` has finite formation capital iff `Φ_{δ,b,T} ∈ H²` iff both window starts
  are causal, `b ≥ max(0, δ)` (**(CDW.5)–(CDW.6)**); off this chamber `|Φ(x)| → ∞` along the real
  axis, which no `H²` function allows;
* on the Euler shell the history is unique and the least work is
  `‖h_{δ,b,T}‖² = 2 min(|δ|, T)/T²`, independent of the admitted delay (**(CDW.8)**, **(CDW.10)**);
* reflection `δ ↦ -δ` admits both orientations iff `b ≥ |δ|`, with paired work `4 min(|δ|,T)/T²`
  (**(CDW.13)–(CDW.15)**); extra delay is the right-shift gauge (**(CDW.15a)–(CDW.15b)**);
* zero source delay with finite capital and reflection forces `δ = 0` (**(CDW.26)–(CDW.29)**), while
  delay alone never selects (**(CDW.30)**); width, sign and the source clock are load-bearing (§7).
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*}

local notation "ℓ²ι" => lp (fun _ : ι => ℂ) 2

/-! ## The delayed smoothed radial multiplier and its history -/

/-- **(CDW.3)** `Φ_{δ,b,T}(z) = e^{-bz}(e^{δz} - 1)(1 - e^{-Tz})/(Tz)`. -/
def delayDriftMultiplier (δ b T : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(b * z)) * (Complex.exp (δ * z) - 1) * ((1 - Complex.exp (-(T * z))) / (T * z))

/-- **(CDW.3)** `Φ_{δ,b,T} = m_{b-δ,T} - m_{b,T}`, a difference of window multipliers. -/
theorem delayDriftMultiplier_eq (δ b T : ℝ) (z : ℂ) :
    delayDriftMultiplier δ b T z = offsetWindowMultiplier (b - δ) T z - offsetWindowMultiplier b T z := by
  rw [delayDriftMultiplier, offsetWindowMultiplier, offsetWindowMultiplier, ← sub_div]
  have h : Complex.exp (-(((b - δ : ℝ) : ℂ) * z)) = Complex.exp (-(b * z)) * Complex.exp (δ * z) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  rw [h]
  ring

theorem delayDriftMultiplier_zero (b T : ℝ) (z : ℂ) : delayDriftMultiplier 0 b T z = 0 := by
  simp [delayDriftMultiplier]

theorem delayDriftMultiplier_ofReal (δ b T x : ℝ) :
    delayDriftMultiplier δ b T x =
      (((Real.exp (-((b - δ) * x)) - Real.exp (-(b * x))) * ((1 - Real.exp (-(T * x))) / (T * x)) : ℝ) : ℂ) := by
  rw [delayDriftMultiplier_eq, offsetWindowMultiplier, offsetWindowMultiplier, ← sub_div, ← sub_mul]
  push_cast
  ring

/-- **(CDW.7)** The signed history `h_{δ,b,T} = T^{-1}(1_{(b-δ,b-δ+T]} - 1_{(b,b+T]})`. -/
def delayDriftControl (δ b T : ℝ) : HalfLineL2 := offsetWindowControl (b - δ) T - offsetWindowControl b T

theorem laplaceRay_sub {f g : HalfLineL2} {w : ℂ} (hw : 0 < w.re) :
    laplaceRay ((f - g : HalfLineL2) : ℝ → ℂ) w = laplaceRay f w - laplaceRay g w := by
  rw [laplaceRay, laplaceRay, laplaceRay, ← integral_sub (integrableOn_laplaceRay (Lp.memLp f) hw)
    (integrableOn_laplaceRay (Lp.memLp g) hw)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f g] with x hx
  rw [hx, Pi.sub_apply, sub_mul]

/-- **(CDW.9)** In the causal chamber `ℒ h_{δ,b,T} = Φ_{δ,b,T}` on the right half-plane. -/
theorem laplaceRay_delayDriftControl {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T) {w : ℂ}
    (hw : 0 < w.re) : laplaceRay (delayDriftControl δ b T) w = delayDriftMultiplier δ b T w := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [delayDriftControl, laplaceRay_sub hw, laplaceRay_offsetWindowControl hbδ hT hw0,
    laplaceRay_offsetWindowControl hb hT hw0, delayDriftMultiplier_eq]

/-- **(CDW.5) ⇒ (CDW.2)** In the causal chamber `Φ_{δ,b,T} ∈ H²`. -/
theorem isHalfPlaneHardy_delayDriftMultiplier {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T) :
    ∃ M, IsHalfPlaneHardy (delayDriftMultiplier δ b T) M :=
  ⟨_, (paleyWiener_halfPlane.1 (delayDriftControl δ b T)).1.congr_right fun _ hw =>
    laplaceRay_delayDriftControl hb hbδ hT hw⟩

/-- An `H²` function tends to zero along the positive real axis. -/
theorem tendsto_isHalfPlaneHardy_atTop {H : ℂ → ℂ} {M : ℝ} (hH : IsHalfPlaneHardy H M) :
    Tendsto (fun x : ℝ => H x) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ((eventually_gt_atTop 0).mono fun x hx =>
    norm_le_of_isHalfPlaneHardy hH (by simpa using hx)) ?_
  have h2 : Tendsto (fun x : ℝ => Real.sqrt (2 * x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop two_pos)
  simpa using (tendsto_const_nhds (x := rayL2Norm (hardyDatum H hH))).div_atTop h2

theorem tendsto_exp_sub_exp_div_atTop {a₁ a₂ : ℝ} (h12 : a₁ < a₂) (ha : a₁ < 0) :
    Tendsto (fun x : ℝ => (Real.exp (-(a₁ * x)) - Real.exp (-(a₂ * x))) / x) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => Real.exp (-a₁ * x) / x ^ (1 : ℝ)) atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop 1 (-a₁) (by linarith)
  have h2 : Tendsto (fun x : ℝ => 1 - Real.exp (-((a₂ - a₁) * x))) atTop (𝓝 (1 - 0)) := by
    refine tendsto_const_nhds.sub ?_
    have hlin : Tendsto (fun x : ℝ => (a₂ - a₁) * x) atTop atTop :=
      tendsto_id.const_mul_atTop (by linarith : 0 < a₂ - a₁)
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
  refine (h1.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 - 0) h2).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_one, div_mul_eq_mul_div, mul_sub, mul_one, ← Real.exp_add]
  congr 2 <;> ring_nf

/-- **(CDW.11)** Off the causal chamber `|Φ_{δ,b,T}(x)| → ∞` along the positive real axis: the term
with negative start grows exponentially and the two rates are distinct. -/
theorem tendsto_norm_delayDriftMultiplier_atTop {δ b T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T)
    (hout : b < 0 ∨ b - δ < 0) :
    Tendsto (fun x : ℝ => ‖delayDriftMultiplier δ b T x‖) atTop atTop := by
  have hfac : Tendsto (fun x : ℝ => (1 - Real.exp (-(T * x))) / T) atTop (𝓝 ((1 - 0) / T)) := by
    refine (tendsto_const_nhds.sub ?_).div_const T
    have hlin : Tendsto (fun x : ℝ => T * x) atTop atTop := tendsto_id.const_mul_atTop hT
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
  have hpos : (0 : ℝ) < (1 - 0) / T := by simpa using hT
  have hgrow : Tendsto (fun x : ℝ => |Real.exp (-((b - δ) * x)) - Real.exp (-(b * x))| / x) atTop atTop := by
    rcases lt_or_gt_of_ne hδ with hneg | hposδ
    · have h := tendsto_exp_sub_exp_div_atTop (a₁ := b) (a₂ := b - δ) (by linarith)
        (by rcases hout with h | h <;> linarith)
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [abs_sub_comm, abs_of_nonneg]
      exact sub_nonneg.2 (Real.exp_le_exp.2 (by nlinarith))
    · have h := tendsto_exp_sub_exp_div_atTop (a₁ := b - δ) (a₂ := b) (by linarith)
        (by rcases hout with h | h <;> linarith)
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [abs_of_nonneg]
      exact sub_nonneg.2 (Real.exp_le_exp.2 (by nlinarith))
  refine (hgrow.atTop_mul_pos hpos hfac).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [delayDriftMultiplier_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (div_nonneg (sub_nonneg.2 (Real.exp_le_one_iff.2 (by nlinarith))) (by positivity))]
  field_simp

/-- **(CDW.11)–(CDW.12)** Off the causal chamber `Φ_{δ,b,T} ∉ H²`. -/
theorem not_isHalfPlaneHardy_delayDriftMultiplier {δ b T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T)
    (hout : b < 0 ∨ b - δ < 0) (M : ℝ) : ¬ IsHalfPlaneHardy (delayDriftMultiplier δ b T) M := fun hH =>
  not_tendsto_nhds_of_tendsto_atTop (tendsto_norm_delayDriftMultiplier_atTop hδ hT hout) 0
    (by simpa using (tendsto_isHalfPlaneHardy_atTop hH).norm)

/-- **(CDW.5)–(CDW.6)** The causal chamber `b ≥ 0, b - δ ≥ 0` is `b ≥ max(0, δ)`. -/
theorem causal_chamber_iff (δ b : ℝ) : (0 ≤ b ∧ 0 ≤ b - δ) ↔ max 0 δ ≤ b := by
  rw [max_le_iff, sub_nonneg]

/-- **(CDW.2) ⟺ (CDW.5)** `Φ_{δ,b,T} ∈ H²` iff both window starts are causal (`δ ≠ 0`). -/
theorem isHalfPlaneHardy_delayDriftMultiplier_iff {δ b T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T) :
    (∃ M, IsHalfPlaneHardy (delayDriftMultiplier δ b T) M) ↔ 0 ≤ b ∧ 0 ≤ b - δ := by
  refine ⟨fun ⟨M, hH⟩ => ?_, fun h => isHalfPlaneHardy_delayDriftMultiplier h.1 h.2 hT⟩
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  exact not_isHalfPlaneHardy_delayDriftMultiplier hδ hT hc M hH

/-! ## The norm of the history -/

theorem measureReal_Ioc_inter_Ioc {a₁ a₂ T : ℝ} (h₁ : 0 ≤ a₁) :
    (volume.restrict (Ioi (0 : ℝ))).real (Ioc a₁ (a₁ + T) ∩ Ioc a₂ (a₂ + T)) = max (T - |a₁ - a₂|) 0 := by
  have hsub : Ioc (max a₁ a₂) (min (a₁ + T) (a₂ + T)) ⊆ Ioi 0 :=
    fun t ht => lt_of_le_of_lt (le_max_of_le_left h₁) ht.1
  rw [Set.Ioc_inter_Ioc, measureReal_def, Measure.restrict_apply measurableSet_Ioc, inter_eq_left.2 hsub,
    Real.volume_Ioc, ENNReal.toReal_ofReal']
  congr 1
  rcases le_total a₁ a₂ with h | h
  · rw [max_eq_right h, min_eq_left (by linarith), abs_of_nonpos (by linarith)]
    ring
  · rw [max_eq_left h, min_eq_right (by linarith), abs_of_nonneg (by linarith)]
    ring

theorem inner_offsetWindowControl {a₁ a₂ T : ℝ} (h₁ : 0 ≤ a₁) :
    ⟪offsetWindowControl a₁ T, offsetWindowControl a₂ T⟫_ℂ =
      ((max (T - |a₁ - a₂|) 0 * (T⁻¹) ^ 2 : ℝ) : ℂ) := by
  rw [offsetWindowControl, offsetWindowControl, MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp
    measurableSet_Ioc measurableSet_Ioc (halfLine_Ioc_offset_ne_top _ _) (halfLine_Ioc_offset_ne_top _ _),
    measureReal_Ioc_inter_Ioc h₁, RCLike.inner_apply, Complex.conj_ofReal, Complex.real_smul]
  push_cast
  ring

/-- **(CDW.10)** `‖h_{δ,b,T}‖² = (2T - 2(T - |δ|)_+)/T² = 2 min(|δ|,T)/T²`. -/
theorem norm_delayDriftControl_sq {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T) :
    ‖delayDriftControl δ b T‖ ^ 2 = 2 * min |δ| T / T ^ 2 := by
  rw [delayDriftControl, @norm_sub_sq ℂ, norm_offsetWindowControl_sq hbδ hT, norm_offsetWindowControl_sq hb hT,
    inner_offsetWindowControl hbδ, RCLike.re_to_complex, Complex.ofReal_re, show b - δ - b = -δ by ring,
    abs_neg]
  have hT' : T ≠ 0 := hT.ne'
  rcases le_total |δ| T with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    field_simp
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]
    field_simp
    ring

/-! ## Theorem 3.1 — causal delay classification -/

namespace HeatSource

variable (s : HeatSource ι) [DecidableEq ι]

/-- In the causal chamber the history realizes the packet: `W h_{δ,b,T} = Φ_{δ,b,T}(L)v`. -/
theorem heatReachability_delayDriftControl {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T)
    (hm : Summable fun j => ‖s.v j * delayDriftMultiplier δ b T (s.lam j)‖ ^ 2) (hF : s.FullSupport) :
    s.heatReachability (delayDriftControl δ b T) = s.spectralPacket (delayDriftMultiplier δ b T) hm :=
  (s.heatReachability_eq_spectralPacket_iff hF _ hm _).2 fun j =>
    laplaceRay_delayDriftControl hb hbδ hT (by simpa using s.lam_pos j)

/-- In the causal chamber the packet satisfies **(HTF.3)**: it is the image of the history. -/
theorem summable_delayDrift {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T) :
    Summable fun j => ‖s.v j * delayDriftMultiplier δ b T (s.lam j)‖ ^ 2 := by
  have h := (lp.memℓp (s.heatReachability (delayDriftControl δ b T))).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  refine (by simpa using h : Summable fun j => ‖s.heatReachability (delayDriftControl δ b T) j‖ ^ 2).congr
    fun j => ?_
  rw [heatReachability_apply_eq_laplace, laplaceRay_delayDriftControl hb hbδ hT (by simpa using s.lam_pos j)]

omit [DecidableEq ι] in
theorem spectralPacket_delayDrift_zero {b T : ℝ}
    (hm : Summable fun j => ‖s.v j * delayDriftMultiplier 0 b T (s.lam j)‖ ^ 2) :
    s.spectralPacket (delayDriftMultiplier 0 b T) hm = 0 := by
  refine lp.ext (funext fun j => ?_)
  rw [spectralPacket_apply, delayDriftMultiplier_zero, mul_zero]
  rfl

omit [DecidableEq ι] in
theorem summable_expDiffPacket {a₁ a₂ : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) :
    Summable fun j => ‖s.v j * (Complex.exp (-(a₁ * s.lam j)) - Complex.exp (-(a₂ * s.lam j)))‖ ^ 2 := by
  refine (s.summable_norm_sq.mul_left 4).of_nonneg_of_le (fun _ => by positivity) fun j => ?_
  have hle : ∀ a : ℝ, 0 ≤ a → ‖Complex.exp (-(a * s.lam j))‖ ≤ 1 := fun a ha => by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [s.lam_pos j]
  have hd : ‖Complex.exp (-(a₁ * s.lam j)) - Complex.exp (-(a₂ * s.lam j))‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [hle a₁ h₁, hle a₂ h₂])
  rw [norm_mul, mul_pow]
  calc ‖s.v j‖ ^ 2 * ‖Complex.exp (-(a₁ * s.lam j)) - Complex.exp (-(a₂ * s.lam j))‖ ^ 2
      ≤ ‖s.v j‖ ^ 2 * 2 ^ 2 := by gcongr
    _ = 4 * ‖s.v j‖ ^ 2 := by ring

omit [DecidableEq ι] in
/-- The exact-time radial packet `e^{-a₁L}v - e^{-a₂L}v` has multiplier `e^{-a₁z} - e^{-a₂z}`. -/
theorem heatOrbit_sub_eq_spectralPacket {a₁ a₂ : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) :
    s.heatOrbit a₁ - s.heatOrbit a₂ =
      s.spectralPacket (fun z => Complex.exp (-(a₁ * z)) - Complex.exp (-(a₂ * z)))
        (s.summable_expDiffPacket h₁ h₂) := by
  refine lp.ext (funext fun j => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, s.heatOrbit_eq_spectralPacket h₁, s.heatOrbit_eq_spectralPacket h₂,
    spectralPacket_apply, spectralPacket_apply, spectralPacket_apply, mul_sub]

end HeatSource

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι) [DecidableEq ι]

/-- **Theorem 3.1, `δ = 0`.**  The packet vanishes and costs nothing, for every delay. -/
theorem orbitCostForm_delayDrift_zero {b T : ℝ}
    (hm : Summable fun j => ‖c.v j * delayDriftMultiplier 0 b T (c.lam j)‖ ^ 2) :
    c.orbitCostForm (c.spectralPacket (delayDriftMultiplier 0 b T) hm) = 0 := by
  rw [HeatSource.spectralPacket_delayDrift_zero, orbitCostForm_zero]

/-- **Theorem 3.1 — causal delay classification.**  For `δ ≠ 0` on an infinite proper spectrum:
finite capital `⟺ Φ_{δ,b,T} ∈ H² ⟺ b ≥ 0 ∧ b - δ ≥ 0 ⟺ b ≥ max(0, δ)`. -/
theorem orbitCostForm_delayDrift_lt_top_iff [Infinite ι] {δ b T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T)
    (hm : Summable fun j => ‖c.v j * delayDriftMultiplier δ b T (c.lam j)‖ ^ 2) :
    (c.orbitCostForm (c.spectralPacket (delayDriftMultiplier δ b T) hm) < ⊤ ↔
        ∃ M, IsHalfPlaneHardy (delayDriftMultiplier δ b T) M) ∧
      ((∃ M, IsHalfPlaneHardy (delayDriftMultiplier δ b T) M) ↔ 0 ≤ b ∧ 0 ≤ b - δ) ∧
      (0 ≤ b ∧ 0 ≤ b - δ ↔ max 0 δ ≤ b) := by
  refine ⟨⟨fun hlt => ?_, fun ⟨M, hH⟩ => ?_⟩, isHalfPlaneHardy_delayDriftMultiplier_iff hδ hT,
    causal_chamber_iff δ b⟩
  · refine (isHalfPlaneHardy_delayDriftMultiplier_iff hδ hT).2 ?_
    by_contra hc
    rw [not_and_or, not_le, not_le] at hc
    have hmem : c.spectralPacket (delayDriftMultiplier δ b T) hm ∈ Set.range c.heatReachability := by
      rw [(c.range_heatReachability).2]
      exact hlt
    obtain ⟨H, M, hH, hint⟩ := (c.spectralPacket_mem_range_iff c.fullSupport _ hm).1 hmem
    have h0 : Tendsto (fun j => ‖delayDriftMultiplier δ b T (c.lam j)‖) cofinite (𝓝 0) := by
      have := (c.tendsto_hardy_lam hH).norm
      simp only [hint, norm_zero] at this
      exact this
    exact not_tendsto_nhds_of_tendsto_atTop
      ((tendsto_norm_delayDriftMultiplier_atTop hδ hT hc).comp c.proper) 0 h0
  · have hmem : c.spectralPacket (delayDriftMultiplier δ b T) hm ∈ Set.range c.heatReachability :=
      (c.spectralPacket_mem_range_iff c.fullSupport _ hm).2 ⟨_, M, hH, fun _ => rfl⟩
    rw [(c.range_heatReachability).2] at hmem
    exact hmem

/-- **(CDW.7)–(CDW.8)** If the reachability map is injective, the history `h_{δ,b,T}` is the unique
control of an admitted packet and the least capital is `2 min(|δ|,T)/T²`, whatever the delay. -/
theorem orbitCostForm_delayDrift_eq (hW : Function.Injective c.heatReachability) {δ b T : ℝ}
    (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T)
    (hm : Summable fun j => ‖c.v j * delayDriftMultiplier δ b T (c.lam j)‖ ^ 2) :
    (∀ u, c.heatReachability u = c.spectralPacket (delayDriftMultiplier δ b T) hm → u = delayDriftControl δ b T) ∧
    c.orbitCostForm (c.spectralPacket (delayDriftMultiplier δ b T) hm) = ENNReal.ofReal (2 * min |δ| T / T ^ 2) := by
  have hWh := c.heatReachability_delayDriftControl hb hbδ hT hm c.fullSupport
  refine ⟨fun u hu => hW (hu.trans hWh.symm), ?_⟩
  rw [orbitCostForm_eq_iInf, ← norm_delayDriftControl_sq hb hbδ hT]
  refine le_antisymm (iInf₂_le (delayDriftControl δ b T) hWh) (le_iInf₂ fun u hu => ?_)
  rw [hW (hu.trans hWh.symm)]

end CyclicHeatSource

/-! ## The Euler shell -/

variable {m : ℕ} (hm : 1 ≤ m) {σ : ℝ} (hσ : 1 < σ)

local notation "ℓ²A" m => lp (fun _ : EulerShell m => ℂ) 2

/-- The delayed smoothed radial packet `x_{δ,b,T} = Φ_{δ,b,T}(L)v` **(CDW.4)** on the Euler shell, in the
causal chamber. -/
def delayDriftPacket {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T) : ℓ²A m :=
  (eulerShellSource hm hσ).spectralPacket (delayDriftMultiplier δ b T)
    ((eulerShellSource hm hσ).summable_delayDrift hb hbδ hT)

/-- **Theorem 3.1 on the Euler shell.**  For `δ ≠ 0` and any admissible packet:
finite capital `⟺ b ≥ max(0, δ)`. -/
theorem eulerShell_orbitCostForm_delayDrift_lt_top_iff {δ b T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T)
    (hm' : Summable fun j => ‖(eulerShellSource hm hσ).v j *
      delayDriftMultiplier δ b T ((eulerShellSource hm hσ).lam j)‖ ^ 2) :
    (eulerShellSource hm hσ).orbitCostForm
        ((eulerShellSource hm hσ).spectralPacket (delayDriftMultiplier δ b T) hm') < ⊤ ↔ max 0 δ ≤ b := by
  haveI := infinite_eulerShell hm
  obtain ⟨h1, h2, h3⟩ := (eulerShellSource hm hσ).orbitCostForm_delayDrift_lt_top_iff hδ hT hm'
  rw [h1, h2, h3]

/-- **(CDW.8) Exact least work on the Euler shell.**  `q_G(x_{δ,b,T}) = 2 min(|δ|,T)/T²`: delay decides
admission, not work. -/
theorem orbitCostForm_delayDriftPacket {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T) :
    (eulerShellSource hm hσ).orbitCostForm (delayDriftPacket hm hσ hb hbδ hT) =
      ENNReal.ofReal (2 * min |δ| T / T ^ 2) :=
  ((eulerShellSource hm hσ).orbitCostForm_delayDrift_eq (heatReachability_injective hm hσ) hb hbδ hT _).2

/-- **(CDW.7)** The history `h_{δ,b,T}` is the unique control of `x_{δ,b,T}`. -/
theorem delayDriftPacket_unique_history {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T)
    (u : HalfLineL2) (hu : (eulerShellSource hm hσ).heatReachability u = delayDriftPacket hm hσ hb hbδ hT) :
    u = delayDriftControl δ b T :=
  ((eulerShellSource hm hσ).orbitCostForm_delayDrift_eq (heatReachability_injective hm hσ) hb hbδ hT _).1 u hu

/-! ## Functional-equation common delay -/

/-- **(CDW.13)–(CDW.14)** One delay admits both orientations `±δ` iff `b ≥ |δ|`. -/
theorem common_delay_iff (δ b : ℝ) : (max 0 δ ≤ b ∧ max 0 (-δ) ≤ b) ↔ |δ| ≤ b := by
  rw [max_le_iff, max_le_iff, abs_le']
  constructor
  · rintro ⟨⟨_, h1⟩, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith [abs_nonneg δ, neg_abs_le δ, le_abs_self δ], h1⟩,
      ⟨by linarith [abs_nonneg δ, neg_abs_le δ, le_abs_self δ], h2⟩⟩

/-- **(CDW.13)–(CDW.14)** On the Euler shell, `x_{δ,b,T}` and its reflection `x_{-δ,b,T}` are both of
finite capital iff `b ≥ |δ|`. -/
theorem eulerShell_common_delay_iff {δ b T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T)
    (hP : Summable fun j => ‖(eulerShellSource hm hσ).v j *
      delayDriftMultiplier δ b T ((eulerShellSource hm hσ).lam j)‖ ^ 2)
    (hN : Summable fun j => ‖(eulerShellSource hm hσ).v j *
      delayDriftMultiplier (-δ) b T ((eulerShellSource hm hσ).lam j)‖ ^ 2) :
    ((eulerShellSource hm hσ).orbitCostForm
        ((eulerShellSource hm hσ).spectralPacket (delayDriftMultiplier δ b T) hP) < ⊤ ∧
      (eulerShellSource hm hσ).orbitCostForm
        ((eulerShellSource hm hσ).spectralPacket (delayDriftMultiplier (-δ) b T) hN) < ⊤) ↔ |δ| ≤ b := by
  rw [eulerShell_orbitCostForm_delayDrift_lt_top_iff hm hσ hδ hT,
    eulerShell_orbitCostForm_delayDrift_lt_top_iff hm hσ (neg_ne_zero.2 hδ) hT, common_delay_iff]

/-- **(CDW.15)** The paired work `𝔠_pair(δ,T) = 4 min(|δ|,T)/T²`. -/
def pairWork (δ T : ℝ) : ℝ := 4 * min |δ| T / T ^ 2

/-- **(CDW.15)** At a common admitted delay both orientations have the same work, and the least
capital of the doubled packet `(x_{δ,b,T}, x_{-δ,b,T})` under the doubled source `W ⊕ W` (control
energy `‖u₁‖² + ‖u₂‖²`) is `4 min(|δ|,T)/T²`. -/
theorem pairCapital_eq {δ b T : ℝ} (hb : |δ| ≤ b) (hT : 0 < T) :
    (eulerShellSource hm hσ).orbitCostForm
        (delayDriftPacket hm hσ (δ := δ) (abs_nonneg δ |>.trans hb) (by linarith [le_abs_self δ]) hT) =
      (eulerShellSource hm hσ).orbitCostForm
        (delayDriftPacket hm hσ (δ := -δ) (abs_nonneg δ |>.trans hb) (by linarith [neg_abs_le δ]) hT) ∧
    (⨅ (u₁ : HalfLineL2) (u₂ : HalfLineL2)
        (_ : (eulerShellSource hm hσ).heatReachability u₁ =
            delayDriftPacket hm hσ (δ := δ) (abs_nonneg δ |>.trans hb) (by linarith [le_abs_self δ]) hT ∧
          (eulerShellSource hm hσ).heatReachability u₂ =
            delayDriftPacket hm hσ (δ := -δ) (abs_nonneg δ |>.trans hb) (by linarith [neg_abs_le δ]) hT),
        ENNReal.ofReal (‖u₁‖ ^ 2 + ‖u₂‖ ^ 2)) = ENNReal.ofReal (pairWork δ T) := by
  have hb0 : 0 ≤ b := abs_nonneg δ |>.trans hb
  have hP : 0 ≤ b - δ := by linarith [le_abs_self δ]
  have hN : 0 ≤ b - -δ := by linarith [neg_abs_le δ]
  refine ⟨by rw [orbitCostForm_delayDriftPacket, orbitCostForm_delayDriftPacket, abs_neg], ?_⟩
  have hWP := (eulerShellSource hm hσ).heatReachability_delayDriftControl hb0 hP hT
    ((eulerShellSource hm hσ).summable_delayDrift hb0 hP hT) (eulerShellSource hm hσ).fullSupport
  have hWN := (eulerShellSource hm hσ).heatReachability_delayDriftControl hb0 hN hT
    ((eulerShellSource hm hσ).summable_delayDrift hb0 hN hT) (eulerShellSource hm hσ).fullSupport
  have hval : ‖delayDriftControl δ b T‖ ^ 2 + ‖delayDriftControl (-δ) b T‖ ^ 2 = pairWork δ T := by
    rw [norm_delayDriftControl_sq hb0 hP hT, norm_delayDriftControl_sq hb0 hN hT, abs_neg, pairWork]
    ring
  refine le_antisymm ((iInf_le_of_le (delayDriftControl δ b T) (iInf_le_of_le (delayDriftControl (-δ) b T)
    (iInf_le _ ⟨hWP, hWN⟩))).trans_eq (by rw [hval])) (le_iInf fun u₁ => le_iInf fun u₂ => le_iInf fun hu => ?_)
  rw [delayDriftPacket_unique_history hm hσ hb0 hP hT u₁ hu.1,
    delayDriftPacket_unique_history hm hσ hb0 hN hT u₂ hu.2, hval]

/-- **(CDW.15a)** Extra delay multiplies the multiplier by `e^{-cz}`. -/
theorem delayDriftMultiplier_add_delay (δ b T c : ℝ) (z : ℂ) :
    delayDriftMultiplier δ (b + c) T z = Complex.exp (-(c * z)) * delayDriftMultiplier δ b T z := by
  rw [delayDriftMultiplier, delayDriftMultiplier, show -(((b + c : ℝ) : ℂ) * z) = -(b * z) + -(c * z) by
    push_cast; ring, Complex.exp_add]
  ring

theorem offsetWindowControl_add_delay {a T : ℝ} (ha : 0 ≤ a) (c : ℝ≥0) :
    offsetWindowControl (a + c) T = burnolRightShift c (offsetWindowControl a T) := by
  refine Lp.ext ?_
  have h1 := indicatorConstLp_coeFn (p := 2) (μ := volume.restrict (Ioi (0 : ℝ)))
    (hs := measurableSet_Ioc (a := a + c) (b := a + c + T))
    (hμs := halfLine_Ioc_offset_ne_top (a + c) T) (c := ((T⁻¹ : ℝ) : ℂ))
  have h2 := rightShiftFun_congr c.coe_nonneg (indicatorConstLp_coeFn (p := 2)
    (μ := volume.restrict (Ioi (0 : ℝ))) (hs := measurableSet_Ioc (a := a) (b := a + T))
    (hμs := halfLine_Ioc_offset_ne_top a T) (c := ((T⁻¹ : ℝ) : ℂ)))
  filter_upwards [h1, h2, burnolRightShift_coeFn c (offsetWindowControl a T)] with t ht1 ht2 ht3
  rw [offsetWindowControl, ht1, ht3, offsetWindowControl, ht2, rightShiftFun]
  by_cases hmem : t ∈ Ioc (a + c) (a + c + T)
  · have hc : t ∈ Ioi (c : ℝ) := lt_of_le_of_lt (by linarith) hmem.1
    have hs : t - c ∈ Ioc a (a + T) := ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hc, Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hmem]
    by_cases hc : t ∈ Ioi (c : ℝ)
    · have hs : t - c ∉ Ioc a (a + T) := fun hs => hmem ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [Set.indicator_of_mem hc, Set.indicator_of_notMem hs]
    · rw [Set.indicator_of_notMem hc]

/-- **(CDW.15a)** `h_{δ,b+c,T} = S_c h_{δ,b,T}` for the right-shift isometry `S_c`. -/
theorem delayDriftControl_add_delay {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (c : ℝ≥0) :
    delayDriftControl δ (b + c) T = burnolRightShift c (delayDriftControl δ b T) := by
  rw [delayDriftControl, delayDriftControl, map_sub, ← offsetWindowControl_add_delay hbδ,
    ← offsetWindowControl_add_delay hb, show b + (c : ℝ) - δ = b - δ + c by ring]

/-- **(CDW.15b)** Absolute delay after admission carries no work. -/
theorem norm_delayDriftControl_add_delay {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (c : ℝ≥0) :
    ‖delayDriftControl δ (b + c) T‖ ^ 2 = ‖delayDriftControl δ b T‖ ^ 2 := by
  rw [delayDriftControl_add_delay hb hbδ c, norm_burnolRightShift_apply]

/-! ## Source-anchor selection -/

/-- **(CDW.26)–(CDW.29) Source-anchor selection.**  If a source-derived delay `b_src` vanishes at
`δ` and the drift packet has finite capital, then `δ ≤ 0`; if the same zero-delay law holds for the
reflection `-δ`, then `δ = 0`. -/
theorem source_anchor_selection (bsrc : ℝ → ℝ) {δ T : ℝ} (hT : 0 < T) (h0 : bsrc δ = 0)
    (hP : Summable fun j => ‖(eulerShellSource hm hσ).v j *
      delayDriftMultiplier δ (bsrc δ) T ((eulerShellSource hm hσ).lam j)‖ ^ 2)
    (hfin : (eulerShellSource hm hσ).orbitCostForm
      ((eulerShellSource hm hσ).spectralPacket (delayDriftMultiplier δ (bsrc δ) T) hP) < ⊤) :
    δ ≤ 0 ∧
    ∀ (_ : bsrc (-δ) = 0) (hN : Summable fun j => ‖(eulerShellSource hm hσ).v j *
        delayDriftMultiplier (-δ) (bsrc (-δ)) T ((eulerShellSource hm hσ).lam j)‖ ^ 2),
      (eulerShellSource hm hσ).orbitCostForm
        ((eulerShellSource hm hσ).spectralPacket (delayDriftMultiplier (-δ) (bsrc (-δ)) T) hN) < ⊤ → δ = 0 := by
  have hle : ∀ {d : ℝ} (hd : bsrc d = 0) (h : Summable fun j => ‖(eulerShellSource hm hσ).v j *
      delayDriftMultiplier d (bsrc d) T ((eulerShellSource hm hσ).lam j)‖ ^ 2),
      (eulerShellSource hm hσ).orbitCostForm
        ((eulerShellSource hm hσ).spectralPacket (delayDriftMultiplier d (bsrc d) T) h) < ⊤ → d ≤ 0 := by
    intro d hd h hq
    by_cases hd0 : d = 0
    · exact hd0.le
    · have := (eulerShell_orbitCostForm_delayDrift_lt_top_iff hm hσ hd0 hT h).1 hq
      rw [hd] at this
      exact (le_max_right 0 d).trans this
  exact ⟨hle h0 hP hfin, fun h0' hN hfin' => le_antisymm (hle h0 hP hfin) (by linarith [hle h0' hN hfin'])⟩

/-! ## Countermodels -/

/-- **(CDW.30) Delay destroys selection.**  Every drift is formable in both orientations at the common
delay `b = |δ|`. -/
theorem delay_destroys_selection (δ : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ (b : ℝ) (hb : 0 ≤ b) (hP : 0 ≤ b - δ) (hN : 0 ≤ b - -δ),
      (eulerShellSource hm hσ).orbitCostForm (delayDriftPacket hm hσ hb hP hT) < ⊤ ∧
      (eulerShellSource hm hσ).orbitCostForm (delayDriftPacket hm hσ hb hN hT) < ⊤ :=
  ⟨|δ|, abs_nonneg δ, by linarith [le_abs_self δ], by linarith [neg_abs_le δ],
    by rw [orbitCostForm_delayDriftPacket]; exact ENNReal.ofReal_lt_top,
    by rw [orbitCostForm_delayDriftPacket]; exact ENNReal.ofReal_lt_top⟩

/-- **§7.4 The source clock is constitutive.**  For `δ ≠ 0` the admissible delays form exactly the
chamber `[max(0, δ), ∞)`. -/
theorem admissible_delays_eq {δ T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T) :
    {b : ℝ | ∃ h : Summable fun j => ‖(eulerShellSource hm hσ).v j *
        delayDriftMultiplier δ b T ((eulerShellSource hm hσ).lam j)‖ ^ 2,
      (eulerShellSource hm hσ).orbitCostForm
        ((eulerShellSource hm hσ).spectralPacket (delayDriftMultiplier δ b T) h) < ⊤} = Ici (max 0 δ) := by
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨h, hq⟩
    exact (eulerShell_orbitCostForm_delayDrift_lt_top_iff hm hσ hδ hT h).1 hq
  · intro hb
    have hc := (causal_chamber_iff δ b).2 hb
    exact ⟨(eulerShellSource hm hσ).summable_delayDrift hc.1 hc.2 hT,
      (eulerShell_orbitCostForm_delayDrift_lt_top_iff hm hσ hδ hT _).2 hb⟩

/-- **§7.2 Width is load-bearing.**  As `T ↓ 0` the least work `2 min(|δ|,T)/T²` of the admitted
packet blows up. -/
theorem tendsto_orbitCostForm_delayDriftPacket {δ b : ℝ} (hδ : δ ≠ 0) (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) :
    Tendsto (fun T : Ioi (0 : ℝ) =>
      (eulerShellSource hm hσ).orbitCostForm (delayDriftPacket hm hσ hb hbδ T.2))
      (comap Subtype.val (𝓝[>] 0)) (𝓝 ⊤) := by
  have hδ' : 0 < |δ| := abs_pos.2 hδ
  have h2 : Tendsto (fun T : ℝ => 2 * T⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop two_pos
  have hreal : Tendsto (fun T : ℝ => ENNReal.ofReal (2 * min |δ| T / T ^ 2)) (𝓝[>] 0) (𝓝 ⊤) := by
    refine (ENNReal.tendsto_ofReal_atTop.comp h2).congr' ?_
    filter_upwards [eventually_mem_nhdsWithin, Ioo_mem_nhdsGT hδ'] with T (hT : 0 < T) hTδ
    rw [Function.comp_apply, min_eq_right hTδ.2.le]
    congr 1
    field_simp
  refine (hreal.comp tendsto_comap).congr fun T => ?_
  rw [Function.comp_apply, orbitCostForm_delayDriftPacket]

/-- **§7.2** The exact-time radial packet `e^{-(b-δ)L}v - e^{-bL}v` has infinite capital for `δ ≠ 0`:
its multiplier is bounded but its modulus on each vertical line stays above `|e^{-(b-δ)x} - e^{-bx}|`. -/
theorem orbitCostForm_exactTime_radial_eq_top {δ b : ℝ} (hδ : δ ≠ 0) (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) :
    (eulerShellSource hm hσ).orbitCostForm
      ((eulerShellSource hm hσ).heatOrbit (b - δ) - (eulerShellSource hm hσ).heatOrbit b) = ⊤ := by
  rw [HeatSource.heatOrbit_sub_eq_spectralPacket _ hbδ hb]
  refine (eulerShellSource hm hσ).orbitCostForm_spectralPacket_eq_top_of_nevanlinna
    (not_summable_eulerShell_blaschke hm) ?_ ?_ _
  · obtain ⟨G₁, -, hG₁, -, ⟨C₁, hC₁⟩, -, -, hm₁⟩ := isHalfPlaneNevanlinna_exp hbδ
    obtain ⟨G₂, -, hG₂, -, ⟨C₂, hC₂⟩, -, -, hm₂⟩ := isHalfPlaneNevanlinna_exp hb
    refine ⟨fun z => Complex.exp (-((b - δ : ℝ) * z)) - Complex.exp (-(b * z)), fun _ => 1, ?_,
      differentiableOn_const 1, ⟨2, fun w hw => ?_⟩, ⟨1, fun _ _ => by simp⟩, fun _ _ => one_ne_zero,
      fun _ _ => (div_one _).symm⟩
    · exact ((Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id).neg).sub
        (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id).neg)).differentiableOn
    · have hle : ∀ a : ℝ, 0 ≤ a → ‖Complex.exp (-(a * w))‖ ≤ 1 := fun a ha => by
        rw [Complex.norm_exp, Real.exp_le_one_iff]
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        have : (0 : ℝ) ≤ a * w.re := mul_nonneg ha (le_of_lt hw)
        linarith
      calc ‖Complex.exp (-((b - δ : ℝ) * w)) - Complex.exp (-(b * w))‖
          ≤ ‖Complex.exp (-((b - δ : ℝ) * w))‖ + ‖Complex.exp (-(b * w))‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hle _ hbδ) (hle _ hb)
        _ = 2 := by norm_num
  · rintro ⟨M, hH⟩
    have hmem := (hH.memLp 1 one_pos).norm
    have hpos : 0 < |Real.exp (-(b - δ)) - Real.exp (-b)| := by
      refine abs_pos.2 (sub_ne_zero.2 fun h => ?_)
      have := Real.exp_injective h
      exact hδ (by linarith)
    have hlow : ∀ ξ : ℝ, |Real.exp (-(b - δ)) - Real.exp (-b)| ≤
        ‖Complex.exp (-(((b - δ : ℝ) : ℂ) * rayLine 1 ξ)) - Complex.exp (-((b : ℂ) * rayLine 1 ξ))‖ := by
      intro ξ
      have h1 : ‖Complex.exp (-(((b - δ : ℝ) : ℂ) * rayLine 1 ξ))‖ = Real.exp (-(b - δ)) := by
        rw [Complex.norm_exp]; simp [rayLine]
      have h2 : ‖Complex.exp (-((b : ℂ) * rayLine 1 ξ))‖ = Real.exp (-b) := by
        rw [Complex.norm_exp]; simp [rayLine]
      rw [← h1, ← h2]
      exact abs_norm_sub_norm_le _ _
    have hint : Integrable (fun _ : ℝ => |Real.exp (-(b - δ)) - Real.exp (-b)| ^ 2) volume := by
      have h2 := (memLp_two_iff_integrable_sq_norm hmem.1).1 hmem
      refine h2.mono' (by fun_prop) (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_norm]
      exact pow_le_pow_left₀ (abs_nonneg _) (hlow ξ) 2
    rw [integrable_const_iff] at hint
    rcases hint with h | h
    · exact (pow_pos hpos 2).ne' h
    · have h' : volume (univ : Set ℝ) < ⊤ := measure_lt_top _ _
      simp at h'

/-- **§7.3 The history is signed.**  For `δ ≠ 0` the unique control of an admitted drift packet takes
the value `-1/T` on a set of positive measure: no nonnegative control realizes it. -/
theorem not_ae_nonneg_delayDriftControl {δ b T : ℝ} (hδ : δ ≠ 0) (hb : 0 ≤ b) (hT : 0 < T) :
    ¬ ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ ((delayDriftControl δ b T : ℝ → ℂ) t).re := by
  intro hnn
  obtain ⟨l, r, hlr, hsub, hdisj⟩ : ∃ l r : ℝ, l < r ∧ Ioc l r ⊆ Ioc b (b + T) ∧
      Disjoint (Ioc l r) (Ioc (b - δ) (b - δ + T)) := by
    rcases lt_or_gt_of_ne hδ with hneg | hpos
    · refine ⟨b, min (b + T) (b - δ), lt_min (by linarith) (by linarith), fun t ht => ⟨ht.1,
        ht.2.trans (min_le_left _ _)⟩, Set.disjoint_left.2 fun t ht ht' => ?_⟩
      linarith [ht.2.trans (min_le_right _ _), ht'.1]
    · refine ⟨max b (b - δ + T), b + T, max_lt (by linarith) (by linarith), fun t ht =>
        ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, ht.2⟩, Set.disjoint_left.2 fun t ht ht' => ?_⟩
      linarith [lt_of_le_of_lt (le_max_right _ _) ht.1, ht'.2]
  have hIoi : Ioc l r ⊆ Ioi 0 := fun t ht => lt_of_le_of_lt hb (hsub ht).1
  have hval : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), t ∈ Ioc l r →
      (delayDriftControl δ b T : ℝ → ℂ) t = -((T⁻¹ : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_sub (offsetWindowControl (b - δ) T) (offsetWindowControl b T),
      indicatorConstLp_coeFn (p := 2) (μ := volume.restrict (Ioi (0 : ℝ)))
        (hs := measurableSet_Ioc (a := b - δ) (b := b - δ + T))
        (hμs := halfLine_Ioc_offset_ne_top (b - δ) T) (c := ((T⁻¹ : ℝ) : ℂ)),
      indicatorConstLp_coeFn (p := 2) (μ := volume.restrict (Ioi (0 : ℝ)))
        (hs := measurableSet_Ioc (a := b) (b := b + T))
        (hμs := halfLine_Ioc_offset_ne_top b T) (c := ((T⁻¹ : ℝ) : ℂ))] with t h0 h1 h2 ht
    rw [delayDriftControl, h0, Pi.sub_apply, offsetWindowControl, h1, offsetWindowControl, h2,
      Set.indicator_of_notMem (Set.disjoint_left.1 hdisj ht), Set.indicator_of_mem (hsub ht), zero_sub]
  have hnull : (volume.restrict (Ioi (0 : ℝ))) (Ioc l r) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hnn, hval] with t h1 h2 ht
    rw [h2 ht] at h1
    simp only [Complex.neg_re, Complex.ofReal_re, Left.nonneg_neg_iff] at h1
    exact absurd h1 (not_le.2 (inv_pos.2 hT))
  rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.2 hIoi, Real.volume_Ioc,
    ENNReal.ofReal_eq_zero] at hnull
  linarith

/-- **§7.3** The positive defect of an admitted drift packet has energy `2 min(|δ|,T)/T²`. -/
theorem orbitDefectCost_delayDriftPacket {δ b T : ℝ} (hb : 0 ≤ b) (hbδ : 0 ≤ b - δ) (hT : 0 < T) :
    (eulerShellSource hm hσ).orbitDefectCost (InnerProductSpace.rankOne ℂ (delayDriftPacket hm hσ hb hbδ hT)
      (delayDriftPacket hm hσ hb hbδ hT)) = ENNReal.ofReal (2 * min |δ| T / T ^ 2) := by
  rw [CyclicHeatSource.orbitDefectCost_rankOne, orbitCostForm_delayDriftPacket]

/-- **§7.5 Source origin does not force zero slack.**  In the admitted chamber the history vanishes
before the latency `b - max(δ, 0)`, which may be positive. -/
theorem delayDriftControl_eq_zero_of_lt {δ b T : ℝ} :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), t ≤ b - max δ 0 → (delayDriftControl δ b T : ℝ → ℂ) t = 0 := by
  filter_upwards [Lp.coeFn_sub (offsetWindowControl (b - δ) T) (offsetWindowControl b T),
    indicatorConstLp_coeFn (p := 2) (μ := volume.restrict (Ioi (0 : ℝ)))
      (hs := measurableSet_Ioc (a := b - δ) (b := b - δ + T))
      (hμs := halfLine_Ioc_offset_ne_top (b - δ) T) (c := ((T⁻¹ : ℝ) : ℂ)),
    indicatorConstLp_coeFn (p := 2) (μ := volume.restrict (Ioi (0 : ℝ)))
      (hs := measurableSet_Ioc (a := b) (b := b + T))
      (hμs := halfLine_Ioc_offset_ne_top b T) (c := ((T⁻¹ : ℝ) : ℂ))] with t h0 h1 h2 ht
  have hn1 : t ∉ Ioc (b - δ) (b - δ + T) := fun h => by linarith [h.1, le_max_left δ 0]
  have hn2 : t ∉ Ioc b (b + T) := fun h => by linarith [h.1, le_max_right δ 0]
  rw [delayDriftControl, h0, Pi.sub_apply, offsetWindowControl, h1, offsetWindowControl, h2,
    Set.indicator_of_notMem hn1, Set.indicator_of_notMem hn2, sub_zero]

end GaloisForLFunctions.HTGeometry
