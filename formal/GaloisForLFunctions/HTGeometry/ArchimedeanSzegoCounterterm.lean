import GaloisForLFunctions.HTGeometry.CayleyThetaRecordFlatness
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.HTGeometry.SzegoWeightOuterMultiplier
import GaloisForLFunctions.HTGeometry.HardyRealBoundaryConstant
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.PoincareDiameter

/-!
# The unique archimedean Szegő counterterm

The literal theta source `k` has the two-sided first-atom envelope
`k(x) ≍ e^{9|x|/2 - π e^{2|x|}}`.  For the balanced theta law `ν_b = Z_b⁻¹ cosh(bx) k(x) dx`, its
contrast law `σ_b = tanh(b·)_* ν_b`, the source Hodge contrast density
`h(v) = (105/16) v²(1-v²)²` and `x_b(v) = artanh(v)/b`:

* **(A)** `σ_b` has density `s_b(v) = k(x_b(v)) / (b Z_b (1-v²)^{3/2})` on `(-1,1)`.
* **(B)** with `A_b(v) = e^{2|x_b(v)|} = Q(v)^{1/b}`, `Q(v) = (1+|v|)/(1-|v|)`, the subtracted
  density `r_{b,c} = (h/s_b) e^{-c A_b}` satisfies `log r_{b,c} = (π - c) A_b + G_b` with `G_b`
  integrable; `A_b(v)(1-|v|)^{1/b} = (1+|v|)^{1/b}`, so `A_b ∈ L¹` iff `b > 1`.
* **(C)** `log r_{b,c} ∈ L¹(-1,1)` iff `c = π` or `b > 1`; for `c < π`, `r_{b,c} ∉ L¹`, and for
  `c > π`, `b ≤ 1`, `r_{b,c} ∈ L¹` while its logarithmic integral is `-∞`.
* **(D)** `d P_b ≤ r_{b,π} ≤ D P_b`, `P_b = v²(1-v²)^{7/2} Q^{-9/(4b)}`; the compactified weight
  `W_b(θ) = r_{b,π}(θ/π)` is a bounded Szegő weight with `1/W_b ∉ L¹`, and its normalized outer
  function `D_b` has `|D_b|² = W_b` a.e., is zero-free, bounded and outer, unique, and
multiplication
  by `D_b` on `H²` is injective with dense non-closed range.
* **(E)** the odd amplitude `Ψ_b = sign(θ)√W_b`, with `Ψ_b² = W_b`, is the boundary of no function
  in scalar `H²`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower _root_.RHTower.HedenmalmThetaSource

/-! ## The exact theta contrast density -/

/-- **(UASA.5).**  The theta contrast density
`s_b(v) = k(artanh(v)/b) / (b Z_b (1-v²)√(1-v²))`. -/
def thetaContrastDensity (b v : ℝ) : ℝ :=
  thetaCuspFullSource (Real.artanh v / b) /
    (b * thetaBalanceMass b * ((1 - v ^ 2) * Real.sqrt (1 - v ^ 2)))

theorem image_tanh_mul_univ {b : ℝ} (hb : 0 < b) :
    (fun x => Real.tanh (b * x)) '' univ = Ioo (-1) 1 := by
  ext v
  constructor
  · rintro ⟨x, -, rfl⟩
    exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  · intro hv
    refine ⟨Real.artanh v / b, trivial, ?_⟩
    show Real.tanh (b * (Real.artanh v / b)) = v
    rw [mul_div_cancel₀ _ hb.ne', Real.tanh_artanh hv]

theorem hasDerivAt_tanh_mul (b x : ℝ) :
    HasDerivAt (fun x => Real.tanh (b * x)) (b / Real.cosh (b * x) ^ 2) x := by
  have h := (_root_.HTGeometry.hasDerivAt_tanh (b * x)).comp x ((hasDerivAt_id x).const_mul b)
  exact h.congr_deriv (by ring)

theorem thetaContrastDensity_tanh {b : ℝ} (hb : 0 < b) (x : ℝ) :
    |b / Real.cosh (b * x) ^ 2| * thetaContrastDensity b (Real.tanh (b * x))
      = thetaBalanceDensity b x := by
  have hc := Real.cosh_pos (b * x)
  have hZ := thetaBalanceMass_pos b
  have h1 : 1 - Real.tanh (b * x) ^ 2 = (Real.cosh (b * x))⁻¹ ^ 2 := by
    rw [_root_.HTGeometry.one_sub_tanh_sq, inv_pow, one_div]
  have h2 : Real.sqrt (1 - Real.tanh (b * x) ^ 2) = (Real.cosh (b * x))⁻¹ := by
    rw [h1, Real.sqrt_sq (inv_nonneg.mpr hc.le)]
  rw [thetaContrastDensity, h2, h1, Real.artanh_tanh, mul_div_cancel_left₀ _ hb.ne',
    abs_of_pos (by positivity), thetaBalanceDensity]
  field_simp

/-- **Lemma UASA-A.**  `∫ f dσ_b = ∫_{(-1,1)} f s_b`. -/
theorem integral_thetaContrastLaw {b : ℝ} (hb : 0 < b) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ v, f v ∂thetaContrastLaw b = ∫ v in Ioo (-1) 1, thetaContrastDensity b v * f v := by
  rw [thetaContrastLaw, integral_map (measurable_tanh_mul b).aemeasurable
    hf.aestronglyMeasurable, integral_thetaBalanceLaw, ← image_tanh_mul_univ hb,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hasDerivAt_tanh_mul b x).hasDerivWithinAt)
      (fun x _ y _ h => (mul_right_injective₀ hb.ne')
        (_root_.HTGeometry.tanh_strictMono.injective h)), Measure.restrict_univ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [← mul_assoc, thetaContrastDensity_tanh hb]

/-! ## The anomaly expansion -/

/-- **(UASA.7).**  The archimedean anomaly `A_b(v) = exp(2|x_b(v)|)`, `x_b = artanh/b`. -/
def archimedeanAnomaly (b v : ℝ) : ℝ := Real.exp (2 * |Real.artanh v / b|)

/-- **(UASA.6)–(UASA.7).**  `r_{b,c} = (h/s_b) exp(-c A_b)`, where `h(v) = (105/16) v²(1-v²)²` is
the source Hodge contrast density `hodgeSpectralDensity`. -/
def subtractedModularDensity (b c v : ℝ) : ℝ :=
  hodgeSpectralDensity v / thetaContrastDensity b v * Real.exp (-c * archimedeanAnomaly b v)

/-- The bounded envelope remainder `ε(x) = log k(x) - 9|x|/2 + π e^{2|x|}`. -/
def envelopeRemainder (x : ℝ) : ℝ :=
  Real.log (thetaCuspFullSource x) - 9 * |x| / 2 + Real.pi * Real.exp (2 * |x|)

theorem thetaCuspFullSource_abs (x : ℝ) : thetaCuspFullSource |x| = thetaCuspFullSource x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, thetaCuspFullSource_neg]

theorem envelopeRemainder_eq (x : ℝ) :
    envelopeRemainder x
      = Real.log (thetaCuspFullSource |x|) - Real.log (thetaEnvelope |x|) := by
  rw [envelopeRemainder, thetaCuspFullSource_abs, thetaEnvelope,
    Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  ring

theorem envelopeRemainder_le (x : ℝ) : envelopeRemainder x ≤ Real.log thetaEnvelopeUpper := by
  rw [envelopeRemainder_eq, sub_le_iff_le_add,
    ← Real.log_mul thetaEnvelopeUpper_pos.ne' (thetaEnvelope_pos _).ne']
  exact Real.log_le_log (thetaCuspFullSource_pos_all _)
    (thetaCuspFullSource_le_envelope (abs_nonneg x))

theorem le_envelopeRemainder {x : ℝ} (hx : x ≠ 0) :
    Real.log thetaEnvelopeLower ≤ envelopeRemainder x := by
  rw [envelopeRemainder_eq, le_sub_iff_add_le,
    ← Real.log_mul thetaEnvelopeLower_pos.ne' (thetaEnvelope_pos _).ne']
  exact Real.log_le_log (mul_pos thetaEnvelopeLower_pos (thetaEnvelope_pos _))
    (thetaCuspFullSource_ge_envelope (abs_pos.mpr hx))

/-- **(UASA.3).**  The envelope remainder `ε` is bounded. -/
theorem exists_abs_envelopeRemainder_le : ∃ C, ∀ x, |envelopeRemainder x| ≤ C := by
  refine ⟨max (max |Real.log thetaEnvelopeLower| |Real.log thetaEnvelopeUpper|)
    |envelopeRemainder 0|, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact le_max_right _ _
  · refine le_trans ?_ (le_max_left _ _)
    rw [abs_le]
    constructor
    · have := le_envelopeRemainder hx
      have := neg_abs_le (Real.log thetaEnvelopeLower)
      have := le_max_left |Real.log thetaEnvelopeLower| |Real.log thetaEnvelopeUpper|
      linarith
    · have := envelopeRemainder_le x
      have := le_abs_self (Real.log thetaEnvelopeUpper)
      have := le_max_right |Real.log thetaEnvelopeLower| |Real.log thetaEnvelopeUpper|
      linarith

/-- The regular part `G_b` of `log r_{b,c}`. -/
def anomalyRegularPart (b v : ℝ) : ℝ :=
  Real.log (105 / 16) + 2 * Real.log v + 7 / 2 * Real.log (1 - v ^ 2) + Real.log b
    + Real.log (thetaBalanceMass b) - 9 / 2 * |Real.artanh v / b|
    - envelopeRemainder (Real.artanh v / b)

/-- **Lemma UASA-B, (UASA.8).**  `log r_{b,c} = (π - c) A_b + G_b` on `(-1,1) \ {0}`. -/
theorem log_subtractedModularDensity {b c v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1)
    (hv0 : v ≠ 0) :
    Real.log (subtractedModularDensity b c v)
      = (Real.pi - c) * archimedeanAnomaly b v + anomalyRegularPart b v := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hs : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.mpr h1
  have hZ := thetaBalanceMass_pos b
  have hk := thetaCuspFullSource_pos_all (Real.artanh v / b)
  have hv2 : 0 < v ^ 2 := by positivity
  have hh : Real.log (hodgeSpectralDensity v)
      = Real.log (105 / 16) + 2 * Real.log v + 2 * Real.log (1 - v ^ 2) := by
    rw [hodgeSpectralDensity, Real.log_mul (by norm_num) (by positivity),
      Real.log_mul hv2.ne' (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hsd : Real.log (thetaContrastDensity b v)
      = Real.log (thetaCuspFullSource (Real.artanh v / b)) - Real.log b
        - Real.log (thetaBalanceMass b) - 3 / 2 * Real.log (1 - v ^ 2) := by
    rw [thetaContrastDensity, Real.log_div hk.ne' (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul hb.ne' hZ.ne',
      Real.log_mul h1.ne' hs.ne', Real.log_sqrt h1.le]
    ring
  have hlogk : Real.log (thetaCuspFullSource (Real.artanh v / b))
      = envelopeRemainder (Real.artanh v / b) + 9 * |Real.artanh v / b| / 2
        - Real.pi * archimedeanAnomaly b v := by
    rw [envelopeRemainder, archimedeanAnomaly]
    ring
  have hpos : 0 < thetaContrastDensity b v := by
    rw [thetaContrastDensity]
    positivity
  rw [subtractedModularDensity, Real.log_mul (div_pos (by rw [hodgeSpectralDensity]; positivity)
    hpos).ne' (Real.exp_pos _).ne', Real.log_div (by rw [hodgeSpectralDensity]; positivity)
    hpos.ne', Real.log_exp, hh, hsd, hlogk, anomalyRegularPart]
  ring

/-! ## Integrability of the anomaly -/

theorem image_tanh_univ : Real.tanh '' univ = Ioo (-1) 1 := by
  simpa using image_tanh_mul_univ one_pos

/-- The pulled-back anomaly `sech² y · e^{2|y|/b}`. -/
theorem integrableOn_archimedeanAnomaly_iff {b : ℝ} (hb : 0 < b) :
    IntegrableOn (archimedeanAnomaly b) (Ioo (-1) 1) ↔
      Integrable (fun y : ℝ => 1 / Real.cosh y ^ 2 * Real.exp (2 * |y| / b)) := by
  rw [← image_tanh_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (_root_.HTGeometry.hasDerivAt_tanh y).hasDerivWithinAt)
    (_root_.HTGeometry.tanh_strictMono.injective.injOn), integrableOn_univ]
  refine integrable_congr (Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, archimedeanAnomaly, Real.artanh_tanh, abs_div, abs_of_pos hb, abs_one,
    abs_of_pos (pow_pos (Real.cosh_pos y) 2)]
  ring_nf

/-- **(UASA.9).**  `A_b` is integrable on `(-1,1)` exactly when `b > 1`. -/
theorem integrableOn_archimedeanAnomaly_iff_one_lt {b : ℝ} (hb : 0 < b) :
    IntegrableOn (archimedeanAnomaly b) (Ioo (-1) 1) ↔ 1 < b := by
  rw [integrableOn_archimedeanAnomaly_iff hb]
  constructor
  · intro hint
    by_contra hle
    have hle' : b ≤ 1 := not_lt.mp hle
    have hge : ∀ y : ℝ, (1 : ℝ) ≤ 1 / Real.cosh y ^ 2 * Real.exp (2 * |y| / b) := fun y => by
      have hc := Real.cosh_pos y
      have hcl := cosh_le_exp_abs y
      have hexp : Real.exp (2 * |y|) ≤ Real.exp (2 * |y| / b) :=
        Real.exp_le_exp.mpr (le_div_self (by positivity) hb hle')
      have hsq : Real.cosh y ^ 2 ≤ Real.exp (2 * |y|) := by
        rw [show 2 * |y| = |y| + |y| by ring, Real.exp_add]
        nlinarith
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
      linarith
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) :=
      hint.mono' (aestronglyMeasurable_const) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_one]
        exact hge y)
    rw [integrable_const_iff] at h1
    rcases h1 with h1 | h1
    · exact one_ne_zero h1
    · exact absurd h1 (by
        rw [isFiniteMeasure_iff, Real.volume_univ]
        exact fun h => lt_irrefl _ h)
  · intro hb1
    set κ := 2 - 2 / b
    have hκ : 0 < κ := by
      have : 2 / b < 2 := by rw [div_lt_iff₀ hb]; linarith
      simp only [κ]
      linarith
    refine ((_root_.HTGeometry.integrable_cosh_rpow_neg hκ).const_mul 4).mono'
      (by fun_prop) (Eventually.of_forall fun y => ?_)
    have hc := Real.cosh_pos y
    have hcl := _root_.HTGeometry.exp_abs_div_two_le_cosh y
    have hsq : Real.exp (2 * |y|) / 4 ≤ Real.cosh y ^ 2 := by
      have h2 : (Real.exp |y| / 2) ^ 2 ≤ Real.cosh y ^ 2 := pow_le_pow_left₀ (by positivity) hcl 2
      have h3 : (Real.exp |y| / 2) ^ 2 = Real.exp (2 * |y|) / 4 := by
        rw [div_pow, ← Real.exp_nat_mul]
        norm_num
      linarith
    have hF : 1 / Real.cosh y ^ 2 * Real.exp (2 * |y| / b) ≤ 4 * Real.exp (-(κ * |y|)) := by
      rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      calc Real.exp (2 * |y| / b) = 4 * Real.exp (-(κ * |y|)) * (Real.exp (2 * |y|) / 4) := by
            rw [mul_comm 4, mul_assoc, mul_div_cancel₀ _ four_ne_zero, ← Real.exp_add]
            congr 1
            simp only [κ]
            ring
        _ ≤ 4 * Real.exp (-(κ * |y|)) * Real.cosh y ^ 2 := by gcongr
    have hE : Real.exp (-(κ * |y|)) ≤ Real.cosh y ^ (-κ) := by
      rw [show -(κ * |y|) = |y| * (-κ) by ring, Real.exp_mul]
      exact Real.rpow_le_rpow_of_nonpos hc (cosh_le_exp_abs y) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith

/-! ## Integrability of the regular part -/

theorem integrableOn_log_Ioo : IntegrableOn Real.log (Ioo (-1) 1) :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
    (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1))).mono_set Ioo_subset_Ioc_self

theorem integrableOn_log_one_add_Ioo : IntegrableOn (fun v => Real.log (1 + v)) (Ioo (-1) 1) := by
  have h := ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
    ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := 2)).comp_add_left 1))
  norm_num at h
  exact h.mono_set Ioo_subset_Ioc_self

theorem integrableOn_log_one_sub_Ioo : IntegrableOn (fun v => Real.log (1 - v)) (Ioo (-1) 1) := by
  have h := ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := 2)).comp_sub_left 1).symm
  have h' := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
  norm_num at h'
  exact h'.mono_set Ioo_subset_Ioc_self

theorem measurable_artanh : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem integrableOn_artanh_Ioo : IntegrableOn Real.artanh (Ioo (-1) 1) := by
  have h1 : Integrable (fun v => Real.log (1 + v)) (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    integrableOn_log_one_add_Ioo
  have h2 : Integrable (fun v => Real.log (1 - v)) (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    integrableOn_log_one_sub_Ioo
  exact IntegrableOn.congr_fun ((h1.sub h2).const_mul (1 / 2))
    (fun v hv => by
      simp only [Pi.sub_apply]
      rw [HadamardLipschitz.artanh_eq_log_sub hv.1 hv.2]
      ring) measurableSet_Ioo

theorem continuous_envelopeRemainder : Continuous envelopeRemainder := by
  unfold envelopeRemainder
  have hk : Continuous fun x => Real.log (thetaCuspFullSource x) :=
    continuous_thetaCuspFullSource.log fun x => (thetaCuspFullSource_pos_all x).ne'
  fun_prop

theorem integrableOn_envelopeRemainder_artanh (b : ℝ) :
    IntegrableOn (fun v => envelopeRemainder (Real.artanh v / b)) (Ioo (-1) 1) := by
  obtain ⟨C, hC⟩ := exists_abs_envelopeRemainder_le
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioo_lt_top.ne
    (continuous_envelopeRemainder.measurable.comp
      (measurable_artanh.div_const b)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]
  exact hC _

/-- The regular part `G_b` is integrable on `(-1,1)`. -/
theorem integrableOn_anomalyRegularPart (b : ℝ) :
    IntegrableOn (anomalyRegularPart b) (Ioo (-1) 1) := by
  have hc : Integrable (fun _ : ℝ => Real.log (105 / 16) + Real.log b
      + Real.log (thetaBalanceMass b)) (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hlog : Integrable Real.log (volume.restrict (Ioo (-1 : ℝ) 1)) := integrableOn_log_Ioo
  have h1 : Integrable (fun v => Real.log (1 + v)) (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    integrableOn_log_one_add_Ioo
  have h2 : Integrable (fun v => Real.log (1 - v)) (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    integrableOn_log_one_sub_Ioo
  have hart : Integrable Real.artanh (volume.restrict (Ioo (-1 : ℝ) 1)) := integrableOn_artanh_Ioo
  have hε : Integrable (fun v => envelopeRemainder (Real.artanh v / b))
      (volume.restrict (Ioo (-1 : ℝ) 1)) := integrableOn_envelopeRemainder_artanh b
  have h := (((hc.add (hlog.const_mul 2)).add ((h2.add h1).const_mul (7 / 2))).sub
    ((hart.div_const b).abs.const_mul (9 / 2))).sub hε
  refine IntegrableOn.congr_fun h (fun v hv => ?_) measurableSet_Ioo
  have hp1 : 0 < 1 - v := by linarith [hv.2]
  have hp2 : 0 < 1 + v := by linarith [hv.1]
  simp only [Pi.add_apply, Pi.sub_apply, anomalyRegularPart]
  rw [show 1 - v ^ 2 = (1 - v) * (1 + v) by ring, Real.log_mul hp1.ne' hp2.ne']
  ring

theorem ae_log_subtractedModularDensity {b c : ℝ} (hb : 0 < b) :
    (fun v => Real.log (subtractedModularDensity b c v)) =ᵐ[volume.restrict (Ioo (-1) 1)]
      fun v => (Real.pi - c) * archimedeanAnomaly b v + anomalyRegularPart b v := by
  have h0 : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem measurableSet_Ioo] with v hv0 hv
  exact log_subtractedModularDensity hb hv hv0

/-- **Theorem UASA-C, (UASA.10).**  `log r_{b,c} ∈ L¹(-1,1)` iff `c = π` or `b > 1`: in the
punctured critical strip `0 < b ≤ 1` the counterterm coefficient `π` is forced, while for `b > 1`
every coefficient is admissible. -/
theorem integrableOn_log_subtractedModularDensity_iff {b : ℝ} (hb : 0 < b) (c : ℝ) :
    IntegrableOn (fun v => Real.log (subtractedModularDensity b c v)) (Ioo (-1) 1) ↔
      c = Real.pi ∨ 1 < b := by
  rw [integrableOn_congr_fun_ae (ae_log_subtractedModularDensity hb)]
  have hG : Integrable (anomalyRegularPart b) (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    integrableOn_anomalyRegularPart b
  have key : IntegrableOn (fun v => (Real.pi - c) * archimedeanAnomaly b v
      + anomalyRegularPart b v) (Ioo (-1) 1) ↔
      IntegrableOn (fun v => (Real.pi - c) * archimedeanAnomaly b v) (Ioo (-1) 1) := by
    constructor
    · intro h
      exact IntegrableOn.congr_fun (Integrable.sub h hG) (fun v _ => by simp)
        measurableSet_Ioo
    · intro h
      exact Integrable.add h hG
  rw [key]
  rcases eq_or_ne c Real.pi with hc | hc
  · subst hc
    refine ⟨fun _ => Or.inl rfl, fun _ => ?_⟩
    simp only [sub_self, zero_mul]
    exact integrableOn_const measure_Ioo_lt_top.ne
  · rw [IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hc.symm)),
      ← IntegrableOn, integrableOn_archimedeanAnomaly_iff_one_lt hb]
    simp [hc]

/-! ## The residual Szegő weight -/

theorem abs_artanh {v : ℝ} (hv : v ∈ Ioo (-1) 1) : |Real.artanh v| = Real.artanh |v| := by
  rcases le_or_gt 0 v with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.artanh_nonneg h)]
  · rw [abs_of_neg h, abs_of_neg (Real.artanh_neg ⟨hv.1, h⟩),
      HadamardLipschitz.artanh_neg_eq hv.1 hv.2]

theorem artanh_ne_zero {v : ℝ} (hv : v ∈ Ioo (-1) 1) (hv0 : v ≠ 0) : Real.artanh v ≠ 0 := by
  intro h
  apply hv0
  rw [← Real.tanh_artanh hv, h, Real.tanh_zero]

/-- `Q(v)^{-9/(4b)} = e^{-(9/2)|x_b(v)|}` with `Q(v) = (1+|v|)/(1-|v|)`. -/
theorem contrastRatio_rpow {b v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1) :
    ((1 + |v|) / (1 - |v|)) ^ (-(9 / (4 * b))) = Real.exp (-(9 / 2) * |Real.artanh v / b|) := by
  have habs : |v| < 1 := abs_lt.mpr ⟨hv.1, hv.2⟩
  have h1 : 0 < 1 - |v| := by linarith
  have h2 : 0 < 1 + |v| := by positivity
  have hv' : |v| ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [abs_nonneg v], habs⟩
  rw [Real.rpow_def_of_pos (div_pos h2 h1), abs_div, abs_of_pos hb, abs_artanh hv,
    HadamardLipschitz.artanh_eq_log_sub hv'.1 hv'.2, Real.log_div h2.ne' h1.ne']
  congr 1
  ring

/-- **(UASA.11).**  The residual profile `P_b(v) = v² (1-v²)^{7/2} Q(v)^{-9/(4b)}`. -/
def residualProfile (b v : ℝ) : ℝ :=
  v ^ 2 * ((1 - v ^ 2) ^ 3 * Real.sqrt (1 - v ^ 2)) * Real.exp (-(9 / 2) * |Real.artanh v / b|)

theorem residualProfile_eq_rpow {b v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1) :
    residualProfile b v
      = v ^ 2 * (1 - v ^ 2) ^ (7 / 2 : ℝ) * ((1 + |v|) / (1 - |v|)) ^ (-(9 / (4 * b))) := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  rw [residualProfile, contrastRatio_rpow hb hv, Real.sqrt_eq_rpow]
  congr 1
  rw [show (7 / 2 : ℝ) = ((3 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add h1, Real.rpow_natCast]

theorem residualProfile_nonneg (b : ℝ) {v : ℝ} (hv : v ∈ Ioo (-1) 1) : 0 ≤ residualProfile b v := by
  have h1 : 0 ≤ 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  unfold residualProfile
  positivity

theorem residualProfile_le_sq (b : ℝ) {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    residualProfile b v ≤ v ^ 2 := by
  have h1 : 0 ≤ 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have h1' : 1 - v ^ 2 ≤ 1 := by nlinarith [sq_nonneg v]
  have hs : Real.sqrt (1 - v ^ 2) ≤ 1 := Real.sqrt_le_one.mpr h1'
  have he : Real.exp (-(9 / 2) * |Real.artanh v / b|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (Real.artanh v / b)])
  have hc : (1 - v ^ 2) ^ 3 ≤ 1 := pow_le_one₀ h1 h1'
  have hsq : 0 ≤ Real.sqrt (1 - v ^ 2) := Real.sqrt_nonneg _
  unfold residualProfile
  calc v ^ 2 * ((1 - v ^ 2) ^ 3 * Real.sqrt (1 - v ^ 2))
        * Real.exp (-(9 / 2) * |Real.artanh v / b|)
      ≤ v ^ 2 * (1 * 1) * 1 := by gcongr
    _ = v ^ 2 := by ring

theorem thetaContrastDensity_pos {b v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1) :
    0 < thetaContrastDensity b v := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hs : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.mpr h1
  have hZ := thetaBalanceMass_pos b
  have hk := thetaCuspFullSource_pos_all (Real.artanh v / b)
  rw [thetaContrastDensity]
  positivity

theorem subtractedModularDensity_pos {b c v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1)
    (hv0 : v ≠ 0) : 0 < subtractedModularDensity b c v := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hs := thetaContrastDensity_pos hb hv
  rw [subtractedModularDensity, hodgeSpectralDensity]
  positivity

/-- **(UASA.11).**  `r_{b,π} = (105/16) b Z_b e^{-ε(x_b)} P_b`. -/
theorem subtractedModularDensity_pi_eq {b v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1)
    (hv0 : v ≠ 0) :
    subtractedModularDensity b Real.pi v = 105 / 16 * b * thetaBalanceMass b *
      Real.exp (-envelopeRemainder (Real.artanh v / b)) * residualProfile b v := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hs : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.mpr h1
  have hZ := thetaBalanceMass_pos b
  have hv2 : 0 < v ^ 2 := by positivity
  have hPpos : 0 < residualProfile b v := by
    rw [residualProfile]
    positivity
  have hR : 0 < 105 / 16 * b * thetaBalanceMass b *
      Real.exp (-envelopeRemainder (Real.artanh v / b)) * residualProfile b v := by
    positivity
  have hL := subtractedModularDensity_pos (c := Real.pi) hb hv hv0
  have hlogL := log_subtractedModularDensity (c := Real.pi) hb hv hv0
  have hP : Real.log (residualProfile b v) = 2 * Real.log v + 7 / 2 * Real.log (1 - v ^ 2)
      - 9 / 2 * |Real.artanh v / b| := by
    rw [residualProfile, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hs.ne',
      Real.log_exp, Real.log_pow, Real.log_pow, Real.log_sqrt h1.le]
    push_cast
    ring
  have hlogR : Real.log (105 / 16 * b * thetaBalanceMass b *
      Real.exp (-envelopeRemainder (Real.artanh v / b)) * residualProfile b v)
        = anomalyRegularPart b v := by
    rw [Real.log_mul (by positivity) hPpos.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hZ.ne', Real.log_mul (by norm_num) hb.ne', Real.log_exp, hP,
      anomalyRegularPart]
    ring
  rw [← Real.exp_log hL, ← Real.exp_log hR, hlogL, hlogR, sub_self, zero_mul, zero_add]

theorem thetaEnvelopeLower_le_upper : thetaEnvelopeLower ≤ thetaEnvelopeUpper :=
  le_of_mul_le_mul_right ((thetaCuspFullSource_ge_envelope (x := 1) one_pos).trans
    (thetaCuspFullSource_le_envelope (x := 1) zero_le_one)) (thetaEnvelope_pos 1)

/-- **(UASA.11).**  `d P_b ≤ r_{b,π} ≤ D P_b`, `d = K/C₊ ≤ D = K/C₋`, `K = (105/16) b Z_b`. -/
theorem subtractedModularDensity_pi_bounds {b v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1)
    (hv0 : v ≠ 0) :
    105 / 16 * b * thetaBalanceMass b * thetaEnvelopeUpper⁻¹ * residualProfile b v
        ≤ subtractedModularDensity b Real.pi v ∧
      subtractedModularDensity b Real.pi v
        ≤ 105 / 16 * b * thetaBalanceMass b * thetaEnvelopeLower⁻¹ * residualProfile b v := by
  rw [subtractedModularDensity_pi_eq hb hv hv0]
  have hP := residualProfile_nonneg b hv
  have hK : 0 ≤ 105 / 16 * b * thetaBalanceMass b := by
    have := thetaBalanceMass_pos b
    positivity
  have hup := envelopeRemainder_le (Real.artanh v / b)
  have hlo := le_envelopeRemainder (div_ne_zero (artanh_ne_zero hv hv0) hb.ne')
  have e1 : thetaEnvelopeUpper⁻¹ ≤ Real.exp (-envelopeRemainder (Real.artanh v / b)) := by
    rw [← Real.exp_log thetaEnvelopeUpper_pos, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (-envelopeRemainder (Real.artanh v / b)) ≤ thetaEnvelopeLower⁻¹ := by
    rw [← Real.exp_log thetaEnvelopeLower_pos, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  exact ⟨mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hK) hP,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hK) hP⟩

/-! ## The compactified residual weight -/

/-- The reduced angular contrast `v(θ) ∈ (-1, 1]`, `v(θ) ≡ θ/π (mod 2)`. -/
def angularContrast (θ : ℝ) : ℝ := toIocMod Real.two_pi_pos (-Real.pi) θ / Real.pi

theorem angularContrast_periodic : Function.Periodic angularContrast (2 * Real.pi) := fun θ => by
  simp only [angularContrast, toIocMod_add_right]

theorem angularContrast_eq {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    angularContrast θ = θ / Real.pi := by
  rw [angularContrast, (toIocMod_eq_self Real.two_pi_pos).mpr ⟨hθ.1, by linarith [hθ.2]⟩]

/-- **(UASA.12).**  The compactified residual weight `W_b(θ) = r_{b,π}(θ/π)` on `(-π, π)`,
extended `2π`-periodically; the seam `θ = 0` and the compactified endpoint `θ = π` carry the
irrelevant value `1`. -/
def residualSzegoWeight (b θ : ℝ) : ℝ :=
  if angularContrast θ ∈ Ioo (-1) 1 ∧ angularContrast θ ≠ 0 then
    subtractedModularDensity b Real.pi (angularContrast θ) else 1

theorem residualSzegoWeight_periodic (b : ℝ) :
    Function.Periodic (residualSzegoWeight b) (2 * Real.pi) := fun θ => by
  simp only [residualSzegoWeight, angularContrast_periodic θ]

theorem residualSzegoWeight_pos {b : ℝ} (hb : 0 < b) (θ : ℝ) : 0 < residualSzegoWeight b θ := by
  unfold residualSzegoWeight
  split_ifs with h
  · exact subtractedModularDensity_pos hb h.1 h.2
  · exact one_pos

/-- The essential bound `M_b = max(K/C₋, 1)` of `W_b`. -/
def residualSzegoBound (b : ℝ) : ℝ :=
  max (105 / 16 * b * thetaBalanceMass b * thetaEnvelopeLower⁻¹) 1

theorem one_le_residualSzegoBound (b : ℝ) : 1 ≤ residualSzegoBound b := le_max_right _ _

theorem subtractedModularDensity_pi_le_sq {b v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1)
    (hv0 : v ≠ 0) : subtractedModularDensity b Real.pi v ≤ residualSzegoBound b * v ^ 2 := by
  have hK : 0 ≤ 105 / 16 * b * thetaBalanceMass b * thetaEnvelopeLower⁻¹ := by
    have := thetaBalanceMass_pos b
    have := thetaEnvelopeLower_pos
    positivity
  calc subtractedModularDensity b Real.pi v
      ≤ 105 / 16 * b * thetaBalanceMass b * thetaEnvelopeLower⁻¹ * residualProfile b v :=
        (subtractedModularDensity_pi_bounds hb hv hv0).2
    _ ≤ residualSzegoBound b * v ^ 2 :=
        mul_le_mul (le_max_left _ _) (residualProfile_le_sq b hv) (residualProfile_nonneg b hv)
          (zero_le_one.trans (one_le_residualSzegoBound b))

theorem residualSzegoWeight_le {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    residualSzegoWeight b θ ≤ residualSzegoBound b := by
  unfold residualSzegoWeight
  split_ifs with h
  · have hsq : angularContrast θ ^ 2 ≤ 1 := by nlinarith [h.1.1, h.1.2]
    calc subtractedModularDensity b Real.pi (angularContrast θ)
        ≤ residualSzegoBound b * angularContrast θ ^ 2 :=
          subtractedModularDensity_pi_le_sq hb h.1 h.2
      _ ≤ residualSzegoBound b * 1 :=
          mul_le_mul_of_nonneg_left hsq (zero_le_one.trans (one_le_residualSzegoBound b))
      _ = residualSzegoBound b := mul_one _
  · exact one_le_residualSzegoBound b

theorem residualSzegoWeight_eq {b θ : ℝ} (hθ : θ ∈ Ioo (-Real.pi) Real.pi) (hθ0 : θ ≠ 0) :
    residualSzegoWeight b θ = subtractedModularDensity b Real.pi (θ / Real.pi) := by
  have hv : θ / Real.pi ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by rw [lt_div_iff₀ Real.pi_pos]; linarith [hθ.1],
      by rw [div_lt_iff₀ Real.pi_pos]; linarith [hθ.2]⟩
  have hv0 : θ / Real.pi ≠ 0 := div_ne_zero hθ0 Real.pi_ne_zero
  rw [residualSzegoWeight, angularContrast_eq ⟨hθ.1, hθ.2.le⟩, if_pos ⟨hv, hv0⟩]

theorem log_residualSzegoWeight_eq {b θ : ℝ} (hb : 0 < b) (hθ : θ ∈ Ioo (-Real.pi) Real.pi)
    (hθ0 : θ ≠ 0) : Real.log (residualSzegoWeight b θ) = anomalyRegularPart b (θ / Real.pi) := by
  have hv : θ / Real.pi ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by rw [lt_div_iff₀ Real.pi_pos]; linarith [hθ.1],
      by rw [div_lt_iff₀ Real.pi_pos]; linarith [hθ.2]⟩
  rw [residualSzegoWeight_eq hθ hθ0, log_subtractedModularDensity hb hv
    (div_ne_zero hθ0 Real.pi_ne_zero), sub_self, zero_mul, zero_add]

theorem intervalIntegrable_log_residualSzegoWeight_pi {b : ℝ} (hb : 0 < b) :
    IntervalIntegrable (fun θ => Real.log (residualSzegoWeight b θ)) volume
      (-Real.pi) Real.pi := by
  have hG : IntervalIntegrable (anomalyRegularPart b) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr
      (integrableOn_anomalyRegularPart b)
  have h := hG.comp_mul_left (c := Real.pi⁻¹)
  simp only [div_inv_eq_mul, neg_one_mul, one_mul] at h
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hle] at h ⊢
  refine h.congr_fun_ae ?_
  have h0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae h0] with θ hθ hθ0
  rw [log_residualSzegoWeight_eq hb hθ hθ0, div_eq_inv_mul]

theorem periodic_log_residualSzegoWeight (b : ℝ) :
    Function.Periodic (fun θ => Real.log (residualSzegoWeight b θ)) (2 * Real.pi) := fun θ => by
  simp only [residualSzegoWeight_periodic b θ]

theorem intervalIntegrable_log_residualSzegoWeight {b : ℝ} (hb : 0 < b) (a₁ a₂ : ℝ) :
    IntervalIntegrable (fun θ => Real.log (residualSzegoWeight b θ)) volume a₁ a₂ := by
  have hbase : IntervalIntegrable (fun θ => Real.log (residualSzegoWeight b θ)) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    exact intervalIntegrable_log_residualSzegoWeight_pi hb
  exact (periodic_log_residualSzegoWeight b).intervalIntegrable Real.two_pi_pos.ne' hbase a₁ a₂

theorem locallyIntegrable_log_residualSzegoWeight {b : ℝ} (hb : 0 < b) :
    LocallyIntegrable (fun θ => Real.log (residualSzegoWeight b θ)) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hkR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hk.isBounded
  have hI := intervalIntegrable_log_residualSzegoWeight hb (-|R|) |R|
  have hIcc := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by linarith [abs_nonneg R])).mp hI
  exact hIcc.mono_set fun y hy => by
    have hyR : |y| ≤ R := by simpa [Metric.mem_closedBall, Real.dist_eq] using hkR hy
    exact abs_le.mp (hyR.trans (le_abs_self R))

/-- `W_b` vanishes quadratically at the seam: `1/W_b` is not integrable on `(0, π)`. -/
theorem not_intervalIntegrable_inv_residualSzegoWeight {b : ℝ} (hb : 0 < b) :
    ¬IntervalIntegrable (fun θ => (residualSzegoWeight b θ)⁻¹) volume 0 Real.pi := by
  intro h
  set M := residualSzegoBound b
  have hM : 1 ≤ M := one_le_residualSzegoBound b
  have hinv : IntervalIntegrable (fun θ : ℝ => θ⁻¹) volume 0 Real.pi := by
    refine (h.const_mul (M / Real.pi)).mono_fun' (by fun_prop) ?_
    rw [uIoc_of_le Real.pi_pos.le]
    refine (ae_restrict_mem measurableSet_Ioc).mono fun θ hθ => ?_
    have hθ0 : 0 < θ := hθ.1
    have hW := residualSzegoWeight_pos hb θ
    show ‖θ⁻¹‖ ≤ M / Real.pi * (residualSzegoWeight b θ)⁻¹
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hθ0)]
    rcases eq_or_lt_of_le hθ.2 with hπ | hπ
    · subst hπ
      have h1 : residualSzegoWeight b Real.pi = 1 := by
        rw [residualSzegoWeight, angularContrast_eq ⟨by linarith [Real.pi_pos], le_rfl⟩,
          div_self Real.pi_ne_zero, if_neg (fun h => lt_irrefl _ h.1.2)]
      rw [h1, inv_one, mul_one, inv_eq_one_div]
      exact div_le_div_of_nonneg_right hM Real.pi_pos.le
    · have hθ' : θ ∈ Ioo (-Real.pi) Real.pi := ⟨by linarith [Real.pi_pos], hπ⟩
      have hv : θ / Real.pi ∈ Ioo (-1 : ℝ) 1 :=
        ⟨by rw [lt_div_iff₀ Real.pi_pos]; linarith, by rw [div_lt_iff₀ Real.pi_pos]; linarith⟩
      have hle := subtractedModularDensity_pi_le_sq hb hv (div_ne_zero hθ0.ne' Real.pi_ne_zero)
      rw [← residualSzegoWeight_eq hθ' hθ0.ne'] at hle
      have hq : (θ / Real.pi) ^ 2 ≤ θ / Real.pi := by
        have h01 : θ / Real.pi ≤ 1 := hv.2.le
        have h00 : 0 ≤ θ / Real.pi := div_nonneg hθ0.le Real.pi_pos.le
        nlinarith
      have hWle : residualSzegoWeight b θ ≤ M * θ / Real.pi := by
        calc residualSzegoWeight b θ ≤ M * (θ / Real.pi) ^ 2 := hle
          _ ≤ M * (θ / Real.pi) := mul_le_mul_of_nonneg_left hq (by linarith)
          _ = M * θ / Real.pi := by ring
      rw [inv_eq_one_div, div_le_iff₀ hθ0]
      calc (1 : ℝ) = M / Real.pi * (M * θ / Real.pi)⁻¹ * θ := by
            field_simp
        _ ≤ M / Real.pi * (residualSzegoWeight b θ)⁻¹ * θ := by
            gcongr
  rw [intervalIntegrable_inv_iff] at hinv
  rcases hinv with h0 | h0
  · exact Real.pi_ne_zero h0.symm
  · exact h0 ⟨by simp [Real.pi_pos.le], by simp [Real.pi_pos.le]⟩

/-! ## The canonical residual Szegő factor -/

theorem measurable_angularContrast : Measurable angularContrast := by
  have h : angularContrast = fun θ => (θ - (((-⌊(-Real.pi + 2 * Real.pi - θ) / (2 * Real.pi)⌋ :
      ℤ) : ℝ)) * (2 * Real.pi)) / Real.pi := by
    funext θ
    rw [angularContrast, ← self_sub_toIocDiv_zsmul, toIocDiv_eq_neg_floor, zsmul_eq_mul]
  rw [h]
  have hf : Measurable fun θ : ℝ => -⌊(-Real.pi + 2 * Real.pi - θ) / (2 * Real.pi)⌋ :=
    (Int.measurable_floor.comp (by fun_prop)).neg
  exact (measurable_id.sub (((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hf).mul_const
    _)).div_const _

theorem measurable_subtractedModularDensity (b c : ℝ) :
    Measurable (subtractedModularDensity b c) := by
  have hk : Measurable thetaCuspFullSource := continuous_thetaCuspFullSource.measurable
  have ha := measurable_artanh
  unfold subtractedModularDensity hodgeSpectralDensity thetaContrastDensity archimedeanAnomaly
  fun_prop

theorem measurable_residualSzegoWeight (b : ℝ) : Measurable (residualSzegoWeight b) := by
  have hs : MeasurableSet {θ : ℝ | angularContrast θ ∈ Ioo (-1) 1 ∧ angularContrast θ ≠ 0} :=
    (measurable_angularContrast measurableSet_Ioo).inter
      (measurable_angularContrast (measurableSet_singleton 0).compl)
  exact Measurable.ite hs
    ((measurable_subtractedModularDensity b Real.pi).comp measurable_angularContrast)
    measurable_const

/-- The residual weight `W_b` as a bounded Szegő weight. -/
def residualSzego {b : ℝ} (hb : 0 < b) : SzegoWeight where
  w := residualSzegoWeight b
  meas := measurable_residualSzegoWeight b
  pos := residualSzegoWeight_pos hb
  bound := residualSzegoBound b
  le_bound := residualSzegoWeight_le hb
  periodic := residualSzegoWeight_periodic b
  logInt := intervalIntegrable_log_residualSzegoWeight hb 0 (2 * Real.pi)

theorem not_intervalIntegrable_inv_residualSzegoWeight_two_pi {b : ℝ} (hb : 0 < b) :
    ¬IntervalIntegrable (fun θ => (residualSzegoWeight b θ)⁻¹) volume 0 (2 * Real.pi) := by
  intro h
  refine not_intervalIntegrable_inv_residualSzegoWeight hb (h.mono_set ?_)
  rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le Real.two_pi_pos.le]
  exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])

/-- **Theorem UASA-D, (UASA.13).**  The normalized outer function `D_b = D_{W_b}` has
`|D_b(e^{iθ})|² = W_b(θ)` almost everywhere (radially and in the `L²` boundary sense), positive
value at the origin, no zeros, and is bounded (`H² ∩ H^∞`); it is outer, multiplication by `D_b`
on `H²` is injective with dense range which is not closed, and `D_b` is the unique outer
multiplier with this boundary modulus and positive value at the origin. -/
theorem residual_szego_factor {b : ℝ} (hb : 0 < b) :
    (∀ᵐ θ ∂volume, Tendsto (fun r => ‖(residualSzego hb).outer.fn (circleMap 0 r θ)‖ ^ (2 : ℕ))
      (𝓝[<] 1) (𝓝 (residualSzegoWeight b θ))) ∧
    (∀ᵐ z ∂circleLebesgue, ‖diskMultiplierBoundaryFun (residualSzego hb).outer z‖ ^ (2 : ℕ) =
      residualSzegoWeight b (Complex.arg (z : ℂ))) ∧
    (∃ s : ℝ, 0 < s ∧ (residualSzego hb).outer.fn 0 = s) ∧
    (∀ z, (residualSzego hb).outer.fn z ≠ 0) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1,
      ‖(residualSzego hb).outer.fn z‖ ≤ Real.sqrt (residualSzegoBound b)) ∧
    (∀ z : ℂ, ‖z‖ < 1 → hardyFun (hardyOf (residualSzego hb).outer) z =
      (residualSzego hb).outer.fn z) ∧
    IsOuterDiskMultiplier (residualSzego hb).outer ∧
    Function.Injective (hardyMul (residualSzego hb).outer) ∧
    DenseRange (hardyMul (residualSzego hb).outer) ∧
    ¬IsClosed (Set.range (hardyMul (residualSzego hb).outer)) ∧
    (∀ ψ : DiskMultiplier, IsOuterDiskMultiplier ψ →
      (∀ᵐ z ∂circleLebesgue, ‖diskMultiplierBoundaryFun ψ z‖ ^ (2 : ℕ) =
        residualSzegoWeight b (Complex.arg (z : ℂ))) →
      ∀ s : ℝ, 0 < s → ψ.fn 0 = s →
        ∀ z ∈ Metric.ball (0 : ℂ) 1, ψ.fn z = (residualSzego hb).outer.fn z) :=
  ⟨(residualSzego hb).tendsto_normSq_outer, (residualSzego hb).ae_norm_sq_boundary_outer,
    ⟨_, Real.exp_pos _, (residualSzego hb).outer_zero⟩, (residualSzego hb).outer_ne_zero,
    (residualSzego hb).outer.bd_le, fun _ hz => hardyFun_hardyOf _ hz,
    (residualSzego hb).isOuter, (residualSzego hb).hardyMul_outer_injective,
    (residualSzego hb).denseRange_hardyMul_outer,
    (residualSzego hb).not_isClosed_range_hardyMul_outer
      (not_intervalIntegrable_inv_residualSzegoWeight_two_pi hb),
    fun ψ hψ hmod _ hs hψ0 => (residualSzego hb).eq_outer_of_isOuter ψ hψ hmod hs hψ0⟩

/-! ## The unsquared orientation amplitude -/

/-- **(UASA.14).**  The reflection-odd orientation amplitude `Ψ_b(θ) = sign(θ) √W_b(θ)`. -/
def orientationAmplitude (b θ : ℝ) : ℝ :=
  Real.sign (angularContrast θ) * Real.sqrt (residualSzegoWeight b θ)

theorem orientationAmplitude_periodic (b : ℝ) :
    Function.Periodic (orientationAmplitude b) (2 * Real.pi) := fun θ => by
  simp only [orientationAmplitude, angularContrast_periodic θ, residualSzegoWeight_periodic b θ]

/-- **(UASA.14).**  Away from the seam, `Ψ_b² = W_b`. -/
theorem orientationAmplitude_sq {b θ : ℝ} (hb : 0 < b) (hθ : angularContrast θ ≠ 0) :
    orientationAmplitude b θ ^ 2 = residualSzegoWeight b θ := by
  rw [orientationAmplitude, mul_pow, Real.sq_sqrt (residualSzegoWeight_pos hb θ).le]
  rcases lt_or_gt_of_ne hθ with h | h
  · rw [Real.sign_of_neg h]
    ring
  · rw [Real.sign_of_pos h]
    ring

theorem orientationAmplitude_pos {b θ : ℝ} (hb : 0 < b) (hθ : θ ∈ Ioo 0 Real.pi) :
    0 < orientationAmplitude b θ := by
  rw [orientationAmplitude, angularContrast_eq ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩,
    Real.sign_of_pos (div_pos hθ.1 Real.pi_pos), one_mul]
  exact Real.sqrt_pos.mpr (residualSzegoWeight_pos hb θ)

theorem orientationAmplitude_neg {b θ : ℝ} (hb : 0 < b)
    (hθ : θ ∈ Ioo Real.pi (2 * Real.pi)) : orientationAmplitude b θ < 0 := by
  have hθ' : θ - 2 * Real.pi ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hper : orientationAmplitude b θ = orientationAmplitude b (θ - 2 * Real.pi) := by
    have := orientationAmplitude_periodic b (θ - 2 * Real.pi)
    rwa [sub_add_cancel] at this
  rw [hper, orientationAmplitude, angularContrast_eq hθ',
    Real.sign_of_neg (div_neg_of_neg_of_pos (by linarith [hθ.2]) Real.pi_pos), neg_one_mul,
    neg_lt_zero]
  exact Real.sqrt_pos.mpr (residualSzegoWeight_pos hb _)

/-- **Theorem UASA-E.**  No function in scalar `H²` has boundary value `Ψ_b`: a real boundary
function of an `H²` function is constant, while `Ψ_b` is positive on `(0, π)` and negative on
`(π, 2π)`. -/
theorem not_exists_hardyDisk_boundary_orientationAmplitude {b : ℝ} (hb : 0 < b) :
    ¬∃ f : HardyDisk, ∀ᵐ z ∂circleLebesgue, (hardyDiskBoundary f : Circle → ℂ) z =
      (orientationAmplitude b (Complex.arg (z : ℂ)) : ℂ) := by
  rintro ⟨f, hf⟩
  have hreal : ∀ᵐ z ∂circleLebesgue, conj ((hardyDiskBoundary f : Circle → ℂ) z) =
      (hardyDiskBoundary f : Circle → ℂ) z := by
    filter_upwards [hf] with z hz
    rw [hz, Complex.conj_ofReal]
  have hconst := hardyDiskBoundary_ae_eq_const_of_real f hreal
  have hcirc : ∀ᵐ z : Circle ∂circleLebesgue,
      (orientationAmplitude b (Complex.arg (z : ℂ)) : ℂ) = f 0 := by
    filter_upwards [hf, hconst] with z h1 h2
    rw [← h1, h2]
  have hang := ae_angularCircle_of_ae_circle hcirc
  have hpt : ∀ᵐ θ ∂volume, θ ∈ Ioc 0 (2 * Real.pi) →
      (orientationAmplitude b θ : ℂ) = f 0 := by
    filter_upwards [hang] with θ hθ hmem
    have h := hθ hmem
    rwa [coe_angularCircle, periodic_apply_arg_circleMap (orientationAmplitude_periodic b)] at h
  have hexists : ∀ {a c : ℝ}, a < c → Ioo a c ⊆ Ioc 0 (2 * Real.pi) →
      ∃ θ ∈ Ioo a c, (orientationAmplitude b θ : ℂ) = f 0 := by
    intro a c hac hsub
    have hne : (ae (volume.restrict (Ioo a c))).NeBot := ae_neBot.mpr (by
      rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo]
      simpa using hac)
    have hev : ∀ᵐ θ ∂volume.restrict (Ioo a c),
        θ ∈ Ioo a c ∧ (orientationAmplitude b θ : ℂ) = f 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hpt] with θ h1 h2
      exact ⟨h1, h2 (hsub h1)⟩
    obtain ⟨θ, h1, h2⟩ := hev.exists
    exact ⟨θ, h1, h2⟩
  obtain ⟨θ₁, h₁, e₁⟩ := hexists Real.pi_pos (fun θ h => ⟨h.1, by linarith [h.2, Real.pi_pos]⟩)
  obtain ⟨θ₂, h₂, e₂⟩ := hexists (by linarith [Real.pi_pos] : Real.pi < 2 * Real.pi)
    (fun θ h => ⟨by linarith [h.1, Real.pi_pos], h.2.le⟩)
  have := e₁.trans e₂.symm
  have hre := congrArg Complex.re this
  simp only [Complex.ofReal_re] at hre
  linarith [orientationAmplitude_pos hb h₁, orientationAmplitude_neg hb h₂]

/-! ## Endpoint growth of the anomaly and the comparison coefficients -/

/-- **(UASA.7).**  `A_b(v) = Q(v)^{1/b}`. -/
theorem archimedeanAnomaly_eq_rpow {b v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1) :
    archimedeanAnomaly b v = ((1 + |v|) / (1 - |v|)) ^ (1 / b) := by
  have habs : |v| < 1 := abs_lt.mpr ⟨hv.1, hv.2⟩
  have h1 : 0 < 1 - |v| := by linarith
  have h2 : 0 < 1 + |v| := by positivity
  have hv' : |v| ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [abs_nonneg v], habs⟩
  rw [archimedeanAnomaly, Real.rpow_def_of_pos (div_pos h2 h1), abs_div, abs_of_pos hb,
    abs_artanh hv, HadamardLipschitz.artanh_eq_log_sub hv'.1 hv'.2,
    Real.log_div h2.ne' h1.ne']
  congr 1
  ring

/-- **(UASA.9).**  `A_b(v) (1-|v|)^{1/b} = (1+|v|)^{1/b} → 2^{1/b}` at either endpoint: `A_b` is
integrable exactly when `b > 1`. -/
theorem archimedeanAnomaly_mul_rpow {b v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1) :
    archimedeanAnomaly b v * (1 - |v|) ^ (1 / b) = (1 + |v|) ^ (1 / b) := by
  have habs : |v| < 1 := abs_lt.mpr ⟨hv.1, hv.2⟩
  have h1 : 0 < 1 - |v| := by linarith
  rw [archimedeanAnomaly_eq_rpow hb hv, Real.div_rpow (by positivity) h1.le,
    div_mul_cancel₀ _ (Real.rpow_pos_of_pos h1 _).ne']

/-- Integrability on `(-1,1)` pulled back through `v = tanh y`. -/
theorem integrableOn_Ioo_iff_tanh (g : ℝ → ℝ) :
    IntegrableOn g (Ioo (-1) 1) ↔
      Integrable (fun y : ℝ => 1 / Real.cosh y ^ 2 * g (Real.tanh y)) := by
  rw [← image_tanh_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (_root_.HTGeometry.hasDerivAt_tanh y).hasDerivWithinAt)
    (_root_.HTGeometry.tanh_strictMono.injective.injOn), integrableOn_univ]
  refine integrable_congr (Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, abs_div, abs_one, abs_of_pos (pow_pos (Real.cosh_pos y) 2)]

theorem subtractedModularDensity_eq_mul (b c v : ℝ) :
    subtractedModularDensity b c v = subtractedModularDensity b Real.pi v *
      Real.exp ((Real.pi - c) * archimedeanAnomaly b v) := by
  rw [subtractedModularDensity, subtractedModularDensity, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem exp_neg_le_cosh_inv {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) ≤ (Real.cosh y)⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ (Real.cosh_pos y) (by simpa [abs_of_nonneg hy] using cosh_le_exp_abs y)

/-- For `y ≥ 1`, the pulled-back density dominates
`K₀ exp((π-c) e^{2y/b} - (9 + 9/(2b)) y)`. -/
theorem pullback_subtractedModularDensity_ge {b c y : ℝ} (hb : 0 < b) (hy : 1 ≤ y) :
    105 / 16 * b * thetaBalanceMass b * thetaEnvelopeUpper⁻¹ * Real.tanh 1 ^ 2 *
        Real.exp ((Real.pi - c) * Real.exp (2 * y / b) - (9 + 9 / (2 * b)) * y)
      ≤ 1 / Real.cosh y ^ 2 * subtractedModularDensity b c (Real.tanh y) := by
  have hy0 : 0 < y := by linarith
  have hv : Real.tanh y ∈ Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩
  have ht1 : 0 < Real.tanh 1 := by
    have := _root_.HTGeometry.tanh_strictMono (show (0 : ℝ) < 1 by norm_num)
    rwa [Real.tanh_zero] at this
  have htanh : Real.tanh 1 ≤ Real.tanh y := _root_.HTGeometry.tanh_strictMono.monotone hy
  have hv0 : Real.tanh y ≠ 0 := (ht1.trans_le htanh).ne'
  have hc := Real.cosh_pos y
  have hA : archimedeanAnomaly b (Real.tanh y) = Real.exp (2 * y / b) := by
    rw [archimedeanAnomaly, Real.artanh_tanh, abs_div, abs_of_pos hy0, abs_of_pos hb]
    ring_nf
  have h1 : 1 - Real.tanh y ^ 2 = (Real.cosh y)⁻¹ ^ 2 := by
    rw [_root_.HTGeometry.one_sub_tanh_sq, inv_pow, one_div]
  have h2 : Real.sqrt (1 - Real.tanh y ^ 2) = (Real.cosh y)⁻¹ := by
    rw [h1, Real.sqrt_sq (inv_nonneg.mpr hc.le)]
  have hP : residualProfile b (Real.tanh y) = Real.tanh y ^ 2 * (Real.cosh y)⁻¹ ^ 7 *
      Real.exp (-(9 / 2) * (y / b)) := by
    rw [residualProfile, h2, h1, Real.artanh_tanh, abs_div, abs_of_pos hy0, abs_of_pos hb]
    ring
  have hKd : 0 ≤ 105 / 16 * b * thetaBalanceMass b * thetaEnvelopeUpper⁻¹ := by
    have := thetaBalanceMass_pos b
    have := thetaEnvelopeUpper_pos
    positivity
  have hlow := (subtractedModularDensity_pi_bounds hb hv hv0).1
  have hc9 : Real.exp (-(9 * y)) ≤ (Real.cosh y)⁻¹ ^ 9 := by
    rw [show -(9 * y) = ((9 : ℕ) : ℝ) * (-y) by push_cast; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_le_cosh_inv hy0.le) 9
  set E := Real.exp ((Real.pi - c) * Real.exp (2 * y / b))
  set Kd := 105 / 16 * b * thetaBalanceMass b * thetaEnvelopeUpper⁻¹
  rw [subtractedModularDensity_eq_mul, hA]
  calc Kd * Real.tanh 1 ^ 2 *
        Real.exp ((Real.pi - c) * Real.exp (2 * y / b) - (9 + 9 / (2 * b)) * y)
      = Kd * (Real.tanh 1 ^ 2 * Real.exp (-(9 * y)) * Real.exp (-(9 / 2) * (y / b))) * E := by
        rw [show (Real.pi - c) * Real.exp (2 * y / b) - (9 + 9 / (2 * b)) * y
            = (Real.pi - c) * Real.exp (2 * y / b) + -(9 * y) + -(9 / 2) * (y / b) by
              field_simp
              ring,
          Real.exp_add, Real.exp_add]
        ring
    _ ≤ Kd * (Real.tanh y ^ 2 * (Real.cosh y)⁻¹ ^ 9 * Real.exp (-(9 / 2) * (y / b))) * E := by
        gcongr
    _ = 1 / Real.cosh y ^ 2 * (Kd * residualProfile b (Real.tanh y)) * E := by
        rw [hP]
        ring
    _ ≤ 1 / Real.cosh y ^ 2 * subtractedModularDensity b Real.pi (Real.tanh y) * E := by
        gcongr
    _ = 1 / Real.cosh y ^ 2 * (subtractedModularDensity b Real.pi (Real.tanh y) * E) := by ring

/-- Below the forced coefficient, `r_{b,c}` itself is not integrable. -/
theorem not_integrableOn_subtractedModularDensity {b c : ℝ} (hb : 0 < b) (hc : c < Real.pi) :
    ¬IntegrableOn (subtractedModularDensity b c) (Ioo (-1) 1) := by
  rw [integrableOn_Ioo_iff_tanh]
  intro hint
  set K0 := 105 / 16 * b * thetaBalanceMass b * thetaEnvelopeUpper⁻¹ * Real.tanh 1 ^ 2
  have hK0 : 0 < K0 := by
    have := thetaBalanceMass_pos b
    have := thetaEnvelopeUpper_pos
    have ht1 : 0 < Real.tanh 1 := by
      have := _root_.HTGeometry.tanh_strictMono (show (0 : ℝ) < 1 by norm_num)
      rwa [Real.tanh_zero] at this
    positivity
  set L := 9 + 9 / (2 * b)
  have ha : 0 < 2 * (Real.pi - c) / b ^ 2 := by
    have : 0 < Real.pi - c := by linarith
    positivity
  have hg : Tendsto (fun y : ℝ => y * (2 * (Real.pi - c) / b ^ 2 * y + -L)) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀
      (tendsto_atTop_add_const_right _ (-L) (tendsto_id.const_mul_atTop ha))
  have hq : Tendsto (fun y => (Real.pi - c) * Real.exp (2 * y / b) - L * y) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ hg
    filter_upwards [eventually_ge_atTop 0] with y hy
    have hexp := Real.pow_div_factorial_le_exp (2 * y / b) (by positivity) 2
    have hpc : 0 ≤ Real.pi - c := by linarith
    have h2 : (2 * y / b) ^ 2 / (Nat.factorial 2 : ℝ) = 2 * y ^ 2 / b ^ 2 := by
      norm_num [Nat.factorial]
      field_simp
    rw [h2] at hexp
    have := mul_le_mul_of_nonneg_left hexp hpc
    have e : y * (2 * (Real.pi - c) / b ^ 2 * y + -L)
        = (Real.pi - c) * (2 * y ^ 2 / b ^ 2) - L * y := by
      ring
    rw [e]
    linarith
  obtain ⟨Y, hY⟩ := eventually_atTop.1 ((hq.eventually_ge_atTop (Real.log K0⁻¹)).and
    (eventually_ge_atTop 1))
  have hge : ∀ y ∈ Ici Y,
      (1 : ℝ) ≤ 1 / Real.cosh y ^ 2 * subtractedModularDensity b c (Real.tanh y) := by
    intro y hy
    obtain ⟨hq1, hy1⟩ := hY y hy
    have h := pullback_subtractedModularDensity_ge (c := c) hb hy1
    have hexp : K0⁻¹ ≤ Real.exp ((Real.pi - c) * Real.exp (2 * y / b) - L * y) := by
      rw [← Real.exp_log (inv_pos.mpr hK0)]
      exact Real.exp_le_exp.mpr hq1
    calc (1 : ℝ) = K0 * K0⁻¹ := (mul_inv_cancel₀ hK0.ne').symm
      _ ≤ K0 * Real.exp ((Real.pi - c) * Real.exp (2 * y / b) - L * y) :=
          mul_le_mul_of_nonneg_left hexp hK0.le
      _ ≤ _ := h
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici Y) :=
    hint.integrableOn.mono' aestronglyMeasurable_const
      ((ae_restrict_mem measurableSet_Ici).mono fun y hy => by
        rw [Real.norm_eq_abs, abs_one]
        exact hge y hy)
  rw [integrableOn_const_iff] at h1
  rcases h1 with h1 | h1
  · simp at h1
  · rw [Real.volume_Ici] at h1
    exact lt_irrefl _ h1

theorem subtractedModularDensity_nonneg {b c v : ℝ} (hb : 0 < b) (hv : v ∈ Ioo (-1) 1) :
    0 ≤ subtractedModularDensity b c v := by
  rw [subtractedModularDensity]
  exact mul_nonneg (div_nonneg (hodgeSpectralDensity_nonneg v)
    (thetaContrastDensity_pos hb hv).le) (Real.exp_pos _).le

theorem subtractedModularDensity_le_bound {b c v : ℝ} (hb : 0 < b) (hc : Real.pi ≤ c)
    (hv : v ∈ Ioo (-1) 1) : subtractedModularDensity b c v ≤ residualSzegoBound b := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp [subtractedModularDensity, hodgeSpectralDensity,
      zero_le_one.trans (one_le_residualSzegoBound b)]
  · have hsq : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have hM := one_le_residualSzegoBound b
    have hA : 0 ≤ archimedeanAnomaly b v := (Real.exp_pos _).le
    have hexp : Real.exp ((Real.pi - c) * archimedeanAnomaly b v) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hA)
    rw [subtractedModularDensity_eq_mul]
    calc subtractedModularDensity b Real.pi v * Real.exp ((Real.pi - c) * archimedeanAnomaly b v)
        ≤ subtractedModularDensity b Real.pi v * 1 :=
          mul_le_mul_of_nonneg_left hexp (subtractedModularDensity_nonneg hb hv)
      _ ≤ residualSzegoBound b * v ^ 2 := by
          rw [mul_one]
          exact subtractedModularDensity_pi_le_sq hb hv hv0
      _ ≤ residualSzegoBound b * 1 := mul_le_mul_of_nonneg_left hsq (by linarith)
      _ = residualSzegoBound b := mul_one _

theorem measurable_log_subtractedModularDensity (b c : ℝ) :
    Measurable fun v => Real.log (subtractedModularDensity b c v) :=
  Real.measurable_log.comp (measurable_subtractedModularDensity b c)

/-- `⨆ₙ ofReal(min(x, n)) = ofReal(x)`. -/
theorem iSup_ofReal_min_natCast (x : ℝ) :
    ⨆ n : ℕ, ENNReal.ofReal (min x n) = ENNReal.ofReal x := by
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  obtain ⟨n, hn⟩ := exists_nat_ge x
  exact le_iSup_of_le n (by rw [min_eq_left hn])

/-- If the negative part of `u` is not integrable, truncations from below have integrals
tending to `-∞`. -/
theorem tendsto_integral_max_neg_natCast_atBot {μ : Measure ℝ} [IsFiniteMeasure μ]
    {u : ℝ → ℝ} (hum : Measurable u) (hpos : Integrable (fun v => max (u v) 0) μ)
    (hu : ¬Integrable u μ) :
    Tendsto (fun n : ℕ => ∫ v, max (u v) (-n) ∂μ) atTop atBot := by
  set uneg : ℝ → ℝ := fun v => max (-u v) 0
  have hnegm : Measurable uneg := hum.neg.max measurable_const
  have hneg : ¬Integrable uneg μ := by
    intro h
    apply hu
    refine (hpos.sub h).congr (Eventually.of_forall fun v => ?_)
    simp only [Pi.sub_apply, uneg]
    rcases le_total 0 (u v) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h0, max_eq_left (by linarith)]
      ring
  have htrunc : ∀ n : ℕ, Integrable (fun v => min (uneg v) n) μ := fun n =>
    (integrable_const (n : ℝ)).mono' (hnegm.min measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) (Nat.cast_nonneg n))]
        exact min_le_right _ _)
  have hsplit : ∀ n : ℕ, ∫ v, max (u v) (-n) ∂μ
      = ∫ v, max (u v) 0 ∂μ - ∫ v, min (uneg v) n ∂μ := fun n => by
    rw [← integral_sub hpos (htrunc n)]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [uneg]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rcases le_total 0 (u v) with h0 | h0
    · rw [max_eq_left (by linarith), max_eq_left h0, max_eq_right (by linarith),
        min_eq_left hn]
      ring
    · rw [max_eq_right h0, max_eq_left (show (0 : ℝ) ≤ -u v by linarith)]
      rcases le_total (u v) (-n) with h1 | h1
      · rw [max_eq_right h1, min_eq_right (by linarith)]
        ring
      · rw [max_eq_left h1, min_eq_left (by linarith)]
        ring
  have hmono : Monotone fun n : ℕ => ∫ v, min (uneg v) n ∂μ := fun m n hmn =>
    integral_mono (htrunc m) (htrunc n) fun v =>
      min_le_min_left _ (Nat.cast_le.mpr hmn)
  have hunbdd : ∀ B : ℝ, ∃ n : ℕ, B ≤ ∫ v, min (uneg v) n ∂μ := by
    intro B
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    apply hneg
    refine ⟨hnegm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (f := uneg)
      (Eventually.of_forall fun v => (le_max_right _ _ : (0 : ℝ) ≤ uneg v))]
    have hsup : ∫⁻ v, ENNReal.ofReal (uneg v) ∂μ
        = ⨆ n : ℕ, ∫⁻ v, ENNReal.ofReal (min (uneg v) n) ∂μ := by
      rw [← lintegral_iSup (f := fun (n : ℕ) (v : ℝ) => ENNReal.ofReal (min (uneg v) n))
        (fun n => ENNReal.measurable_ofReal.comp (hnegm.min measurable_const))
        (fun m n hmn v => ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hmn)))]
      exact lintegral_congr fun v => (iSup_ofReal_min_natCast _).symm
    rw [hsup]
    refine lt_of_le_of_lt (iSup_le fun n => ?_) (ENNReal.ofReal_lt_top (r := B))
    rw [← ofReal_integral_eq_lintegral_ofReal (htrunc n)
      (Eventually.of_forall fun v => le_min (le_max_right _ _) (Nat.cast_nonneg n))]
    exact ENNReal.ofReal_le_ofReal (hcon n).le
  have hdiv := tendsto_atTop_atTop_of_monotone hmono hunbdd
  simp_rw [hsplit]
  have h := (tendsto_neg_atTop_atBot.comp hdiv).atBot_add
    (tendsto_const_nhds (x := ∫ v, max (u v) 0 ∂μ))
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  ring

/-- **Comparison above `π`.**  For `0 < b ≤ 1` and `c > π`, `r_{b,c}` is integrable while its
logarithmic integral is `-∞`: the positive part of `log r_{b,c}` is integrable, `log r_{b,c}` is
not, and every lower-truncated logarithmic integral tends to `-∞`, so all truncated Szegő
determinants collapse to zero. -/
theorem subtractedModularDensity_of_pi_lt {b c : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hc : Real.pi < c) :
    IntegrableOn (subtractedModularDensity b c) (Ioo (-1) 1) ∧
      IntegrableOn (fun v => max (Real.log (subtractedModularDensity b c v)) 0) (Ioo (-1) 1) ∧
      ¬IntegrableOn (fun v => Real.log (subtractedModularDensity b c v)) (Ioo (-1) 1) ∧
      Tendsto (fun n : ℕ => ∫ v in Ioo (-1) 1,
        max (Real.log (subtractedModularDensity b c v)) (-n)) atTop atBot := by
  have hbound : ∀ v ∈ Ioo (-1 : ℝ) 1, ‖subtractedModularDensity b c v‖ ≤ residualSzegoBound b :=
    fun v hv => by
      rw [Real.norm_eq_abs, abs_of_nonneg (subtractedModularDensity_nonneg hb hv)]
      exact subtractedModularDensity_le_bound hb hc.le hv
  have hint : IntegrableOn (subtractedModularDensity b c) (Ioo (-1) 1) :=
    Measure.integrableOn_of_bounded measure_Ioo_lt_top.ne
      (measurable_subtractedModularDensity b c).aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioo).mono hbound)
  have hposm : Measurable fun v => max (Real.log (subtractedModularDensity b c v)) 0 :=
    (measurable_log_subtractedModularDensity b c).max measurable_const
  have hpos : IntegrableOn (fun v => max (Real.log (subtractedModularDensity b c v)) 0)
      (Ioo (-1) 1) := by
    refine Measure.integrableOn_of_bounded (M := max (Real.log (residualSzegoBound b)) 0)
      measure_Ioo_lt_top.ne hposm.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioo).mono fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le_max ?_ le_rfl
    rcases eq_or_lt_of_le (subtractedModularDensity_nonneg (c := c) hb hv) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg (one_le_residualSzegoBound b)
    · exact Real.log_le_log h0 (subtractedModularDensity_le_bound hb hc.le hv)
  have hnot : ¬IntegrableOn (fun v => Real.log (subtractedModularDensity b c v)) (Ioo (-1) 1) := by
    rw [integrableOn_log_subtractedModularDensity_iff hb]
    rintro (h | h)
    · exact (ne_of_gt hc) h
    · linarith
  exact ⟨hint, hpos, hnot, tendsto_integral_max_neg_natCast_atBot
    (measurable_log_subtractedModularDensity b c) hpos hnot⟩

/-- **(UASA.3).**  The literal theta source has a two-sided first-atom envelope:
`C₋ e^{9|x|/2 - π e^{2|x|}} ≤ k(x) ≤ C₊ e^{9|x|/2 - π e^{2|x|}}` for all real `x`. -/
theorem thetaCuspFullSource_two_sided_envelope :
    ∃ Cm Cp : ℝ, 0 < Cm ∧ Cm ≤ Cp ∧ ∀ x : ℝ,
      Cm * Real.exp (9 * |x| / 2 - Real.pi * Real.exp (2 * |x|)) ≤ thetaCuspFullSource x ∧
        thetaCuspFullSource x ≤ Cp * Real.exp (9 * |x| / 2 - Real.pi * Real.exp (2 * |x|)) := by
  obtain ⟨C, hC⟩ := exists_abs_envelopeRemainder_le
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨Real.exp (-C), Real.exp C, Real.exp_pos _, Real.exp_le_exp.mpr (by linarith),
    fun x => ?_⟩
  have hk := thetaCuspFullSource_pos_all x
  have heq : thetaCuspFullSource x = Real.exp (envelopeRemainder x) *
      Real.exp (9 * |x| / 2 - Real.pi * Real.exp (2 * |x|)) := by
    rw [← Real.exp_add, envelopeRemainder]
    rw [show Real.log (thetaCuspFullSource x) - 9 * |x| / 2 + Real.pi * Real.exp (2 * |x|) +
      (9 * |x| / 2 - Real.pi * Real.exp (2 * |x|)) = Real.log (thetaCuspFullSource x) by ring,
      Real.exp_log hk]
  have hε := abs_le.mp (hC x)
  rw [heq]
  constructor
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hε.1) (Real.exp_pos _).le
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hε.2) (Real.exp_pos _).le

/-- **ULF-UASA-001.**  For the balanced theta contrast law `σ_b` (density `s_b`, Lemma A) and the
source Hodge contrast density `h`, the anomaly-subtracted modular density
`r_{b,c} = (h/s_b) e^{-c A_b}`, `A_b = Q^{1/b}`, satisfies `log r_{b,c} = (π - c) A_b + G_b`
with `G_b` integrable (Lemma B); `log r_{b,c} ∈ L¹(-1,1)` iff `c = π` or `b > 1`
(Theorem C); for `c < π` the density `r_{b,c}` is not integrable and for `c > π`, `b ≤ 1`, its
logarithmic integral is `-∞`; at `c = π`, `d P_b ≤ r_{b,π} ≤ D P_b`, the compactified weight
`W_b` is a bounded Szegő weight whose normalized outer function `D_b` is zero-free, bounded,
outer, unique, with injective dense non-closed multiplication range (Theorem D); and the odd
orientation amplitude `sign(θ)√W_b` is the boundary of no scalar `H²` function (Theorem E). -/
theorem unique_archimedean_szego_anomaly_subtraction :
    (∃ Cm Cp : ℝ, 0 < Cm ∧ Cm ≤ Cp ∧ ∀ x : ℝ,
      Cm * Real.exp (9 * |x| / 2 - Real.pi * Real.exp (2 * |x|)) ≤ thetaCuspFullSource x ∧
        thetaCuspFullSource x ≤ Cp * Real.exp (9 * |x| / 2 - Real.pi * Real.exp (2 * |x|))) ∧
    (∀ {b : ℝ}, 0 < b → ∀ {f : ℝ → ℝ}, Measurable f →
      ∫ v, f v ∂thetaContrastLaw b = ∫ v in Ioo (-1) 1, thetaContrastDensity b v * f v) ∧
    (∀ {b c v : ℝ}, 0 < b → v ∈ Ioo (-1) 1 → v ≠ 0 →
      Real.log (subtractedModularDensity b c v)
        = (Real.pi - c) * archimedeanAnomaly b v + anomalyRegularPart b v) ∧
    (∃ C, ∀ x, |envelopeRemainder x| ≤ C) ∧
    (∀ b : ℝ, IntegrableOn (anomalyRegularPart b) (Ioo (-1) 1)) ∧
    (∀ {b v : ℝ}, 0 < b → v ∈ Ioo (-1) 1 →
      archimedeanAnomaly b v * (1 - |v|) ^ (1 / b) = (1 + |v|) ^ (1 / b)) ∧
    (∀ {b : ℝ}, 0 < b → (IntegrableOn (archimedeanAnomaly b) (Ioo (-1) 1) ↔ 1 < b)) ∧
    (∀ {b : ℝ}, 0 < b → ∀ c : ℝ,
      (IntegrableOn (fun v => Real.log (subtractedModularDensity b c v)) (Ioo (-1) 1) ↔
        c = Real.pi ∨ 1 < b)) ∧
    (∀ {b c : ℝ}, 0 < b → c < Real.pi →
      ¬IntegrableOn (subtractedModularDensity b c) (Ioo (-1) 1)) ∧
    (∀ {b c : ℝ}, 0 < b → b ≤ 1 → Real.pi < c →
      IntegrableOn (subtractedModularDensity b c) (Ioo (-1) 1) ∧
      IntegrableOn (fun v => max (Real.log (subtractedModularDensity b c v)) 0) (Ioo (-1) 1) ∧
      ¬IntegrableOn (fun v => Real.log (subtractedModularDensity b c v)) (Ioo (-1) 1) ∧
      Tendsto (fun n : ℕ => ∫ v in Ioo (-1) 1,
        max (Real.log (subtractedModularDensity b c v)) (-n)) atTop atBot) ∧
    (∀ {b v : ℝ}, 0 < b → v ∈ Ioo (-1) 1 → v ≠ 0 →
      105 / 16 * b * thetaBalanceMass b * thetaEnvelopeUpper⁻¹ * residualProfile b v
          ≤ subtractedModularDensity b Real.pi v ∧
        subtractedModularDensity b Real.pi v
          ≤ 105 / 16 * b * thetaBalanceMass b * thetaEnvelopeLower⁻¹ * residualProfile b v) ∧
    (∀ {b v : ℝ}, 0 < b → v ∈ Ioo (-1) 1 →
      residualProfile b v
        = v ^ 2 * (1 - v ^ 2) ^ (7 / 2 : ℝ) * ((1 + |v|) / (1 - |v|)) ^ (-(9 / (4 * b)))) ∧
    (∀ {b : ℝ}, 0 < b →
      ¬IntervalIntegrable (fun θ => (residualSzegoWeight b θ)⁻¹) volume 0 Real.pi) ∧
    (∀ {b : ℝ} (hb : 0 < b),
      (∀ᵐ θ ∂volume, Tendsto (fun r => ‖(residualSzego hb).outer.fn (circleMap 0 r θ)‖ ^ (2 : ℕ))
        (𝓝[<] 1) (𝓝 (residualSzegoWeight b θ))) ∧
      (∀ᵐ z ∂circleLebesgue, ‖diskMultiplierBoundaryFun (residualSzego hb).outer z‖ ^ (2 : ℕ) =
        residualSzegoWeight b (Complex.arg (z : ℂ))) ∧
      (∃ s : ℝ, 0 < s ∧ (residualSzego hb).outer.fn 0 = s) ∧
      (∀ z, (residualSzego hb).outer.fn z ≠ 0) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1,
        ‖(residualSzego hb).outer.fn z‖ ≤ Real.sqrt (residualSzegoBound b)) ∧
      (∀ z : ℂ, ‖z‖ < 1 → hardyFun (hardyOf (residualSzego hb).outer) z =
        (residualSzego hb).outer.fn z) ∧
      IsOuterDiskMultiplier (residualSzego hb).outer ∧
      Function.Injective (hardyMul (residualSzego hb).outer) ∧
      DenseRange (hardyMul (residualSzego hb).outer) ∧
      ¬IsClosed (Set.range (hardyMul (residualSzego hb).outer)) ∧
      (∀ ψ : DiskMultiplier, IsOuterDiskMultiplier ψ →
        (∀ᵐ z ∂circleLebesgue, ‖diskMultiplierBoundaryFun ψ z‖ ^ (2 : ℕ) =
          residualSzegoWeight b (Complex.arg (z : ℂ))) →
        ∀ s : ℝ, 0 < s → ψ.fn 0 = s →
          ∀ z ∈ Metric.ball (0 : ℂ) 1, ψ.fn z = (residualSzego hb).outer.fn z)) ∧
    (∀ {b θ : ℝ}, 0 < b → angularContrast θ ≠ 0 →
      orientationAmplitude b θ ^ 2 = residualSzegoWeight b θ) ∧
    (∀ {b : ℝ}, 0 < b → ¬∃ f : HardyDisk, ∀ᵐ z ∂circleLebesgue,
      (hardyDiskBoundary f : Circle → ℂ) z =
        (orientationAmplitude b (Complex.arg (z : ℂ)) : ℂ)) :=
  ⟨thetaCuspFullSource_two_sided_envelope, fun hb _ hf => integral_thetaContrastLaw hb hf,
    fun hb hv hv0 => log_subtractedModularDensity hb hv hv0, exists_abs_envelopeRemainder_le,
    integrableOn_anomalyRegularPart, fun hb hv => archimedeanAnomaly_mul_rpow hb hv,
    fun hb => integrableOn_archimedeanAnomaly_iff_one_lt hb,
    fun hb c => integrableOn_log_subtractedModularDensity_iff hb c,
    fun hb hc => not_integrableOn_subtractedModularDensity hb hc,
    fun hb hb1 hc => subtractedModularDensity_of_pi_lt hb hb1 hc,
    fun hb hv hv0 => subtractedModularDensity_pi_bounds hb hv hv0,
    fun hb hv => residualProfile_eq_rpow hb hv,
    fun hb => not_intervalIntegrable_inv_residualSzegoWeight hb,
    fun hb => residual_szego_factor hb,
    fun hb hθ => orientationAmplitude_sq hb hθ,
    fun hb => not_exists_hardyDisk_boundary_orientationAmplitude hb⟩

end GaloisForLFunctions.HTGeometry
