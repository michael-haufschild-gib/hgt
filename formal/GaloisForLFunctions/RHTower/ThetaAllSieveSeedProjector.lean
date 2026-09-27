import GaloisForLFunctions.RHTower.ThetaTranslationMeasureGauge

/-!
# Cofinal prime deletion recovers the hidden translation measure

For finite translation measures `ν₁, ν₂` with `∫ e^{|s|/2} < ∞` and the signed gauge
`g = ∫ k(· + s) d(ν₁ - ν₂)(s)` of the completed theta source:

* **All-sieve theorem** (`allSieve_completelyMonotone_iff`): every deleted flux `b_{D_S g}` is
  completely monotone iff `ν₁ - ν₂ ≥ 0`.
* **Two-charge rigidity.**  All-sieve positivity, the ordinary mass and both critical charges
  `L_{±1/2}` of `k` force `ν₁ - ν₂ = δ₀` and `g = k`; for even `g` the `+1/2` charge suffices.
* **Sharp failure without the reflected charge.**  `μ_p = δ_{-log p}/(√p+1) + √p δ_{log p}/(√p+1)`
  is a positive probability measure passing every sieve with the mass and `+1/2` charge of `k`,
  a strictly larger `-1/2` charge, and an exact off-line zero at `1/4 + iπ/(2 log p)`.
* **Gap law.**  For positive symmetric probability measures with shift gap `|s| ≥ L`,
  `|M(w) - 1| ≤ C_{L,σ} δ` on `|Re w| ≤ σ` at all heights, with finite `C_{L,σ}`.
* **The gap is essential.**  `μ_ε = (1-θ_ε)δ₀ + (θ_ε/2)(δ_ε + δ_{-ε})` has a zero at `σ + iπ/ε`,
  charge `→ 1`, and `T_ε² (M(1/2) - 1) → π²/16`.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-! ## Boundary charges of translation mixtures -/

theorem integrable_exp_mul_of_abs_half {ρ : Measure ℝ}
    (hρ : Integrable (fun s => Real.exp (|s| / 2)) ρ) {w : ℝ} (hw : |w| ≤ 1 / 2) :
    Integrable (fun s => Real.exp (-(w * s))) ρ :=
  Integrable.mono' hρ (by fun_prop : Continuous fun s : ℝ => Real.exp (-(w * s))).aestronglyMeasurable
    (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr ?_
      calc -(w * s) ≤ |w * s| := neg_le_abs _
        _ = |w| * |s| := abs_mul _ _
        _ ≤ 1 / 2 * |s| := by gcongr
        _ = |s| / 2 := by ring)

/-- The three anchors of a translation mixture: ordinary mass and both critical charges. -/
theorem thetaMeasureGauge_anchors {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : Integrable (fun s => Real.exp (|s| / 2)) ρ) :
    (∫ x, thetaMeasureGauge ρ thetaCuspFullSource x) =
        (ρ univ).toReal * ∫ x, thetaCuspFullSource x ∧
      (∫ x, Real.exp (x / 2) * thetaMeasureGauge ρ thetaCuspFullSource x) =
        (∫ s, Real.exp (-(s / 2)) ∂ρ) * ∫ x, Real.exp (x / 2) * thetaCuspFullSource x ∧
      (∫ x, Real.exp (-(x / 2)) * thetaMeasureGauge ρ thetaCuspFullSource x) =
        (∫ s, Real.exp (s / 2) ∂ρ) * ∫ x, Real.exp (-(x / 2)) * thetaCuspFullSource x := by
  have h0 := (integral_exp_mul_thetaMeasureGauge (ν := ρ) (w := 0)
    (integrable_exp_mul_of_abs_half hρ (by norm_num))).2
  have h1 := (integral_exp_mul_thetaMeasureGauge (ν := ρ) (w := 1 / 2)
    (integrable_exp_mul_of_abs_half hρ (by norm_num [abs_of_pos]))).2
  have h2 := (integral_exp_mul_thetaMeasureGauge (ν := ρ) (w := -(1 / 2))
    (integrable_exp_mul_of_abs_half hρ (by norm_num [abs_of_pos]))).2
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, integral_const, smul_eq_mul,
    mul_one] at h0
  have e1 : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  have e2 : ∀ x : ℝ, -(1 / 2) * x = -(x / 2) := fun x => by ring
  have e3 : ∀ x : ℝ, -(-(x / 2)) = x / 2 := fun x => by ring
  simp only [e1, e2, e3] at h1 h2
  exact ⟨h0, h1, h2⟩

theorem integral_cosh_half_eq {ρ : Measure ℝ} (hρ : Integrable (fun s => Real.exp (|s| / 2)) ρ) :
    (∫ s, Real.cosh (s / 2) ∂ρ) =
      ((∫ s, Real.exp (s / 2) ∂ρ) + ∫ s, Real.exp (-(s / 2)) ∂ρ) / 2 := by
  have ha := integrable_exp_mul_of_abs_half hρ (w := -(1 / 2)) (by norm_num [abs_of_pos])
  have hb := integrable_exp_mul_of_abs_half hρ (w := 1 / 2) (by norm_num [abs_of_pos])
  rw [← integral_add (ha.congr (ae_of_all _ fun s => by simp only; ring_nf))
    (hb.congr (ae_of_all _ fun s => by simp only; ring_nf)), ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [Real.cosh_eq]

theorem measure_eq_dirac_of_cosh_half {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun s => Real.exp (|s| / 2)) ρ) (h : (∫ s, Real.cosh (s / 2) ∂ρ) = 1) :
    ρ = Measure.dirac 0 := by
  have hcint : Integrable (fun s => Real.cosh (s / 2)) ρ :=
    Integrable.mono' hρ (by fun_prop : Continuous fun s : ℝ => Real.cosh (s / 2)).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _), Real.cosh_eq]
        have h1 : Real.exp (s / 2) ≤ Real.exp (|s| / 2) :=
          Real.exp_le_exp.mpr (by have := le_abs_self s; linarith)
        have h2 : Real.exp (-(s / 2)) ≤ Real.exp (|s| / 2) :=
          Real.exp_le_exp.mpr (by have := neg_abs_le s; linarith)
        linarith)
  have hzero : (∫ s, (Real.cosh (s / 2) - 1) ∂ρ) = 0 := by
    rw [integral_sub hcint (integrable_const 1), h]
    simp
  have hnn : 0 ≤ fun s : ℝ => Real.cosh (s / 2) - 1 := fun s => by
    simp only [Pi.zero_apply]
    linarith [Real.one_le_cosh (s / 2)]
  have hae := (integral_eq_zero_iff_of_nonneg hnn (hcint.sub (integrable_const 1))).mp hzero
  refine measure_eq_dirac_zero_of_ae ?_
  filter_upwards [hae] with s hs
  simp only [Pi.zero_apply] at hs
  by_contra hne
  have := Real.one_lt_cosh.mpr (div_ne_zero hne two_ne_zero)
  linarith

theorem thetaMeasureGauge_dirac_zero : thetaMeasureGauge (Measure.dirac 0) thetaCuspFullSource =
    thetaCuspFullSource := by
  funext x
  simp [thetaMeasureGauge]

/-- **Two-charge rigidity.**  All-sieve complete monotonicity, the ordinary mass of `k` and both
critical charges of `k` force the translation measure to be `δ₀` and the source to be `k`. -/
theorem allSieve_two_charge_rigidity {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : Integrable (fun s => Real.exp (|s| / 2)) ν₁)
    (h₂ : Integrable (fun s => Real.exp (|s| / 2)) ν₂)
    (hall : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      CompletelyMonotoneOn (thetaNormalizedFlux
        (thetaPrimeDeletion S (thetaSignedMeasureGauge ν₁ ν₂))))
    (hmass : ∫ x, thetaSignedMeasureGauge ν₁ ν₂ x = ∫ x, thetaCuspFullSource x)
    (hplus : ∫ x, Real.exp (x / 2) * thetaSignedMeasureGauge ν₁ ν₂ x =
      ∫ x, Real.exp (x / 2) * thetaCuspFullSource x)
    (hminus : ∫ x, Real.exp (-(x / 2)) * thetaSignedMeasureGauge ν₁ ν₂ x =
      ∫ x, Real.exp (-(x / 2)) * thetaCuspFullSource x) :
    ν₂ ≤ ν₁ ∧ ν₁ - ν₂ = Measure.dirac 0 ∧
      thetaSignedMeasureGauge ν₁ ν₂ = thetaCuspFullSource := by
  have hle := (allSieve_completelyMonotone_iff h₁ h₂).mp hall
  haveI : IsFiniteMeasure (ν₁ - ν₂) := isFiniteMeasure_of_le ν₁ Measure.sub_le
  have hρ : Integrable (fun s => Real.exp (|s| / 2)) (ν₁ - ν₂) := h₁.mono_measure Measure.sub_le
  have hg := thetaSignedMeasureGauge_of_le hle
  rw [hg] at hmass hplus hminus
  obtain ⟨a0, a1, a2⟩ := thetaMeasureGauge_anchors hρ
  have hk0 : 0 < ∫ x, thetaCuspFullSource x := by
    simpa using integral_exp_mul_thetaCuspFullSource_pos 0
  have hk1 : 0 < ∫ x, Real.exp (x / 2) * thetaCuspFullSource x := by
    have := integral_exp_mul_thetaCuspFullSource_pos (1 / 2)
    simpa only [show ∀ x : ℝ, 1 / 2 * x = x / 2 from fun x => by ring] using this
  have hk2 : 0 < ∫ x, Real.exp (-(x / 2)) * thetaCuspFullSource x := by
    have := integral_exp_mul_thetaCuspFullSource_pos (-(1 / 2))
    simpa only [show ∀ x : ℝ, -(1 / 2) * x = -(x / 2) from fun x => by ring] using this
  have hm : ((ν₁ - ν₂) univ).toReal = 1 := by
    rw [a0] at hmass; exact (mul_eq_right₀ hk0.ne').mp hmass
  have hp : (∫ s, Real.exp (-(s / 2)) ∂(ν₁ - ν₂)) = 1 := by
    rw [a1] at hplus; exact (mul_eq_right₀ hk1.ne').mp hplus
  have hn : (∫ s, Real.exp (s / 2) ∂(ν₁ - ν₂)) = 1 := by
    rw [a2] at hminus; exact (mul_eq_right₀ hk2.ne').mp hminus
  haveI : IsProbabilityMeasure (ν₁ - ν₂) := ⟨by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), hm, ENNReal.ofReal_one]⟩
  have hdirac := measure_eq_dirac_of_cosh_half hρ (by rw [integral_cosh_half_eq hρ, hp, hn]; norm_num)
  refine ⟨hle, hdirac, ?_⟩
  rw [hg, hdirac, thetaMeasureGauge_dirac_zero]

/-- **Even sources need one charge.**  For an even signed gauge, all-sieve complete
monotonicity, ordinary mass and the `+1/2` charge already force `g = k`. -/
theorem allSieve_even_rigidity {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : Integrable (fun s => Real.exp (|s| / 2)) ν₁)
    (h₂ : Integrable (fun s => Real.exp (|s| / 2)) ν₂)
    (hall : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      CompletelyMonotoneOn (thetaNormalizedFlux
        (thetaPrimeDeletion S (thetaSignedMeasureGauge ν₁ ν₂))))
    (heven : ∀ x, thetaSignedMeasureGauge ν₁ ν₂ (-x) = thetaSignedMeasureGauge ν₁ ν₂ x)
    (hmass : ∫ x, thetaSignedMeasureGauge ν₁ ν₂ x = ∫ x, thetaCuspFullSource x)
    (hplus : ∫ x, Real.exp (x / 2) * thetaSignedMeasureGauge ν₁ ν₂ x =
      ∫ x, Real.exp (x / 2) * thetaCuspFullSource x) :
    ν₂ ≤ ν₁ ∧ ν₁ - ν₂ = Measure.dirac 0 ∧
      thetaSignedMeasureGauge ν₁ ν₂ = thetaCuspFullSource := by
  refine allSieve_two_charge_rigidity h₁ h₂ hall hmass hplus ?_
  have hrefl : ∀ f : ℝ → ℝ, (∀ x, f (-x) = f x) →
      (∫ x, Real.exp (-(x / 2)) * f x) = ∫ x, Real.exp (x / 2) * f x := by
    intro f hf
    rw [← integral_neg_eq_self (fun x => Real.exp (x / 2) * f x) volume]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hf]
    ring_nf
  rw [hrefl _ heven, hrefl _ thetaCuspFullSource_neg, hplus]

/-! ## Atomic translation measures -/

theorem integrable_smul_dirac {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (c x : ℝ) :
    Integrable f (ENNReal.ofReal c • Measure.dirac x) :=
  (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

theorem integral_smul_dirac {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    ∫ y, f y ∂(ENNReal.ofReal c • Measure.dirac x) = c • f x := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hc]

instance isFiniteMeasure_smul_dirac (c x : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal c • Measure.dirac x) :=
  ⟨by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact ENNReal.ofReal_lt_top⟩

/-! ## Sharp failure without the reflected charge -/

/-- The positive two-shift measure `μ_p = a δ_{-log p} + b δ_{log p}`, `a = 1/(√p+1)`,
`b = √p/(√p+1)`. -/
noncomputable def thetaTwoShiftCounterMeasure (p : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 / (Real.sqrt p + 1)) • Measure.dirac (-Real.log p) +
    ENNReal.ofReal (Real.sqrt p / (Real.sqrt p + 1)) • Measure.dirac (Real.log p)

theorem integral_thetaTwoShiftCounterMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (p : ℕ) (f : ℝ → E) :
    ∫ s, f s ∂thetaTwoShiftCounterMeasure p =
      (1 / (Real.sqrt p + 1)) • f (-Real.log p) +
        (Real.sqrt p / (Real.sqrt p + 1)) • f (Real.log p) := by
  unfold thetaTwoShiftCounterMeasure
  rw [integral_add_measure (integrable_smul_dirac _ _ _) (integrable_smul_dirac _ _ _),
    integral_smul_dirac _ (by positivity), integral_smul_dirac _ (by positivity)]

theorem integrable_thetaTwoShiftCounterMeasure (p : ℕ) (f : ℝ → ℝ) :
    Integrable f (thetaTwoShiftCounterMeasure p) :=
  integrable_add_measure.mpr ⟨integrable_smul_dirac _ _ _, integrable_smul_dirac _ _ _⟩

theorem sqrt_nat_eq_exp_half_log {p : ℕ} (hp : 0 < p) : Real.sqrt p = Real.exp (Real.log p / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast hp)]
  ring_nf

/-- The off-line point `1/4 + iπ/(2 log p)`. -/
noncomputable def thetaTwoShiftZero (p : ℕ) : ℂ :=
  ((1 / 4 : ℝ) : ℂ) + ((Real.pi / (2 * Real.log p) : ℝ) : ℂ) * I

theorem thetaTwoShiftZero_re (p : ℕ) : (thetaTwoShiftZero p).re = 1 / 4 := by
  unfold thetaTwoShiftZero
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]

theorem thetaTwoShiftZero_mul_log {p : ℕ} (hL : Real.log p ≠ 0) :
    thetaTwoShiftZero p * ((Real.log p : ℝ) : ℂ) =
      ((Real.log p / 4 : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I := by
  have h1 : (1 / 4 : ℝ) * Real.log p = Real.log p / 4 := by ring
  have h2 : Real.pi / (2 * Real.log p) * Real.log p = Real.pi / 2 := by field_simp
  unfold thetaTwoShiftZero
  rw [add_mul, mul_right_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul, h1, h2]

/-- The two-shift countermodel: a positive probability measure whose gauge is positive, passes
every finite sieve, keeps the ordinary mass and the `+1/2` charge of `k`, has a strictly larger
`-1/2` charge, and whose Mellin multiplier and Mellin transform vanish at the off-line point
`1/4 + iπ/(2 log p)`. -/
theorem thetaTwoShiftCounterMeasure_properties {p : ℕ} (hp : 2 ≤ p) :
    IsProbabilityMeasure (thetaTwoShiftCounterMeasure p) ∧
    (∀ x, thetaMeasureGauge (thetaTwoShiftCounterMeasure p) thetaCuspFullSource x =
      1 / (Real.sqrt p + 1) * thetaCuspFullSource (x - Real.log p) +
        Real.sqrt p / (Real.sqrt p + 1) * thetaCuspFullSource (x + Real.log p)) ∧
    (∀ x, 0 < thetaMeasureGauge (thetaTwoShiftCounterMeasure p) thetaCuspFullSource x) ∧
    (∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → CompletelyMonotoneOn (thetaNormalizedFlux
      (thetaPrimeDeletion S (thetaMeasureGauge (thetaTwoShiftCounterMeasure p)
        thetaCuspFullSource)))) ∧
    (∫ x, thetaMeasureGauge (thetaTwoShiftCounterMeasure p) thetaCuspFullSource x) =
      ∫ x, thetaCuspFullSource x ∧
    (∫ x, Real.exp (x / 2) * thetaMeasureGauge (thetaTwoShiftCounterMeasure p)
      thetaCuspFullSource x) = ∫ x, Real.exp (x / 2) * thetaCuspFullSource x ∧
    (∫ x, Real.exp (-(x / 2)) * thetaCuspFullSource x) <
      ∫ x, Real.exp (-(x / 2)) * thetaMeasureGauge (thetaTwoShiftCounterMeasure p)
        thetaCuspFullSource x ∧
    (∫ s, Complex.exp (-(thetaTwoShiftZero p * s)) ∂thetaTwoShiftCounterMeasure p) = 0 ∧
    (∫ x : ℝ, Complex.exp (thetaTwoShiftZero p * x) *
      (thetaMeasureGauge (thetaTwoShiftCounterMeasure p) thetaCuspFullSource x : ℂ)) = 0 := by
  have hp0 : 0 < p := by omega
  have hL0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have ha1 : 1 < Real.sqrt p := Real.lt_sqrt (by norm_num) |>.mpr (by
    rw [one_pow]; exact_mod_cast (by omega : 1 < p))
  have haL : Real.sqrt p = Real.exp (Real.log p / 2) := sqrt_nat_eq_exp_half_log hp0
  have hainv : Real.exp (-(Real.log p / 2)) = (Real.sqrt p)⁻¹ := by rw [haL, Real.exp_neg]
  have hμ := integrable_thetaTwoShiftCounterMeasure p
  haveI : IsFiniteMeasure (thetaTwoShiftCounterMeasure p) := by
    unfold thetaTwoShiftCounterMeasure; infer_instance
  have hprob : IsProbabilityMeasure (thetaTwoShiftCounterMeasure p) := by
    constructor
    unfold thetaTwoShiftCounterMeasure
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add (by positivity)
      (by positivity), ← add_div, add_comm 1, div_self (by linarith), ENNReal.ofReal_one]
  have hmom : Integrable (fun s => Real.exp (|s| / 2)) (thetaTwoShiftCounterMeasure p) := hμ _
  obtain ⟨a0, a1, a2⟩ := thetaMeasureGauge_anchors hmom
  have hgauge : ∀ x, thetaMeasureGauge (thetaTwoShiftCounterMeasure p) thetaCuspFullSource x =
      1 / (Real.sqrt p + 1) * thetaCuspFullSource (x - Real.log p) +
        Real.sqrt p / (Real.sqrt p + 1) * thetaCuspFullSource (x + Real.log p) := by
    intro x
    unfold thetaMeasureGauge
    rw [integral_thetaTwoShiftCounterMeasure, smul_eq_mul, smul_eq_mul, ← sub_eq_add_neg]
  have hplus : (∫ s, Real.exp (-(s / 2)) ∂thetaTwoShiftCounterMeasure p) = 1 := by
    rw [integral_thetaTwoShiftCounterMeasure, smul_eq_mul, smul_eq_mul, neg_div, neg_neg,
      ← haL, hainv]
    have : (0 : ℝ) < Real.sqrt p := by linarith
    field_simp
  have hminus : 1 < ∫ s, Real.exp (s / 2) ∂thetaTwoShiftCounterMeasure p := by
    rw [integral_thetaTwoShiftCounterMeasure, smul_eq_mul, smul_eq_mul, ← haL, neg_div, hainv]
    have ha0 : (0 : ℝ) < Real.sqrt p := by linarith
    rw [show 1 / (Real.sqrt p + 1) * (Real.sqrt p)⁻¹ + Real.sqrt p / (Real.sqrt p + 1) *
        Real.sqrt p = (1 + Real.sqrt p ^ 3) / (Real.sqrt p * (Real.sqrt p + 1)) by
      field_simp, one_lt_div (by positivity)]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < Real.sqrt p - 1)
      (by positivity : (0 : ℝ) < Real.sqrt p * (Real.sqrt p + 1))]
  have hk2 : 0 < ∫ x, Real.exp (-(x / 2)) * thetaCuspFullSource x := by
    have := integral_exp_mul_thetaCuspFullSource_pos (-(1 / 2))
    simpa only [show ∀ x : ℝ, -(1 / 2) * x = -(x / 2) from fun x => by ring] using this
  have hM : (∫ s, Complex.exp (-(thetaTwoShiftZero p * s)) ∂thetaTwoShiftCounterMeasure p) = 0 := by
    rw [integral_thetaTwoShiftCounterMeasure]
    simp only [Complex.real_smul]
    have hz := thetaTwoShiftZero_mul_log (p := p) hL0.ne'
    have e1 : -(thetaTwoShiftZero p * ((-Real.log p : ℝ) : ℂ)) =
        ((Real.log p / 4 : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I := by
      rw [Complex.ofReal_neg, mul_neg, neg_neg, hz]
    have e2 : -(thetaTwoShiftZero p * ((Real.log p : ℝ) : ℂ)) =
        ((-(Real.log p / 4) : ℝ) : ℂ) + ((-(Real.pi / 2) : ℝ) : ℂ) * I := by
      rw [hz, Complex.ofReal_neg, Complex.ofReal_neg]
      ring
    rw [e1, e2, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    have hI : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
      push_cast; exact Complex.exp_pi_div_two_mul_I
    have hI' : Complex.exp (((-(Real.pi / 2)) : ℝ) * I) = -I := by
      push_cast; rw [neg_mul, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
    rw [hI, hI']
    have h4 : Real.exp (Real.log p / 4) = Real.sqrt p * Real.exp (-(Real.log p / 4)) := by
      rw [haL, ← Real.exp_add]; ring_nf
    rw [h4]
    have hs : (0 : ℝ) < Real.sqrt p + 1 := by linarith
    rw [show (((1 / (Real.sqrt p + 1)) : ℝ) : ℂ) * (((Real.sqrt p * Real.exp (-(Real.log p / 4)) :
        ℝ) : ℂ) * I) = (((Real.sqrt p / (Real.sqrt p + 1)) : ℝ) : ℂ) *
        ((Real.exp (-(Real.log p / 4)) : ℝ) : ℂ) * I by
      rw [← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul]
      congr 2
      field_simp]
    ring
  refine ⟨hprob, hgauge, fun x => ?_, fun S hS =>
    completelyMonotoneOn_thetaPrimeDeletion_thetaMeasureGauge hmom hS, ?_, ?_, ?_, hM, ?_⟩
  · rw [hgauge]
    have := thetaCuspFullSource_pos_all (x - Real.log p)
    have := thetaCuspFullSource_pos_all (x + Real.log p)
    have : (0 : ℝ) < Real.sqrt p := by linarith
    positivity
  · rw [a0, measure_univ, ENNReal.toReal_one, one_mul]
  · rw [a1, hplus, one_mul]
  · rw [a2]
    exact lt_mul_of_one_lt_left hk2 hminus
  · rw [integral_cexp_mul_thetaMeasureGauge hmom (by rw [thetaTwoShiftZero_re]; norm_num), hM,
      zero_mul]

/-! ## The quantitative gap law -/

/-- The gap ratio `(cosh(σu) + 1)/(cosh(u/2) - 1)`. -/
noncomputable def thetaGapRatio (σ u : ℝ) : ℝ := (Real.cosh (σ * u) + 1) / (Real.cosh (u / 2) - 1)

/-- The gap constant `C_{L,σ} = sup_{u ≥ L} (cosh(σu) + 1)/(cosh(u/2) - 1)`. -/
noncomputable def thetaGapConstant (L σ : ℝ) : ℝ := sSup (thetaGapRatio σ '' Ici L)

theorem thetaGapRatio_le {L σ u : ℝ} (hL : 0 < L) (hσ : |σ| ≤ 1 / 2) (hu : L ≤ u) :
    thetaGapRatio σ u ≤ 2 * Real.cosh (L / 2) / (Real.cosh (L / 2) - 1) := by
  have hL1 : 1 < Real.cosh (L / 2) := Real.one_lt_cosh.mpr (by positivity)
  have hcu : Real.cosh (L / 2) ≤ Real.cosh (u / 2) :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_pos (by positivity), abs_of_pos (by linarith)]; linarith)
  have hσu : Real.cosh (σ * u) ≤ Real.cosh (u / 2) := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < u), abs_of_pos (by linarith : (0 : ℝ) < u / 2)]
    nlinarith
  have hden : 0 < Real.cosh (u / 2) - 1 := by linarith
  unfold thetaGapRatio
  rw [div_le_div_iff₀ hden (by linarith)]
  nlinarith [Real.one_le_cosh (u / 2)]

theorem bddAbove_thetaGapRatio {L σ : ℝ} (hL : 0 < L) (hσ : |σ| ≤ 1 / 2) :
    BddAbove (thetaGapRatio σ '' Ici L) :=
  ⟨_, by rintro _ ⟨u, hu, rfl⟩; exact thetaGapRatio_le hL hσ hu⟩

/-- The gap constant is finite: `C_{L,σ} ≤ 2 cosh(L/2)/(cosh(L/2) - 1)`. -/
theorem thetaGapConstant_le {L σ : ℝ} (hL : 0 < L) (hσ : |σ| ≤ 1 / 2) :
    thetaGapConstant L σ ≤ 2 * Real.cosh (L / 2) / (Real.cosh (L / 2) - 1) :=
  csSup_le (Set.image_nonempty.mpr nonempty_Ici) (by
    rintro _ ⟨u, hu, rfl⟩; exact thetaGapRatio_le hL hσ hu)

theorem thetaGapRatio_le_constant {L σ u : ℝ} (hL : 0 < L) (hσ : |σ| ≤ 1 / 2) (hu : L ≤ u) :
    thetaGapRatio σ u ≤ thetaGapConstant L σ :=
  le_csSup (bddAbove_thetaGapRatio hL hσ) ⟨u, hu, rfl⟩

theorem thetaGapConstant_nonneg {L σ : ℝ} (hL : 0 < L) (hσ : |σ| ≤ 1 / 2) :
    0 ≤ thetaGapConstant L σ := by
  refine le_trans ?_ (thetaGapRatio_le_constant hL hσ (le_refl L))
  have hL1 : 1 < Real.cosh (L / 2) := Real.one_lt_cosh.mpr (by positivity)
  unfold thetaGapRatio
  exact div_nonneg (by linarith [Real.one_le_cosh (σ * L)]) (by linarith)

theorem integrable_cosh_half {μ : Measure ℝ} (hμ : Integrable (fun s => Real.exp (|s| / 2)) μ) :
    Integrable (fun s => Real.cosh (s / 2)) μ :=
  Integrable.mono' hμ (by fun_prop : Continuous fun s : ℝ => Real.cosh (s / 2)).aestronglyMeasurable
    (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _), Real.cosh_eq]
      have h1 : Real.exp (s / 2) ≤ Real.exp (|s| / 2) :=
        Real.exp_le_exp.mpr (by have := le_abs_self s; linarith)
      have h2 : Real.exp (-(s / 2)) ≤ Real.exp (|s| / 2) :=
        Real.exp_le_exp.mpr (by have := neg_abs_le s; linarith)
      linarith)

/-- **Quantitative gap law.**  For a positive symmetric probability translation measure whose
nonzero shifts satisfy `|s| ≥ L > 0`, and every `w` with `|Re w| ≤ σ ≤ 1/2` at all heights,
`|M(w) - 1| ≤ C_{L,σ} δ` with `δ = ∫ (cosh(s/2) - 1) dμ`. -/
theorem norm_measureMultiplier_sub_one_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun s => Real.exp (|s| / 2)) μ) (hsym : μ.map Neg.neg = μ) {L σ : ℝ}
    (hL : 0 < L) (hσ : |σ| ≤ 1 / 2) (hgap : ∀ᵐ s ∂μ, s = 0 ∨ L ≤ |s|) {w : ℂ} (hw : |w.re| ≤ σ) :
    ‖(∫ s, Complex.exp (-(w * s)) ∂μ) - 1‖ ≤
      thetaGapConstant L σ * ((∫ s, Real.cosh (s / 2) ∂μ) - 1) := by
  set C := thetaGapConstant L σ
  have hC := thetaGapConstant_nonneg hL hσ
  have hexp_int : ∀ z : ℂ, |z.re| ≤ 1 / 2 → Integrable (fun s : ℝ => Complex.exp (z * s)) μ := by
    intro z hz
    refine Integrable.mono' hμ (by fun_prop : Continuous fun s : ℝ =>
      Complex.exp (z * s)).aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc z.re * s ≤ |z.re * s| := le_abs_self _
      _ = |z.re| * |s| := abs_mul _ _
      _ ≤ 1 / 2 * |s| := by gcongr
      _ = |s| / 2 := by ring
  have hwσ : |w.re| ≤ 1 / 2 := hw.trans ((le_abs_self σ).trans hσ)
  have hsymint : (∫ s, Complex.exp (-(w * s)) ∂μ) = ∫ s, Complex.exp (w * s) ∂μ := by
    conv_rhs => rw [← hsym]
    rw [integral_map measurable_neg.aemeasurable (by fun_prop : Continuous fun s : ℝ =>
      Complex.exp (w * s)).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    push_cast
    ring_nf
  have hcosh : (∫ s, Complex.exp (-(w * s)) ∂μ) = ∫ s, Complex.cosh (w * s) ∂μ := by
    have hneg : Integrable (fun s : ℝ => Complex.exp (-(w * s))) μ := by
      have := hexp_int (-w) (by rwa [Complex.neg_re, abs_neg])
      exact this.congr (ae_of_all _ fun s => by simp only [neg_mul])
    have h2 : (∫ s, Complex.exp (-(w * s)) ∂μ) =
        ((∫ s, Complex.exp (w * s) ∂μ) + ∫ s, Complex.exp (-(w * s)) ∂μ) / 2 := by
      rw [← hsymint]; ring
    rw [h2, ← integral_add (hexp_int w hwσ) hneg, ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [Complex.cosh]
  have hcint : Integrable (fun s : ℝ => Complex.cosh (w * s)) μ := by
    have hneg : Integrable (fun s : ℝ => Complex.exp (-(w * s))) μ := by
      have := hexp_int (-w) (by rwa [Complex.neg_re, abs_neg])
      exact this.congr (ae_of_all _ fun s => by simp only [neg_mul])
    exact ((hexp_int w hwσ).add hneg).div_const 2 |>.congr (ae_of_all _ fun s => by
      simp only [Pi.add_apply, Complex.cosh])
  have hsub : (∫ s, Complex.exp (-(w * s)) ∂μ) - 1 = ∫ s, (Complex.cosh (w * s) - 1) ∂μ := by
    rw [hcosh, integral_sub hcint (integrable_const 1)]
    simp
  have hpt : ∀ᵐ (s : ℝ) ∂μ, ‖Complex.cosh (w * s) - 1‖ ≤ C * (Real.cosh (s / 2) - 1) := by
    filter_upwards [hgap] with s hs
    rcases hs with rfl | hs
    · simp
    · have hsL : 0 < |s| := lt_of_lt_of_le hL hs
      have hs0 : s ≠ 0 := abs_pos.mp hsL
      have hden : 0 < Real.cosh (s / 2) - 1 := by
        linarith [Real.one_lt_cosh.mpr (div_ne_zero hs0 two_ne_zero)]
      have h1 : ‖Complex.cosh (w * s) - 1‖ ≤ Real.cosh (σ * |s|) + 1 := by
        calc ‖Complex.cosh (w * s) - 1‖ ≤ ‖Complex.cosh (w * s)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ Real.cosh ((w * s).re) + 1 := by
              rw [norm_one]; gcongr; exact norm_cosh_le_cosh_re _
          _ ≤ Real.cosh (σ * |s|) + 1 := by
              gcongr
              refine Real.cosh_le_cosh.mpr ?_
              simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
              rw [abs_mul, abs_mul, abs_abs]
              exact mul_le_mul_of_nonneg_right (hw.trans (le_abs_self σ)) (abs_nonneg _)
      have h2 : Real.cosh (σ * |s|) + 1 ≤ C * (Real.cosh (s / 2) - 1) := by
        have hr := thetaGapRatio_le_constant hL hσ hs
        unfold thetaGapRatio at hr
        rw [show |s| / 2 = |s / 2| by rw [abs_div, abs_two], Real.cosh_abs,
          div_le_iff₀ hden] at hr
        exact hr
      exact h1.trans h2
  have hint1 : Integrable (fun s : ℝ => ‖Complex.cosh (w * s) - 1‖) μ :=
    (hcint.sub (integrable_const 1)).norm
  have hint2 : Integrable (fun s : ℝ => C * (Real.cosh (s / 2) - 1)) μ :=
    ((integrable_cosh_half hμ).sub (integrable_const 1)).const_mul C
  rw [hsub]
  calc ‖∫ s, (Complex.cosh (w * s) - 1) ∂μ‖ ≤ ∫ s, ‖Complex.cosh (w * s) - 1‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ s, C * (Real.cosh (s / 2) - 1) ∂μ := integral_mono_ae hint1 hint2 hpt
    _ = C * ((∫ s, Real.cosh (s / 2) ∂μ) - 1) := by
        rw [integral_const_mul, integral_sub (integrable_cosh_half hμ) (integrable_const 1)]
        simp

/-- Under the gap law, `C_{L,σ} δ < 1` excludes zeros of the multiplier in `|Re w| ≤ σ`. -/
theorem measureMultiplier_ne_zero_of_gap {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun s => Real.exp (|s| / 2)) μ) (hsym : μ.map Neg.neg = μ) {L σ : ℝ}
    (hL : 0 < L) (hσ : |σ| ≤ 1 / 2) (hgap : ∀ᵐ s ∂μ, s = 0 ∨ L ≤ |s|)
    (hδ : thetaGapConstant L σ * ((∫ s, Real.cosh (s / 2) ∂μ) - 1) < 1) {w : ℂ}
    (hw : |w.re| ≤ σ) : (∫ s, Complex.exp (-(w * s)) ∂μ) ≠ 0 := by
  intro h
  have := norm_measureMultiplier_sub_one_le hμ hsym hL hσ hgap hw
  rw [h, zero_sub, norm_neg, norm_one] at this
  linarith

/-! ## The gap condition is essential -/

/-- `θ_ε = 1/(1 + cosh(εσ))`. -/
noncomputable def thetaGapFamilyWeight (ε σ : ℝ) : ℝ := 1 / (1 + Real.cosh (ε * σ))

/-- The positive even family `μ_ε = (1-θ_ε)δ₀ + (θ_ε/2)(δ_ε + δ_{-ε})`. -/
noncomputable def thetaGapFamilyMeasure (ε σ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - thetaGapFamilyWeight ε σ) • Measure.dirac 0 +
    ENNReal.ofReal (thetaGapFamilyWeight ε σ / 2) • Measure.dirac ε +
    ENNReal.ofReal (thetaGapFamilyWeight ε σ / 2) • Measure.dirac (-ε)

/-- The moving zero `σ + iπ/ε`. -/
noncomputable def thetaGapFamilyZero (ε σ : ℝ) : ℂ := (σ : ℂ) + ((Real.pi / ε : ℝ) : ℂ) * I

theorem thetaGapFamilyWeight_pos (ε σ : ℝ) : 0 < thetaGapFamilyWeight ε σ := by
  unfold thetaGapFamilyWeight
  have := Real.one_le_cosh (ε * σ)
  positivity

theorem thetaGapFamilyWeight_le_half (ε σ : ℝ) : thetaGapFamilyWeight ε σ ≤ 1 / 2 := by
  unfold thetaGapFamilyWeight
  have := Real.one_le_cosh (ε * σ)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem integral_thetaGapFamilyMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ε σ : ℝ) (f : ℝ → E) :
    ∫ s, f s ∂thetaGapFamilyMeasure ε σ =
      (1 - thetaGapFamilyWeight ε σ) • f 0 + (thetaGapFamilyWeight ε σ / 2) • f ε +
        (thetaGapFamilyWeight ε σ / 2) • f (-ε) := by
  have hθ := thetaGapFamilyWeight_pos ε σ
  have hθ2 := thetaGapFamilyWeight_le_half ε σ
  unfold thetaGapFamilyMeasure
  rw [integral_add_measure (integrable_add_measure.mpr ⟨integrable_smul_dirac _ _ _,
    integrable_smul_dirac _ _ _⟩) (integrable_smul_dirac _ _ _),
    integral_add_measure (integrable_smul_dirac _ _ _) (integrable_smul_dirac _ _ _),
    integral_smul_dirac _ (by linarith), integral_smul_dirac _ (by linarith),
    integral_smul_dirac _ (by linarith)]

theorem integrable_thetaGapFamilyMeasure (ε σ : ℝ) (f : ℝ → ℝ) :
    Integrable f (thetaGapFamilyMeasure ε σ) :=
  integrable_add_measure.mpr ⟨integrable_add_measure.mpr ⟨integrable_smul_dirac _ _ _,
    integrable_smul_dirac _ _ _⟩, integrable_smul_dirac _ _ _⟩

theorem isProbabilityMeasure_thetaGapFamilyMeasure (ε σ : ℝ) :
    IsProbabilityMeasure (thetaGapFamilyMeasure ε σ) := by
  have hθ := thetaGapFamilyWeight_pos ε σ
  have hθ2 := thetaGapFamilyWeight_le_half ε σ
  constructor
  unfold thetaGapFamilyMeasure
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) (by linarith), ← ENNReal.ofReal_add (by linarith)
    (by linarith)]
  rw [show 1 - thetaGapFamilyWeight ε σ + thetaGapFamilyWeight ε σ / 2 +
    thetaGapFamilyWeight ε σ / 2 = 1 by ring, ENNReal.ofReal_one]

theorem thetaGapFamilyMeasure_map_neg (ε σ : ℝ) :
    (thetaGapFamilyMeasure ε σ).map Neg.neg = thetaGapFamilyMeasure ε σ := by
  unfold thetaGapFamilyMeasure
  rw [Measure.map_add _ _ measurable_neg, Measure.map_add _ _ measurable_neg, Measure.map_smul,
    Measure.map_smul, Measure.map_smul, Measure.map_dirac, Measure.map_dirac, Measure.map_dirac,
    neg_zero, neg_neg]
  abel

/-- The multiplier of the family: `M(w) = 1 - θ + θ cosh(wε)`. -/
theorem thetaGapFamily_multiplier (ε σ : ℝ) (w : ℂ) :
    (∫ s, Complex.exp (-(w * s)) ∂thetaGapFamilyMeasure ε σ) =
      1 - thetaGapFamilyWeight ε σ + thetaGapFamilyWeight ε σ * Complex.cosh (w * ε) := by
  rw [integral_thetaGapFamilyMeasure]
  simp only [Complex.real_smul, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    mul_one, Complex.ofReal_neg, mul_neg, neg_neg, Complex.cosh]
  push_cast
  ring

/-- **Moving zero.**  `M(σ + iπ/ε) = 0` for every `ε > 0`. -/
theorem thetaGapFamily_multiplier_zero {ε : ℝ} (hε : 0 < ε) (σ : ℝ) :
    (∫ s, Complex.exp (-(thetaGapFamilyZero ε σ * s)) ∂thetaGapFamilyMeasure ε σ) = 0 := by
  rw [thetaGapFamily_multiplier]
  have hz : thetaGapFamilyZero ε σ * (ε : ℂ) = ((ε * σ : ℝ) : ℂ) + (Real.pi : ℂ) * I := by
    unfold thetaGapFamilyZero
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    push_cast
    field_simp
  rw [hz, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi,
    Complex.sin_pi]
  simp only [zero_mul, mul_zero, add_zero]
  rw [← Complex.ofReal_cosh]
  have h1 : (1 : ℝ) + Real.cosh (ε * σ) ≠ 0 := by have := Real.one_le_cosh (ε * σ); linarith
  have key : (1 : ℝ) - thetaGapFamilyWeight ε σ +
      thetaGapFamilyWeight ε σ * (Real.cosh (ε * σ) * -1) = 0 := by
    unfold thetaGapFamilyWeight
    field_simp
    ring
  exact_mod_cast key

/-- The critical charge of the family: `M(1/2) = 1 + θ_ε(cosh(ε/2) - 1)`. -/
theorem thetaGapFamily_charge (ε σ : ℝ) :
    (∫ s, Real.exp (-(s / 2)) ∂thetaGapFamilyMeasure ε σ) =
      1 + thetaGapFamilyWeight ε σ * (Real.cosh (ε / 2) - 1) := by
  rw [integral_thetaGapFamilyMeasure]
  simp only [smul_eq_mul, zero_div, neg_zero, Real.exp_zero, mul_one, neg_div, neg_neg,
    Real.cosh_eq]
  ring

theorem cosh_sub_one_ge_sq_half (y : ℝ) : y ^ 2 / 2 ≤ Real.cosh y - 1 := by
  have h := Real.cosh_two_mul (y / 2)
  rw [show 2 * (y / 2) = y by ring, Real.cosh_sq] at h
  have hs : (y / 2) ^ 2 ≤ Real.sinh (y / 2) ^ 2 := by
    rcases le_total 0 y with hy | hy
    · have h1 := Real.self_le_sinh_iff.mpr (by linarith : (0 : ℝ) ≤ y / 2)
      nlinarith
    · have h1 := Real.sinh_le_self_iff.mpr (by linarith : y / 2 ≤ 0)
      nlinarith
  nlinarith

theorem cosh_sub_one_le_quartic {y : ℝ} (hy : |y| ≤ 1) : Real.cosh y - 1 ≤ y ^ 2 / 2 + y ^ 4 / 4 := by
  have h1 := Real.cosh_le_exp_half_sq y
  have hz : |y ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [abs_nonneg y, sq_abs y]
  have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hz)).2
  nlinarith

theorem tendsto_cosh_sub_one_div_sq :
    Tendsto (fun y => (Real.cosh y - 1) / y ^ 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hup : Tendsto (fun y : ℝ => 1 / 2 + y ^ 2 / 4) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have : Tendsto (fun y : ℝ => 1 / 2 + y ^ 2 / 4) (𝓝 0) (𝓝 (1 / 2 + 0 ^ 2 / 4)) :=
      (continuous_const.add ((continuous_pow 2).div_const 4)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hy2 : 0 < y ^ 2 := by have := mem_Ioi.mp hy; positivity
    rw [le_div_iff₀ hy2]
    linarith [cosh_sub_one_ge_sq_half y]
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with y hy hy1
    have hy0 := mem_Ioi.mp hy
    have hy2 : 0 < y ^ 2 := by positivity
    rw [div_le_iff₀ hy2]
    have := cosh_sub_one_le_quartic (y := y) (by rw [abs_of_pos hy0]; exact hy1.2.le)
    nlinarith

/-- **Charge convergence and the exact rate.**  As `ε → 0⁺`, `M_ε(1/2) → 1` and
`T_ε² (M_ε(1/2) - 1) → π²/16` with `T_ε = π/ε`. -/
theorem thetaGapFamily_charge_limits (σ : ℝ) :
    Tendsto (fun ε => ∫ s, Real.exp (-(s / 2)) ∂thetaGapFamilyMeasure ε σ) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun ε => (Real.pi / ε) ^ 2 *
      ((∫ s, Real.exp (-(s / 2)) ∂thetaGapFamilyMeasure ε σ) - 1)) (𝓝[>] 0)
      (𝓝 (Real.pi ^ 2 / 16)) := by
  simp_rw [thetaGapFamily_charge]
  have hθ : Tendsto (fun ε => thetaGapFamilyWeight ε σ) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have hc : Continuous fun ε : ℝ => thetaGapFamilyWeight ε σ := by
      unfold thetaGapFamilyWeight
      exact continuous_const.div (continuous_const.add (Real.continuous_cosh.comp
        (continuous_id.mul continuous_const))) fun ε => by
          have := Real.one_le_cosh (ε * σ); linarith
    have h0 : thetaGapFamilyWeight 0 σ = 1 / 2 := by
      unfold thetaGapFamilyWeight
      rw [zero_mul, Real.cosh_zero]
      norm_num
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [h0] at this
  have hhalf : Tendsto (fun ε : ℝ => ε / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.div_const (2 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mem_Ioi.mpr (by have := mem_Ioi.mp hε; linarith)
  have hq := tendsto_cosh_sub_one_div_sq.comp hhalf
  constructor
  · have hc : Tendsto (fun ε : ℝ => Real.cosh (ε / 2) - 1) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => Real.cosh (ε / 2) - 1) (𝓝 0)
          (𝓝 (Real.cosh (0 / 2) - 1)) :=
        ((Real.continuous_cosh.comp (continuous_id.div_const (2 : ℝ))).sub
          continuous_const).tendsto 0
      simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).add
      (hθ.mul hc)
  · have key : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (Real.pi / ε) ^ 2 *
        (1 + thetaGapFamilyWeight ε σ * (Real.cosh (ε / 2) - 1) - 1) =
        Real.pi ^ 2 / 4 * (thetaGapFamilyWeight ε σ *
          ((Real.cosh (ε / 2) - 1) / (ε / 2) ^ 2)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have := mem_Ioi.mp hε
      field_simp
      ring
    refine Tendsto.congr' (EventuallyEq.symm key) ?_
    have := (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.pi ^ 2 / 4) (𝓝[>] 0)
      (𝓝 (Real.pi ^ 2 / 4))).mul (hθ.mul hq)
    rw [show Real.pi ^ 2 / 16 = Real.pi ^ 2 / 4 * (1 / 2 * (1 / 2)) by ring]
    exact this

/-- **The gap condition is essential.**  For every `ε > 0` the family `μ_ε` is a positive even
probability measure whose gauge passes every finite sieve and keeps the ordinary mass of `k`,
while its Mellin multiplier vanishes at the off-line point `σ + iπ/ε`. -/
theorem thetaGapFamily_properties {ε : ℝ} (hε : 0 < ε) (σ : ℝ) :
    IsProbabilityMeasure (thetaGapFamilyMeasure ε σ) ∧
    (thetaGapFamilyMeasure ε σ).map Neg.neg = thetaGapFamilyMeasure ε σ ∧
    (∀ x, 0 < thetaMeasureGauge (thetaGapFamilyMeasure ε σ) thetaCuspFullSource x) ∧
    (∀ x, thetaMeasureGauge (thetaGapFamilyMeasure ε σ) thetaCuspFullSource (-x) =
      thetaMeasureGauge (thetaGapFamilyMeasure ε σ) thetaCuspFullSource x) ∧
    (∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → CompletelyMonotoneOn (thetaNormalizedFlux
      (thetaPrimeDeletion S (thetaMeasureGauge (thetaGapFamilyMeasure ε σ)
        thetaCuspFullSource)))) ∧
    (∫ x, thetaMeasureGauge (thetaGapFamilyMeasure ε σ) thetaCuspFullSource x) =
      ∫ x, thetaCuspFullSource x ∧
    (∫ s, Complex.exp (-(thetaGapFamilyZero ε σ * s)) ∂thetaGapFamilyMeasure ε σ) = 0 := by
  have hprob := isProbabilityMeasure_thetaGapFamilyMeasure ε σ
  have hmom := integrable_thetaGapFamilyMeasure ε σ (fun s => Real.exp (|s| / 2))
  have hθ := thetaGapFamilyWeight_pos ε σ
  have hθ2 := thetaGapFamilyWeight_le_half ε σ
  have hgauge : ∀ x, thetaMeasureGauge (thetaGapFamilyMeasure ε σ) thetaCuspFullSource x =
      (1 - thetaGapFamilyWeight ε σ) * thetaCuspFullSource x +
        thetaGapFamilyWeight ε σ / 2 * thetaCuspFullSource (x + ε) +
        thetaGapFamilyWeight ε σ / 2 * thetaCuspFullSource (x - ε) := by
    intro x
    unfold thetaMeasureGauge
    rw [integral_thetaGapFamilyMeasure]
    simp only [smul_eq_mul, add_zero, ← sub_eq_add_neg]
  refine ⟨hprob, thetaGapFamilyMeasure_map_neg ε σ, fun x => ?_, fun x => ?_, fun S hS =>
    completelyMonotoneOn_thetaPrimeDeletion_thetaMeasureGauge hmom hS, ?_,
    thetaGapFamily_multiplier_zero hε σ⟩
  · rw [hgauge]
    have := thetaCuspFullSource_pos_all x
    have := thetaCuspFullSource_pos_all (x + ε)
    have := thetaCuspFullSource_pos_all (x - ε)
    have : 0 < 1 - thetaGapFamilyWeight ε σ := by linarith
    positivity
  · rw [hgauge, hgauge, thetaCuspFullSource_neg, show -x + ε = -(x - ε) by ring,
      show -x - ε = -(x + ε) by ring, thetaCuspFullSource_neg, thetaCuspFullSource_neg]
    ring
  · rw [(thetaMeasureGauge_anchors hmom).1, measure_univ, ENNReal.toReal_one, one_mul]

/-! ## The signed translation multiplier -/

theorem integrable_cexp_mul_thetaMeasureGauge {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (|s| / 2)) ν) {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    Integrable (fun x : ℝ => Complex.exp (w * x) *
      (thetaMeasureGauge ν thetaCuspFullSource x : ℂ)) := by
  have hr := (integral_exp_mul_thetaMeasureGauge (ν := ν) (w := w.re)
    (integrable_exp_mul_of_abs_half hν hw)).1
  have hg : Continuous (thetaMeasureGauge ν thetaCuspFullSource) := by
    obtain ⟨C, hC⟩ := exists_abs_thetaCuspFullSource_le_const
    exact continuous_thetaMeasureGauge continuous_thetaCuspFullSource hC
  refine Integrable.mono' hr (by fun_prop) (ae_of_all _ fun x => ?_)
  have hpos : 0 ≤ thetaMeasureGauge ν thetaCuspFullSource x :=
    integral_nonneg fun s => (thetaCuspFullSource_pos_all _).le
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hpos]
  simp

/-- **Signed translation multiplier.**  For `|Re w| ≤ 1/2`,
`L_w g_μ = M_μ(w) L_w k` with `M_μ(w) = ∫ e^{-ws} dμ(s)` for `μ = ν₁ - ν₂`. -/
theorem integral_cexp_mul_thetaSignedMeasureGauge {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] (h₁ : Integrable (fun s => Real.exp (|s| / 2)) ν₁)
    (h₂ : Integrable (fun s => Real.exp (|s| / 2)) ν₂) {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaSignedMeasureGauge ν₁ ν₂ x : ℂ)) =
      ((∫ s, Complex.exp (-(w * s)) ∂ν₁) - ∫ s, Complex.exp (-(w * s)) ∂ν₂) * XiC (I * w) := by
  have e : (fun x : ℝ => Complex.exp (w * x) * (thetaSignedMeasureGauge ν₁ ν₂ x : ℂ)) =
      fun x : ℝ => Complex.exp (w * x) * (thetaMeasureGauge ν₁ thetaCuspFullSource x : ℂ) -
        Complex.exp (w * x) * (thetaMeasureGauge ν₂ thetaCuspFullSource x : ℂ) := by
    funext x
    unfold thetaSignedMeasureGauge
    push_cast
    ring
  rw [e, integral_sub (integrable_cexp_mul_thetaMeasureGauge h₁ hw)
    (integrable_cexp_mul_thetaMeasureGauge h₂ hw), integral_cexp_mul_thetaMeasureGauge h₁ hw,
    integral_cexp_mul_thetaMeasureGauge h₂ hw, sub_mul]

/-- Integer-scale shifts `±log n`, `n ≥ 2`, have the fixed gap `log 2`. -/
theorem log_two_le_abs_log_nat {n : ℕ} (hn : 2 ≤ n) : Real.log 2 ≤ |Real.log n| := by
  rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)

end RHTower
