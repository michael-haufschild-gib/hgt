import GaloisForLFunctions.HTGeometry.FZZCigarReplicaKreinScale

/-!
# Vaidya evaporation horizons, repeated scattering, and the FZZ scale

For constant mass-loss rate `ε = |M'|`, the outgoing Vaidya geometry is conformal to a static
two-horizon metric with radial factor

`f_ε(x) = 1 - 1/x - 4 ε x`.

This file parametrizes its physical two-horizon range by the event/outer surface-gravity ratio
`0 < q < 1`.  At

`ε(q) = q / (4(1+q)²)`,

the two roots are exactly `x_H = 1+q` and `x_C = (1+q)/q`; the ratio of the magnitudes of their
slopes is `q`.  Repeated horizon-to-horizon scattering therefore has the exact fixed-point
completion

`q + q² + ⋯ = q/(1-q)`.

Two results are structurally new here.

* This dynamical scale defeats stationary Schwarzschild self-similarity: `|M'|` changes the
  dimensionless radial potential and rescaled QNM spectrum before the ordinary `1/M(w)` frequency
  scaling.
* Under `q = 2/k`, repeated Vaidya horizon scale is literally the finite-level FZZ fractional-
  winding replica scale `2/k / (1-2/k)`.  This equality is proved algebraically; no claim is made
  here that Hawking flux dynamics enforces `q = 2/k`.

Passive sign along any nonempty early-evaporation interval `0 < q < qCap < 1` already selects
imaginary-axis frequency.  Horizon coalescence and Planckian extrapolation are unnecessary.
Every fixed evaporation rate remains blind, so selector is genuinely nonstationary horizon
backreaction, not KMS/passivity at one background.

Physics sources:

* Capuano--Santoni--Barausse, arXiv:2407.06009, equations (8)--(12), (52)--(59).
* Halder--Jafferis, arXiv:2402.00932, finite-level fractional-winding replica dressing.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def vaidyaConformalHorizonFunction (ε x : ℝ) : ℝ :=
  1 - 1 / x - 4 * ε * x

def vaidyaMassRateOfHorizonRatio (q : ℝ) : ℝ :=
  q / (4 * (1 + q) ^ (2 : ℕ))

def vaidyaEventHorizon (q : ℝ) : ℝ :=
  1 + q

def vaidyaOuterHorizon (q : ℝ) : ℝ :=
  (1 + q) / q

theorem vaidyaConformalHorizonFunction_event_eq_zero
    {q : ℝ} (hq0 : 0 < q) :
    vaidyaConformalHorizonFunction (vaidyaMassRateOfHorizonRatio q)
      (vaidyaEventHorizon q) = 0 := by
  rw [vaidyaConformalHorizonFunction, vaidyaMassRateOfHorizonRatio, vaidyaEventHorizon]
  have hq1 : 1 + q ≠ 0 := ne_of_gt (by linarith)
  field_simp [hq1]
  ring

theorem vaidyaConformalHorizonFunction_outer_eq_zero
    {q : ℝ} (hq0 : 0 < q) :
    vaidyaConformalHorizonFunction (vaidyaMassRateOfHorizonRatio q)
      (vaidyaOuterHorizon q) = 0 := by
  rw [vaidyaConformalHorizonFunction, vaidyaMassRateOfHorizonRatio, vaidyaOuterHorizon]
  have hq : q ≠ 0 := ne_of_gt hq0
  have hq1 : 1 + q ≠ 0 := ne_of_gt (by linarith)
  field_simp [hq, hq1]
  ring

theorem vaidyaMassRateOfHorizonRatio_pos
    {q : ℝ} (hq0 : 0 < q) :
    0 < vaidyaMassRateOfHorizonRatio q := by
  rw [vaidyaMassRateOfHorizonRatio]
  exact div_pos hq0 (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))

theorem vaidyaMassRateOfHorizonRatio_lt_critical
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    vaidyaMassRateOfHorizonRatio q < 1 / 16 := by
  rw [vaidyaMassRateOfHorizonRatio]
  have hden : 0 < 4 * (1 + q) ^ (2 : ℕ) :=
    mul_pos (by norm_num) (sq_pos_of_pos (by linarith))
  rw [div_lt_iff₀ hden]
  nlinarith [sq_pos_of_pos (by linarith : 0 < 1 - q)]

theorem vaidyaEventHorizon_lt_outerHorizon
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    vaidyaEventHorizon q < vaidyaOuterHorizon q := by
  rw [vaidyaEventHorizon, vaidyaOuterHorizon, lt_div_iff₀ hq0]
  nlinarith [mul_pos (by linarith : 0 < 1 + q) (by linarith : 0 < 1 - q)]

theorem vaidyaEventHorizon_div_outerHorizon
    {q : ℝ} (hq0 : 0 < q) :
    vaidyaEventHorizon q / vaidyaOuterHorizon q = q := by
  rw [vaidyaEventHorizon, vaidyaOuterHorizon]
  have hq : q ≠ 0 := ne_of_gt hq0
  have hq1 : 1 + q ≠ 0 := ne_of_gt (by linarith)
  field_simp [hq, hq1]

def vaidyaConformalHorizonSlope (ε x : ℝ) : ℝ :=
  1 / x ^ (2 : ℕ) - 4 * ε

theorem vaidyaEventHorizonSlope_eq
    {q : ℝ} (hq0 : 0 < q) :
    vaidyaConformalHorizonSlope (vaidyaMassRateOfHorizonRatio q)
      (vaidyaEventHorizon q) = (1 - q) / (1 + q) ^ (2 : ℕ) := by
  rw [vaidyaConformalHorizonSlope, vaidyaMassRateOfHorizonRatio, vaidyaEventHorizon]
  have hq1 : 1 + q ≠ 0 := ne_of_gt (by linarith)
  field_simp [hq1]

theorem vaidyaOuterHorizonSlope_eq
    {q : ℝ} (hq0 : 0 < q) :
    vaidyaConformalHorizonSlope (vaidyaMassRateOfHorizonRatio q)
      (vaidyaOuterHorizon q) = -q * (1 - q) / (1 + q) ^ (2 : ℕ) := by
  rw [vaidyaConformalHorizonSlope, vaidyaMassRateOfHorizonRatio, vaidyaOuterHorizon]
  have hq : q ≠ 0 := ne_of_gt hq0
  have hq1 : 1 + q ≠ 0 := ne_of_gt (by linarith)
  field_simp [hq, hq1]
  ring

theorem neg_outerSlope_div_eventSlope_eq_horizonRatio
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    -vaidyaConformalHorizonSlope (vaidyaMassRateOfHorizonRatio q)
        (vaidyaOuterHorizon q) /
      vaidyaConformalHorizonSlope (vaidyaMassRateOfHorizonRatio q)
        (vaidyaEventHorizon q) = q := by
  rw [vaidyaEventHorizonSlope_eq hq0, vaidyaOuterHorizonSlope_eq hq0]
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hq1p : 1 + q ≠ 0 := ne_of_gt (by linarith)
  have hqm : 1 - q ≠ 0 := ne_of_gt (by linarith)
  field_simp [hqne, hq1p, hqm]

def vaidyaRepeatedHorizonScale (q : ℝ) : ℝ :=
  q / (1 - q)

theorem vaidyaRepeatedHorizonScale_fixedPoint
    {q : ℝ} (hq1 : q ≠ 1) :
    vaidyaRepeatedHorizonScale q = q + q * vaidyaRepeatedHorizonScale q := by
  rw [vaidyaRepeatedHorizonScale]
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.symm
  field_simp [hden]
  ring

def vaidyaHorizonRatioForScale (β : ℝ) : ℝ :=
  β / (1 + β)

theorem vaidyaHorizonRatioForScale_pos {β : ℝ} (hβ : 0 < β) :
    0 < vaidyaHorizonRatioForScale β := by
  rw [vaidyaHorizonRatioForScale]
  exact div_pos hβ (by linarith)

theorem vaidyaHorizonRatioForScale_lt_one {β : ℝ} (hβ : 0 < β) :
    vaidyaHorizonRatioForScale β < 1 := by
  rw [vaidyaHorizonRatioForScale]
  rw [div_lt_one (by linarith)]
  linarith

theorem vaidyaRepeatedHorizonScale_horizonRatioForScale
    {β : ℝ} (hβ : 0 < β) :
    vaidyaRepeatedHorizonScale (vaidyaHorizonRatioForScale β) = β := by
  rw [vaidyaRepeatedHorizonScale, vaidyaHorizonRatioForScale]
  have h1 : 1 + β ≠ 0 := ne_of_gt (by linarith)
  field_simp [h1]
  ring

theorem vaidyaRepeatedHorizonScale_two_mul_replicaLevel
    (a : ℝ) :
    vaidyaRepeatedHorizonScale (2 * a) =
      FZZCigar.replicaLinearizedDressingScale a := by
  rw [vaidyaRepeatedHorizonScale, FZZCigar.replicaLinearizedDressingScale]

def VaidyaEvaporationUniversalKreinSign (ω : ℂ) : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 →
    ((Complex.sinh (((vaidyaRepeatedHorizonScale q : ℝ) : ℂ) * ω / 2)) ^ (2 : ℕ)).im = 0 ∧
    ((Complex.sinh (((vaidyaRepeatedHorizonScale q : ℝ) : ℂ) * ω / 2)) ^ (2 : ℕ)).re ≤ 0

theorem vaidyaEvaporationUniversalKreinSign_iff_re_eq_zero (ω : ℂ) :
    VaidyaEvaporationUniversalKreinSign ω ↔ ω.re = 0 := by
  constructor
  · intro hevap
    apply (GaloisForLFunctions.hawkingTemperatureUniversalKreinSign_iff_re_eq_zero ω).mp
    intro β hβ
    have hchamber := hevap (vaidyaHorizonRatioForScale β)
      (vaidyaHorizonRatioForScale_pos hβ) (vaidyaHorizonRatioForScale_lt_one hβ)
    rw [vaidyaRepeatedHorizonScale_horizonRatioForScale hβ] at hchamber
    exact hchamber
  · intro hre q hq0 hq1
    exact (GaloisForLFunctions.hawkingTemperatureUniversalKreinSign_iff_re_eq_zero ω).mpr hre
      (vaidyaRepeatedHorizonScale q)
      (div_pos hq0 (by linarith))

theorem fixed_vaidyaMassRate_has_offAxis_krein_blind_point
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ ω : ℂ,
      ω.re ≠ 0 ∧
        ((Complex.sinh (((vaidyaRepeatedHorizonScale q : ℝ) : ℂ) * ω / 2)) ^ (2 : ℕ)).im = 0 ∧
        ((Complex.sinh (((vaidyaRepeatedHorizonScale q : ℝ) : ℂ) * ω / 2)) ^ (2 : ℕ)).re < 0 := by
  exact GaloisForLFunctions.fixed_hawking_temperature_has_offAxis_krein_blind_point
    (vaidyaRepeatedHorizonScale q) (div_pos hq0 (by linarith))

private lemma real_sinh_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    Real.sinh x ≠ 0 := by
  intro hs
  rw [Real.sinh_eq] at hs
  have he : Real.exp x = Real.exp (-x) := by linarith
  have hxneg : x = -x := Real.exp_injective he
  apply hx
  linarith

private lemma complex_sinh_re_local (z : ℂ) :
    (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im := by
  have h : Complex.sinh z
      = ((Real.sinh z.re * Real.cos z.im : ℝ) : ℂ)
        + ((Real.cosh z.re * Real.sin z.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh]
    push_cast
    ring
  rw [h, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma complex_sinh_im_local (z : ℂ) :
    (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  have h : Complex.sinh z
      = ((Real.sinh z.re * Real.cos z.im : ℝ) : ℂ)
        + ((Real.cosh z.re * Real.sin z.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh]
    push_cast
    ring
  rw [h, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma complex_sinh_sq_im_local (z : ℂ) :
    ((Complex.sinh z) ^ (2 : ℕ)).im =
      Real.sinh (2 * z.re) * Real.sin (2 * z.im) / 2 := by
  rw [pow_two, Complex.mul_im, complex_sinh_re_local, complex_sinh_im_local,
    Real.sinh_two_mul, Real.sin_two_mul]
  ring

def PositiveScaleGermKreinSign (cap : ℝ) (ω : ℂ) : Prop :=
  ∀ β : ℝ, 0 < β → β < cap →
    ((Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ)).im = 0 ∧
      ((Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ)).re ≤ 0

theorem positiveScaleGermKreinSign_iff_re_eq_zero
    {cap : ℝ} (hcap : 0 < cap) (ω : ℂ) :
    PositiveScaleGermKreinSign cap ω ↔ ω.re = 0 := by
  constructor
  · intro hgerm
    by_contra hre
    by_cases him : ω.im = 0
    · let β : ℝ := cap / 2
      have hβ : 0 < β := div_pos hcap zero_lt_two
      have hβcap : β < cap := by dsimp only [β]; linarith
      obtain ⟨_, hnonpos⟩ := hgerm β hβ hβcap
      let z : ℂ := ((β : ℂ) * ω) / 2
      have hzim : z.im = 0 := by simp [z, him]
      have hzre : z.re = β * ω.re / 2 := by simp [z, Complex.mul_re]
      have hzre_ne : z.re ≠ 0 := by
        rw [hzre]
        exact div_ne_zero (mul_ne_zero hβ.ne' hre) (by norm_num)
      have hsre : (Complex.sinh z).re = Real.sinh z.re := by
        rw [complex_sinh_re_local, hzim, Real.cos_zero, mul_one]
      have hsim : (Complex.sinh z).im = 0 := by
        rw [complex_sinh_im_local, hzim, Real.sin_zero, mul_zero]
      have hsqre : ((Complex.sinh z) ^ (2 : ℕ)).re = (Real.sinh z.re) ^ (2 : ℕ) := by
        rw [pow_two, Complex.mul_re, hsre, hsim]
        ring
      have hpos : 0 < ((Complex.sinh z) ^ (2 : ℕ)).re := by
        rw [hsqre]
        exact sq_pos_of_ne_zero (real_sinh_ne_zero_of_ne_zero hzre_ne)
      exact (not_lt_of_ge hnonpos) hpos
    · have himabs : 0 < |ω.im| := abs_pos.mpr him
      let β : ℝ := min (cap / 2) (Real.pi / (2 * |ω.im|))
      have hβ : 0 < β := by
        apply lt_min
        · exact div_pos hcap zero_lt_two
        · exact div_pos Real.pi_pos (mul_pos zero_lt_two himabs)
      have hβcap : β < cap := by
        have hle := min_le_left (cap / 2) (Real.pi / (2 * |ω.im|))
        dsimp only [β]
        linarith
      have hβabs : β * |ω.im| ≤ Real.pi / 2 := by
        have hle := min_le_right (cap / 2) (Real.pi / (2 * |ω.im|))
        have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt himabs)
        dsimp only [β] at hmul ⊢
        calc
          min (cap / 2) (Real.pi / (2 * |ω.im|)) * |ω.im|
              ≤ (Real.pi / (2 * |ω.im|)) * |ω.im| := hmul
          _ = Real.pi / 2 := by field_simp [ne_of_gt himabs]
      obtain ⟨himZero, _⟩ := hgerm β hβ hβcap
      have hsinh : Real.sinh (β * ω.re) ≠ 0 := by
        apply real_sinh_ne_zero_of_ne_zero
        exact mul_ne_zero hβ.ne' hre
      have hsin : Real.sin (β * ω.im) ≠ 0 := by
        rcases lt_or_gt_of_ne him with himneg | himpos
        · have habs : |ω.im| = -ω.im := abs_of_neg himneg
          have hargneg : β * ω.im < 0 := mul_neg_of_pos_of_neg hβ himneg
          have harglower : -Real.pi < β * ω.im := by
            rw [habs] at hβabs
            nlinarith [Real.pi_pos]
          exact (Real.sin_neg_of_neg_of_neg_pi_lt hargneg harglower).ne
        · have habs : |ω.im| = ω.im := abs_of_pos himpos
          have hargpos : 0 < β * ω.im := mul_pos hβ himpos
          have hargupper : β * ω.im < Real.pi := by
            rw [habs] at hβabs
            nlinarith [Real.pi_pos]
          exact (Real.sin_pos_of_pos_of_lt_pi hargpos hargupper).ne'
      have hsqim :
          ((Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ)).im =
            Real.sinh (β * ω.re) * Real.sin (β * ω.im) / 2 := by
        rw [complex_sinh_sq_im_local]
        congr 2 <;> simp [Complex.mul_re, Complex.mul_im] <;> ring_nf
      rw [hsqim] at himZero
      exact (div_ne_zero (mul_ne_zero hsinh hsin) (by norm_num)) himZero
  · intro hre β hβ _
    exact (GaloisForLFunctions.hawkingTemperatureUniversalKreinSign_iff_re_eq_zero ω).mpr hre
      β hβ

def VaidyaEvaporationGermKreinSign (qCap : ℝ) (ω : ℂ) : Prop :=
  ∀ q : ℝ, 0 < q → q < qCap →
    ((Complex.sinh (((vaidyaRepeatedHorizonScale q : ℝ) : ℂ) * ω / 2)) ^ (2 : ℕ)).im = 0 ∧
    ((Complex.sinh (((vaidyaRepeatedHorizonScale q : ℝ) : ℂ) * ω / 2)) ^ (2 : ℕ)).re ≤ 0

theorem vaidyaEvaporationGermKreinSign_iff_re_eq_zero
    {qCap : ℝ} (hqCap0 : 0 < qCap) (hqCap1 : qCap < 1) (ω : ℂ) :
    VaidyaEvaporationGermKreinSign qCap ω ↔ ω.re = 0 := by
  constructor
  · intro hevap
    have hscaleCap : 0 < vaidyaRepeatedHorizonScale qCap :=
      div_pos hqCap0 (by linarith)
    apply (positiveScaleGermKreinSign_iff_re_eq_zero hscaleCap ω).mp
    intro β hβ hβCap
    have hq0 := vaidyaHorizonRatioForScale_pos hβ
    have hq1 : vaidyaHorizonRatioForScale β < qCap := by
      rw [vaidyaHorizonRatioForScale]
      rw [div_lt_iff₀ (by linarith : 0 < 1 + β)]
      rw [vaidyaRepeatedHorizonScale] at hβCap
      rw [lt_div_iff₀ (by linarith : 0 < 1 - qCap)] at hβCap
      nlinarith
    have hchamber := hevap (vaidyaHorizonRatioForScale β) hq0 hq1
    rw [vaidyaRepeatedHorizonScale_horizonRatioForScale hβ] at hchamber
    exact hchamber
  · intro hre q hq0 hqCap
    have hq1 : q < 1 := lt_trans hqCap hqCap1
    exact (GaloisForLFunctions.hawkingTemperatureUniversalKreinSign_iff_re_eq_zero ω).mpr hre
      (vaidyaRepeatedHorizonScale q) (div_pos hq0 (by linarith))

end

end GaloisForLFunctions.HTGeometry
