import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NegativeDirectionsCannotEscapeLogarithmicWindows
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheContinuumWindowThresholdGrowsExponentially
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalFormHasAGammaLiminf
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CriticalWindowsSurviveLowConductorRemoval
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLowPacketPaymentAtEveryRatioIsTheRiemannHypothesis
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheLiouvilleProperty
import GaloisForLFunctions.HTGeometry.CompactKernelL2Convolution
import GaloisForLFunctions.HTGeometry.MollifierL2Contraction
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The Critical Positivity Threshold Law

At critical overlap ratios `1 ≤ c`, `c⁸ ≤ R log N`, let `criticalPositivityThreshold` (`R_c(ζ)`),
`criticalNonnegativityThreshold`, `poleOrthogonalCriticalThreshold`, `highConductorCriticalThreshold`
(`R_c^{high}(ζ)`), and `highConductorNonnegativityThreshold` denote the supremum in `EReal` of
positive ratios `R > 0` below which `completeWeilEnergy tiltedUnitSpline c N` is eventually positive
definite (respectively positive semidefinite) on the whole horizon space `ℝ^N`, on the primitive
hyperplane `(conductorSubspace 1 N)ᗮ`, and on the polylogarithmic high-conductor complement
`(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ`.

1. **Monotonicity chain and certified floor** (`criticalPositivityThreshold_pos`,
   `criticalPositivityThreshold_le_highConductorCriticalThreshold`,
   `criticalNonnegativityThreshold_le_highConductorNonnegativityThreshold`):
   `0 < criticalPositivityThreshold ≤ poleOrthogonalCriticalThreshold ≤ highConductorCriticalThreshold ≤ highConductorNonnegativityThreshold`,
   and `criticalPositivityThreshold ≤ criticalNonnegativityThreshold ≤ highConductorNonnegativityThreshold`.
2. **Low-conductor-removed window upper bound** (`highConductorNonnegativityThreshold_le_iInf_windowThreshold`):
   projecting smooth terminal window vectors orthogonally off `conductorSubspace ⌊(log N)^{13/32}⌋₊ N`
   (`horizon_layer_criticalCurve_exact_after_low_projection`) yields
   `highConductorNonnegativityThreshold ≤ ⨅ A ≥ 0, windowThreshold A`.
3. **One-sided spline mollification and Kolmogorov–Riesz `L²` precompactness**
   (`eventuallyHighConductorPosDef_of_lt_iInf_windowThreshold`):
   any sequence of high-conductor nonpositive directions at `c⁸ ≤ R_* log N` (`R_* < ⨅ A ≥ 0, windowThreshold A`)
   produces normalized collar profiles `V_k` (`eventually_complement_collar_weilQuad_bridge`) whose
   high Fourier tails are uniformly small (`high_tails_of_bounded_weilQuad`). Convolving with the
   reflected spline mollifier `leftSplineMollifier` yields `L²` precompactness
   (`totallyBounded_toLp_of_tight_deriv`), a strong `L²` + `L¹` limit `F₀` supported on `(-∞, 0)`
   satisfying the critical `Γ`-liminf bound (`eventually_lt_weilQuad_of_L1_limit_full`), and smooth
   window tests `windowMollify F₀ A δ` whose critical pencil becomes negative, a contradiction.
4. **Exact threshold identity, exponential growth, and whole-space localization**
   (`highConductorCriticalThreshold_eq_iInf_windowThreshold`,
   `exp_six_mul_le_highConductorCriticalThreshold`,
   `eventually_lowConductorProjection_and_topWindow_ne_zero_of_nonpos`,
   `criticalPositivityThreshold_eq_top_iff_riemannHypothesis`):
   `highConductorCriticalThreshold = highConductorNonnegativityThreshold = ⨅ A ≥ 0, windowThreshold A ≥ windowThresholdExponentialConstant * e^{6 a*(ζ)}`
   (`log R_c^{high}(ζ) ≥ 6 a*(ζ) + log c₀`), every nonzero nonpositive whole-space vector below
   `c₀ e^{6 a*(ζ)}` must simultaneously charge `conductorSubspace ⌊(log N)^{13/32}⌋₊ N` and the top
   logarithmic window of length `(1/8) log(R + 1) + C₀`, and all five critical thresholds equal `⊤`
   if and only if `onsetAperture zetaZeroConfig = ⊤` (equivalently `RiemannHypothesis`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset Zeta23 RHTower
open scoped RealInnerProductSpace ENNReal Convolution Classical

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open CriticalArithmeticCorrelationTheory ArithmeticDegenerationTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ
  WindowVisibilityLaw SquareRootThreshold ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory RenormalizedIntersectionTheory

/-! ### 1. Critical positivity predicates, threshold definitions, certified floor, and monotonicity -/

/-- Eventual positive definiteness of `completeWeilEnergy tiltedUnitSpline c N` on all of `ℝ^N`
across `1 ≤ c`, `c⁸ ≤ R log N`. -/
def EventuallyCriticalPosDef (R : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R * Real.log (N : ℝ) →
    ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ≠ 0 →
      0 < completeWeilEnergy tiltedUnitSpline c N z

/-- Eventual positive semidefiniteness of `completeWeilEnergy tiltedUnitSpline c N` on all of `ℝ^N`
across `1 ≤ c`, `c⁸ ≤ R log N`. -/
def EventuallyCriticalNonneg (R : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R * Real.log (N : ℝ) →
    ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
      0 ≤ completeWeilEnergy tiltedUnitSpline c N z

/-- Eventual positive definiteness of `completeWeilEnergy tiltedUnitSpline c N` on the primitive
hyperplane `(conductorSubspace 1 N)ᗮ` across `1 ≤ c`, `c⁸ ≤ R log N`. -/
def EventuallyPoleOrthogonalPosDef (R : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R * Real.log (N : ℝ) →
    ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      z ∈ (conductorSubspace 1 N)ᗮ → z ≠ 0 →
        0 < completeWeilEnergy tiltedUnitSpline c N z

/-- Eventual positive definiteness of `completeWeilEnergy tiltedUnitSpline c N` on the
polylogarithmic high-conductor complement `(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ` across
`1 ≤ c`, `c⁸ ≤ R log N`. -/
def EventuallyHighConductorPosDef (R : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R * Real.log (N : ℝ) →
    ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ → z ≠ 0 →
        0 < completeWeilEnergy tiltedUnitSpline c N z

/-- Eventual positive semidefiniteness of `completeWeilEnergy tiltedUnitSpline c N` on
`(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ` across `1 ≤ c`, `c⁸ ≤ R log N`. -/
def EventuallyHighConductorNonneg (R : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R * Real.log (N : ℝ) →
    ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ →
        0 ≤ completeWeilEnergy tiltedUnitSpline c N z

/-- **The whole-space critical positivity threshold `R_c(ζ)`**: the supremum in `EReal` of ratios
`R > 0` at which `completeWeilEnergy tiltedUnitSpline` is eventually positive definite. -/
def criticalPositivityThreshold : EReal :=
  sSup ((fun R : ℝ => (R : EReal)) '' {R : ℝ | 0 < R ∧ EventuallyCriticalPosDef R})

/-- The whole-space critical nonnegativity threshold. -/
def criticalNonnegativityThreshold : EReal :=
  sSup ((fun R : ℝ => (R : EReal)) '' {R : ℝ | 0 < R ∧ EventuallyCriticalNonneg R})

/-- The primitive-hyperplane critical positivity threshold on `(conductorSubspace 1 N)ᗮ`. -/
def poleOrthogonalCriticalThreshold : EReal :=
  sSup ((fun R : ℝ => (R : EReal)) '' {R : ℝ | 0 < R ∧ EventuallyPoleOrthogonalPosDef R})

/-- **The high-conductor critical positivity threshold `R_c^{high}(ζ)`** on
`(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ`. -/
def highConductorCriticalThreshold : EReal :=
  sSup ((fun R : ℝ => (R : EReal)) '' {R : ℝ | 0 < R ∧ EventuallyHighConductorPosDef R})

/-- The high-conductor critical nonnegativity threshold on
`(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ`. -/
def highConductorNonnegativityThreshold : EReal :=
  sSup ((fun R : ℝ => (R : EReal)) '' {R : ℝ | 0 < R ∧ EventuallyHighConductorNonneg R})

private theorem completeWeilEnergy_zero (c : ℝ) (N : ℕ) :
    completeWeilEnergy tiltedUnitSpline c N 0 = 0 := by
  simp [completeWeilEnergy]

theorem eventuallyCriticalPosDef_antitone {R₁ R₂ : ℝ} (hle : R₁ ≤ R₂)
    (h₂ : EventuallyCriticalPosDef R₂) : EventuallyCriticalPosDef R₁ := by
  filter_upwards [h₂, eventually_ge_atTop 1] with N hN hN1 c hc1 hc8 z hz
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  exact hN hc1 (hc8.trans (mul_le_mul_of_nonneg_right hle hL)) hz

theorem eventuallyCriticalNonneg_antitone {R₁ R₂ : ℝ} (hle : R₁ ≤ R₂)
    (h₂ : EventuallyCriticalNonneg R₂) : EventuallyCriticalNonneg R₁ := by
  filter_upwards [h₂, eventually_ge_atTop 1] with N hN hN1 c hc1 hc8 z
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  exact hN hc1 (hc8.trans (mul_le_mul_of_nonneg_right hle hL)) z

theorem eventuallyHighConductorPosDef_antitone {R₁ R₂ : ℝ} (hle : R₁ ≤ R₂)
    (h₂ : EventuallyHighConductorPosDef R₂) : EventuallyHighConductorPosDef R₁ := by
  filter_upwards [h₂, eventually_ge_atTop 1] with N hN hN1 c hc1 hc8 z hz hzne
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  exact hN hc1 (hc8.trans (mul_le_mul_of_nonneg_right hle hL)) hz hzne

theorem eventuallyCriticalNonneg_of_posDef {R : ℝ} (h : EventuallyCriticalPosDef R) :
    EventuallyCriticalNonneg R := by
  filter_upwards [h] with N hN c hc1 hc8 z
  rcases eq_or_ne z 0 with rfl | hzne
  · rw [completeWeilEnergy_zero]
  · exact (hN hc1 hc8 hzne).le

theorem eventuallyPoleOrthogonalPosDef_of_posDef {R : ℝ} (h : EventuallyCriticalPosDef R) :
    EventuallyPoleOrthogonalPosDef R := by
  filter_upwards [h] with N hN c hc1 hc8 z _ hzne
  exact hN hc1 hc8 hzne

theorem eventuallyHighConductorPosDef_of_poleOrthogonal {R : ℝ}
    (h : EventuallyPoleOrthogonalPosDef R) : EventuallyHighConductorPosDef R := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h, hlog.eventually_ge_atTop 1] with N hN hL1 c hc1 hc8 z hz hzne
  have hQ1 : 1 ≤ ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ :=
    Nat.le_floor (by exact_mod_cast Real.one_le_rpow hL1 (by norm_num : (0 : ℝ) ≤ 13 / 32))
  have horth1 : z ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hz v (conductorSubspace_mono hQ1 N hv)
  exact hN hc1 hc8 horth1 hzne

theorem eventuallyHighConductorNonneg_of_posDef {R : ℝ}
    (h : EventuallyHighConductorPosDef R) : EventuallyHighConductorNonneg R := by
  filter_upwards [h] with N hN c hc1 hc8 z hz
  rcases eq_or_ne z 0 with rfl | hzne
  · rw [completeWeilEnergy_zero]
  · exact (hN hc1 hc8 hz hzne).le

theorem eventuallyHighConductorNonneg_of_criticalNonneg {R : ℝ}
    (h : EventuallyCriticalNonneg R) : EventuallyHighConductorNonneg R := by
  filter_upwards [h] with N hN c hc1 hc8 z _
  exact hN hc1 hc8 z

theorem criticalPositivityThreshold_le_criticalNonnegativityThreshold :
    criticalPositivityThreshold ≤ criticalNonnegativityThreshold :=
  sSup_le_sSup (Set.image_mono fun _ h => ⟨h.1, eventuallyCriticalNonneg_of_posDef h.2⟩)

theorem criticalPositivityThreshold_le_poleOrthogonalCriticalThreshold :
    criticalPositivityThreshold ≤ poleOrthogonalCriticalThreshold :=
  sSup_le_sSup (Set.image_mono fun _ h => ⟨h.1, eventuallyPoleOrthogonalPosDef_of_posDef h.2⟩)

theorem poleOrthogonalCriticalThreshold_le_highConductorCriticalThreshold :
    poleOrthogonalCriticalThreshold ≤ highConductorCriticalThreshold :=
  sSup_le_sSup (Set.image_mono fun _ h =>
    ⟨h.1, eventuallyHighConductorPosDef_of_poleOrthogonal h.2⟩)

theorem highConductorCriticalThreshold_le_highConductorNonnegativityThreshold :
    highConductorCriticalThreshold ≤ highConductorNonnegativityThreshold :=
  sSup_le_sSup (Set.image_mono fun _ h => ⟨h.1, eventuallyHighConductorNonneg_of_posDef h.2⟩)

theorem criticalNonnegativityThreshold_le_highConductorNonnegativityThreshold :
    criticalNonnegativityThreshold ≤ highConductorNonnegativityThreshold :=
  sSup_le_sSup (Set.image_mono fun _ h =>
    ⟨h.1, eventuallyHighConductorNonneg_of_criticalNonneg h.2⟩)

theorem criticalPositivityThreshold_le_highConductorCriticalThreshold :
    criticalPositivityThreshold ≤ highConductorCriticalThreshold :=
  criticalPositivityThreshold_le_poleOrthogonalCriticalThreshold.trans
    poleOrthogonalCriticalThreshold_le_highConductorCriticalThreshold

/-- **Certified positive floor for `R_c(ζ)`**: the universal critical-multiple reserve implies
`0 < criticalPositivityThreshold`. -/
theorem exists_pos_eventuallyCriticalPosDef :
    ∃ R₀ : ℝ, 0 < R₀ ∧ EventuallyCriticalPosDef R₀ := by
  obtain ⟨K₁, hK₁, _, hfl⟩ :=
    exists_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_at_critical_multiple
  refine ⟨(2 * K₁) ^ 8, by positivity, ?_⟩
  filter_upwards [hfl, eventually_ge_atTop 3] with N hN hN3 c hc1 hc8 z hzne
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc_up : c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) := by
    have hr := Real.rpow_le_rpow (pow_nonneg hc0.le 8) hc8 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hlhs : (c ^ 8) ^ (1 / 8 : ℝ) = c := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_one]
    have hrhs : ((2 * K₁) ^ 8 * Real.log (N : ℝ)) ^ (1 / 8 : ℝ) =
        2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) := by
      rw [Real.mul_rpow (by positivity) hL0.le, ← Real.rpow_natCast (2 * K₁) 8,
        ← Real.rpow_mul (by positivity)]
      norm_num [Real.rpow_one]
    rwa [hlhs, hrhs] at hr
  have hpos : 0 < (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖z‖ ^ 2 :=
    mul_pos (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity))
      (sq_pos_of_pos (norm_pos_iff.mpr hzne))
  exact hpos.trans_le (hN c hc1 hc_up z)

theorem criticalPositivityThreshold_pos : (0 : EReal) < criticalPositivityThreshold := by
  obtain ⟨R₀, hR₀, hpos⟩ := exists_pos_eventuallyCriticalPosDef
  exact (EReal.coe_pos.mpr hR₀).trans_le (le_sSup ⟨R₀, ⟨hR₀, hpos⟩, rfl⟩)

theorem eventuallyCriticalNonneg_of_lt_threshold {R : ℝ} (_hR : 0 < R)
    (hlt : (R : EReal) < criticalNonnegativityThreshold) : EventuallyCriticalNonneg R := by
  obtain ⟨y, ⟨R', ⟨_, hR'⟩, rfl⟩, hy⟩ := lt_sSup_iff.mp hlt
  exact eventuallyCriticalNonneg_antitone (EReal.coe_lt_coe_iff.mp hy).le hR'

/-! ### 2. Canonical critical schedule and window upper bound -/

/-- Canonical critical schedule `c_N = max 1 ((R log N)^{1/8})` realizing `c_N⁸ = R log N`
eventually. -/
private def localCriticalCurve (R : ℝ) (N : ℕ) : ℝ :=
  max 1 ((R * Real.log (N : ℝ)) ^ (1 / 8 : ℝ))

private theorem one_le_localCriticalCurve (R : ℝ) (N : ℕ) : 1 ≤ localCriticalCurve R N :=
  le_max_left 1 _

private theorem eventually_localCriticalCurve_pow_eight {R : ℝ} (hR : 0 < R) :
    ∀ᶠ N : ℕ in atTop, localCriticalCurve R N ^ 8 = R * Real.log (N : ℝ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (max 1 (1 / R))] with N hLN
  have h1R : 1 / R ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hLN
  have hRL1 : 1 ≤ R * Real.log (N : ℝ) := by
    have hm := (div_le_iff₀ hR).mp h1R
    linarith only [hm]
  have hmax : localCriticalCurve R N = (R * Real.log (N : ℝ)) ^ (1 / 8 : ℝ) :=
    max_eq_right (Real.one_le_rpow hRL1 (by norm_num))
  rw [hmax, ← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hRL1)]
  norm_num [Real.rpow_one]

private theorem tendsto_localCriticalCurve_ratio {R : ℝ} (hR : 0 < R) :
    Tendsto (fun N : ℕ => localCriticalCurve R N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_localCriticalCurve_pow_eight hR, hlog.eventually_ge_atTop 1]
    with N hpow hL1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  rw [hpow, mul_div_cancel_right₀ R hL0.ne']

/-- Eventual nonnegativity on `(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ` at ratio `R > 0` forces
`(R : EReal) ≤ windowThreshold A` for every `A ≥ 0`. -/
theorem le_windowThreshold_of_eventuallyHighConductorNonneg {R A : ℝ} (hR : 0 < R) (hA : 0 ≤ A)
    (hnn : EventuallyHighConductorNonneg R) :
    (R : EReal) ≤ windowThreshold A := by
  refine le_iInf fun H => le_iInf fun hH => le_iInf fun hQ => EReal.coe_le_coe_iff.mpr ?_
  set h : ℝ → ℝ := fun y => Real.exp (-(y / 2)) * H y
  have hh : ContDiff ℝ 2 h := (Real.contDiff_exp.comp (by fun_prop)).mul hH.contDiff
  have hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0 := fun y hy => by
    simp only [h, hH.vanish y hy, mul_zero]
  have hc1 : ∀ N, 1 ≤ localCriticalCurve R N := one_le_localCriticalCurve R
  have hcrit := tendsto_localCriticalCurve_ratio hR
  have hlim := horizon_layer_criticalCurve_exact_after_low_projection hh hA hsupp hc1 hR hcrit
  have hev_nonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ (localCriticalCurve R N)⁻¹ *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (localCriticalCurve R N) N)
          (horizonProfileVector (horizonWeights h N) N -
            (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N).starProjection
              (horizonProfileVector (horizonWeights h N) N)),
          horizonProfileVector (horizonWeights h N) N -
            (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N).starProjection
              (horizonProfileVector (horizonWeights h N) N)⟫ := by
    filter_upwards [hnn, eventually_localCriticalCurve_pow_eight hR] with N hN hpow
    have horth :
        horizonProfileVector (horizonWeights h N) N -
            (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N).starProjection
              (horizonProfileVector (horizonWeights h N) N) ∈
          (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal _
    exact mul_nonneg (inv_nonneg.mpr (zero_le_one.trans (hc1 N)))
      (hN (hc1 N) hpow.le horth)
  have hpen_raw := ge_of_tendsto hlim hev_nonneg
  rw [show halfWeight h = H from halfWeight_inv] at hpen_raw
  have hpen : 0 ≤ splineAtom * weilQuad H + 7 * tiltedJordanOne / R * exponentialMass 8 H :=
    hpen_raw
  have hq : 0 < -weilQuad H := neg_pos.mpr hQ
  have hκ := splineAtom_pos
  rw [testCriticalMultiple, le_div_iff₀ (mul_pos hκ hq)]
  have h1 : splineAtom * -weilQuad H ≤ 7 * tiltedJordanOne / R * exponentialMass 8 H := by
    linarith only [hpen]
  have h2 := mul_le_mul_of_nonneg_left h1 hR.le
  have h3 : R * (7 * tiltedJordanOne / R * exponentialMass 8 H) =
      7 * tiltedJordanOne * exponentialMass 8 H := by
    field_simp
  linarith only [h2, h3]

/-- **Window upper bound on the high-conductor threshold**:
`highConductorNonnegativityThreshold ≤ ⨅ A ≥ 0, windowThreshold A`. -/
theorem highConductorNonnegativityThreshold_le_iInf_windowThreshold :
    highConductorNonnegativityThreshold ≤ ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
  refine sSup_le ?_
  rintro _ ⟨R, ⟨hR, hnn⟩, rfl⟩
  exact le_iInf fun A => le_iInf fun hA =>
    le_windowThreshold_of_eventuallyHighConductorNonneg hR hA hnn

/-! ### 3. Reflected spline mollifier and weighted `L²` / Fourier estimates -/

/-- One-sided `C²` probability density supported in `[−δ, 0]`, obtained by reflecting and dilating
`tiltedUnitSpline`. -/
def leftSplineMollifier (δ s : ℝ) : ℝ :=
  (δ * ∫ u, tiltedUnitSpline u)⁻¹ * tiltedUnitSpline (-(s / δ))

theorem leftSplineMollifier_nonneg {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 ≤ leftSplineMollifier δ s := by
  have hm : 0 < ∫ u, tiltedUnitSpline u :=
    CriticalArithmeticCorrelationTheory.integral_tiltedUnitSpline_pos
  exact mul_nonneg (inv_nonneg.mpr (mul_pos hδ hm).le) (tiltedUnitSpline_nonneg _)

theorem leftSplineMollifier_eq_zero {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ∉ Set.Icc (-δ) 0) :
    leftSplineMollifier δ s = 0 := by
  unfold leftSplineMollifier
  have hnot : -(s / δ) ∉ Set.Icc (0 : ℝ) 1 := by
    intro hm
    apply hs
    rw [Set.mem_Icc] at hm ⊢
    have h1 := (le_div_iff₀ hδ).mp (show -1 ≤ s / δ by linarith only [hm.2])
    have h2 := (div_le_iff₀ hδ).mp (show s / δ ≤ 0 by linarith only [hm.1])
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  rw [tiltedUnitSpline_support _ hnot, mul_zero]

theorem hasCompactSupport_leftSplineMollifier {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (leftSplineMollifier δ) :=
  HasCompactSupport.intro isCompact_Icc fun _ hs => leftSplineMollifier_eq_zero hδ hs

theorem contDiff_leftSplineMollifier (δ : ℝ) : ContDiff ℝ 2 (leftSplineMollifier δ) :=
  contDiff_const.mul (contDiff_tiltedUnitSpline.comp (contDiff_id.div_const δ).neg)

theorem integrable_leftSplineMollifier {δ : ℝ} (hδ : 0 < δ) :
    Integrable (leftSplineMollifier δ) :=
  (contDiff_leftSplineMollifier δ).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_leftSplineMollifier hδ)

theorem integral_leftSplineMollifier {δ : ℝ} (hδ : 0 < δ) :
    (∫ s, leftSplineMollifier δ s) = 1 := by
  have hm : 0 < ∫ u, tiltedUnitSpline u :=
    CriticalArithmeticCorrelationTheory.integral_tiltedUnitSpline_pos
  unfold leftSplineMollifier
  rw [integral_const_mul]
  have hneg : (∫ s : ℝ, tiltedUnitSpline (-(s / δ))) = ∫ s : ℝ, tiltedUnitSpline (s / δ) := by
    simpa only [neg_div] using
      MeasureTheory.integral_neg_eq_self (fun s : ℝ => tiltedUnitSpline (s / δ)) volume
  have hdiv := MeasureTheory.Measure.integral_comp_div tiltedUnitSpline δ
  simp only [smul_eq_mul, abs_of_pos hδ] at hdiv
  rw [hneg, hdiv, inv_mul_cancel₀ (mul_pos hδ hm).ne']

theorem norm_paperFT_leftSplineMollifier_le {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ‖paperFT (cx (leftSplineMollifier δ)) r‖ ≤ 1 := by
  refine (norm_paperFT_le (leftSplineMollifier δ) r).trans ?_
  have habs : (∫ s, ‖leftSplineMollifier δ s‖) = ∫ s, leftSplineMollifier δ s :=
    integral_congr_ae (Eventually.of_forall fun s => by
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg (leftSplineMollifier_nonneg hδ s)])
  rw [habs, integral_leftSplineMollifier hδ]

theorem norm_one_sub_paperFT_leftSplineMollifier_le {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ‖1 - paperFT (cx (leftSplineMollifier δ)) r‖ ≤ |r| * δ := by
  have hi := integrable_leftSplineMollifier hδ
  have hic : Integrable (cx (leftSplineMollifier δ)) := hi.ofReal
  have hker : Integrable fun s : ℝ =>
      cx (leftSplineMollifier δ) s * Complex.exp (Complex.I * (r : ℂ) * (s : ℂ)) :=
    WeilHerglotz.integrable_mul_cexp hic
      ((hasCompactSupport_leftSplineMollifier hδ).comp_left Complex.ofReal_zero) r
  have h1 : (∫ s, cx (leftSplineMollifier δ) s) = 1 := by
    unfold cx
    rw [integral_complex_ofReal, integral_leftSplineMollifier hδ, Complex.ofReal_one]
  have hsub : (1 : ℂ) - paperFT (cx (leftSplineMollifier δ)) r =
      ∫ s, cx (leftSplineMollifier δ) s * (1 - Complex.exp (Complex.I * (r : ℂ) * (s : ℂ))) := by
    calc (1 : ℂ) - paperFT (cx (leftSplineMollifier δ)) r
        = (∫ s, cx (leftSplineMollifier δ) s) -
            ∫ s, cx (leftSplineMollifier δ) s * Complex.exp (Complex.I * (r : ℂ) * (s : ℂ)) := by
          rw [h1, paperFT_def]
      _ = ∫ s, (cx (leftSplineMollifier δ) s -
            cx (leftSplineMollifier δ) s * Complex.exp (Complex.I * (r : ℂ) * (s : ℂ))) :=
          (integral_sub hic hker).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun s => by dsimp only; ring)
  rw [hsub]
  refine (norm_integral_le_of_norm_le (hi.mul_const (|r| * δ))
    (Eventually.of_forall fun s => ?_)).trans ?_
  · dsimp only [cx]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (leftSplineMollifier_nonneg hδ s)]
    by_cases hs : s ∈ Set.Icc (-δ) 0
    · refine mul_le_mul_of_nonneg_left ?_ (leftSplineMollifier_nonneg hδ s)
      rw [norm_sub_rev,
        show Complex.I * (r : ℂ) * (s : ℂ) = Complex.I * ((r * s : ℝ) : ℂ) by push_cast; ring]
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
      rw [Real.norm_eq_abs, abs_mul]
      have habs_s : |s| ≤ δ := abs_le.mpr ⟨hs.1, hs.2.trans hδ.le⟩
      exact mul_le_mul_of_nonneg_left habs_s (abs_nonneg r)
    · rw [leftSplineMollifier_eq_zero hδ hs, zero_mul, zero_mul]
  · rw [integral_mul_const, integral_leftSplineMollifier hδ, one_mul]

private theorem cx_lineConvolution_eq {ρ G : ℝ → ℝ} (x : ℝ) :
    cx (HTGeometry.lineConvolution ρ G) x =
      convolution (cx ρ) (cx G) (ContinuousLinearMap.mul ℝ ℂ) volume x := by
  simp only [cx, HTGeometry.lineConvolution, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal]
  exact integral_congr_ae (Eventually.of_forall fun s => by dsimp only; push_cast; rfl)

private theorem paperFT_lineConvolution_leftSplineMollifier {δ : ℝ} (hδ : 0 < δ) {G : ℝ → ℝ}
    (hGi : Integrable G) (hGc : HasCompactSupport G) (r : ℝ) :
    paperFT (cx (HTGeometry.lineConvolution (leftSplineMollifier δ) G)) r =
      paperFT (cx (leftSplineMollifier δ)) r * paperFT (cx G) r := by
  have hfn : cx (HTGeometry.lineConvolution (leftSplineMollifier δ) G) =
      convolution (cx (leftSplineMollifier δ)) (cx G) (ContinuousLinearMap.mul ℝ ℂ) volume :=
    funext cx_lineConvolution_eq
  rw [hfn]
  exact WeilHerglotz.paperFT_convolution (integrable_leftSplineMollifier hδ).ofReal hGi.ofReal
    ((hasCompactSupport_leftSplineMollifier hδ).comp_left Complex.ofReal_zero)
    (hGc.comp_left Complex.ofReal_zero) r

/-- Multiplying by `e^{−4 x}` intertwines `lineConvolution (leftSplineMollifier δ)` with a weighted
kernel of `L¹` mass at most `e^{4 δ}`, giving an explicit `e^{8 δ}` bound on the eighth exponential
mass. -/
private theorem integral_exp8_lineConvolution_leftSplineMollifier_le {δ : ℝ} (hδ : 0 < δ)
    {G : ℝ → ℝ} (hGm : Measurable G) (_hG2 : Integrable fun u => G u ^ 2)
    (hG8 : Integrable fun u => G u ^ 2 * Real.exp (-(8 * u))) :
    Integrable (fun x => HTGeometry.lineConvolution (leftSplineMollifier δ) G x ^ 2 *
        Real.exp (-(8 * x))) ∧
      (∫ x, HTGeometry.lineConvolution (leftSplineMollifier δ) G x ^ 2 * Real.exp (-(8 * x))) ≤
        Real.exp (8 * δ) * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
  set ρw : ℝ → ℝ := fun s => Real.exp (-(4 * s)) * leftSplineMollifier δ s
  set Gw : ℝ → ℝ := fun u => Real.exp (-(4 * u)) * G u
  have hρw_cont : Continuous ρw :=
    (Real.continuous_exp.comp (by fun_prop)).mul (contDiff_leftSplineMollifier δ).continuous
  have hρw_cs : HasCompactSupport ρw := (hasCompactSupport_leftSplineMollifier hδ).mul_left
  have hGw_m : Measurable Gw := (Real.continuous_exp.comp (by fun_prop)).measurable.mul hGm
  have hGw_sq : (fun u => Gw u ^ 2) = fun u => G u ^ 2 * Real.exp (-(8 * u)) := by
    funext u
    dsimp only [Gw]
    rw [mul_pow, ← Real.exp_nat_mul]
    have hexp : ((2 : ℕ) : ℝ) * -(4 * u) = -(8 * u) := by push_cast; ring
    rw [hexp, mul_comm]
  have hGw2 : Integrable fun u => Gw u ^ 2 := hGw_sq.symm ▸ hG8
  have hρ_cont := (contDiff_leftSplineMollifier δ).continuous
  have hρ_cs := hasCompactSupport_leftSplineMollifier hδ
  have hρ2 : Integrable fun s => leftSplineMollifier δ s ^ 2 :=
    (hρ_cont.pow 2).integrable_of_hasCompactSupport (HTGeometry.hasCompactSupport_sq hρ_cs)
  have hpt : ∀ x, HTGeometry.lineConvolution ρw Gw x =
      Real.exp (-(4 * x)) * HTGeometry.lineConvolution (leftSplineMollifier δ) G x := by
    intro x
    unfold HTGeometry.lineConvolution
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    dsimp only [ρw, Gw]
    have hexp : Real.exp (-(4 * s)) * Real.exp (-(4 * (x - s))) = Real.exp (-(4 * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination leftSplineMollifier δ s * G (x - s) * hexp
  have hsq_eq : (fun x => HTGeometry.lineConvolution ρw Gw x ^ 2) =
      fun x => HTGeometry.lineConvolution (leftSplineMollifier δ) G x ^ 2 *
        Real.exp (-(8 * x)) := by
    funext x
    rw [hpt x, mul_pow, ← Real.exp_nat_mul]
    have hexp : ((2 : ℕ) : ℝ) * -(4 * x) = -(8 * x) := by push_cast; ring
    rw [hexp, mul_comm]
  have hconv_int : Integrable fun x => HTGeometry.lineConvolution ρw Gw x ^ 2 :=
    HTGeometry.integrable_sq_lineConvolution hρw_cont hρw_cs hGw_m hGw2
  have hρw_i : Integrable fun s => |ρw s| :=
    (hρw_cont.integrable_of_hasCompactSupport hρw_cs).abs
  have hyoung := HTGeometry.integral_sq_lineConvolution_le hρw_cont.measurable hGw_m hρw_i
    hGw2 hconv_int
  have hρw_L1 : (∫ s, |ρw s|) ≤ Real.exp (4 * δ) := by
    have hpt_le : ∀ s, |ρw s| ≤ Real.exp (4 * δ) * leftSplineMollifier δ s := by
      intro s
      have hnn : 0 ≤ ρw s := mul_nonneg (Real.exp_pos _).le (leftSplineMollifier_nonneg hδ s)
      rw [abs_of_nonneg hnn]
      by_cases hs : s ∈ Set.Icc (-δ) 0
      · exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith only [hs.1])) (leftSplineMollifier_nonneg hδ s)
      · dsimp only [ρw]; rw [leftSplineMollifier_eq_zero hδ hs, mul_zero, mul_zero]
    refine (integral_mono hρw_i ((integrable_leftSplineMollifier hδ).const_mul _) hpt_le).trans_eq ?_
    rw [integral_const_mul, integral_leftSplineMollifier hδ, mul_one]
  have hρw_sq : (∫ s, |ρw s|) ^ 2 ≤ Real.exp (8 * δ) := by
    calc (∫ s, |ρw s|) ^ 2 ≤ Real.exp (4 * δ) ^ 2 :=
          pow_le_pow_left₀ (integral_nonneg fun _ => abs_nonneg _) hρw_L1 2
      _ = Real.exp (8 * δ) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hsq_eq, hGw_sq] at hyoung
  exact ⟨hsq_eq ▸ hconv_int, hyoung.trans (mul_le_mul_of_nonneg_right hρw_sq
    (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))⟩

/-- `L²` approximation of an `L²` profile by `leftSplineMollifier δ` as `δ → 0⁺`. -/
private theorem tendsto_integral_sq_lineConvolution_leftSplineMollifier_sub {F : ℝ → ℝ}
    (hFm : Measurable F) (hF2 : Integrable fun x => F x ^ 2) :
    Tendsto (fun k : ℕ => ∫ x,
      (HTGeometry.lineConvolution (leftSplineMollifier (1 / ((k : ℝ) + 1))) F x - F x) ^ 2)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hF_lp : MemLp F (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).mpr hF2
  obtain ⟨g, hgc, hg_dist, hg_cont, hg_lp⟩ :=
    hF_lp.exists_hasCompactSupport_integral_rpow_sub_le zero_lt_two (by positivity : 0 < ε / 16)
  rw [ENNReal.ofReal_ofNat] at hg_lp
  have hg2 : Integrable fun x => g x ^ 2 :=
    (memLp_two_iff_integrable_sq hg_cont.aestronglyMeasurable).mp hg_lp
  have hFg_sq : (∫ x, (F x - g x) ^ 2) ≤ ε / 16 := by
    refine le_trans (le_of_eq ?_) hg_dist
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← sq_abs, Real.norm_eq_abs, ← Real.rpow_natCast, Nat.cast_two]
  obtain ⟨Rg, hRg_sub⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  set R₁ : ℝ := max Rg 1
  have hR₁_pos : 0 < R₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hg_out : ∀ u, R₁ < |u| → g u = 0 := by
    intro u hu
    by_contra hne
    have hm := hRg_sub (subset_tsupport g hne)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hm
    linarith [le_max_left Rg 1]
  set η_g : ℝ := Real.sqrt (ε / (16 * (2 * R₁ + 2)))
  have hηg_pos : 0 < η_g := Real.sqrt_pos.mpr (by positivity)
  have hunif := Metric.uniformContinuous_iff.mp (hgc.uniformContinuous_of_continuous hg_cont)
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hunif η_g hηg_pos
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [hinv.eventually (gt_mem_nhds (lt_min one_pos hδ₁_pos))] with k hk_lt
  set δ : ℝ := 1 / ((k : ℝ) + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ1 : δ ≤ 1 := (hk_lt.trans_le (min_le_left _ _)).le
  have hδ_δ₁ : δ < δ₁ := hk_lt.trans_le (min_le_right _ _)
  have hρ_cont := (contDiff_leftSplineMollifier δ).continuous
  have hρ_cs := hasCompactSupport_leftSplineMollifier hδ
  have hρ2 : Integrable fun s => leftSplineMollifier δ s ^ 2 :=
    (hρ_cont.pow 2).integrable_of_hasCompactSupport (HTGeometry.hasCompactSupport_sq hρ_cs)
  have hconv_Fg_int : Integrable fun x =>
      HTGeometry.lineConvolution (leftSplineMollifier δ) (fun t => F t - g t) x ^ 2 :=
    HTGeometry.integrable_sq_lineConvolution hρ_cont hρ_cs (hFm.sub hg_cont.measurable)
      (by
        have hdom : Integrable fun t => 2 * F t ^ 2 + 2 * g t ^ 2 :=
          (hF2.const_mul 2).add (hg2.const_mul 2)
        refine hdom.mono' ((hFm.sub hg_cont.measurable).pow_const 2).aestronglyMeasurable
          (Eventually.of_forall fun t => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith only [sq_nonneg (F t + g t)])
  have hFg2 : Integrable fun t => (F t - g t) ^ 2 := by
    have hdom : Integrable fun t => 2 * F t ^ 2 + 2 * g t ^ 2 :=
      (hF2.const_mul 2).add (hg2.const_mul 2)
    refine hdom.mono' ((hFm.sub hg_cont.measurable).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [sq_nonneg (F t + g t)]
  have hcontr : (∫ x, HTGeometry.lineConvolution (leftSplineMollifier δ)
      (fun t => F t - g t) x ^ 2) ≤ ε / 16 :=
    (HTGeometry.integral_sq_mollify_le_of_isProbabilityDensity hρ_cont.measurable
      (hFm.sub hg_cont.measurable) (leftSplineMollifier_nonneg hδ)
      (integrable_leftSplineMollifier hδ) (integral_leftSplineMollifier hδ) hFg2
      hconv_Fg_int).trans hFg_sq
  have hmid_supp : ∀ x ∉ Set.Icc (-(R₁ + 1)) (R₁ + 1),
      (HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x) ^ 2 = 0 := by
    intro x hx
    have hx_abs : R₁ + 1 < |x| := by
      by_contra hle; push Not at hle
      exact hx (abs_le.mp hle)
    have hg0 : g x = 0 := hg_out x (by linarith only [hx_abs])
    have hc0 : HTGeometry.lineConvolution (leftSplineMollifier δ) g x = 0 := by
      unfold HTGeometry.lineConvolution
      refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      dsimp only [Pi.zero_apply]
      by_cases hs : s ∈ Set.Icc (-δ) 0
      · have hs_abs : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2.trans zero_le_one⟩
        have hxs : R₁ < |x - s| := by
          have htri := abs_sub_abs_le_abs_sub x s
          linarith only [hx_abs, hs_abs, htri]
        rw [hg_out _ hxs, mul_zero]
      · rw [leftSplineMollifier_eq_zero hδ hs, zero_mul]
    rw [hc0, hg0, sub_self, sq, mul_zero]
  have hmid_pt : ∀ x, |HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x| ≤ η_g := by
    intro x
    have hid : HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x =
        ∫ s, leftSplineMollifier δ s * (g (x - s) - g x) := by
      have h1 : (∫ s, leftSplineMollifier δ s * g x) = g x := by
        rw [integral_mul_const, integral_leftSplineMollifier hδ, one_mul]
      have hint1 := HTGeometry.integrable_kernel_mul_sq hρ_cont.aestronglyMeasurable hρ2
        hg_cont.aestronglyMeasurable hg2 x
      have hint2 := (integrable_leftSplineMollifier hδ).mul_const (g x)
      calc HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x
          = (∫ s, leftSplineMollifier δ s * g (x - s)) -
              ∫ s, leftSplineMollifier δ s * g x := by
            rw [HTGeometry.lineConvolution, h1]
        _ = ∫ s, (leftSplineMollifier δ s * g (x - s) - leftSplineMollifier δ s * g x) :=
            (integral_sub hint1 hint2).symm
        _ = _ := integral_congr_ae (Eventually.of_forall fun s => by dsimp only; ring)
    rw [hid, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le ((integrable_leftSplineMollifier hδ).mul_const η_g)
      (Eventually.of_forall fun s => ?_)).trans ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (leftSplineMollifier_nonneg hδ s)]
      by_cases hs : s ∈ Set.Icc (-δ) 0
      · refine mul_le_mul_of_nonneg_left ?_ (leftSplineMollifier_nonneg hδ s)
        have hd : dist (x - s) x < δ₁ := by
          rw [Real.dist_eq, show x - s - x = -s by ring, abs_neg]
          exact (abs_le.mpr ⟨hs.1, hs.2.trans hδ.le⟩).trans_lt hδ_δ₁
        exact (Real.dist_eq (g (x - s)) (g x) ▸ hδ₁ hd).le
      · rw [leftSplineMollifier_eq_zero hδ hs, zero_mul, zero_mul]
    · rw [integral_mul_const, integral_leftSplineMollifier hδ, one_mul]
  have hmid_cont : Continuous fun x =>
      (HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x) ^ 2 :=
    ((HTGeometry.continuous_lineConvolution hρ_cont hρ_cs
      (HTGeometry.locallyIntegrable_of_sq_integrable hg_cont.aestronglyMeasurable hg2)).sub
        hg_cont).pow 2
  have hmid_int : Integrable fun x =>
      (HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x) ^ 2 :=
    hmid_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_Icc fun x hx => hmid_supp x hx)
  have hmid_le : (∫ x, (HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x) ^ 2) ≤
      ε / 16 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hmid_supp]
    have hb : (∫ x in Set.Icc (-(R₁ + 1)) (R₁ + 1),
        (HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x) ^ 2) ≤
        ∫ _x in Set.Icc (-(R₁ + 1)) (R₁ + 1), η_g ^ 2 :=
      setIntegral_mono_on hmid_int.integrableOn (integrableOn_const isCompact_Icc.measure_ne_top)
        measurableSet_Icc fun x _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hmid_pt x) 2
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith only [hR₁_pos])] at hb
    refine hb.trans_eq ?_
    dsimp only [η_g]
    rw [Real.sq_sqrt (by positivity)]
    have hne : 2 * R₁ + 2 ≠ 0 := by positivity
    field_simp [hne]; ring
  have hlin : ∀ x, HTGeometry.lineConvolution (leftSplineMollifier δ) F x - F x =
      HTGeometry.lineConvolution (leftSplineMollifier δ) (fun t => F t - g t) x +
        (HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x) + (g x - F x) := by
    intro x
    have hintF := HTGeometry.integrable_kernel_mul_sq hρ_cont.aestronglyMeasurable hρ2
      hFm.aestronglyMeasurable hF2 x
    have hintg := HTGeometry.integrable_kernel_mul_sq hρ_cont.aestronglyMeasurable hρ2
      hg_cont.aestronglyMeasurable hg2 x
    have hsub : HTGeometry.lineConvolution (leftSplineMollifier δ) (fun t => F t - g t) x =
        HTGeometry.lineConvolution (leftSplineMollifier δ) F x -
          HTGeometry.lineConvolution (leftSplineMollifier δ) g x := by
      unfold HTGeometry.lineConvolution
      rw [← integral_sub hintF hintg]
      exact integral_congr_ae (Eventually.of_forall fun s => by dsimp only; ring)
    linarith only [hsub]
  have hgF2 : Integrable fun x => (g x - F x) ^ 2 := by
    refine hFg2.congr (Eventually.of_forall fun x => by dsimp only; ring)
  have hgF_sq : (∫ x, (g x - F x) ^ 2) = ∫ x, (F x - g x) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun x => by dsimp only; ring)
  have hdom_tot : Integrable fun x =>
      3 * HTGeometry.lineConvolution (leftSplineMollifier δ) (fun t => F t - g t) x ^ 2 +
        3 * (HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x) ^ 2 +
        3 * (g x - F x) ^ 2 :=
    ((hconv_Fg_int.const_mul 3).add (hmid_int.const_mul 3)).add (hgF2.const_mul 3)
  have htot_int : Integrable fun x =>
      (HTGeometry.lineConvolution (leftSplineMollifier δ) F x - F x) ^ 2 := by
    have hm : Measurable fun x =>
        (HTGeometry.lineConvolution (leftSplineMollifier δ) F x - F x) ^ 2 :=
      (((HTGeometry.continuous_lineConvolution hρ_cont hρ_cs
        (HTGeometry.locallyIntegrable_of_sq_integrable hFm.aestronglyMeasurable hF2)).measurable.sub
          hFm).pow_const 2)
    refine hdom_tot.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hlin x]
    set a := HTGeometry.lineConvolution (leftSplineMollifier δ) (fun t => F t - g t) x
    set b := HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x
    set c := g x - F x
    nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have htot_le : (∫ x, (HTGeometry.lineConvolution (leftSplineMollifier δ) F x - F x) ^ 2) ≤
      (9 / 16 : ℝ) * ε := by
    have hm := integral_mono htot_int hdom_tot fun x => by
      rw [hlin x]
      set a := HTGeometry.lineConvolution (leftSplineMollifier δ) (fun t => F t - g t) x
      set b := HTGeometry.lineConvolution (leftSplineMollifier δ) g x - g x
      set c := g x - F x
      nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have hadd1 := integral_add ((hconv_Fg_int.const_mul 3).add (hmid_int.const_mul 3))
      (hgF2.const_mul 3)
    have hadd2 := integral_add (hconv_Fg_int.const_mul 3) (hmid_int.const_mul 3)
    dsimp only [Pi.add_apply] at hadd1 hadd2
    rw [hadd1, hadd2, integral_const_mul, integral_const_mul, integral_const_mul, hgF_sq] at hm
    linarith only [hm, hcontr, hmid_le, hFg_sq]
  have h0 : 0 ≤ ∫ x, (HTGeometry.lineConvolution (leftSplineMollifier δ) F x - F x) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith only [htot_le, hε]

/-! ### 4. `L²` precompactness and window mollification of collar limits -/

/-- Kolmogorov–Riesz `L²` precompactness for smooth compactly supported profiles of unit `L²` norm,
bounded eighth exponential mass, support bounded above by `1`, and bounded `weilQuad`. -/
private theorem totallyBounded_toLp_of_bounded_weilQuad {V : ℕ → ℝ → ℝ}
    (hVd : ∀ k, ContDiff ℝ 2 (V k)) (hVc : ∀ k, HasCompactSupport (V k))
    (hmass : ∀ k, (∫ u, V k u ^ 2) ≤ 1)
    {M₈ : ℝ} (hM₈0 : 0 ≤ M₈) (hM₈ : ∀ k, (∫ u, V k u ^ 2 * Real.exp (-(8 * u))) ≤ M₈)
    (hsupp1 : ∀ k u, 1 < u → V k u = 0)
    {b : ℝ} (hb : ∀ k, weilQuad (V k) ≤ b)
    (hmem : ∀ k, MemLp (V k) 2 (volume : Measure ℝ)) :
    TotallyBounded (Set.range fun k : ℕ => (hmem k).toLp (V k)) := by
  have htails : ∀ ε > 0, ∃ T > 0, ∀ k, highFourierMass (V k) T ≤ ε := by
    intro ε hε
    obtain ⟨T, hT, hall⟩ := high_tails_of_bounded_weilQuad (l := ⊤) hVd hVc hmass hM₈
      (Filter.eventually_top.mpr hsupp1) (Filter.eventually_top.mpr hb) ε hε
    exact ⟨T, hT, Filter.eventually_top.mp hall⟩
  rw [Metric.totallyBounded_iff]
  intro r_ball hr_ball
  set ε_sq : ℝ := (r_ball / 2) ^ 2
  have hε_sq : 0 < ε_sq := by positivity
  obtain ⟨T, hT, hT_tail⟩ := htails (ε_sq / 8) (by positivity)
  set η : ℝ := min 1 (Real.sqrt (ε_sq / 2) / T)
  have hη : 0 < η := lt_min zero_lt_one (div_pos (Real.sqrt_pos.mpr (by positivity)) hT)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hTη_sq : (T * η) ^ 2 ≤ ε_sq / 2 := by
    have hle : T * η ≤ Real.sqrt (ε_sq / 2) := by
      have hm := mul_le_mul_of_nonneg_left (min_le_right 1 (Real.sqrt (ε_sq / 2) / T)) hT.le
      rwa [mul_div_cancel₀ _ hT.ne'] at hm
    calc (T * η) ^ 2 ≤ Real.sqrt (ε_sq / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
      _ = ε_sq / 2 := Real.sq_sqrt (by positivity)
  set W : ℕ → ℝ → ℝ := fun k => HTGeometry.lineConvolution (leftSplineMollifier η) (V k)
  set W' : ℕ → ℝ → ℝ := fun k => HTGeometry.lineConvolution (deriv (leftSplineMollifier η)) (V k)
  have hρ_cd1 : ContDiff ℝ 1 (leftSplineMollifier η) :=
    (contDiff_leftSplineMollifier η).of_le (by norm_num)
  have hρ_cs := hasCompactSupport_leftSplineMollifier hη
  have hρ'_cont : Continuous (deriv (leftSplineMollifier η)) := hρ_cd1.continuous_deriv le_rfl
  have hρ'_cs : HasCompactSupport (deriv (leftSplineMollifier η)) := hρ_cs.deriv
  have hρ'_L1 : Integrable fun s => |deriv (leftSplineMollifier η) s| :=
    (hρ'_cont.integrable_of_hasCompactSupport hρ'_cs).abs
  have hVk2 : ∀ k, Integrable fun u => V k u ^ 2 := fun k =>
    ((hVd k).continuous.pow 2).integrable_of_hasCompactSupport (HTGeometry.hasCompactSupport_sq (hVc k))
  have hVk8 : ∀ k, Integrable fun u => V k u ^ 2 * Real.exp (-(8 * u)) := fun k =>
    (((hVd k).continuous.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport
      (HTGeometry.hasCompactSupport_sq (hVc k)).mul_right
  have hW_cd : ∀ k, ContDiff ℝ 2 (W k) := fun k => by
    dsimp only [W]
    rw [HTGeometry.lineConvolution_eq_convolution]
    exact hρ_cs.contDiff_convolution_left _ (contDiff_leftSplineMollifier η)
      ((hVd k).continuous.integrable_of_hasCompactSupport (hVc k)).locallyIntegrable
  have hW_cs : ∀ k, HasCompactSupport (W k) := fun k => by
    dsimp only [W]
    rw [HTGeometry.lineConvolution_eq_convolution]
    exact hρ_cs.convolution _ (hVc k)
  have hW_mem : ∀ k, MemLp (W k) 2 (volume : Measure ℝ) := fun k =>
    (hW_cd k).continuous.memLp_of_hasCompactSupport (hW_cs k)
  have hW_deriv : ∀ k x, HasDerivAt (W k) (W' k x) x := fun k x =>
    HTGeometry.hasDerivAt_lineConvolution hρ_cd1 hρ_cs
      (HTGeometry.locallyIntegrable_of_sq_integrable (hVd k).continuous.aestronglyMeasurable
        (hVk2 k)) x
  have hW'_cont : ∀ k, Continuous (W' k) := fun k =>
    HTGeometry.continuous_lineConvolution hρ'_cont hρ'_cs
      (HTGeometry.locallyIntegrable_of_sq_integrable (hVd k).continuous.aestronglyMeasurable
        (hVk2 k))
  have hW_bound : ∀ k, (∫ x, W k x ^ 2) ≤ 1 := fun k =>
    (HTGeometry.integral_sq_mollify_le_of_isProbabilityDensity
      (contDiff_leftSplineMollifier η).continuous.measurable (hVd k).continuous.measurable
      (leftSplineMollifier_nonneg hη) (integrable_leftSplineMollifier hη)
      (integral_leftSplineMollifier hη) (hVk2 k)
      ((hW_cd k).continuous.pow 2 |>.integrable_of_hasCompactSupport
        (HTGeometry.hasCompactSupport_sq (hW_cs k)))).trans (hmass k)
  set D : ℝ := (∫ s, |deriv (leftSplineMollifier η) s|) ^ 2
  have hD0 : 0 ≤ D := sq_nonneg _
  have hW'_int : ∀ k, Integrable fun x => W' k x ^ 2 := fun k =>
    HTGeometry.integrable_sq_lineConvolution hρ'_cont hρ'_cs (hVd k).continuous.measurable (hVk2 k)
  have hW'_bound : ∀ k, (∫ x, W' k x ^ 2) ≤ D := fun k => by
    refine (HTGeometry.integral_sq_lineConvolution_le hρ'_cont.measurable
      (hVd k).continuous.measurable hρ'_L1 (hVk2 k) (hW'_int k)).trans ?_
    simpa only [D, mul_one] using mul_le_mul_of_nonneg_left (hmass k) hD0
  have hW_supp1 : ∀ k x, 1 < x → W k x = 0 := by
    intro k x hx
    dsimp only [W, HTGeometry.lineConvolution]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
    dsimp only [Pi.zero_apply]
    by_cases hs : s ∈ Set.Icc (-η) 0
    · rw [hsupp1 k (x - s) (by linarith only [hx, hs.2]), mul_zero]
    · rw [leftSplineMollifier_eq_zero hη hs, zero_mul]
  have hW_tight : ∀ ε_t : ℝ, 0 < ε_t → ∃ R : ℝ, 0 < R ∧ ∀ k : ℕ,
      (∫ x in {x : ℝ | R < |x|}, W k x ^ 2) ≤ ε_t := by
    intro ε_t hε_t
    set C_t : ℝ := Real.exp 8 * M₈ + 1
    have hCt : 0 < C_t := by positivity
    set R : ℝ := max 2 (Real.log (C_t / ε_t) / 8 + 1)
    refine ⟨R, lt_of_lt_of_le two_pos (le_max_left _ _), fun k => ?_⟩
    have hR1 : 1 < R := lt_of_lt_of_le one_lt_two (le_max_left _ _)
    obtain ⟨hW8_int, hW8_le⟩ := integral_exp8_lineConvolution_leftSplineMollifier_le hη
      (hVd k).continuous.measurable (hVk2 k) (hVk8 k)
    have hW8_bd : (∫ x, W k x ^ 2 * Real.exp (-(8 * x))) ≤ C_t := by
      have hexp : Real.exp (8 * η) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith only [hη1])
      have hm := mul_le_mul hexp (hM₈ k)
        (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le
      dsimp only [C_t]
      linarith only [hW8_le, hm]
    have hW2_int : Integrable fun x => W k x ^ 2 :=
      ((hW_cd k).continuous.pow 2).integrable_of_hasCompactSupport
        (HTGeometry.hasCompactSupport_sq (hW_cs k))
    have hmeas_abs : MeasurableSet {x : ℝ | R < |x|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have hpt : ∀ x ∈ {x : ℝ | R < |x|},
        W k x ^ 2 ≤ Real.exp (-8 * R) * (W k x ^ 2 * Real.exp (-(8 * x))) := by
      intro x hx
      rw [Set.mem_setOf_eq] at hx
      rcases lt_or_ge 1 x with hx1 | hx1
      · rw [hW_supp1 k x hx1]; simp
      · have hxR : x < -R := by
          rcases lt_or_ge x 0 with hxn | hxp
          · rw [abs_of_neg hxn] at hx; linarith only [hx]
          · rw [abs_of_nonneg hxp] at hx; linarith only [hx, hx1, hR1]
        have hexp_ge : 1 ≤ Real.exp (-8 * R) * Real.exp (-(8 * x)) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith only [hxR])
        have hm := mul_le_mul_of_nonneg_left hexp_ge (sq_nonneg (W k x))
        linarith only [hm]
    have hW8_int' : Integrable fun x => W k x ^ 2 * Real.exp (-(8 * x)) := hW8_int
    have htail_le : (∫ x in {x : ℝ | R < |x|}, W k x ^ 2) ≤
        Real.exp (-8 * R) * C_t := by
      have hm := setIntegral_mono_on hW2_int.integrableOn
        (hW8_int'.const_mul (Real.exp (-8 * R))).integrableOn hmeas_abs hpt
      have htot : (∫ x in {x : ℝ | R < |x|},
          Real.exp (-8 * R) * (W k x ^ 2 * Real.exp (-(8 * x)))) ≤
          Real.exp (-8 * R) * ∫ x, W k x ^ 2 * Real.exp (-(8 * x)) := by
        refine (setIntegral_le_integral (hW8_int'.const_mul (Real.exp (-8 * R)))
          (Eventually.of_forall fun _ => by positivity)).trans_eq ?_
        exact MeasureTheory.integral_const_mul (Real.exp (-8 * R)) _
      exact (hm.trans htot).trans (mul_le_mul_of_nonneg_left hW8_bd (Real.exp_pos _).le)
    refine htail_le.trans ?_
    have hR_log : Real.log (C_t / ε_t) / 8 + 1 ≤ R := le_max_right _ _
    have hexp_le : Real.exp (-8 * R) ≤ ε_t / C_t := by
      have h1 : -8 * R ≤ -Real.log (C_t / ε_t) := by linarith only [hR_log]
      calc Real.exp (-8 * R) ≤ Real.exp (-Real.log (C_t / ε_t)) := Real.exp_le_exp.mpr h1
        _ = (C_t / ε_t)⁻¹ := by rw [Real.exp_neg, Real.exp_log (div_pos hCt hε_t)]
        _ = ε_t / C_t := inv_div C_t ε_t
    exact (mul_le_mul_of_nonneg_right hexp_le hCt.le).trans_eq (div_mul_cancel₀ ε_t hCt.ne')
  have hW_tb := HTGeometry.totallyBounded_toLp_of_tight_deriv hW_mem hW_deriv hW'_cont
    hW_bound hD0 hW'_int hW'_bound hW_tight
  obtain ⟨t_centers, ht_fin, ht_cov⟩ := Metric.totallyBounded_iff.mp hW_tb (r_ball / 2)
    (half_pos hr_ball)
  refine ⟨t_centers, ht_fin, ?_⟩
  rintro _ ⟨k, rfl⟩
  obtain ⟨c_lp, hc_mem, hc_dist⟩ := Set.mem_iUnion₂.mp (ht_cov (Set.mem_range_self k))
  rw [Metric.mem_ball] at hc_dist
  refine Set.mem_iUnion₂.mpr ⟨c_lp, hc_mem, Metric.mem_ball.mpr ?_⟩
  have hVW_close : ‖(hmem k).toLp (V k) - (hW_mem k).toLp (W k)‖ ≤ r_ball / 2 := by
    have hsq_eq := HTGeometry.norm_toLp_sub_sq (hmem k) (hW_mem k)
    set Dk : ℝ → ℝ := fun x => V k x - W k x
    have hDk_cd : ContDiff ℝ 2 Dk := (hVd k).sub (hW_cd k)
    have hDk_cs : HasCompactSupport Dk := (hVc k).sub (hW_cs k)
    have hVki : Integrable (V k) := (hVd k).continuous.integrable_of_hasCompactSupport (hVc k)
    have hWki : Integrable (W k) := (hW_cd k).continuous.integrable_of_hasCompactSupport (hW_cs k)
    have hft_Dk : ∀ r : ℝ, paperFT (cx Dk) r =
        (1 - paperFT (cx (leftSplineMollifier η)) r) * paperFT (cx (V k)) r := by
      intro r
      rw [paperFT_cx_sub hVki hWki r, paperFT_lineConvolution_leftSplineMollifier hη hVki (hVc k) r]
      ring
    have hi_Dk := integrable_normSq_paperFT_ofReal hDk_cd hDk_cs
    have hi_Vk := integrable_normSq_paperFT_ofReal (hVd k) (hVc k)
    have hlow_le : lowFourierMass Dk T ≤ (T * η) ^ 2 := by
      have hm : (∫ r in (highFrequencies T)ᶜ, ‖paperFT (cx Dk) r‖ ^ 2) ≤
          ∫ r in (highFrequencies T)ᶜ, (T * η) ^ 2 * ‖paperFT (cx (V k)) r‖ ^ 2 := by
        refine setIntegral_mono_on hi_Dk.integrableOn (hi_Vk.const_mul _).integrableOn
          (measurableSet_highFrequencies T).compl fun r hr => ?_
        have hrT : |r| < T := not_le.mp hr
        rw [hft_Dk r, norm_mul, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        refine pow_le_pow_left₀ (norm_nonneg _)
          ((norm_one_sub_paperFT_leftSplineMollifier_le hη r).trans ?_) 2
        exact mul_le_mul_of_nonneg_right hrT.le hη.le
      rw [integral_const_mul] at hm
      have hlow_V : lowFourierMass (V k) T ≤ 1 :=
        (lowFourierMass_le_integral_sq (hVd k) (hVc k) T).trans (hmass k)
      unfold lowFourierMass at hlow_V ⊢
      have hm' := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
      nlinarith only [hm', hlow_V, sq_nonneg (T * η)]
    have hhigh_le : highFourierMass Dk T ≤ 4 * highFourierMass (V k) T := by
      have hm : (∫ r in highFrequencies T, ‖paperFT (cx Dk) r‖ ^ 2) ≤
          ∫ r in highFrequencies T, 4 * ‖paperFT (cx (V k)) r‖ ^ 2 := by
        refine setIntegral_mono_on hi_Dk.integrableOn (hi_Vk.const_mul 4).integrableOn
          (measurableSet_highFrequencies T) fun r _ => ?_
        rw [hft_Dk r, norm_mul, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h2 : ‖1 - paperFT (cx (leftSplineMollifier η)) r‖ ≤ 2 := by
          have ht := norm_sub_le (1 : ℂ) (paperFT (cx (leftSplineMollifier η)) r)
          have h1 := norm_paperFT_leftSplineMollifier_le hη r
          rw [norm_one] at ht
          linarith only [ht, h1]
        exact (pow_le_pow_left₀ (norm_nonneg _) h2 2).trans_eq (by norm_num)
      rw [integral_const_mul] at hm
      unfold highFourierMass
      have hm' := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
      linarith only [hm']
    have hpl := lowFourierMass_add_highFourierMass hDk_cd hDk_cs T
    have htot_sq : ‖(hmem k).toLp (V k) - (hW_mem k).toLp (W k)‖ ^ 2 ≤ (r_ball / 2) ^ 2 := by
      rw [hsq_eq]
      change (∫ x, Dk x ^ 2) ≤ (r_ball / 2) ^ 2
      have htk := hT_tail k
      dsimp only [ε_sq] at hTη_sq htk
      linarith only [hpl, hlow_le, hhigh_le, hTη_sq, htk]
    have hnn := norm_nonneg ((hmem k).toLp (V k) - (hW_mem k).toLp (W k))
    nlinarith only [htot_sq, hnn, hr_ball]
  rw [dist_eq_norm] at hc_dist ⊢
  calc ‖(hmem k).toLp (V k) - c_lp‖
      = ‖((hmem k).toLp (V k) - (hW_mem k).toLp (W k)) + ((hW_mem k).toLp (W k) - c_lp)‖ := by
        congr 1; abel
    _ ≤ ‖(hmem k).toLp (V k) - (hW_mem k).toLp (W k)‖ + ‖(hW_mem k).toLp (W k) - c_lp‖ :=
        norm_add_le _ _
    _ < r_ball / 2 + r_ball / 2 := add_lt_add_of_le_of_lt hVW_close hc_dist
    _ = r_ball := add_halves r_ball

/-- `L²` convergence plus bounded eighth exponential mass and support bounded above by `1` implies
`L¹` integrability of the limit and global `L¹(ℝ)` convergence. -/
private theorem integrable_and_tendsto_L1_of_L2_and_exp8 {V : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hVd : ∀ j, ContDiff ℝ 2 (V j)) (hVc : ∀ j, HasCompactSupport (V j))
    (hsupp1 : ∀ j y, 1 < y → V j y = 0)
    {M₈ : ℝ} (hM₈0 : 0 ≤ M₈) (hM₈ : ∀ j, (∫ y, V j y ^ 2 * Real.exp (-(8 * y))) ≤ M₈)
    (hFm : Measurable F) (hF2 : Integrable fun y => F y ^ 2)
    (hF8 : Integrable fun y => F y ^ 2 * Real.exp (-(8 * y)))
    (hF8_le : (∫ y, F y ^ 2 * Real.exp (-(8 * y))) ≤ M₈)
    (hF_supp1 : ∀ᵐ y, 1 < y → F y = 0)
    (hL2 : Tendsto (fun j => ∫ y, (V j y - F y) ^ 2) atTop (𝓝 0)) :
    Integrable F ∧ Tendsto (fun j => ∫ y, ‖V j y - F y‖) atTop (𝓝 0) := by
  have hexp_iio : ∀ a : ℝ, Integrable ((Set.Iio a).indicator fun y => Real.exp (8 * y)) ∧
      (∫ y, (Set.Iio a).indicator (fun y => Real.exp (8 * y)) y) =
        (1 / 8 : ℝ) * Real.exp (8 * a) := by
    intro a
    have hon : IntegrableOn (fun x : ℝ => Real.exp (-8 * x)) (Set.Ioi (-a)) :=
      integrableOn_exp_mul_Ioi (by norm_num : (-8 : ℝ) < 0) (-a)
    have hfn : (fun y : ℝ => (Set.Ioi (-a)).indicator (fun x => Real.exp (-8 * x)) (-y)) =
        (Set.Iio a).indicator fun y => Real.exp (8 * y) := by
      funext y
      by_cases hy : y ∈ Set.Iio a
      · have hy_lt : y < a := hy
        rw [Set.indicator_of_mem (Set.mem_Ioi.mpr (by linarith only [hy_lt])),
          Set.indicator_of_mem hy]
        congr 1; ring
      · rw [Set.indicator_of_notMem (fun h => hy (by rw [Set.mem_Ioi] at h; rw [Set.mem_Iio]; linarith only [h])),
          Set.indicator_of_notMem hy]
    have hint : Integrable ((Set.Iio a).indicator fun y => Real.exp (8 * y)) :=
      hfn ▸ (hon.integrable_indicator measurableSet_Ioi).comp_neg
    refine ⟨hint, ?_⟩
    have hneg := MeasureTheory.integral_neg_eq_self
      ((Set.Ioi (-a)).indicator fun x : ℝ => Real.exp (-8 * x)) volume
    rw [hfn] at hneg
    refine hneg.trans ?_
    rw [MeasureTheory.integral_indicator measurableSet_Ioi,
      integral_exp_mul_Ioi (by norm_num : (-8 : ℝ) < 0) (-a)]
    ring
  have hexp4_sq : ∀ (a y : ℝ),
      ((Set.Iio a).indicator (fun t => Real.exp (4 * t)) y) ^ 2 =
        (Set.Iio a).indicator (fun t => Real.exp (8 * t)) y := by
    intro a y
    by_cases hy : y ∈ Set.Iio a
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, sq, mul_zero]
  have hFi : Integrable F := by
    set g₁ : ℝ → ℝ := fun y => |F y| * Real.exp (-(4 * y))
    set g₂ : ℝ → ℝ := (Set.Iio (2 : ℝ)).indicator fun y => Real.exp (4 * y)
    have hg₁m : Measurable g₁ := hFm.abs.mul (Real.continuous_exp.comp (by fun_prop)).measurable
    have hg₂m : Measurable g₂ :=
      ((Real.continuous_exp.comp (by fun_prop)).measurable).indicator measurableSet_Iio
    have hg₁2 : Integrable fun y => g₁ y ^ 2 := by
      refine hF8.congr (Eventually.of_forall fun y => ?_)
      dsimp only [g₁]
      rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
      congr 2; push_cast; ring
    have hg₂2 : Integrable fun y => g₂ y ^ 2 := by
      simpa only [g₂, hexp4_sq] using (hexp_iio 2).1
    have hprod := HTGeometry.integrable_mul_of_sq_integrable
      hg₁m.aestronglyMeasurable hg₂m.aestronglyMeasurable hg₁2 hg₂2
    refine hprod.mono' hFm.aestronglyMeasurable ?_
    filter_upwards [hF_supp1] with y hy1
    by_cases hy2 : y ∈ Set.Iio (2 : ℝ)
    · dsimp only [g₁, g₂]
      rw [Set.indicator_of_mem hy2, Real.norm_eq_abs, mul_assoc, ← Real.exp_add,
        show -(4 * y) + 4 * y = 0 by ring, Real.exp_zero, mul_one]
    · have hy2_ge : 2 ≤ y := not_lt.mp hy2
      rw [hy1 (by linarith only [hy2_ge]), norm_zero]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y)
  refine ⟨hFi, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C_tail : ℝ := (4 * M₈ + 1) / 8
  have hCt_pos : 0 < C_tail := by positivity
  set Y : ℝ := max 1 (Real.log (C_tail / (ε / 3) ^ 2) / 8 + 1)
  have hY1 : 1 ≤ Y := le_max_left _ _
  have hY_log : Real.log (C_tail / (ε / 3) ^ 2) / 8 + 1 ≤ Y := le_max_right _ _
  have htail_exp : C_tail * Real.exp (-8 * Y) ≤ (ε / 3) ^ 2 := by
    have h1 : -8 * Y ≤ -Real.log (C_tail / (ε / 3) ^ 2) := by linarith only [hY_log]
    have h2 : Real.exp (-8 * Y) ≤ (ε / 3) ^ 2 / C_tail := by
      calc Real.exp (-8 * Y)
          ≤ Real.exp (-Real.log (C_tail / (ε / 3) ^ 2)) := Real.exp_le_exp.mpr h1
        _ = (C_tail / (ε / 3) ^ 2)⁻¹ := by
            rw [Real.exp_neg, Real.exp_log (div_pos hCt_pos (by positivity))]
        _ = (ε / 3) ^ 2 / C_tail := inv_div _ _
    exact (mul_le_mul_of_nonneg_left h2 hCt_pos.le).trans_eq (mul_div_cancel₀ _ hCt_pos.ne')
  set η_mid : ℝ := (ε / 3) ^ 2 / (Y + 2)
  have hη_mid : 0 < η_mid := by positivity
  filter_upwards [hL2.eventually (gt_mem_nhds hη_mid)] with j hj_L2
  have hVj_i : Integrable (V j) := (hVd j).continuous.integrable_of_hasCompactSupport (hVc j)
  have hVj2 : Integrable fun y => V j y ^ 2 :=
    ((hVd j).continuous.pow 2).integrable_of_hasCompactSupport
      (HTGeometry.hasCompactSupport_sq (hVc j))
  have hVj8 : Integrable fun y => V j y ^ 2 * Real.exp (-(8 * y)) :=
    (((hVd j).continuous.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport
      (HTGeometry.hasCompactSupport_sq (hVc j)).mul_right
  set d : ℝ → ℝ := fun y => |V j y - F y|
  have hdm : Measurable d := ((hVd j).continuous.measurable.sub hFm).abs
  have hdi : Integrable d :=
    (hVj_i.sub hFi).norm.congr (Eventually.of_forall fun y => by
      simp only [d, Pi.sub_apply, Real.norm_eq_abs])
  have hd2 : Integrable fun y => d y ^ 2 := by
    have hdom : Integrable fun y => 2 * V j y ^ 2 + 2 * F y ^ 2 :=
      (hVj2.const_mul 2).add (hF2.const_mul 2)
    refine hdom.mono' (hdm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    dsimp only [d]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    nlinarith only [sq_nonneg (V j y + F y)]
  have hd8 : Integrable fun y => d y ^ 2 * Real.exp (-(8 * y)) := by
    have hdom : Integrable fun y => 2 * (V j y ^ 2 * Real.exp (-(8 * y))) +
        2 * (F y ^ 2 * Real.exp (-(8 * y))) := (hVj8.const_mul 2).add (hF8.const_mul 2)
    refine hdom.mono' ((hdm.pow_const 2).mul (Real.continuous_exp.comp (by fun_prop)).measurable).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    dsimp only [d]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le), sq_abs]
    have h1 : (V j y - F y) ^ 2 ≤ 2 * V j y ^ 2 + 2 * F y ^ 2 := by
      nlinarith only [sq_nonneg (V j y + F y)]
    have hm := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(8 * y))).le
    linarith only [hm]
  have hd8_le : (∫ y, d y ^ 2 * Real.exp (-(8 * y))) ≤ 4 * M₈ := by
    have hdom : Integrable fun y => 2 * (V j y ^ 2 * Real.exp (-(8 * y))) +
        2 * (F y ^ 2 * Real.exp (-(8 * y))) := (hVj8.const_mul 2).add (hF8.const_mul 2)
    have hm := integral_mono hd8 hdom fun y => by
      dsimp only [d]; rw [sq_abs]
      have h1 : (V j y - F y) ^ 2 ≤ 2 * V j y ^ 2 + 2 * F y ^ 2 := by
        nlinarith only [sq_nonneg (V j y + F y)]
      have hm' := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(8 * y))).le
      linarith only [hm']
    have hadd := integral_add (hVj8.const_mul 2) (hF8.const_mul 2)
    rw [hadd, integral_const_mul, integral_const_mul] at hm
    linarith only [hm, hM₈ j, hF8_le]
  have hmid_le : (∫ y, (Set.Icc (-Y) 1).indicator d y) ≤ ε / 3 := by
    set ind_mid : ℝ → ℝ := (Set.Icc (-Y) 1).indicator fun _ => 1
    have hind_m : Measurable ind_mid := measurable_const.indicator measurableSet_Icc
    have hind2 : Integrable fun y => ind_mid y ^ 2 := by
      have heq : (fun y => ind_mid y ^ 2) = ind_mid := by
        funext y; dsimp only [ind_mid]
        by_cases hy : y ∈ Set.Icc (-Y) 1 <;> simp [hy]
      rw [heq]
      exact (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
    have hcs := HTGeometry.sq_integral_mul_le (μ := volume) hind_m.aestronglyMeasurable
      hdm.aestronglyMeasurable hind2 hd2
    have hmul_eq : (fun y => ind_mid y * d y) = (Set.Icc (-Y) 1).indicator d := by
      funext y; dsimp only [ind_mid]
      by_cases hy : y ∈ Set.Icc (-Y) 1 <;> simp [hy]
    have hind_int : (∫ y, ind_mid y ^ 2) = Y + 1 := by
      have heq : (fun y => ind_mid y ^ 2) = ind_mid := by
        funext y; dsimp only [ind_mid]
        by_cases hy : y ∈ Set.Icc (-Y) 1 <;> simp [hy]
      rw [heq, MeasureTheory.integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
        Real.volume_real_Icc_of_le (by linarith only [hY1])]
      ring
    have hd2_eq : (∫ y, d y ^ 2) = ∫ y, (V j y - F y) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun y => sq_abs _)
    rw [hmul_eq, hind_int, hd2_eq] at hcs
    have hsq_le : (∫ y, (Set.Icc (-Y) 1).indicator d y) ^ 2 ≤ (ε / 3) ^ 2 := by
      have hm := (mul_le_mul_of_nonneg_left hj_L2.le (by linarith only [hY1] : 0 ≤ Y + 1)).trans
        (mul_le_mul_of_nonneg_right (by linarith : Y + 1 ≤ Y + 2) hη_mid.le)
      have hid : (Y + 2) * η_mid = (ε / 3) ^ 2 := by
        dsimp only [η_mid]; field_simp [(by linarith only [hY1] : Y + 2 ≠ 0)]
      linarith only [hcs, hm, hid]
    have hnn : 0 ≤ ∫ y, (Set.Icc (-Y) 1).indicator d y :=
      integral_nonneg fun y => Set.indicator_nonneg (fun x _ => abs_nonneg (V j x - F x)) y
    nlinarith only [hsq_le, hnn, hε]
  have htail_le : (∫ y, (Set.Iio (-Y)).indicator d y) ≤ ε / 3 := by
    set g₁ : ℝ → ℝ := fun y => d y * Real.exp (-(4 * y))
    set g₂ : ℝ → ℝ := (Set.Iio (-Y)).indicator fun y => Real.exp (4 * y)
    have hg₁m : Measurable g₁ := hdm.mul (Real.continuous_exp.comp (by fun_prop)).measurable
    have hg₂m : Measurable g₂ :=
      ((Real.continuous_exp.comp (by fun_prop)).measurable).indicator measurableSet_Iio
    have hg₁2 : Integrable fun y => g₁ y ^ 2 := by
      refine hd8.congr (Eventually.of_forall fun y => ?_)
      dsimp only [g₁]
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    have hg₁2_eq : (∫ y, g₁ y ^ 2) = ∫ y, d y ^ 2 * Real.exp (-(8 * y)) :=
      integral_congr_ae (Eventually.of_forall fun y => by
        dsimp only [g₁]; rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring)
    have hg₂2 : Integrable fun y => g₂ y ^ 2 := by
      simpa only [g₂, hexp4_sq] using (hexp_iio (-Y)).1
    have hg₂2_eq : (∫ y, g₂ y ^ 2) = (1 / 8 : ℝ) * Real.exp (-8 * Y) := by
      have heq : (∫ y, g₂ y ^ 2) = ∫ y, (Set.Iio (-Y)).indicator (fun t => Real.exp (8 * t)) y :=
        integral_congr_ae (Eventually.of_forall fun y => hexp4_sq (-Y) y)
      rw [heq, (hexp_iio (-Y)).2]; ring_nf
    have hcs := HTGeometry.sq_integral_mul_le (μ := volume) hg₁m.aestronglyMeasurable
      hg₂m.aestronglyMeasurable hg₁2 hg₂2
    have hmul_eq : (fun y => g₁ y * g₂ y) = (Set.Iio (-Y)).indicator d := by
      funext y; dsimp only [g₁, g₂]
      by_cases hy : y ∈ Set.Iio (-Y)
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_assoc, ← Real.exp_add,
          show -(4 * y) + 4 * y = 0 by ring, Real.exp_zero, mul_one]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
    rw [hmul_eq, hg₁2_eq, hg₂2_eq] at hcs
    have hsq_le : (∫ y, (Set.Iio (-Y)).indicator d y) ^ 2 ≤ (ε / 3) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right
        (hd8_le.trans (by linarith : 4 * M₈ ≤ 4 * M₈ + 1))
        (by positivity : 0 ≤ (1 / 8 : ℝ) * Real.exp (-8 * Y))
      have hid : (4 * M₈ + 1) * ((1 / 8 : ℝ) * Real.exp (-8 * Y)) = C_tail * Real.exp (-8 * Y) := by
        dsimp only [C_tail]; ring
      linarith only [hcs, hm, hid, htail_exp]
    have hnn : 0 ≤ ∫ y, (Set.Iio (-Y)).indicator d y :=
      integral_nonneg fun y => Set.indicator_nonneg (fun x _ => abs_nonneg (V j x - F x)) y
    nlinarith only [hsq_le, hnn, hε]
  have hsplit_ae : d =ᵐ[volume]
      fun y => (Set.Iio (-Y)).indicator d y + (Set.Icc (-Y) 1).indicator d y := by
    filter_upwards [hF_supp1] with y hyF
    rcases lt_or_ge y (-Y) with hy1 | hy1
    · have hm1 : y ∈ Set.Iio (-Y) := hy1
      have hm2 : y ∉ Set.Icc (-Y) 1 := fun h => not_le.mpr hy1 h.1
      rw [Set.indicator_of_mem hm1, Set.indicator_of_notMem hm2, add_zero]
    · rcases le_or_gt y 1 with hy2 | hy2
      · have hm1 : y ∉ Set.Iio (-Y) := not_lt.mpr hy1
        have hm2 : y ∈ Set.Icc (-Y) 1 := ⟨hy1, hy2⟩
        rw [Set.indicator_of_notMem hm1, Set.indicator_of_mem hm2, zero_add]
      · have hm1 : y ∉ Set.Iio (-Y) := not_lt.mpr (hy1.trans (by linarith only [hY1, hy2]))
        have hm2 : y ∉ Set.Icc (-Y) 1 := fun h => not_le.mpr hy2 h.2
        rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2, add_zero]
        dsimp only [d]
        rw [hsupp1 j y hy2, hyF hy2, sub_self, abs_zero]
  have hi_tail : Integrable ((Set.Iio (-Y)).indicator d) := hdi.indicator measurableSet_Iio
  have hi_mid : Integrable ((Set.Icc (-Y) 1).indicator d) := hdi.indicator measurableSet_Icc
  have htot : (∫ y, ‖V j y - F y‖) ≤ 2 * ε / 3 := by
    have heq : (∫ y, ‖V j y - F y‖) =
        (∫ y, (Set.Iio (-Y)).indicator d y) + ∫ y, (Set.Icc (-Y) 1).indicator d y := by
      have h1 : (∫ y, ‖V j y - F y‖) = ∫ y, d y :=
        integral_congr_ae (Eventually.of_forall fun _ => Real.norm_eq_abs _)
      rw [h1, integral_congr_ae hsplit_ae, integral_add hi_tail hi_mid]
    linarith only [heq, htail_le, hmid_le]
  have h0 : 0 ≤ ∫ y, ‖V j y - F y‖ := integral_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith only [htot, hε]

/-- Truncated one-sided mollification `leftSplineMollifier δ ⋆ (1_{(-A, 0)} F)` producing a smooth
window test on `[−(A + δ), 0]`. -/
def windowMollify (F : ℝ → ℝ) (A δ : ℝ) : ℝ → ℝ :=
  HTGeometry.lineConvolution (leftSplineMollifier δ) ((Set.Ioo (-A) 0).indicator F)

theorem isWindowTest_windowMollify {F : ℝ → ℝ} {A δ : ℝ} (_hA : 0 < A) (hδ : 0 < δ)
    (hFi : Integrable F) : IsWindowTest (A + δ) (windowMollify F A δ) := by
  have hGi : Integrable ((Set.Ioo (-A) 0).indicator F) := hFi.indicator measurableSet_Ioo
  refine ⟨?_, ?_⟩
  · unfold windowMollify
    rw [HTGeometry.lineConvolution_eq_convolution]
    exact (hasCompactSupport_leftSplineMollifier hδ).contDiff_convolution_left _
      (contDiff_leftSplineMollifier δ) hGi.locallyIntegrable
  · intro x hx
    unfold windowMollify HTGeometry.lineConvolution
    refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
    dsimp only [Pi.zero_apply]
    by_cases hs : s ∈ Set.Icc (-δ) 0
    · have hnot : x - s ∉ Set.Ioo (-A) 0 := by
        intro hm
        exact hx ⟨by linarith only [hs.1, hm.1], by linarith only [hs.2, hm.2]⟩
      rw [Set.indicator_of_notMem hnot, mul_zero]
    · rw [leftSplineMollifier_eq_zero hδ hs, zero_mul]

private theorem exponentialMass_windowMollify_le {F : ℝ → ℝ} {A δ : ℝ} (hδ : 0 < δ)
    (hFm : Measurable F) (hF2 : Integrable fun u => F u ^ 2)
    (hF8 : Integrable fun u => F u ^ 2 * Real.exp (-(8 * u))) :
    exponentialMass 8 (windowMollify F A δ) ≤
      Real.exp (8 * δ) * ∫ u in Set.Iio 0, F u ^ 2 * Real.exp (-(8 * u)) := by
  set G : ℝ → ℝ := (Set.Ioo (-A) 0).indicator F
  have hGm : Measurable G := hFm.indicator measurableSet_Ioo
  have hG2 : Integrable fun u => G u ^ 2 := by
    refine hF2.mono' (hGm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    dsimp only [G]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hu : u ∈ Set.Ioo (-A) 0 <;> simp [hu, sq_nonneg]
  have hG8 : Integrable fun u => G u ^ 2 * Real.exp (-(8 * u)) := by
    refine hF8.mono' ((hGm.pow_const 2).mul
      (Real.continuous_exp.comp (by fun_prop)).measurable).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    dsimp only [G]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    by_cases hu : u ∈ Set.Ioo (-A) 0
    · simp [hu]
    · simp [hu]; positivity
  obtain ⟨_, hbd⟩ := integral_exp8_lineConvolution_leftSplineMollifier_le hδ hGm hG2 hG8
  have hG8_le : (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
      ∫ u in Set.Iio 0, F u ^ 2 * Real.exp (-(8 * u)) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Iio]
    refine integral_mono hG8 (hF8.indicator measurableSet_Iio) fun u => ?_
    dsimp only [G]
    by_cases hu : u ∈ Set.Ioo (-A) 0
    · have hu0 : u ∈ Set.Iio (0 : ℝ) := hu.2
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu0]
    · rw [Set.indicator_of_notMem hu, sq, zero_mul, zero_mul]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) u
  have hexp_eq : exponentialMass 8 (windowMollify F A δ) =
      ∫ x, HTGeometry.lineConvolution (leftSplineMollifier δ) G x ^ 2 * Real.exp (-(8 * x)) := by
    unfold exponentialMass windowMollify
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hexp_eq]
  exact hbd.trans (mul_le_mul_of_nonneg_left hG8_le (Real.exp_pos _).le)

/-- Dominated-convergence upper bound on `archForm (windowMollify F₀ ((n : ℝ) + 1) δ)` from the
critical `Γ`-liminf inequality with an arbitrary finite upper bound on `F₀`. -/
theorem exists_archForm_windowMollify_le_of_gammaLiminf_bound {F₀ : ℝ → ℝ} {Rstar B : ℝ}
    (_hF₀m : Measurable F₀) (hF₀i : Integrable F₀)
    (_hF₀8 : Integrable fun u => F₀ u ^ 2 * Real.exp (-(8 * u)))
    (hF₀_zero : ∀ u, 0 ≤ u → F₀ u = 0)
    (hliminf : ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F₀ T + criticalAliasCoefficient Rstar *
        (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) ≤ B) :
    ∃ C_arch : ℝ, 0 ≤ C_arch ∧
      ∀ {δ : ℝ}, 0 < δ → ∀ N_min : ℕ, ∃ n : ℕ, N_min ≤ n ∧
        archForm (windowMollify F₀ ((n : ℝ) + 1) δ) ≤
          primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
            criticalAliasCoefficient Rstar * (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) +
            (C_arch + 1) * δ + B := by
  set T₀ : ℝ := Real.exp factorialSpanGammaOffset
  have hT₀_pos : 0 < T₀ := Real.exp_pos _
  obtain ⟨B_γ, hB_γ⟩ := (isCompact_Icc (a := -T₀) (b := T₀)).exists_bound_of_continuousOn
    WeilHerglotz.continuous_gammaBracket.continuousOn
  set C_F : ℝ := ∫ u, ‖F₀ u‖
  have hCF_nn : 0 ≤ C_F := integral_nonneg fun _ => norm_nonneg _
  set C_arch : ℝ := 2 * T₀ ^ 2 * C_F ^ 2 * (|B_γ| + 1) / Real.pi
  refine ⟨C_arch, by positivity, fun {δ} hδ N_min => ?_⟩
  set ρ : ℝ → ℝ := leftSplineMollifier δ
  have hρ_cd := contDiff_leftSplineMollifier δ
  have hρ_cs := hasCompactSupport_leftSplineMollifier hδ
  have hρ_γ_int : Integrable fun r : ℝ =>
      C_F ^ 2 * ‖‖paperFT (cx ρ) r‖ ^ 2 * EF.gammaBracket r‖ :=
    (integrable_normSq_paperFT_mul_gammaBracket hρ_cd hρ_cs).norm.const_mul (C_F ^ 2)
  set G : ℕ → ℝ → ℝ := fun n => (Set.Ioo (-((n : ℝ) + 1)) 0).indicator F₀
  have hG_i : ∀ n, Integrable (G n) := fun n => hF₀i.indicator measurableSet_Ioo
  have hG_cs : ∀ n, HasCompactSupport (G n) := fun n =>
    HasCompactSupport.intro (isCompact_Icc (a := -((n : ℝ) + 1)) (b := 0)) fun u hu =>
      Set.indicator_of_notMem (fun hm => hu ⟨hm.1.le, hm.2.le⟩) _
  have hG_L1_lim : Tendsto (fun n : ℕ => ∫ u, ‖G n u - F₀ u‖) atTop (𝓝 0) := by
    have hs : Monotone fun n : ℕ => Set.Ioo (-((n : ℝ) + 1)) (0 : ℝ) := fun i j hij u hu =>
      ⟨by have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
          linarith only [hu.1, hij'], hu.2⟩
    have hunion : (⋃ n : ℕ, Set.Ioo (-((n : ℝ) + 1)) (0 : ℝ)) = Set.Iio 0 := by
      ext u
      simp only [Set.mem_iUnion, Set.mem_Ioo, Set.mem_Iio]
      refine ⟨fun ⟨_, _, hu⟩ => hu, fun hu => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (-u)
      exact ⟨n, by linarith only [hn], hu⟩
    have hmon := tendsto_setIntegral_of_monotone (μ := volume) (f := fun u => ‖F₀ u‖)
      (fun _ => measurableSet_Ioo) hs hF₀i.norm.integrableOn
    rw [hunion] at hmon
    have htot_eq : (∫ u in Set.Iio 0, ‖F₀ u‖) = ∫ u, ‖F₀ u‖ := by
      rw [← MeasureTheory.integral_indicator measurableSet_Iio]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      by_cases hu : u ∈ Set.Iio (0 : ℝ)
      · rw [Set.indicator_of_mem hu]
      · have hu0 : 0 ≤ u := not_lt.mp hu
        rw [Set.indicator_of_notMem hu, hF₀_zero u hu0, norm_zero]
    rw [htot_eq] at hmon
    have hsub := (tendsto_const_nhds (α := ℕ) (x := ∫ u, ‖F₀ u‖)).sub hmon
    rw [sub_self] at hsub
    refine hsub.congr fun n => ?_
    rw [← MeasureTheory.integral_indicator measurableSet_Ioo,
      ← integral_sub hF₀i.norm (hF₀i.norm.indicator measurableSet_Ioo)]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only [Pi.sub_apply, G]
    by_cases hv : v ∈ Set.Ioo (-((n : ℝ) + 1)) 0
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, sub_self, sub_self, norm_zero]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, sub_zero, zero_sub, norm_neg]
  set q : ℝ → ℝ := fun r =>
    ‖paperFT (cx ρ) r‖ ^ 2 * ‖paperFT (cx F₀) r‖ ^ 2 * EF.gammaBracket r
  have hq_meas : AEStronglyMeasurable q volume :=
    ((((continuous_paperFT_cx (integrable_leftSplineMollifier hδ)).norm.pow 2).mul
      ((continuous_paperFT_cx hF₀i).norm.pow 2)).mul
      WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
  have hq_dom : ∀ r, ‖q r‖ ≤ C_F ^ 2 * ‖‖paperFT (cx ρ) r‖ ^ 2 * EF.gammaBracket r‖ := by
    intro r
    dsimp only [q]
    have hft := norm_paperFT_le F₀ r
    have hsq : ‖paperFT (cx F₀) r‖ ^ 2 ≤ C_F ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hft 2
    rw [mul_right_comm, norm_mul, Real.norm_of_nonneg (sq_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
  have hq_int : Integrable q := hρ_γ_int.mono' hq_meas (Eventually.of_forall hq_dom)
  have harch_tendsto : Tendsto (fun n : ℕ => archForm (windowMollify F₀ ((n : ℝ) + 1) δ)) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ r, q r)) := by
    have hint_lim : Tendsto (fun n : ℕ =>
        ∫ r : ℝ, ‖paperFT (cx (windowMollify F₀ ((n : ℝ) + 1) δ)) r‖ ^ 2 * EF.gammaBracket r)
        atTop (𝓝 (∫ r, q r)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun r : ℝ => C_F ^ 2 * ‖‖paperFT (cx ρ) r‖ ^ 2 * EF.gammaBracket r‖) ?_ hρ_γ_int ?_ ?_
      · intro n
        have hH := isWindowTest_windowMollify (by positivity : (0 : ℝ) < (n : ℝ) + 1) hδ hF₀i
        exact (integrable_normSq_paperFT_mul_gammaBracket hH.contDiff
          hH.hasCompactSupport).aestronglyMeasurable
      · intro n
        refine Eventually.of_forall fun r => ?_
        have hft_conv : paperFT (cx (HTGeometry.lineConvolution ρ (G n))) r =
            paperFT (cx ρ) r * paperFT (cx (G n)) r :=
          paperFT_lineConvolution_leftSplineMollifier hδ (hG_i n) (hG_cs n) r
        change ‖‖paperFT (cx (HTGeometry.lineConvolution ρ (G n))) r‖ ^ 2 *
          EF.gammaBracket r‖ ≤ _
        rw [hft_conv, Complex.norm_mul, mul_pow, mul_right_comm, norm_mul,
          Real.norm_of_nonneg (sq_nonneg _), mul_comm]
        have hG_norm : ‖paperFT (cx (G n)) r‖ ≤ C_F := by
          refine (norm_paperFT_le (G n) r).trans ?_
          refine integral_mono (hG_i n).norm hF₀i.norm fun u => ?_
          dsimp only [G]
          by_cases hu : u ∈ Set.Ioo (-((n : ℝ) + 1)) 0
          · rw [Set.indicator_of_mem hu]
          · rw [Set.indicator_of_notMem hu, norm_zero]
            exact norm_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hG_norm 2)
          (norm_nonneg _)
      · refine Eventually.of_forall fun r => ?_
        have hpt : Tendsto (fun n => paperFT (cx (G n)) r) atTop (𝓝 (paperFT (cx F₀) r)) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          exact squeeze_zero (fun _ => norm_nonneg _)
            (fun n => CriticalArithmeticCorrelationTheory.norm_paperFT_sub_le (hG_i n) hF₀i r)
            hG_L1_lim
        have hmul := ((hpt.const_mul (paperFT (cx ρ) r)).norm.pow 2).mul_const (EF.gammaBracket r)
        refine (hmul.congr fun n => ?_).trans ?_
        · have hft_conv := paperFT_lineConvolution_leftSplineMollifier hδ (hG_i n) (hG_cs n) r
          change _ = ‖paperFT (cx (HTGeometry.lineConvolution ρ (G n))) r‖ ^ 2 * EF.gammaBracket r
          rw [hft_conv]
        · dsimp only [q]
          rw [norm_mul, mul_pow]
    exact hint_lim.const_mul (1 / (2 * Real.pi))
  have hL_ub : (1 / (2 * Real.pi)) * (∫ r, q r) ≤
      primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
        criticalAliasCoefficient Rstar * (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) +
        C_arch * δ + B := by
    have htrunc_lim : Tendsto (fun m : ℕ =>
        (1 / (2 * Real.pi)) * ∫ r in (highFrequencies (T₀ + (m : ℝ)))ᶜ, q r)
        atTop (𝓝 ((1 / (2 * Real.pi)) * ∫ r, q r)) := by
      have hind_lim : Tendsto (fun m : ℕ =>
          ∫ r, (highFrequencies (T₀ + (m : ℝ)))ᶜ.indicator q r) atTop (𝓝 (∫ r, q r)) := by
        refine tendsto_integral_of_dominated_convergence (fun r => ‖q r‖)
          (fun m => hq_meas.indicator (measurableSet_highFrequencies _).compl) hq_int.norm
          (fun m => Eventually.of_forall fun r => norm_indicator_le_norm_self _ _) ?_
        refine Eventually.of_forall fun r => ?_
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨M_r, hMr⟩ := exists_nat_gt |r|
        filter_upwards [eventually_ge_atTop M_r] with m hm
        have hr_mem : r ∈ (highFrequencies (T₀ + (m : ℝ)))ᶜ := by
          change ¬ (T₀ + (m : ℝ) ≤ |r|); push Not
          have hmR : (M_r : ℝ) ≤ m := by exact_mod_cast hm
          linarith only [hT₀_pos, hMr, hmR]
        exact (Set.indicator_of_mem hr_mem q).symm
      refine (hind_lim.const_mul (1 / (2 * Real.pi))).congr fun m => ?_
      rw [MeasureTheory.integral_indicator (measurableSet_highFrequencies _).compl]
    refine le_of_tendsto htrunc_lim (Eventually.of_forall fun m => ?_)
    set Tm : ℝ := T₀ + (m : ℝ)
    have hTm_ge : T₀ ≤ Tm := by dsimp only [Tm]; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hHm := (measurableSet_highFrequencies Tm).compl
    have hvol_Tm : volume (highFrequencies Tm)ᶜ ≠ ⊤ :=
      ((measure_mono (compl_highFrequencies_subset Tm)).trans_lt isCompact_Icc.measure_lt_top).ne
    set pF : ℝ → ℝ := fun r => ‖paperFT (cx F₀) r‖ ^ 2 * EF.gammaBracket r
    have hpF_on : IntegrableOn pF (highFrequencies Tm)ᶜ := by
      have hcont : Continuous pF :=
        ((continuous_paperFT_cx hF₀i).norm.pow 2).mul WeilHerglotz.continuous_gammaBracket
      exact (hcont.integrableOn_Icc).mono_set (compl_highFrequencies_subset Tm)
    set err : ℝ → ℝ := (highFrequencies T₀)ᶜ.indicator
      fun _ => 2 * T₀ * C_F ^ 2 * (|B_γ| + 1) * δ
    have herr_int : Integrable err :=
      (integrableOn_const ((measure_mono (compl_highFrequencies_subset T₀)).trans_lt
        isCompact_Icc.measure_lt_top).ne).integrable_indicator (measurableSet_highFrequencies T₀).compl
    have hpt_m : ∀ r ∈ (highFrequencies Tm)ᶜ, q r ≤ pF r + err r := by
      intro r _
      by_cases hr0 : r ∈ (highFrequencies T₀)ᶜ
      · have hr_lt : |r| < T₀ := not_le.mp hr0
        have hr_icc : r ∈ Set.Icc (-T₀) T₀ := compl_highFrequencies_subset T₀ hr0
        dsimp only [err, q, pF]
        rw [Set.indicator_of_mem hr0]
        have hρ1 := norm_paperFT_leftSplineMollifier_le hδ r
        have hρ_diff := (norm_one_sub_paperFT_leftSplineMollifier_le hδ r).trans
          (mul_le_mul_of_nonneg_right hr_lt.le hδ.le)
        have hsq_diff : |‖paperFT (cx ρ) r‖ ^ 2 - 1| ≤ 2 * T₀ * δ := by
          have hid : ‖paperFT (cx ρ) r‖ ^ 2 - 1 =
              (‖paperFT (cx ρ) r‖ + 1) * (‖paperFT (cx ρ) r‖ - 1) := by ring
          have habs_norm : |‖paperFT (cx ρ) r‖ - 1| ≤ ‖1 - paperFT (cx ρ) r‖ := by
            rw [norm_sub_rev]
            simpa only [norm_one] using abs_norm_sub_norm_le (paperFT (cx ρ) r) 1
          rw [hid, abs_mul, abs_of_nonneg (by positivity)]
          calc (‖paperFT (cx ρ) r‖ + 1) * |‖paperFT (cx ρ) r‖ - 1|
              ≤ 2 * (T₀ * δ) := mul_le_mul (by linarith only [hρ1])
                (habs_norm.trans hρ_diff) (abs_nonneg _) zero_le_two
            _ = 2 * T₀ * δ := by ring
        have hF_sq : ‖paperFT (cx F₀) r‖ ^ 2 ≤ C_F ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_paperFT_le F₀ r) 2
        have hγ_bd : |EF.gammaBracket r| ≤ |B_γ| + 1 := by
          have h1 := (hB_γ r hr_icc).trans (le_abs_self B_γ)
          rw [Real.norm_eq_abs] at h1
          linarith only [h1]
        have hprod_le : |(‖paperFT (cx ρ) r‖ ^ 2 - 1) *
            (‖paperFT (cx F₀) r‖ ^ 2 * EF.gammaBracket r)| ≤
            2 * T₀ * C_F ^ 2 * (|B_γ| + 1) * δ := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖paperFT (cx F₀) r‖)]
          have hm1 := mul_le_mul hF_sq hγ_bd (abs_nonneg _) (sq_nonneg _)
          have hm2 := mul_le_mul hsq_diff hm1 (by positivity) (by positivity)
          linarith only [hm2,
            (by ring : (2 * T₀ * δ) * (C_F ^ 2 * (|B_γ| + 1)) =
              2 * T₀ * C_F ^ 2 * (|B_γ| + 1) * δ)]
        have hle := le_abs_self ((‖paperFT (cx ρ) r‖ ^ 2 - 1) *
          (‖paperFT (cx F₀) r‖ ^ 2 * EF.gammaBracket r))
        linarith only [hle, hprod_le,
          (by ring : ‖paperFT (cx ρ) r‖ ^ 2 * ‖paperFT (cx F₀) r‖ ^ 2 * EF.gammaBracket r -
              ‖paperFT (cx F₀) r‖ ^ 2 * EF.gammaBracket r =
            (‖paperFT (cx ρ) r‖ ^ 2 - 1) * (‖paperFT (cx F₀) r‖ ^ 2 * EF.gammaBracket r))]
      · have hr_ge : T₀ ≤ |r| := not_lt.mp fun hlt => hr0 (not_le.mpr hlt)
        dsimp only [err, q, pF]
        rw [Set.indicator_of_notMem hr0, add_zero]
        have hγ_nn : 0 ≤ EF.gammaBracket r := by
          have hg := gammaBracket_ge_log_of_le_abs hT₀_pos hr_ge
          have hlog0 : Real.log T₀ - factorialSpanGammaOffset = 0 := by
            dsimp only [T₀]; rw [Real.log_exp, sub_self]
          linarith only [hg, hlog0]
        have hρ_sq : ‖paperFT (cx ρ) r‖ ^ 2 ≤ 1 := by
          simpa only [one_pow] using
            pow_le_pow_left₀ (norm_nonneg _) (norm_paperFT_leftSplineMollifier_le hδ r) 2
        have hm := mul_le_mul_of_nonneg_right hρ_sq
          (mul_nonneg (sq_nonneg ‖paperFT (cx F₀) r‖) hγ_nn)
        linarith only [hm]
    have hint_mono : (∫ x in (highFrequencies Tm)ᶜ, q x) ≤
        ∫ a in (highFrequencies Tm)ᶜ, (pF a + err a) :=
      setIntegral_mono_on hq_int.integrableOn (hpF_on.add herr_int.integrableOn) hHm hpt_m
    have hadd_on := integral_add hpF_on herr_int.integrableOn
    rw [hadd_on] at hint_mono
    have herr_ub : (∫ r in (highFrequencies Tm)ᶜ, err r) ≤
        (2 * T₀) * (2 * T₀ * C_F ^ 2 * (|B_γ| + 1) * δ) := by
      have htot : (∫ r in (highFrequencies Tm)ᶜ, err r) ≤ ∫ r, err r :=
        setIntegral_le_integral herr_int
          (Eventually.of_forall fun r => Set.indicator_nonneg (fun _ _ => by positivity) r)
      have hsub : (∫ r, err r) ≤
          ∫ _r in Set.Icc (-T₀) T₀, 2 * T₀ * C_F ^ 2 * (|B_γ| + 1) * δ := by
        rw [MeasureTheory.integral_indicator (measurableSet_highFrequencies T₀).compl]
        exact setIntegral_mono_set (integrableOn_const isCompact_Icc.measure_ne_top)
          (Eventually.of_forall fun _ => by positivity)
          (compl_highFrequencies_subset T₀).eventuallyLE
      rw [setIntegral_const, smul_eq_mul,
        Real.volume_real_Icc_of_le (by linarith only [hT₀_pos])] at hsub
      exact htot.trans (hsub.trans_eq (by ring))
    have hlow_eq : (1 / (2 * Real.pi)) * (∫ r in (highFrequencies Tm)ᶜ, pF r) =
        lowGammaForm F₀ Tm := rfl
    have hpi_nn : 0 ≤ 1 / (2 * Real.pi) := by positivity
    have hm1 := mul_le_mul_of_nonneg_left (hint_mono.trans (add_le_add le_rfl herr_ub)) hpi_nn
    have hid_err : (1 / (2 * Real.pi)) * ((2 * T₀) * (2 * T₀ * C_F ^ 2 * (|B_γ| + 1) * δ)) =
        C_arch * δ := by
      dsimp only [C_arch]; field_simp [Real.pi_pos.ne']
    have hlim_m := hliminf Tm hTm_ge
    unfold truncatedWeilForm at hlim_m
    linarith only [hm1, hlow_eq, hid_err, hlim_m]
  have hev := (harch_tendsto.eventually (gt_mem_nhds
    (show (1 / (2 * Real.pi)) * (∫ r, q r) <
        (1 / (2 * Real.pi)) * (∫ r, q r) + δ by linarith only [hδ]))).and
    (eventually_ge_atTop N_min)
  obtain ⟨n, hn_lt, hn_ge⟩ := hev.exists
  exact ⟨n, hn_ge, by linarith only [hn_lt, hL_ub]⟩

/-- Dominated-convergence upper bound on `archForm (windowMollify F₀ ((n : ℝ) + 1) δ)` from the
critical `Γ`-liminf inequality on `F₀`. -/
private theorem exists_archForm_windowMollify_le_of_gammaLiminf {F₀ : ℝ → ℝ} {Rstar : ℝ}
    (_hF₀m : Measurable F₀) (hF₀i : Integrable F₀)
    (_hF₀8 : Integrable fun u => F₀ u ^ 2 * Real.exp (-(8 * u)))
    (hF₀_zero : ∀ u, 0 ≤ u → F₀ u = 0)
    (hliminf : ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F₀ T + criticalAliasCoefficient Rstar *
        (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) ≤ 0) :
    ∃ C_arch : ℝ, 0 ≤ C_arch ∧
      ∀ {δ : ℝ}, 0 < δ → ∀ N_min : ℕ, ∃ n : ℕ, N_min ≤ n ∧
        archForm (windowMollify F₀ ((n : ℝ) + 1) δ) ≤
          primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
            criticalAliasCoefficient Rstar * (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) +
            (C_arch + 1) * δ := by
  simpa only [add_zero] using
    exists_archForm_windowMollify_le_of_gammaLiminf_bound _hF₀m hF₀i _hF₀8 hF₀_zero hliminf

/-- Truncation and one-sided mollification approximate a rough negative-half-line profile
in the exponential source norm while preserving an arbitrary finite Gamma-liminf upper bound. -/
theorem exists_window_sequence_of_gammaLiminf_bound {F₀ : ℝ → ℝ} {Rstar B M₈ : ℝ}
    (hF₀m : Measurable F₀) (hF₀i : Integrable F₀)
    (hF₀2 : Integrable fun u => F₀ u ^ 2)
    (hF₀8 : Integrable fun u => F₀ u ^ 2 * Real.exp (-(8 * u)))
    (hF₀8_le : (∫ u, F₀ u ^ 2 * Real.exp (-(8 * u))) ≤ M₈)
    (hF₀_zero : ∀ u, 0 ≤ u → F₀ u = 0)
    (hliminf : ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F₀ T + criticalAliasCoefficient Rstar *
        (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) ≤ B) :
    ∃ (C : ℝ) (A : ℕ → ℝ) (H : ℕ → ℝ → ℝ), 0 ≤ C ∧
      (∀ k, 0 ≤ A k ∧ IsWindowTest (A k) (H k)) ∧
      (∀ k, (∫ u, H k u ^ 2) ≤ ∫ u, F₀ u ^ 2) ∧
      (∀ k, exponentialMass 8 (H k) ≤ Real.exp (8 / ((k : ℝ) + 1)) *
        (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u)))) ∧
      Tendsto (fun k => ∫ u, (H k u - F₀ u) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun k => exponentialSourceMass (fun u => H k u - F₀ u)) atTop (𝓝 0) ∧
      (∀ k, archForm (H k) ≤
        primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
          criticalAliasCoefficient Rstar * (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) +
          C / ((k : ℝ) + 1) + B) := by
  obtain ⟨C_arch, _hC_arch, hex_n⟩ :=
    exists_archForm_windowMollify_le_of_gammaLiminf_bound hF₀m hF₀i hF₀8 hF₀_zero hliminf
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ_pos : ∀ k, 0 < δ k := fun k => by dsimp only [δ]; positivity
  have hδ_le1 : ∀ k, δ k ≤ 1 := fun k => by
    dsimp only [δ]
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hδ_lim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex_k : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      archForm (windowMollify F₀ ((n : ℝ) + 1) (δ k)) ≤
        primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
          criticalAliasCoefficient Rstar * (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) +
          (C_arch + 1) * δ k + B := fun k => hex_n (hδ_pos k) k
  set n_seq : ℕ → ℕ := fun k => Classical.choose (hex_k k)
  have hn_ge : ∀ k, k ≤ n_seq k := fun k => (Classical.choose_spec (hex_k k)).1
  have hn_arch : ∀ k, archForm (windowMollify F₀ ((n_seq k : ℝ) + 1) (δ k)) ≤
      primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
        criticalAliasCoefficient Rstar * (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) +
        (C_arch + 1) * δ k + B := fun k => (Classical.choose_spec (hex_k k)).2
  set A_seq : ℕ → ℝ := fun k => (n_seq k : ℝ) + 1
  set H : ℕ → ℝ → ℝ := fun k => windowMollify F₀ (A_seq k) (δ k)
  have hA_pos : ∀ k, 0 < A_seq k := fun k => by dsimp only [A_seq]; positivity
  have hH_win : ∀ k, IsWindowTest (A_seq k + δ k) (H k) := fun k =>
    isWindowTest_windowMollify (hA_pos k) (hδ_pos k) hF₀i
  have hH_cd : ∀ k, ContDiff ℝ 2 (H k) := fun k => (hH_win k).contDiff
  have hH_cs : ∀ k, HasCompactSupport (H k) := fun k => (hH_win k).hasCompactSupport
  have hH_supp1 : ∀ k y, 1 < y → H k y = 0 := fun k y hy =>
    (hH_win k).vanish y fun hm => by linarith only [hy, hm.2]
  have hH_mass : ∀ k, (∫ y, H k y ^ 2) ≤ ∫ y, F₀ y ^ 2 := by
    intro k
    set Gk : ℝ → ℝ := (Set.Ioo (-A_seq k) 0).indicator F₀
    have hGkm : Measurable Gk := hF₀m.indicator measurableSet_Ioo
    have hGk2 : Integrable fun y => Gk y ^ 2 := by
      refine hF₀2.mono' (hGkm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      dsimp only [Gk]; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hy : y ∈ Set.Ioo (-A_seq k) 0 <;> simp [hy, sq_nonneg]
    have hGk_le : (∫ y, Gk y ^ 2) ≤ ∫ y, F₀ y ^ 2 := by
      refine integral_mono hGk2 hF₀2 fun y => ?_
      dsimp only [Gk]
      by_cases hy : y ∈ Set.Ioo (-A_seq k) 0 <;> simp [hy, sq_nonneg]
    exact (HTGeometry.integral_sq_mollify_le_of_isProbabilityDensity
      (contDiff_leftSplineMollifier (δ k)).continuous.measurable hGkm
      (leftSplineMollifier_nonneg (hδ_pos k)) (integrable_leftSplineMollifier (hδ_pos k))
      (integral_leftSplineMollifier (hδ_pos k)) hGk2
      (((hH_cd k).continuous.pow 2).integrable_of_hasCompactSupport
        (HTGeometry.hasCompactSupport_sq (hH_cs k)))).trans hGk_le
  set I₈ : ℝ := ∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))
  have hI₈_nonneg : 0 ≤ I₈ := setIntegral_nonneg measurableSet_Iio
    (fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hI₈_le : I₈ ≤ M₈ :=
    (setIntegral_le_integral hF₀8
      (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)).trans hF₀8_le
  have hH_exp8 : ∀ k, (∫ y, H k y ^ 2 * Real.exp (-(8 * y))) ≤ Real.exp 8 * M₈ := by
    intro k
    have hm1 := exponentialMass_windowMollify_le (A := A_seq k) (hδ_pos k) hF₀m hF₀2 hF₀8
    have hexp_eq : (∫ y, H k y ^ 2 * Real.exp (-(8 * y))) = exponentialMass 8 (H k) :=
      integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    have hexp_le : Real.exp (8 * δ k) ≤ Real.exp 8 :=
      Real.exp_le_exp.mpr (by linarith only [hδ_le1 k])
    rw [hexp_eq]
    exact hm1.trans (mul_le_mul hexp_le hI₈_le hI₈_nonneg (Real.exp_pos _).le)
  have hH_L2 : Tendsto (fun k : ℕ => ∫ y, (H k y - F₀ y) ^ 2) atTop (𝓝 0) := by
    have hmoll_lim := tendsto_integral_sq_lineConvolution_leftSplineMollifier_sub hF₀m hF₀2
    have htail_lim : Tendsto (fun k : ℕ => 2 * (M₈ * Real.exp (-8 * ((k : ℝ) + 1))) +
        2 * ∫ y, (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2)
        atTop (𝓝 0) := by
      have hexp_z : Tendsto (fun k : ℕ => M₈ * Real.exp (-8 * ((k : ℝ) + 1))) atTop (𝓝 0) := by
        have hlin : Tendsto (fun k : ℕ => -8 * ((k : ℝ) + 1)) atTop atBot :=
          (Filter.tendsto_neg_atTop_atBot.comp
            ((tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))).const_mul_atTop
              (by norm_num : (0 : ℝ) < 8))).congr fun k => by
            dsimp only [Function.comp_def]; ring
        simpa only [Function.comp_def, mul_zero] using
          (Real.tendsto_exp_atBot.comp hlin).const_mul M₈
      simpa only [mul_zero, add_zero] using (hexp_z.const_mul 2).add (hmoll_lim.const_mul 2)
    refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun k => ?_) htail_lim
    set Gk : ℝ → ℝ := (Set.Ioo (-A_seq k) 0).indicator F₀
    have hGkm : Measurable Gk := hF₀m.indicator measurableSet_Ioo
    have hGk2 : Integrable fun y => Gk y ^ 2 := by
      refine hF₀2.mono' (hGkm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      dsimp only [Gk]; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hy : y ∈ Set.Ioo (-A_seq k) 0 <;> simp [hy, sq_nonneg]
    have hGF2 : Integrable fun y => (Gk y - F₀ y) ^ 2 := by
      have hdom : Integrable fun y => 2 * Gk y ^ 2 + 2 * F₀ y ^ 2 :=
        (hGk2.const_mul 2).add (hF₀2.const_mul 2)
      refine hdom.mono' ((hGkm.sub hF₀m).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith only [sq_nonneg (Gk y + F₀ y)]
    have hρ_cont := (contDiff_leftSplineMollifier (δ k)).continuous
    have hρ_cs := hasCompactSupport_leftSplineMollifier (hδ_pos k)
    have hρ2 : Integrable fun s => leftSplineMollifier (δ k) s ^ 2 :=
      (hρ_cont.pow 2).integrable_of_hasCompactSupport (HTGeometry.hasCompactSupport_sq hρ_cs)
    have hconv_diff_int : Integrable fun y =>
        HTGeometry.lineConvolution (leftSplineMollifier (δ k)) (fun t => Gk t - F₀ t) y ^ 2 :=
      HTGeometry.integrable_sq_lineConvolution hρ_cont hρ_cs (hGkm.sub hF₀m) hGF2
    have hcontr := HTGeometry.integral_sq_mollify_le_of_isProbabilityDensity
      hρ_cont.measurable (hGkm.sub hF₀m) (leftSplineMollifier_nonneg (hδ_pos k))
      (integrable_leftSplineMollifier (hδ_pos k)) (integral_leftSplineMollifier (hδ_pos k))
      hGF2 hconv_diff_int
    have hGF_tail : (∫ y, (Gk y - F₀ y) ^ 2) ≤ M₈ * Real.exp (-8 * ((k : ℝ) + 1)) := by
      have hpt : ∀ y, (Gk y - F₀ y) ^ 2 ≤
          Real.exp (-8 * ((k : ℝ) + 1)) * (F₀ y ^ 2 * Real.exp (-(8 * y))) := by
        intro y
        dsimp only [Gk]
        by_cases hy : y ∈ Set.Ioo (-A_seq k) 0
        · rw [Set.indicator_of_mem hy, sub_self, sq, zero_mul]
          positivity
        · rw [Set.indicator_of_notMem hy, zero_sub, neg_sq]
          rcases le_or_gt 0 y with hy0 | hy0
          · rw [hF₀_zero y hy0, sq, zero_mul, zero_mul, mul_zero]
          · have hyA : y ≤ -A_seq k := not_lt.mp fun hlt => hy ⟨hlt, hy0⟩
            have hk_le : (k : ℝ) + 1 ≤ A_seq k := by
              dsimp only [A_seq]; exact_mod_cast Nat.add_le_add_right (hn_ge k) 1
            have hexp1 : 1 ≤ Real.exp (-8 * ((k : ℝ) + 1)) * Real.exp (-(8 * y)) := by
              rw [← Real.exp_add]; exact Real.one_le_exp (by linarith only [hyA, hk_le])
            have hm := mul_le_mul_of_nonneg_left hexp1 (sq_nonneg (F₀ y))
            linarith only [hm]
      exact (integral_mono hGF2 (hF₀8.const_mul _) hpt).trans
        (by
          rw [integral_const_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hF₀8_le (Real.exp_pos _).le)
    have hmoll_F_int : Integrable fun y =>
        (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2 := by
      have hc_int := HTGeometry.integrable_sq_lineConvolution hρ_cont hρ_cs hF₀m hF₀2
      have hdom : Integrable fun y =>
          2 * HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y ^ 2 + 2 * F₀ y ^ 2 :=
        (hc_int.const_mul 2).add (hF₀2.const_mul 2)
      refine hdom.mono' (((HTGeometry.continuous_lineConvolution hρ_cont hρ_cs
        (HTGeometry.locallyIntegrable_of_sq_integrable hF₀m.aestronglyMeasurable hF₀2)).measurable.sub
          hF₀m).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith only [sq_nonneg (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y + F₀ y)]
    have hHF_int : Integrable fun y => (H k y - F₀ y) ^ 2 := by
      have hH2 : Integrable fun y => H k y ^ 2 :=
        ((hH_cd k).continuous.pow 2).integrable_of_hasCompactSupport
          (HTGeometry.hasCompactSupport_sq (hH_cs k))
      have hdom : Integrable fun y => 2 * H k y ^ 2 + 2 * F₀ y ^ 2 :=
        (hH2.const_mul 2).add (hF₀2.const_mul 2)
      refine hdom.mono' (((hH_cd k).continuous.measurable.sub hF₀m).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith only [sq_nonneg (H k y + F₀ y)]
    have hsplit_pt : ∀ y, (H k y - F₀ y) ^ 2 ≤
        2 * HTGeometry.lineConvolution (leftSplineMollifier (δ k)) (fun t => Gk t - F₀ t) y ^ 2 +
          2 * (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2 := by
      intro y
      have hintG := HTGeometry.integrable_kernel_mul_sq hρ_cont.aestronglyMeasurable hρ2
        hGkm.aestronglyMeasurable hGk2 y
      have hintF := HTGeometry.integrable_kernel_mul_sq hρ_cont.aestronglyMeasurable hρ2
        hF₀m.aestronglyMeasurable hF₀2 y
      have hsub : H k y - HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y =
          HTGeometry.lineConvolution (leftSplineMollifier (δ k)) (fun t => Gk t - F₀ t) y := by
        dsimp only [H, windowMollify, HTGeometry.lineConvolution]
        rw [← integral_sub hintG hintF]
        exact integral_congr_ae (Eventually.of_forall fun s => by dsimp only; ring)
      set a := HTGeometry.lineConvolution (leftSplineMollifier (δ k)) (fun t => Gk t - F₀ t) y
      set b := HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y
      have hab : H k y - F₀ y = a + b := by dsimp only [a, b]; linarith only [hsub]
      rw [hab]
      nlinarith only [sq_nonneg (a - b)]
    have hm : (∫ y, (H k y - F₀ y) ^ 2) ≤
        ∫ y, (2 * HTGeometry.lineConvolution (leftSplineMollifier (δ k))
          (fun t => Gk t - F₀ t) y ^ 2 +
          2 * (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2) :=
      integral_mono hHF_int ((hconv_diff_int.const_mul 2).add (hmoll_F_int.const_mul 2))
        hsplit_pt
    have hadd_m : (∫ y, (2 * HTGeometry.lineConvolution (leftSplineMollifier (δ k))
        (fun t => Gk t - F₀ t) y ^ 2 +
        2 * (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2)) =
        2 * (∫ y, HTGeometry.lineConvolution (leftSplineMollifier (δ k))
          (fun t => Gk t - F₀ t) y ^ 2) +
        2 * ∫ y, (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2 := by
      rw [integral_add (hconv_diff_int.const_mul 2) (hmoll_F_int.const_mul 2),
        integral_const_mul, integral_const_mul]
    rw [hadd_m] at hm
    have hcontr' : (∫ y, HTGeometry.lineConvolution (leftSplineMollifier (δ k))
        (fun t => Gk t - F₀ t) y ^ 2) ≤ M₈ * Real.exp (-8 * ((k : ℝ) + 1)) :=
      hcontr.trans hGF_tail
    linarith only [hm, hcontr']
  have hF₀_supp1 : ∀ᵐ y, 1 < y → F₀ y = 0 :=
    Eventually.of_forall fun y hy => hF₀_zero y (zero_lt_one.trans hy).le
  have hF₀W : WeightedTwo F₀ :=
    (exponentialSourceMass_le_of_support zero_le_one hF₀m.aestronglyMeasurable hF₀2 hF₀8
      hF₀_supp1).1
  have hstrong : ∀ ε > 0, ∀ᶠ k in atTop, (∫ y, (H k y - F₀ y) ^ 2) ≤ ε := fun ε hε =>
    (hH_L2.eventually (gt_mem_nhds hε)).mono fun _ hk => hk.le
  have hd := tendsto_exponentialSourceMass_sub (fun k => (hH_cd k).continuous) hH_cs
    hF₀m.aestronglyMeasurable hF₀2 hF₀8 hH_exp8 (Eventually.of_forall hH_supp1) hF₀_supp1 hstrong
  refine ⟨C_arch + 1, (fun k => A_seq k + δ k), H, by linarith only [_hC_arch],
    fun k => ⟨by positivity, hH_win k⟩, hH_mass, ?_, hH_L2, hd, ?_⟩
  · intro k
    have hh := exponentialMass_windowMollify_le (A := A_seq k) (hδ_pos k) hF₀m hF₀2 hF₀8
    simpa only [H, δ, mul_one_div] using hh
  · intro k
    simpa only [H, δ, mul_one_div] using hn_arch k

/-- A unit-norm `L²` profile `F₀` vanishing on `[0, ∞)` that satisfies the critical `Γ`-liminf
inequality at `Rstar` cannot coexist with `∀ A ≥ 0, (R₁ : EReal) < windowThreshold A` for any
`R₁ > Rstar`. -/
private theorem contradiction_of_limit_profile_below_windowThreshold {Rstar R₁ : ℝ}
    (hRstar : 0 < Rstar) (hR_lt : Rstar < R₁)
    (hR₁_win : ∀ A : ℝ, 0 ≤ A → (R₁ : EReal) < windowThreshold A)
    {F₀ : ℝ → ℝ} (hF₀m : Measurable F₀) (hF₀i : Integrable F₀)
    (hF₀2 : Integrable fun u => F₀ u ^ 2) (hF₀_norm : (∫ u, F₀ u ^ 2) = 1)
    {M₈ : ℝ} (_hM₈0 : 0 ≤ M₈) (hF₀8 : Integrable fun u => F₀ u ^ 2 * Real.exp (-(8 * u)))
    (hF₀8_le : (∫ u, F₀ u ^ 2 * Real.exp (-(8 * u))) ≤ M₈)
    (hF₀_zero : ∀ u, 0 ≤ u → F₀ u = 0)
    (hliminf : ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F₀ T + criticalAliasCoefficient Rstar *
        (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) ≤ 0) : False := by
  have hR₁ : 0 < R₁ := hRstar.trans hR_lt
  obtain ⟨C_arch, _hC_arch, hex_n⟩ :=
    exists_archForm_windowMollify_le_of_gammaLiminf hF₀m hF₀i hF₀8 hF₀_zero hliminf
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ_pos : ∀ k, 0 < δ k := fun k => by dsimp only [δ]; positivity
  have hδ_le1 : ∀ k, δ k ≤ 1 := fun k => by
    dsimp only [δ]
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hδ_lim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex_k : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      archForm (windowMollify F₀ ((n : ℝ) + 1) (δ k)) ≤
        primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
          criticalAliasCoefficient Rstar * (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) +
          (C_arch + 1) * δ k := fun k => hex_n (hδ_pos k) k
  set n_seq : ℕ → ℕ := fun k => Classical.choose (hex_k k)
  have hn_ge : ∀ k, k ≤ n_seq k := fun k => (Classical.choose_spec (hex_k k)).1
  have hn_arch : ∀ k, archForm (windowMollify F₀ ((n_seq k : ℝ) + 1) (δ k)) ≤
      primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
        criticalAliasCoefficient Rstar * (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) +
        (C_arch + 1) * δ k := fun k => (Classical.choose_spec (hex_k k)).2
  set A_seq : ℕ → ℝ := fun k => (n_seq k : ℝ) + 1
  set H : ℕ → ℝ → ℝ := fun k => windowMollify F₀ (A_seq k) (δ k)
  have hA_pos : ∀ k, 0 < A_seq k := fun k => by dsimp only [A_seq]; positivity
  have hH_win : ∀ k, IsWindowTest (A_seq k + δ k) (H k) := fun k =>
    isWindowTest_windowMollify (hA_pos k) (hδ_pos k) hF₀i
  have hH_cd : ∀ k, ContDiff ℝ 2 (H k) := fun k => (hH_win k).contDiff
  have hH_cs : ∀ k, HasCompactSupport (H k) := fun k => (hH_win k).hasCompactSupport
  have hH_supp1 : ∀ k y, 1 < y → H k y = 0 := fun k y hy =>
    (hH_win k).vanish y fun hm => by linarith only [hy, hm.2]
  have hH_mass : ∀ k, (∫ y, H k y ^ 2) ≤ 1 := by
    intro k
    set Gk : ℝ → ℝ := (Set.Ioo (-A_seq k) 0).indicator F₀
    have hGkm : Measurable Gk := hF₀m.indicator measurableSet_Ioo
    have hGk2 : Integrable fun y => Gk y ^ 2 := by
      refine hF₀2.mono' (hGkm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      dsimp only [Gk]; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hy : y ∈ Set.Ioo (-A_seq k) 0 <;> simp [hy, sq_nonneg]
    have hGk_le : (∫ y, Gk y ^ 2) ≤ 1 := by
      rw [← hF₀_norm]
      refine integral_mono hGk2 hF₀2 fun y => ?_
      dsimp only [Gk]
      by_cases hy : y ∈ Set.Ioo (-A_seq k) 0 <;> simp [hy, sq_nonneg]
    exact (HTGeometry.integral_sq_mollify_le_of_isProbabilityDensity
      (contDiff_leftSplineMollifier (δ k)).continuous.measurable hGkm
      (leftSplineMollifier_nonneg (hδ_pos k)) (integrable_leftSplineMollifier (hδ_pos k))
      (integral_leftSplineMollifier (hδ_pos k)) hGk2
      (((hH_cd k).continuous.pow 2).integrable_of_hasCompactSupport
        (HTGeometry.hasCompactSupport_sq (hH_cs k)))).trans hGk_le
  set I₈ : ℝ := ∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))
  have hI₈_ge1 : 1 ≤ I₈ := by
    rw [← hF₀_norm]
    have htot_eq : (∫ u, F₀ u ^ 2) = ∫ u in Set.Iio 0, F₀ u ^ 2 := by
      rw [← MeasureTheory.integral_indicator measurableSet_Iio]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      by_cases hu : u ∈ Set.Iio (0 : ℝ)
      · rw [Set.indicator_of_mem hu]
      · have hu0 : 0 ≤ u := not_lt.mp hu
        rw [Set.indicator_of_notMem hu, hF₀_zero u hu0, sq, mul_zero]
    rw [htot_eq]
    refine setIntegral_mono_on hF₀2.integrableOn hF₀8.integrableOn measurableSet_Iio fun u hu => ?_
    rw [Set.mem_Iio] at hu
    exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by linarith only [hu]))
  have hI₈_le : I₈ ≤ M₈ :=
    (setIntegral_le_integral hF₀8
      (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)).trans hF₀8_le
  have hH_exp8 : ∀ k, (∫ y, H k y ^ 2 * Real.exp (-(8 * y))) ≤ Real.exp 8 * M₈ := by
    intro k
    have hm1 := exponentialMass_windowMollify_le (A := A_seq k) (hδ_pos k) hF₀m hF₀2 hF₀8
    have hexp_eq : (∫ y, H k y ^ 2 * Real.exp (-(8 * y))) = exponentialMass 8 (H k) :=
      integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    have hexp_le : Real.exp (8 * δ k) ≤ Real.exp 8 :=
      Real.exp_le_exp.mpr (by linarith only [hδ_le1 k])
    rw [hexp_eq]
    exact hm1.trans (mul_le_mul hexp_le hI₈_le (by linarith only [hI₈_ge1]) (Real.exp_pos _).le)
  have hH_L2 : Tendsto (fun k : ℕ => ∫ y, (H k y - F₀ y) ^ 2) atTop (𝓝 0) := by
    have hmoll_lim := tendsto_integral_sq_lineConvolution_leftSplineMollifier_sub hF₀m hF₀2
    have htail_lim : Tendsto (fun k : ℕ => 2 * (M₈ * Real.exp (-8 * ((k : ℝ) + 1))) +
        2 * ∫ y, (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2)
        atTop (𝓝 0) := by
      have hexp_z : Tendsto (fun k : ℕ => M₈ * Real.exp (-8 * ((k : ℝ) + 1))) atTop (𝓝 0) := by
        have hlin : Tendsto (fun k : ℕ => -8 * ((k : ℝ) + 1)) atTop atBot :=
          (Filter.tendsto_neg_atTop_atBot.comp
            ((tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))).const_mul_atTop
              (by norm_num : (0 : ℝ) < 8))).congr fun k => by
            dsimp only [Function.comp_def]; ring
        simpa only [Function.comp_def, mul_zero] using
          (Real.tendsto_exp_atBot.comp hlin).const_mul M₈
      simpa only [mul_zero, add_zero] using (hexp_z.const_mul 2).add (hmoll_lim.const_mul 2)
    refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun k => ?_) htail_lim
    set Gk : ℝ → ℝ := (Set.Ioo (-A_seq k) 0).indicator F₀
    have hGkm : Measurable Gk := hF₀m.indicator measurableSet_Ioo
    have hGk2 : Integrable fun y => Gk y ^ 2 := by
      refine hF₀2.mono' (hGkm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      dsimp only [Gk]; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hy : y ∈ Set.Ioo (-A_seq k) 0 <;> simp [hy, sq_nonneg]
    have hGF2 : Integrable fun y => (Gk y - F₀ y) ^ 2 := by
      have hdom : Integrable fun y => 2 * Gk y ^ 2 + 2 * F₀ y ^ 2 :=
        (hGk2.const_mul 2).add (hF₀2.const_mul 2)
      refine hdom.mono' ((hGkm.sub hF₀m).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith only [sq_nonneg (Gk y + F₀ y)]
    have hρ_cont := (contDiff_leftSplineMollifier (δ k)).continuous
    have hρ_cs := hasCompactSupport_leftSplineMollifier (hδ_pos k)
    have hρ2 : Integrable fun s => leftSplineMollifier (δ k) s ^ 2 :=
      (hρ_cont.pow 2).integrable_of_hasCompactSupport (HTGeometry.hasCompactSupport_sq hρ_cs)
    have hconv_diff_int : Integrable fun y =>
        HTGeometry.lineConvolution (leftSplineMollifier (δ k)) (fun t => Gk t - F₀ t) y ^ 2 :=
      HTGeometry.integrable_sq_lineConvolution hρ_cont hρ_cs (hGkm.sub hF₀m) hGF2
    have hcontr := HTGeometry.integral_sq_mollify_le_of_isProbabilityDensity
      hρ_cont.measurable (hGkm.sub hF₀m) (leftSplineMollifier_nonneg (hδ_pos k))
      (integrable_leftSplineMollifier (hδ_pos k)) (integral_leftSplineMollifier (hδ_pos k))
      hGF2 hconv_diff_int
    have hGF_tail : (∫ y, (Gk y - F₀ y) ^ 2) ≤ M₈ * Real.exp (-8 * ((k : ℝ) + 1)) := by
      have hpt : ∀ y, (Gk y - F₀ y) ^ 2 ≤
          Real.exp (-8 * ((k : ℝ) + 1)) * (F₀ y ^ 2 * Real.exp (-(8 * y))) := by
        intro y
        dsimp only [Gk]
        by_cases hy : y ∈ Set.Ioo (-A_seq k) 0
        · rw [Set.indicator_of_mem hy, sub_self, sq, zero_mul]
          positivity
        · rw [Set.indicator_of_notMem hy, zero_sub, neg_sq]
          rcases le_or_gt 0 y with hy0 | hy0
          · rw [hF₀_zero y hy0, sq, zero_mul, zero_mul, mul_zero]
          · have hyA : y ≤ -A_seq k := not_lt.mp fun hlt => hy ⟨hlt, hy0⟩
            have hk_le : (k : ℝ) + 1 ≤ A_seq k := by
              dsimp only [A_seq]; exact_mod_cast Nat.add_le_add_right (hn_ge k) 1
            have hexp1 : 1 ≤ Real.exp (-8 * ((k : ℝ) + 1)) * Real.exp (-(8 * y)) := by
              rw [← Real.exp_add]; exact Real.one_le_exp (by linarith only [hyA, hk_le])
            have hm := mul_le_mul_of_nonneg_left hexp1 (sq_nonneg (F₀ y))
            linarith only [hm]
      exact (integral_mono hGF2 (hF₀8.const_mul _) hpt).trans
        (by
          rw [integral_const_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hF₀8_le (Real.exp_pos _).le)
    have hmoll_F_int : Integrable fun y =>
        (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2 := by
      have hc_int := HTGeometry.integrable_sq_lineConvolution hρ_cont hρ_cs hF₀m hF₀2
      have hdom : Integrable fun y =>
          2 * HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y ^ 2 + 2 * F₀ y ^ 2 :=
        (hc_int.const_mul 2).add (hF₀2.const_mul 2)
      refine hdom.mono' (((HTGeometry.continuous_lineConvolution hρ_cont hρ_cs
        (HTGeometry.locallyIntegrable_of_sq_integrable hF₀m.aestronglyMeasurable hF₀2)).measurable.sub
          hF₀m).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith only [sq_nonneg (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y + F₀ y)]
    have hHF_int : Integrable fun y => (H k y - F₀ y) ^ 2 := by
      have hH2 : Integrable fun y => H k y ^ 2 :=
        ((hH_cd k).continuous.pow 2).integrable_of_hasCompactSupport
          (HTGeometry.hasCompactSupport_sq (hH_cs k))
      have hdom : Integrable fun y => 2 * H k y ^ 2 + 2 * F₀ y ^ 2 :=
        (hH2.const_mul 2).add (hF₀2.const_mul 2)
      refine hdom.mono' (((hH_cd k).continuous.measurable.sub hF₀m).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith only [sq_nonneg (H k y + F₀ y)]
    have hsplit_pt : ∀ y, (H k y - F₀ y) ^ 2 ≤
        2 * HTGeometry.lineConvolution (leftSplineMollifier (δ k)) (fun t => Gk t - F₀ t) y ^ 2 +
          2 * (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2 := by
      intro y
      have hintG := HTGeometry.integrable_kernel_mul_sq hρ_cont.aestronglyMeasurable hρ2
        hGkm.aestronglyMeasurable hGk2 y
      have hintF := HTGeometry.integrable_kernel_mul_sq hρ_cont.aestronglyMeasurable hρ2
        hF₀m.aestronglyMeasurable hF₀2 y
      have hsub : H k y - HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y =
          HTGeometry.lineConvolution (leftSplineMollifier (δ k)) (fun t => Gk t - F₀ t) y := by
        dsimp only [H, windowMollify, HTGeometry.lineConvolution]
        rw [← integral_sub hintG hintF]
        exact integral_congr_ae (Eventually.of_forall fun s => by dsimp only; ring)
      set a := HTGeometry.lineConvolution (leftSplineMollifier (δ k)) (fun t => Gk t - F₀ t) y
      set b := HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y
      have hab : H k y - F₀ y = a + b := by dsimp only [a, b]; linarith only [hsub]
      rw [hab]
      nlinarith only [sq_nonneg (a - b)]
    have hm : (∫ y, (H k y - F₀ y) ^ 2) ≤
        ∫ y, (2 * HTGeometry.lineConvolution (leftSplineMollifier (δ k))
          (fun t => Gk t - F₀ t) y ^ 2 +
          2 * (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2) :=
      integral_mono hHF_int ((hconv_diff_int.const_mul 2).add (hmoll_F_int.const_mul 2))
        hsplit_pt
    have hadd_m : (∫ y, (2 * HTGeometry.lineConvolution (leftSplineMollifier (δ k))
        (fun t => Gk t - F₀ t) y ^ 2 +
        2 * (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2)) =
        2 * (∫ y, HTGeometry.lineConvolution (leftSplineMollifier (δ k))
          (fun t => Gk t - F₀ t) y ^ 2) +
        2 * ∫ y, (HTGeometry.lineConvolution (leftSplineMollifier (δ k)) F₀ y - F₀ y) ^ 2 := by
      rw [integral_add (hconv_diff_int.const_mul 2) (hmoll_F_int.const_mul 2),
        integral_const_mul, integral_const_mul]
    rw [hadd_m] at hm
    have hcontr' : (∫ y, HTGeometry.lineConvolution (leftSplineMollifier (δ k))
        (fun t => Gk t - F₀ t) y ^ 2) ≤ M₈ * Real.exp (-8 * ((k : ℝ) + 1)) :=
      hcontr.trans hGF_tail
    linarith only [hm, hcontr']
  have hF₀_supp1 : ∀ᵐ y, 1 < y → F₀ y = 0 :=
    Eventually.of_forall fun y hy => hF₀_zero y (zero_lt_one.trans hy).le
  have hF₀W : WeightedTwo F₀ :=
    (exponentialSourceMass_le_of_support zero_le_one hF₀m.aestronglyMeasurable hF₀2 hF₀8
      hF₀_supp1).1
  have hstrong : ∀ ε > 0, ∀ᶠ k in atTop, (∫ y, (H k y - F₀ y) ^ 2) ≤ ε := fun ε hε =>
    (hH_L2.eventually (gt_mem_nhds hε)).mono fun _ hk => hk.le
  have hd := tendsto_exponentialSourceMass_sub (fun k => (hH_cd k).continuous) hH_cs
    hF₀m.aestronglyMeasurable hF₀2 hF₀8 hH_exp8 (Eventually.of_forall hH_supp1) hF₀_supp1 hstrong
  obtain ⟨hP, hC, hS⟩ := tendsto_prime_and_pole_of_strong_limit (fun k => (hH_cd k).continuous)
    hH_cs hF₀W hH_mass hH_exp8 (Eventually.of_forall hH_supp1) hd
  have hkappa_alias : splineAtom * criticalAliasCoefficient Rstar = 7 * tiltedJordanOne / Rstar := by
    unfold splineAtom criticalAliasCoefficient
    have hm1_ne : (∫ u, tiltedUnitSpline u) ≠ 0 := integral_tiltedUnitSpline_ne_zero
    have hm_ne : (∫ u, tiltedUnitSpline u) ^ 2 ≠ 0 := pow_ne_zero 2 hm1_ne
    have hsq_ne : (∫ u, tiltedUnitSpline u ^ 2) ≠ 0 := integral_tiltedUnitSpline_sq_pos.ne'
    field_simp [hm1_ne, hm_ne, hsq_ne, hRstar.ne']
  set gap : ℝ := (7 * tiltedJordanOne / Rstar - 7 * tiltedJordanOne / R₁) * I₈
  have hgap_pos : 0 < gap := by
    have hJ : 0 < 7 * tiltedJordanOne := by have := tiltedJordanOne_pos; positivity
    have hdiv_lt : 7 * tiltedJordanOne / R₁ < 7 * tiltedJordanOne / Rstar :=
      div_lt_div_of_pos_left hJ hRstar hR_lt
    exact mul_pos (by linarith only [hdiv_lt]) (zero_lt_one.trans_le hI₈_ge1)
  have hub_lim : Tendsto (fun k : ℕ =>
      splineAtom * (primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
        criticalAliasCoefficient Rstar * I₈ + (C_arch + 1) * δ k - primeSum (H k) +
        (2 * coshHalfMoment (H k) ^ 2 - 2 * sinhHalfMoment (H k) ^ 2)) +
      (7 * tiltedJordanOne / R₁) * (Real.exp (8 * δ k) * I₈))
      atTop (𝓝 (-gap)) := by
    have h8δ : Tendsto (fun k : ℕ => 8 * δ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using hδ_lim.const_mul 8
    have hexp_lim : Tendsto (fun k : ℕ => Real.exp (8 * δ k)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, Real.exp_zero] using
        (Real.continuous_exp.tendsto 0).comp h8δ
    have h1 := ((((tendsto_const_nhds (x := primeSum F₀ -
        (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
        criticalAliasCoefficient Rstar * I₈)).add
        (hδ_lim.const_mul (C_arch + 1))).sub hP).add
      (((hC.pow 2).const_mul 2).sub ((hS.pow 2).const_mul 2))).const_mul splineAtom
    have h2 := (hexp_lim.mul_const I₈).const_mul (7 * tiltedJordanOne / R₁)
    refine (h1.add h2).trans (le_of_eq ?_)
    congr 1
    dsimp only [gap]
    have hlin : splineAtom * (primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
        criticalAliasCoefficient Rstar * I₈ + (C_arch + 1) * 0 - primeSum F₀ +
        (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2)) +
        7 * tiltedJordanOne / R₁ * (1 * I₈) =
        -(splineAtom * criticalAliasCoefficient Rstar) * I₈ + (7 * tiltedJordanOne / R₁) * I₈ := by
      ring
    rw [hlin, hkappa_alias]
    ring
  have hH_norm_pos : ∀ᶠ k in atTop, H k ≠ 0 := by
    filter_upwards [hH_L2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with k hk
    intro h0
    have heq : (∫ y, (H k y - F₀ y) ^ 2) = ∫ y, F₀ y ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      rw [h0, Pi.zero_apply, zero_sub, neg_sq]
    rw [heq, hF₀_norm] at hk
    linarith only [hk]
  obtain ⟨k, hk_neg, hk_ne⟩ := ((hub_lim.eventually (gt_mem_nhds (neg_lt_zero.mpr hgap_pos))).and
    hH_norm_pos).exists
  have hpen_ub : windowPencil R₁ (H k) ≤
      splineAtom * (primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
        criticalAliasCoefficient Rstar * I₈ + (C_arch + 1) * δ k - primeSum (H k) +
        (2 * coshHalfMoment (H k) ^ 2 - 2 * sinhHalfMoment (H k) ^ 2)) +
      (7 * tiltedJordanOne / R₁) * (Real.exp (8 * δ k) * I₈) := by
    unfold windowPencil
    rw [weilQuad_eq_arch_sub_prime_add_pole (hH_cd k) (hH_cs k)]
    have hw_le := mul_le_mul_of_nonneg_left
      (show archForm (H k) - primeSum (H k) +
          (2 * coshHalfMoment (H k) ^ 2 - 2 * sinhHalfMoment (H k) ^ 2) ≤
        primeSum F₀ - (2 * coshHalfMoment F₀ ^ 2 - 2 * sinhHalfMoment F₀ ^ 2) -
          criticalAliasCoefficient Rstar * I₈ + (C_arch + 1) * δ k - primeSum (H k) +
          (2 * coshHalfMoment (H k) ^ 2 - 2 * sinhHalfMoment (H k) ^ 2) by
        linarith only [hn_arch k])
      splineAtom_pos.le
    have he_le := mul_le_mul_of_nonneg_left
      (exponentialMass_windowMollify_le (A := A_seq k) (hδ_pos k) hF₀m hF₀2 hF₀8)
      (by have := tiltedJordanOne_pos; positivity : 0 ≤ 7 * tiltedJordanOne / R₁)
    linarith only [hw_le, he_le]
  have hpen_pos := pencil_pos_of_lt_windowThreshold hR₁
    (hR₁_win (A_seq k + δ k) (add_pos (hA_pos k) (hδ_pos k)).le) (hH_win k) hk_ne
  linarith only [hpen_ub, hk_neg, hpen_pos]


/-- Scaling atomic coefficients scales the normalized centred test. -/
theorem normalizedCentredAtomicTest_const_mul (α : ℝ) (y : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    normalizedCentredAtomicTest tiltedUnitSpline (fun n => α * y n) c N =
      fun u => α * normalizedCentredAtomicTest tiltedUnitSpline y c N u := by
  funext u
  unfold normalizedCentredAtomicTest centredAtomicTest atomicTest
  simp_rw [mul_assoc, ← mul_sum]
  ring

private theorem normalizedCentredAtomicTest_zero (c : ℝ) (N : ℕ) :
    normalizedCentredAtomicTest tiltedUnitSpline 0 c N = 0 := by
  funext u
  simp [normalizedCentredAtomicTest, centredAtomicTest, atomicTest]

private theorem normalizedCentredAtomicTest_eq_zero_of_gt {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : 1 ≤ N) (y : ℕ → ℝ) {u : ℝ} (hu : c / (N : ℝ) < u) :
    normalizedCentredAtomicTest tiltedUnitSpline y c N u = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / (N : ℝ) := div_pos hc hN0
  have hsupp := tiltedUnitSpline_atom_support hw
  simp only [normalizedCentredAtomicTest, centredAtomicTest, atomicTest]
  rw [mul_eq_zero]
  right
  refine sum_eq_zero fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hnN)
  rw [hsupp _ fun hmem => by linarith only [hmem.2, hu, hlog], mul_zero]

/-- A unit-mass critical atomic sequence with bounded eighth exponential mass cannot have
asymptotically nonpositive Weil form below every continuum window threshold. -/
theorem no_nonpositive_atomic_sequence_below_windowThreshold
    {Rstar : ℝ} (hRstar : 0 < Rstar)
    (hlt : (Rstar : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A)
    {N_seq : ℕ → ℕ} (hN_strict : StrictMono N_seq) (hN_pos : ∀ k, 1 ≤ N_seq k)
    {c_seq : ℕ → ℝ} (hc_seq : ∀ k, 1 ≤ c_seq k)
    (hcrit_seq : Tendsto (fun k => c_seq k ^ 8 / Real.log (N_seq k : ℝ)) atTop (𝓝 Rstar))
    (hc_width : ∀ k, c_seq k / (N_seq k : ℝ) ≤ 1 / ((k : ℝ) + 1))
    (y_norm : ℕ → ℕ → ℝ)
    (hV_norm : ∀ k, ∫ u, normalizedCentredAtomicTest tiltedUnitSpline (y_norm k)
      (c_seq k) (N_seq k) u ^ 2 = 1)
    {M₈ : ℝ} (hM₈_pos : 0 < M₈)
    (hV_M₈ : ∀ k, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (y_norm k)
      (c_seq k) (N_seq k) u ^ 2 * Real.exp (-(8 * u))) ≤ M₈)
    (hV_wq : ∀ k, weilQuad (normalizedCentredAtomicTest tiltedUnitSpline (y_norm k)
      (c_seq k) (N_seq k)) ≤ 1 / ((k : ℝ) + 1)) : False := by
  have hex_R₁ : ∃ R₁ : ℝ, Rstar < R₁ ∧ ∀ A : ℝ, 0 ≤ A → (R₁ : EReal) < windowThreshold A := by
    cases hinf : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) with
    | bot =>
      rw [hinf] at hlt
      exact absurd hlt not_lt_bot
    | top =>
      refine ⟨Rstar + 1, by linarith, fun A hA => ?_⟩
      have hle : (⨅ (B : ℝ) (_ : 0 ≤ B), windowThreshold B) ≤ windowThreshold A :=
        iInf_le_of_le A (iInf_le _ hA)
      rw [hinf, top_le_iff] at hle
      rw [hle]
      exact EReal.coe_lt_top _
    | coe M =>
      rw [hinf, EReal.coe_lt_coe_iff] at hlt
      refine ⟨(Rstar + M) / 2, by linarith, fun A hA => ?_⟩
      have hle : ((M : ℝ) : EReal) ≤ windowThreshold A := by
        rw [← hinf]
        exact iInf_le_of_le A (iInf_le _ hA)
      exact (EReal.coe_lt_coe_iff.mpr (by linarith)).trans_le hle
  obtain ⟨R₁, hR_lt, hR₁_win⟩ := hex_R₁
  let V : ℕ → ℝ → ℝ := fun k =>
    normalizedCentredAtomicTest tiltedUnitSpline (y_norm k) (c_seq k) (N_seq k)
  have hVd : ∀ k, ContDiff ℝ 2 (V k) := fun k =>
    contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline _ _ _)
  have hVc : ∀ k, HasCompactSupport (V k) := fun k =>
    (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero (y_norm k)
      (zero_lt_one.trans_le (hc_seq k)) (hN_pos k)).mul_left
  have hV_supp_k : ∀ (k : ℕ) (u : ℝ), 1 / (Nat.cast k + 1) < u → V k u = 0 := fun k u hu =>
    normalizedCentredAtomicTest_eq_zero_of_gt (zero_lt_one.trans_le (hc_seq k))
      (hN_pos k) (y_norm k) ((hc_width k).trans_lt hu)
  have hV_supp1 : ∀ (k : ℕ) (u : ℝ), 1 < u → V k u = 0 := fun k u hu =>
    hV_supp_k k u ((div_le_one_of_le₀
      (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)).trans_lt hu)
  have hV_wq1 : ∀ k, weilQuad (V k) ≤ 1 := fun k =>
    (hV_wq k).trans (div_le_one_of_le₀
      (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity))
  have hV_mem : ∀ k, MemLp (V k) 2 (volume : Measure ℝ) := fun k =>
    (hVd k).continuous.memLp_of_hasCompactSupport (hVc k)
  let φ₁ : ℕ → ℕ := fun k => k
  have hφ₁_mono : StrictMono φ₁ := fun _ _ h => h
  let R_lim := Rstar
  have hR_lim_pos : 0 < R_lim := hRstar
  have hR_lim_le : R_lim ≤ Rstar := le_rfl
  have hφ₁_lim : Tendsto (fun k => c_seq (φ₁ k) ^ 8 / Real.log (N_seq (φ₁ k) : ℝ))
      atTop (𝓝 R_lim) := hcrit_seq
  have hS_tb := totallyBounded_toLp_of_bounded_weilQuad hVd hVc (fun k => (hV_norm k).le)
    hM₈_pos.le hV_M₈ hV_supp1 hV_wq1 hV_mem
  have hS_seq : IsSeqCompact (closure (Set.range fun k : ℕ => (hV_mem k).toLp (V k))) :=
    (hS_tb.closure.isCompact_of_isComplete isClosed_closure.isComplete).isSeqCompact
  obtain ⟨F_Lp, _, φ₂, hφ₂_mono, hφ₂_lim⟩ :=
    hS_seq fun k => subset_closure ⟨φ₁ k, rfl⟩
  have hF_raw : MemLp F_Lp 2 (volume : Measure ℝ) := Lp.memLp F_Lp
  set F : ℝ → ℝ := hF_raw.aestronglyMeasurable.mk F_Lp
  have hFm : Measurable F := hF_raw.aestronglyMeasurable.measurable_mk
  have hF_ae : (F_Lp : ℝ → ℝ) =ᵐ[volume] F := hF_raw.aestronglyMeasurable.ae_eq_mk
  have hF_mem : MemLp F 2 (volume : Measure ℝ) := hF_raw.ae_eq hF_ae
  have hF_toLp : hF_mem.toLp F = F_Lp := Lp.ext (hF_mem.coeFn_toLp.trans hF_ae.symm)
  have hlp_eLp : Tendsto (fun i : ℕ => eLpNorm (fun u => V (φ₁ (φ₂ i)) u - F u) 2 volume)
      atTop (𝓝 0) := by
    have hnorm0 : Tendsto (fun i : ℕ => ‖(hV_mem (φ₁ (φ₂ i))).toLp (V (φ₁ (φ₂ i))) - F_Lp‖)
        atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hφ₂_lim
    have hof := (ENNReal.continuous_ofReal.tendsto 0).comp hnorm0
    simp only [ENNReal.ofReal_zero] at hof
    refine hof.congr fun i => ?_
    have hsub_mem : MemLp (V (φ₁ (φ₂ i)) - F) 2 (volume : Measure ℝ) :=
      (hV_mem (φ₁ (φ₂ i))).sub hF_mem
    have hto : hsub_mem.toLp (V (φ₁ (φ₂ i)) - F) =
        (hV_mem (φ₁ (φ₂ i))).toLp (V (φ₁ (φ₂ i))) - F_Lp := by
      rw [← hF_toLp, MemLp.toLp_sub]
    dsimp only [Function.comp_def]
    rw [← hto, Lp.norm_toLp, ENNReal.ofReal_toReal hsub_mem.eLpNorm_ne_top]
    rfl
  have hin_meas := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun i => (hV_mem (φ₁ (φ₂ i))).aestronglyMeasurable) hF_mem.aestronglyMeasurable hlp_eLp
  obtain ⟨φ₃, hφ₃_mono, hφ₃_ae⟩ := hin_meas.exists_seq_tendsto_ae
  set s : ℕ → ℕ := fun j => φ₁ (φ₂ (φ₃ j))
  have hs_mono : StrictMono s := hφ₁_mono.comp (hφ₂_mono.comp hφ₃_mono)
  have hs_Lp_lim : Tendsto (fun j : ℕ => (hV_mem (s j)).toLp (V (s j))) atTop (𝓝 F_Lp) :=
    hφ₂_lim.comp hφ₃_mono.tendsto_atTop
  have hs_L2 : Tendsto (fun j : ℕ => ∫ u, (V (s j) u - F u) ^ 2) atTop (𝓝 0) := by
    have hnorm_sq : Tendsto (fun j : ℕ => ‖(hV_mem (s j)).toLp (V (s j)) - hF_mem.toLp F‖ ^ 2)
        atTop (𝓝 (0 ^ 2)) := by
      rw [hF_toLp]
      exact (tendsto_iff_norm_sub_tendsto_zero.mp hs_Lp_lim).pow 2
    rw [zero_pow (by norm_num)] at hnorm_sq
    exact hnorm_sq.congr fun j => HTGeometry.norm_toLp_sub_sq (hV_mem (s j)) hF_mem
  have hF_norm : (∫ u, F u ^ 2) = 1 := by
    have hn1 : Tendsto (fun j : ℕ => ‖(hV_mem (s j)).toLp (V (s j))‖ ^ 2)
        atTop (𝓝 (‖hF_mem.toLp F‖ ^ 2)) := by
      rw [hF_toLp]
      exact (hs_Lp_lim.norm).pow 2
    have hn2 : ∀ j : ℕ, ‖(hV_mem (s j)).toLp (V (s j))‖ ^ 2 = 1 := fun j => by
      rw [HTGeometry.norm_toLp_sq, hV_norm (s j)]
    rw [← HTGeometry.norm_toLp_sq hF_mem]
    exact tendsto_nhds_unique hn1 (by simpa only [hn2] using tendsto_const_nhds)
  have hF_pos_ae : ∀ᵐ u : ℝ, 0 < u → F u = 0 := by
    filter_upwards [hφ₃_ae] with u hu_lim hu_pos
    have hex_j : ∃ j₀ : ℕ, (1 : ℝ) / (Nat.cast (s j₀) + 1) < u := by
      have hz : Tendsto (fun j : ℕ => (1 : ℝ) / (Nat.cast (s j) + 1)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hs_mono.tendsto_atTop).congr fun _ => rfl
      exact (hz.eventually (gt_mem_nhds hu_pos)).exists
    obtain ⟨j₀, hj₀⟩ := hex_j
    have hev0 : ∀ᶠ j : ℕ in atTop, V (s j) u = 0 := by
      filter_upwards [eventually_ge_atTop j₀] with j hj
      have hle : (1 : ℝ) / (Nat.cast (s j) + 1) ≤ (1 : ℝ) / (Nat.cast (s j₀) + 1) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity)
          (by exact_mod_cast Nat.add_le_add_right (hs_mono.monotone hj) 1)
      exact hV_supp_k (s j) u (hle.trans_lt hj₀)
    exact tendsto_nhds_unique hu_lim (tendsto_const_nhds.congr' (hev0.mono fun _ h => h.symm))
  have hF8_pair : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u))) ∧
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ≤ M₈ := by
    let w : ℝ → ℝ := fun u => Real.exp (-(4 * u))
    have hwc : Continuous w := by fun_prop
    have hsq : ∀ (a u : ℝ), (w u * a) ^ 2 = a ^ 2 * Real.exp (-(8 * u)) := fun a u => by
      dsimp only [w]
      rw [mul_pow, ← Real.exp_nat_mul, mul_comm]
      congr 2; push_cast; ring
    have hVw : ∀ j : ℕ, MemLp (fun u => w u * V (s j) u) 2 (volume : Measure ℝ) := fun j =>
      (hwc.mul (hVd (s j)).continuous).memLp_of_hasCompactSupport (hVc (s j)).mul_left
    have hae_w : ∀ᵐ u, Tendsto (fun j => w u * V (s j) u) atTop (𝓝 (w u * F u)) := by
      filter_upwards [hφ₃_ae] with u hu
      exact hu.const_mul _
    obtain ⟨hmem_w, hbd_w⟩ := integral_sq_le_of_eLpNorm_two_le
      (hwc.aestronglyMeasurable.mul hFm.aestronglyMeasurable) hM₈_pos.le
      (Lp.eLpNorm_le_of_ae_tendsto
        (Eventually.of_forall fun j =>
          eLpNorm_two_le_of_integral_sq_le (hVw j) (by simpa only [hsq] using hV_M₈ (s j)))
        (fun j => (hVw j).aestronglyMeasurable) hae_w)
    exact ⟨by simpa only [Pi.mul_apply, hsq] using hmem_w.integrable_sq,
      by simpa only [Pi.mul_apply, hsq] using hbd_w⟩
  set F₀ : ℝ → ℝ := (Set.Iio (0 : ℝ)).indicator F
  have hF₀m : Measurable F₀ := hFm.indicator measurableSet_Iio
  have hF₀_zero : ∀ u, 0 ≤ u → F₀ u = 0 := fun u hu =>
    Set.indicator_of_notMem (show u ∉ Set.Iio (0 : ℝ) by simp [hu]) F
  have hF₀_ae : F₀ =ᵐ[volume] F := by
    have hnot0 : ∀ᵐ u : ℝ, u ≠ 0 := by
      rw [ae_iff]
      have hset : {u : ℝ | ¬ u ≠ 0} = ({0} : Set ℝ) := by ext u; simp
      rw [hset]
      exact measure_singleton (0 : ℝ)
    filter_upwards [hF_pos_ae, hnot0] with u hu_pos hne
    rcases lt_trichotomy u 0 with hlt | rfl | hgt
    · exact Set.indicator_of_mem (show u ∈ Set.Iio (0 : ℝ) from hlt) F
    · exact absurd rfl hne
    · dsimp only [F₀]
      rw [Set.indicator_of_notMem (show u ∉ Set.Iio (0 : ℝ) by simp [hgt.le]), hu_pos hgt]
  have hF₀2 : Integrable fun u => F₀ u ^ 2 :=
    hF_mem.integrable_sq.congr (hF₀_ae.symm.mono fun _ h => by dsimp only; rw [h])
  have hF₀_norm : (∫ u, F₀ u ^ 2) = 1 := by
    rw [integral_congr_ae (hF₀_ae.mono fun _ h => by rw [h]), hF_norm]
  have hF₀8 : Integrable fun u => F₀ u ^ 2 * Real.exp (-(8 * u)) :=
    hF8_pair.1.congr (hF₀_ae.symm.mono fun _ h => by dsimp only; rw [h])
  have hF₀8_le : (∫ u, F₀ u ^ 2 * Real.exp (-(8 * u))) ≤ M₈ := by
    rw [integral_congr_ae (hF₀_ae.mono fun _ h => by rw [h])]
    exact hF8_pair.2
  have hs_L2_F₀ : Tendsto (fun j : ℕ => ∫ u, (V (s j) u - F₀ u) ^ 2) atTop (𝓝 0) :=
    hs_L2.congr fun j => integral_congr_ae (hF₀_ae.symm.mono fun _ h => by rw [h])
  obtain ⟨hF₀i, hL1_sub⟩ := integrable_and_tendsto_L1_of_L2_and_exp8
    (fun j => hVd (s j)) (fun j => hVc (s j)) (fun j => hV_supp1 (s j))
    hM₈_pos.le (fun j => hV_M₈ (s j)) hF₀m hF₀2 hF₀8 hF₀8_le
    (Eventually.of_forall fun u hu => hF₀_zero u (zero_lt_one.trans hu).le) hs_L2_F₀
  let N_sub : ℕ → ℕ := fun j => N_seq (s j)
  have hN_sub : StrictMono N_sub := hN_strict.comp hs_mono
  letI : DecidablePred (fun N : ℕ => ∃ j : ℕ, N_sub j = N) := Classical.decPred _
  let c_full : ℕ → ℝ := fun N =>
    if h : ∃ j : ℕ, N_sub j = N then c_seq (s (Classical.choose h)) else localCriticalCurve R_lim N
  let x_full : ℕ → ℕ → ℝ := fun N =>
    if h : ∃ j : ℕ, N_sub j = N then y_norm (s (Classical.choose h)) else 0
  have hc_full_sub : ∀ j : ℕ, c_full (N_sub j) = c_seq (s j) := by
    intro j
    have hex : ∃ i : ℕ, N_sub i = N_sub j := ⟨j, rfl⟩
    have hch : Classical.choose hex = j := hN_sub.injective (Classical.choose_spec hex)
    dsimp only [c_full]
    rw [dif_pos hex, hch]
  have hx_full_sub : ∀ j : ℕ, x_full (N_sub j) = y_norm (s j) := by
    intro j
    have hex : ∃ i : ℕ, N_sub i = N_sub j := ⟨j, rfl⟩
    have hch : Classical.choose hex = j := hN_sub.injective (Classical.choose_spec hex)
    dsimp only [x_full]
    rw [dif_pos hex, hch]
  have hU_full_sub : ∀ j : ℕ,
      normalizedCentredAtomicTest tiltedUnitSpline (x_full (N_sub j)) (c_full (N_sub j)) (N_sub j) =
        V (s j) := fun j => by
    rw [hc_full_sub j, hx_full_sub j]
  have hc1_full : ∀ N : ℕ, 1 ≤ c_full N := by
    intro N
    rcases Classical.em (∃ j : ℕ, N_sub j = N) with h | h
    · have hc_eq : c_full N = c_seq (s (Classical.choose h)) := by
        dsimp only [c_full]; rw [dif_pos h]
      rw [hc_eq]
      exact hc_seq _
    · have hc_eq : c_full N = localCriticalCurve R_lim N := by
        dsimp only [c_full]; rw [dif_neg h]
      rw [hc_eq]
      exact one_le_localCriticalCurve R_lim N
  have hmass_full : ∀ N : ℕ,
      (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x_full N) (c_full N) N u ^ 2) ≤ 1 := by
    intro N
    rcases Classical.em (∃ j : ℕ, N_sub j = N) with ⟨j, rfl⟩ | h
    · rw [hU_full_sub j, hV_norm (s j)]
    · have hx0 : x_full N = 0 := by dsimp only [x_full]; rw [dif_neg h]
      rw [hx0, normalizedCentredAtomicTest_zero]
      simp
  have hM_full : ∀ N : ℕ,
      (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x_full N) (c_full N) N u ^ 2 *
        Real.exp (-(8 * u))) ≤ M₈ := by
    intro N
    rcases Classical.em (∃ j : ℕ, N_sub j = N) with ⟨j, rfl⟩ | h
    · rw [hU_full_sub j]
      exact hV_M₈ (s j)
    · have hx0 : x_full N = 0 := by dsimp only [x_full]; rw [dif_neg h]
      rw [hx0, normalizedCentredAtomicTest_zero]
      simpa using hM₈_pos.le
  have hcrit_full : Tendsto (fun N : ℕ => c_full N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R_lim) := by
    have hsub_ratio : Tendsto (fun j : ℕ => c_seq (s j) ^ 8 / Real.log (Nat.cast (N_sub j)))
        atTop (𝓝 R_lim) :=
      hφ₁_lim.comp (hφ₂_mono.comp hφ₃_mono).tendsto_atTop
    have hloc_ratio := tendsto_localCriticalCurve_ratio hR_lim_pos
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hsub_ratio) ε hε)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hloc_ratio) ε hε)
    refine eventually_atTop.mpr ⟨max N₁ (N_sub J), fun N hN => ?_⟩
    rcases Classical.em (∃ j : ℕ, N_sub j = N) with ⟨j, rfl⟩ | h
    · rw [hc_full_sub j]
      exact hJ j (hN_sub.le_iff_le.mp ((le_max_right N₁ (N_sub J)).trans hN))
    · have hc_loc : c_full N = localCriticalCurve R_lim N := by dsimp only [c_full]; rw [dif_neg h]
      rw [hc_loc]
      exact hN₁ N ((le_max_left N₁ (N_sub J)).trans hN)
  let l : Filter ℕ := Filter.map N_sub atTop
  have hl_le : l ≤ atTop := hN_sub.tendsto_atTop
  have hL1_l : Tendsto (fun N : ℕ =>
      ∫ u, ‖normalizedCentredAtomicTest tiltedUnitSpline (x_full N) (c_full N) N u - F₀ u‖)
      l (𝓝 0) := by
    rw [Filter.tendsto_map'_iff]
    refine hL1_sub.congr fun j => ?_
    dsimp only [Function.comp_def]
    rw [hU_full_sub j]
  have hliminf : ∀ T : ℝ, Real.exp factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F₀ T + criticalAliasCoefficient Rstar *
        (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) ≤ 0 := by
    intro T hT
    have hlim_Rlim : truncatedWeilForm F₀ T + criticalAliasCoefficient R_lim *
        (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) ≤ 0 := by
      by_contra hpos_sum
      push Not at hpos_sum
      set b_half : ℝ := (truncatedWeilForm F₀ T + criticalAliasCoefficient R_lim *
        (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u)))) / 2
      have hb_pos : 0 < b_half := half_pos hpos_sum
      have hb_lt : b_half < truncatedWeilForm F₀ T + criticalAliasCoefficient R_lim *
          (∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u))) := half_lt_self hpos_sum
      have hev_gt := eventually_lt_weilQuad_of_L1_limit_full hl_le hc1_full hR_lim_pos
        hcrit_full hmass_full hM_full hF₀i hL1_l hT hb_lt
      rw [Filter.eventually_map] at hev_gt
      have hev_gt' : ∀ᶠ j : ℕ in atTop, b_half < weilQuad (V (s j)) :=
        hev_gt.mono fun j hj => by rwa [hU_full_sub j] at hj
      have hz_inv : Tendsto (fun j : ℕ => (1 : ℝ) / (Nat.cast (s j) + 1)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hs_mono.tendsto_atTop).congr fun _ => rfl
      obtain ⟨j, hj_gt, hj_lt⟩ :=
        (hev_gt'.and (hz_inv.eventually (gt_mem_nhds hb_pos))).exists
      have hwq_j := hV_wq (s j)
      linarith only [hj_gt, hj_lt, hwq_j]
    have halias_le : criticalAliasCoefficient Rstar ≤ criticalAliasCoefficient R_lim := by
      unfold criticalAliasCoefficient
      have hnum : 0 ≤ 7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne := by
        have := integral_tiltedUnitSpline_sq_pos
        have := tiltedJordanOne_pos
        positivity
      have hm_pos : 0 < (∫ u, tiltedUnitSpline u) ^ 2 :=
        sq_pos_of_ne_zero integral_tiltedUnitSpline_ne_zero
      exact div_le_div_of_nonneg_left hnum (mul_pos hm_pos hR_lim_pos)
        (mul_le_mul_of_nonneg_left hR_lim_le hm_pos.le)
    have hI₈_nn : 0 ≤ ∫ u in Set.Iio 0, F₀ u ^ 2 * Real.exp (-(8 * u)) :=
      setIntegral_nonneg measurableSet_Iio fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have hm := mul_le_mul_of_nonneg_right halias_le hI₈_nn
    linarith only [hlim_Rlim, hm]
  exact contradiction_of_limit_profile_below_windowThreshold hRstar hR_lt hR₁_win hF₀m hF₀i hF₀2
    hF₀_norm hM₈_pos.le hF₀8 hF₀8_le hF₀_zero hliminf

/-- **Every ratio below `⨅ A ≥ 0, windowThreshold A` is eventually positive definite on the
high-conductor complement `(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ`.** -/
theorem eventuallyHighConductorPosDef_of_lt_iInf_windowThreshold {Rstar : ℝ} (hRstar : 0 < Rstar)
    (hlt : (Rstar : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) :
    EventuallyHighConductorPosDef Rstar := by
  by_contra hnot_pos
  obtain ⟨R₀, hR₀, hpos_R₀⟩ := exists_pos_eventuallyCriticalPosDef
  obtain ⟨c_W, hc_W, hbridge_gen⟩ := eventually_complement_collar_weilQuad_bridge
  obtain ⟨B_far, hB_far, hbridge_ev⟩ := hbridge_gen hRstar
  let BadAt (N : ℕ) : Prop :=
    ∃ (c : ℝ) (z : EuclideanSpace ℝ (PrimeHorizonIndex N)),
      1 ≤ c ∧ c ^ 8 ≤ Rstar * Real.log (N : ℝ) ∧
        z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ ∧
        z ≠ 0 ∧ completeWeilEnergy tiltedUnitSpline c N z ≤ 0
  have hfreq_bad : ∃ᶠ N : ℕ in atTop, BadAt N := by
    rw [EventuallyHighConductorPosDef, Filter.not_eventually] at hnot_pos
    refine hnot_pos.mono fun N hN => ?_
    push Not at hN
    obtain ⟨c, hc1, hc8, z, hz, hzne, hle⟩ := hN
    exact ⟨c, z, hc1, hc8, hz, hzne, hle⟩
  let GoodAt (k N : ℕ) : Prop :=
    3 ≤ N ∧ ((k : ℝ) + 1) ≤ (N : ℝ) ∧
      ((k : ℝ) + 1) * (Rstar + 1) * Real.log (N : ℝ) ≤ (N : ℝ) ∧
      (∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R₀ * Real.log (N : ℝ) →
        ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ≠ 0 →
          0 < completeWeilEnergy tiltedUnitSpline c N z) ∧
      (∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ Rstar * Real.log (N : ℝ) →
        ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
          z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ →
          completeWeilEnergy tiltedUnitSpline c N z ≤ 0 →
          ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
            w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
            let U_w := normalizedCentredAtomicTest tiltedUnitSpline
              (atomicTailCoefficients (N / linearDefectCutoff c) (primeHorizonExtension w)) c N
            (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 ≤
                (c * B_far) * (∫ u, U_w u ^ 2) ∧
              (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) ≤
                (Rstar * B_far / c_W) * (∫ u, U_w u ^ 2) ∧
              levyEnergy U_w ≤
                (4 * (∫ u, tiltedUnitSpline u ^ 2) * B_far) * (∫ u, U_w u ^ 2) ∧
              weilQuad U_w ≤ (1 / ((k : ℝ) + 1)) * ∫ u, U_w u ^ 2)
  have hLN_zero : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hgood_ev : ∀ k : ℕ, ∀ᶠ N : ℕ in atTop, GoodAt k N := by
    intro k
    have hK_pos : 0 < ((k : ℝ) + 1) * (Rstar + 1) := by positivity
    have hev_log := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (inv_pos.mpr hK_pos))
    filter_upwards [eventually_ge_atTop (max 3 (k + 1)), hev_log, hpos_R₀,
      hbridge_ev (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))] with N hN_ge hlt_log hR₀N hbrN
    have hN3 : 3 ≤ N := (le_max_left _ _).trans hN_ge
    have hkN : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (le_max_right 3 (k + 1)).trans hN_ge
    have hN0 : (0 : ℝ) < N := by positivity
    dsimp only [Function.comp_def] at hlt_log
    have hlog_le : ((k : ℝ) + 1) * (Rstar + 1) * Real.log (N : ℝ) ≤ (N : ℝ) := by
      have hm := (div_lt_iff₀ hN0).mp hlt_log
      have hm2 := mul_lt_mul_of_pos_left hm hK_pos
      have hid : ((k : ℝ) + 1) * (Rstar + 1) * ((((k : ℝ) + 1) * (Rstar + 1))⁻¹ * (N : ℝ)) =
          (N : ℝ) := by field_simp [hK_pos.ne']
      linarith only [hm2, hid]
    exact ⟨hN3, hkN, hlog_le, hR₀N, hbrN⟩
  have hex_step : ∀ k M : ℕ, ∃ N : ℕ, M ≤ N ∧ GoodAt k N ∧ BadAt N := fun k M => by
    obtain ⟨N, hbad, hMN, hgk⟩ :=
      (hfreq_bad.and_eventually ((eventually_ge_atTop M).and (hgood_ev k))).exists
    exact ⟨N, hMN, hgk, hbad⟩
  let N_seq : ℕ → ℕ := fun k =>
    Nat.recOn k (Classical.choose (hex_step 0 3))
      (fun k' prev => Classical.choose (hex_step (k' + 1) (prev + 1)))
  have hN_step : ∀ k : ℕ, GoodAt k (N_seq k) ∧ BadAt (N_seq k) := by
    intro k
    cases k with
    | zero =>
      have hs := Classical.choose_spec (hex_step 0 3)
      exact ⟨hs.2.1, hs.2.2⟩
    | succ k' =>
      have hs := Classical.choose_spec (hex_step (k' + 1) (N_seq k' + 1))
      exact ⟨hs.2.1, hs.2.2⟩
  have hN_strict : StrictMono N_seq :=
    strictMono_nat_of_lt_succ fun k =>
      Nat.lt_of_succ_le (Classical.choose_spec (hex_step (k + 1) (N_seq k + 1))).1
  have hbad_seq : ∀ k : ℕ, BadAt (N_seq k) := fun k => (hN_step k).2
  choose c_seq z_seq hz_spec using hbad_seq
  have hN3_seq : ∀ k, 3 ≤ N_seq k := fun k => (hN_step k).1.1
  have hL_pos : ∀ k, 0 < Real.log (Nat.cast (N_seq k)) := fun k =>
    Real.log_pos (Nat.one_lt_cast.mpr (by have := hN3_seq k; omega))
  have hratio_mem : ∀ k, c_seq k ^ 8 / Real.log (Nat.cast (N_seq k)) ∈ Set.Icc R₀ Rstar := by
    intro k
    obtain ⟨hc1, hc8, _, hzne, hle0⟩ := hz_spec k
    refine ⟨?_, (div_le_iff₀ (hL_pos k)).mpr hc8⟩
    by_contra hlt_R₀
    push Not at hlt_R₀
    have hc8_R₀ : c_seq k ^ 8 ≤ R₀ * Real.log (Nat.cast (N_seq k)) :=
      ((div_lt_iff₀ (hL_pos k)).mp hlt_R₀).le
    have hpos := (hN_step k).1.2.2.2.1 hc1 hc8_R₀ hzne
    linarith only [hpos, hle0]
  have hc_width : ∀ k, c_seq k / Nat.cast (N_seq k) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨hc1, hc8, _, _, _⟩ := hz_spec k
    obtain ⟨hN3, hkN, hlog_le, _, _⟩ := (hN_step k).1
    have hN0 : (0 : ℝ) < Nat.cast (N_seq k) := Nat.cast_pos.mpr (by omega)
    have hc_le : ((k : ℝ) + 1) * c_seq k ≤ Nat.cast (N_seq k) := by
      by_cases hcL : c_seq k ≤ (Rstar + 1) * Real.log (Nat.cast (N_seq k))
      · calc ((k : ℝ) + 1) * c_seq k
            ≤ ((k : ℝ) + 1) * ((Rstar + 1) * Real.log (Nat.cast (N_seq k))) :=
              mul_le_mul_of_nonneg_left hcL (by positivity)
          _ = ((k : ℝ) + 1) * (Rstar + 1) * Real.log (Nat.cast (N_seq k)) := (mul_assoc _ _ _).symm
          _ ≤ Nat.cast (N_seq k) := hlog_le
      · push Not at hcL
        have hc8_gt : (Rstar + 1) * Real.log (Nat.cast (N_seq k)) < c_seq k ^ 8 :=
          hcL.trans_le (le_self_pow₀ hc1 (by norm_num))
        linarith only [hc8_gt, hc8, hL_pos k]
    rw [div_le_div_iff₀ hN0 (by positivity)]
    linarith only [hc_le]
  have hbr_k : ∀ k : ℕ, ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex (N_seq k)),
      let U_w := normalizedCentredAtomicTest tiltedUnitSpline
        (atomicTailCoefficients (N_seq k / linearDefectCutoff (c_seq k)) (primeHorizonExtension w))
        (c_seq k) (N_seq k)
      (tiltedSplineSpectralFloorConstant + 2) * ‖z_seq k‖ ^ 2 ≤
          (c_seq k * B_far) * (∫ u, U_w u ^ 2) ∧
        (∫ u, U_w u ^ 2 * Real.exp (-(8 * u))) ≤
          (Rstar * B_far / c_W) * (∫ u, U_w u ^ 2) ∧
        weilQuad U_w ≤ (1 / ((k : ℝ) + 1)) * ∫ u, U_w u ^ 2 := by
    intro k
    obtain ⟨hc1, hc8, hz_orth, _, hle0⟩ := hz_spec k
    obtain ⟨w, _, hb1, hb2, _, hb4⟩ := (hN_step k).1.2.2.2.2 hc1 hc8 hz_orth hle0
    exact ⟨w, hb1, hb2, hb4⟩
  let w_seq : ∀ k : ℕ, EuclideanSpace ℝ (PrimeHorizonIndex (N_seq k)) :=
    fun k => Classical.choose (hbr_k k)
  let y_raw : ℕ → ℕ → ℝ := fun k =>
    atomicTailCoefficients (N_seq k / linearDefectCutoff (c_seq k)) (primeHorizonExtension (w_seq k))
  let U_raw : ℕ → ℝ → ℝ := fun k =>
    normalizedCentredAtomicTest tiltedUnitSpline (y_raw k) (c_seq k) (N_seq k)
  have hU_raw_pos : ∀ k, 0 < ∫ u, U_raw k u ^ 2 := by
    intro k
    obtain ⟨hb1, _, _⟩ := Classical.choose_spec (hbr_k k)
    obtain ⟨hc1, _, _, hzne, _⟩ := hz_spec k
    have hzl : 0 < (tiltedSplineSpectralFloorConstant + 2) * ‖z_seq k‖ ^ 2 :=
      mul_pos (by have := tiltedSplineSpectralFloorConstant_pos; positivity)
        (sq_pos_of_pos (norm_pos_iff.mpr hzne))
    have hcf : 0 < c_seq k * B_far := mul_pos (zero_lt_one.trans_le hc1) hB_far
    by_contra hle
    push Not at hle
    have hle' : (c_seq k * B_far) * (∫ u, U_raw k u ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcf.le hle
    linarith only [hzl, hb1, hle']
  let ν : ℕ → ℝ := fun k => Real.sqrt (∫ u, U_raw k u ^ 2)
  have hν_pos : ∀ k, 0 < ν k := fun k => Real.sqrt_pos.mpr (hU_raw_pos k)
  have hν_sq : ∀ k, ν k ^ 2 = ∫ u, U_raw k u ^ 2 := fun k => Real.sq_sqrt (hU_raw_pos k).le
  let y_norm : ℕ → ℕ → ℝ := fun k n => (ν k)⁻¹ * y_raw k n
  let V : ℕ → ℝ → ℝ := fun k =>
    normalizedCentredAtomicTest tiltedUnitSpline (y_norm k) (c_seq k) (N_seq k)
  have hV_eq : ∀ k, V k = fun u => (ν k)⁻¹ * U_raw k u := fun k =>
    normalizedCentredAtomicTest_const_mul (ν k)⁻¹ (y_raw k) (c_seq k) (N_seq k)
  have hUd : ∀ k, ContDiff ℝ 2 (U_raw k) := fun k =>
    contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline _ _ _)
  have hUc : ∀ k, HasCompactSupport (U_raw k) := fun k =>
    (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero (y_raw k)
      (zero_lt_one.trans_le (hz_spec k).1) (by have := hN3_seq k; omega)).mul_left
  have hV_norm : ∀ k, (∫ u, V k u ^ 2) = 1 := by
    intro k
    rw [hV_eq k]
    simp_rw [mul_pow]
    rw [integral_const_mul, inv_pow, ← hν_sq k, inv_mul_cancel₀ (pow_ne_zero 2 (hν_pos k).ne')]
  set M₈ : ℝ := Rstar * B_far / c_W
  have hM₈_pos : 0 < M₈ := by dsimp only [M₈]; positivity
  have hV_M₈ : ∀ k, (∫ u, V k u ^ 2 * Real.exp (-(8 * u))) ≤ M₈ := by
    intro k
    obtain ⟨_, hb2, _⟩ := Classical.choose_spec (hbr_k k)
    have heq : (∫ u, V k u ^ 2 * Real.exp (-(8 * u))) =
        (ν k)⁻¹ ^ 2 * ∫ u, U_raw k u ^ 2 * Real.exp (-(8 * u)) := by
      rw [hV_eq k, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun u => by dsimp only; ring)
    rw [heq]
    have hm := mul_le_mul_of_nonneg_left hb2 (sq_nonneg (ν k)⁻¹)
    have hid : (ν k)⁻¹ ^ 2 * (M₈ * ∫ u, U_raw k u ^ 2) = M₈ := by
      have hne : (∫ u, U_raw k u ^ 2) ≠ 0 := (hU_raw_pos k).ne'
      rw [inv_pow, hν_sq k, mul_comm M₈, inv_mul_cancel_left₀ hne]
    linarith only [hm, hid]
  have hV_wq : ∀ (k : ℕ), weilQuad (V k) ≤ 1 / (Nat.cast k + 1) := by
    intro k
    obtain ⟨_, _, hb3⟩ := Classical.choose_spec (hbr_k k)
    rw [hV_eq k, weilQuad_const_mul (hUd k) (hUc k) (ν k)⁻¹]
    have hm := mul_le_mul_of_nonneg_left hb3 (sq_nonneg (ν k)⁻¹)
    have hid : (ν k)⁻¹ ^ 2 * ((1 / (Nat.cast k + 1)) * ∫ u, U_raw k u ^ 2) =
        1 / (Nat.cast k + 1) := by
      have hne : (∫ u, U_raw k u ^ 2) ≠ 0 := (hU_raw_pos k).ne'
      rw [inv_pow, hν_sq k, mul_comm (1 / (Nat.cast k + 1)), inv_mul_cancel_left₀ hne]
    linarith only [hm, hid]
  obtain ⟨R_lim, hR_lim_mem, φ₁, hφ₁_mono, hφ₁_lim⟩ :=
    isCompact_Icc.isSeqCompact hratio_mem
  have hR_lim_pos : 0 < R_lim := hR₀.trans_le hR_lim_mem.1
  have hR_lim_le : R_lim ≤ Rstar := hR_lim_mem.2
  have hindex : ∀ k : ℕ, k ≤ φ₁ k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (ih.trans_lt (hφ₁_mono (Nat.lt_succ_self k)))
  have hinv : ∀ k : ℕ, (1 : ℝ) / (φ₁ k + 1) ≤ 1 / (k + 1) := fun k =>
    div_le_div_of_nonneg_left zero_le_one (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (hindex k) 1)
  exact no_nonpositive_atomic_sequence_below_windowThreshold hR_lim_pos
    ((EReal.coe_le_coe_iff.mpr hR_lim_le).trans_lt hlt)
    (hN_strict.comp hφ₁_mono) (fun k => (by decide : 1 ≤ 3).trans (hN3_seq (φ₁ k)))
    (fun k => (hz_spec (φ₁ k)).1) hφ₁_lim
    (fun k => (hc_width (φ₁ k)).trans (hinv k))
    (fun k => y_norm (φ₁ k)) (fun k => hV_norm (φ₁ k)) hM₈_pos
    (fun k => hV_M₈ (φ₁ k)) (fun k => (hV_wq (φ₁ k)).trans (hinv k))

/-! ### 5. Exact high-conductor threshold identity and exponential lower bounds -/

/-- Lower bound matching `highConductorNonnegativityThreshold_le_iInf_windowThreshold`:
`⨅ A ≥ 0, windowThreshold A ≤ highConductorCriticalThreshold`. -/
theorem iInf_windowThreshold_le_highConductorCriticalThreshold :
    (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) ≤ highConductorCriticalThreshold := by
  have hpos_thr : (0 : EReal) < highConductorCriticalThreshold :=
    criticalPositivityThreshold_pos.trans_le criticalPositivityThreshold_le_highConductorCriticalThreshold
  cases hW : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) with
  | bot => exact bot_le
  | top =>
    rw [top_le_iff]
    refine (EReal.eq_top_iff_forall_lt _).mpr fun r => ?_
    set R : ℝ := max (r + 1) 1
    have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hrR : (r : EReal) < (R : EReal) :=
      EReal.coe_lt_coe_iff.mpr (by dsimp only [R]; linarith [le_max_left (r + 1) 1])
    have hlt_W : (R : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
      rw [hW]; exact EReal.coe_lt_top R
    exact hrR.trans_le
      (le_sSup ⟨R, ⟨hR, eventuallyHighConductorPosDef_of_lt_iInf_windowThreshold hR hlt_W⟩, rfl⟩)
  | coe M =>
    rcases le_or_gt M 0 with hM0 | hM0
    · exact (EReal.coe_le_coe_iff.mpr hM0).trans hpos_thr.le
    · by_contra hnot_le
      push Not at hnot_le
      cases hT : highConductorCriticalThreshold with
      | bot =>
        rw [hT] at hpos_thr
        exact not_lt_bot hpos_thr
      | top =>
        rw [hT] at hnot_le
        exact not_top_lt hnot_le
      | coe T =>
        rw [hT, EReal.coe_lt_coe_iff] at hnot_le
        rw [hT, EReal.coe_pos] at hpos_thr
        set Rstar : ℝ := (T + M) / 2
        have hRstar : 0 < Rstar := by dsimp only [Rstar]; linarith
        have hlt_W : (Rstar : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
          rw [hW, EReal.coe_lt_coe_iff]; dsimp only [Rstar]; linarith
        have hle_T : (Rstar : EReal) ≤ (T : EReal) := by
          rw [← hT]
          exact le_sSup
            ⟨Rstar, ⟨hRstar, eventuallyHighConductorPosDef_of_lt_iInf_windowThreshold hRstar hlt_W⟩,
              rfl⟩
        have hRT : Rstar ≤ T := EReal.coe_le_coe_iff.mp hle_T
        dsimp only [Rstar] at hRT
        linarith

/-- **Exact high-conductor critical threshold law (`R_c^{high}(ζ) = ⨅_{A ≥ 0} R₁(A)`).**
On the polylogarithmic high-conductor complement `(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ`, the
critical positivity threshold equals the global infimum of the continuum window thresholds. -/
theorem highConductorCriticalThreshold_eq_iInf_windowThreshold :
    highConductorCriticalThreshold = ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A :=
  le_antisymm
    (highConductorCriticalThreshold_le_highConductorNonnegativityThreshold.trans
      highConductorNonnegativityThreshold_le_iInf_windowThreshold)
    iInf_windowThreshold_le_highConductorCriticalThreshold

/-- Positivity and nonnegativity share the exact same critical threshold on the high-conductor
complement. -/
theorem highConductorNonnegativityThreshold_eq_iInf_windowThreshold :
    highConductorNonnegativityThreshold = ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A :=
  le_antisymm highConductorNonnegativityThreshold_le_iInf_windowThreshold
    (iInf_windowThreshold_le_highConductorCriticalThreshold.trans
      highConductorCriticalThreshold_le_highConductorNonnegativityThreshold)

theorem highConductorCriticalThreshold_eq_nonnegativityThreshold :
    highConductorCriticalThreshold = highConductorNonnegativityThreshold := by
  rw [highConductorCriticalThreshold_eq_iInf_windowThreshold,
    highConductorNonnegativityThreshold_eq_iInf_windowThreshold]

/-- **Exponential growth of `R_c^{high}(ζ)` in the onset aperture (`R_c^{high}(ζ) ≥ c₀ e^{6 a*(ζ)}`).**
For every `0 ≤ a` with `(a : EReal) ≤ onsetAperture zetaZeroConfig`,
`windowThresholdExponentialConstant * e^{6 a} ≤ highConductorCriticalThreshold`. -/
theorem exp_six_mul_le_highConductorCriticalThreshold {a : ℝ} (ha0 : 0 ≤ a)
    (ha : (a : EReal) ≤ onsetAperture zetaZeroConfig) :
    ((windowThresholdExponentialConstant * Real.exp (6 * a) : ℝ) : EReal) ≤
      highConductorCriticalThreshold := by
  rw [highConductorCriticalThreshold_eq_iInf_windowThreshold]
  exact iInf_windowThreshold_ge_exp_six_mul_of_le_onsetAperture ha0 ha

/-- Every positive ratio `R < windowThresholdExponentialConstant * e^{6 a}` (`(a : EReal) ≤ a*(ζ)`)
is eventually positive definite on `(conductorSubspace ⌊(log N)^{13/32}⌋₊ N)ᗮ`. -/
theorem eventuallyHighConductorPosDef_of_lt_exp_six_mul {a R : ℝ} (ha0 : 0 ≤ a)
    (ha : (a : EReal) ≤ onsetAperture zetaZeroConfig) (hR : 0 < R)
    (hlt : R < windowThresholdExponentialConstant * Real.exp (6 * a)) :
    EventuallyHighConductorPosDef R :=
  eventuallyHighConductorPosDef_of_lt_iInf_windowThreshold hR
    ((EReal.coe_lt_coe_iff.mpr hlt).trans_le
      (iInf_windowThreshold_ge_exp_six_mul_of_le_onsetAperture ha0 ha))

/-- **Logarithmic threshold inequality (`log R_c^{high}(ζ) ≥ 6 a*(ζ) + log c₀`).**
Whenever `highConductorCriticalThreshold ≠ ⊤` and `(a : EReal) ≤ onsetAperture zetaZeroConfig`
(`0 ≤ a`), `Real.log windowThresholdExponentialConstant + 6 * a ≤ Real.log highConductorCriticalThreshold.toReal`. -/
theorem log_highConductorCriticalThreshold_ge_six_mul_onsetAperture
    (htop : highConductorCriticalThreshold ≠ ⊤) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : (a : EReal) ≤ onsetAperture zetaZeroConfig) :
    Real.log windowThresholdExponentialConstant + 6 * a ≤
      Real.log highConductorCriticalThreshold.toReal := by
  have hpos_thr : (0 : EReal) < highConductorCriticalThreshold :=
    criticalPositivityThreshold_pos.trans_le criticalPositivityThreshold_le_highConductorCriticalThreshold
  have hexp_le := exp_six_mul_le_highConductorCriticalThreshold ha0 ha
  cases hT : highConductorCriticalThreshold with
  | bot =>
    rw [hT] at hpos_thr
    exact absurd hpos_thr not_lt_bot
  | top => exact absurd hT htop
  | coe M =>
    rw [hT, EReal.coe_le_coe_iff] at hexp_le
    simp only [EReal.toReal_coe]
    have hc₀ := windowThresholdExponentialConstant_pos
    have hlog := Real.log_le_log (mul_pos hc₀ (Real.exp_pos _)) hexp_le
    rwa [Real.log_mul hc₀.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog

/-- **Endpoint-sharp off-RH exponential lower bound on `R_c^{high}(ζ)`.** -/
theorem exp_six_mul_contact_le_highConductorCriticalThreshold_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ((windowThresholdExponentialConstant * Real.exp (6 * zetaContactAperture) : ℝ) : EReal) ≤
      highConductorCriticalThreshold := by
  rw [highConductorCriticalThreshold_eq_iInf_windowThreshold]
  exact iInf_windowThreshold_ge_exp_six_mul_contact_of_not_rh hRH

/-! ### 6. Whole-space low-conductor and top-window localization below `c₀ e^{6 a*(ζ)}` -/

/-- **Whole-space localization below `c₀ e^{6 a*(ζ)}`.**
For any `0 ≤ a` with `(a : EReal) ≤ onsetAperture zetaZeroConfig` and any ratio
`0 < R < windowThresholdExponentialConstant * e^{6 a}`, eventually every nonzero whole-space vector
`z ∈ ℝ^N` with nonpositive complete Weil energy at `1 ≤ c`, `c⁸ ≤ R log N` must simultaneously have
a nonzero projection onto the low-conductor packet `conductorSubspace ⌊(log N)^{13/32}⌋₊ N` and a
nonzero coordinate in the top logarithmic window `Ioc (N / S_R) N` of logarithmic length
`log S_R ≤ (1/8) log(R + 1) + C₀`. -/
theorem eventually_lowConductorProjection_and_topWindow_ne_zero_of_nonpos :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ {a R : ℝ}, 0 ≤ a → (a : EReal) ≤ onsetAperture zetaZeroConfig →
        0 < R → R < windowThresholdExponentialConstant * Real.exp (6 * a) →
        ∃ S_R : ℕ, 2 ≤ S_R ∧ Real.log (S_R : ℝ) ≤ (1 / 8 : ℝ) * Real.log (R + 1) + C₀ ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R * Real.log (N : ℝ) →
              ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
                z ≠ 0 → completeWeilEnergy tiltedUnitSpline c N z ≤ 0 →
                  (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N).starProjection z ≠ 0 ∧
                    ∃ n ∈ Finset.Ioc (N / S_R) N, primeHorizonExtension z n ≠ 0 := by
  obtain ⟨C₀, hC₀, hwin⟩ := eventually_nonpos_completeWeilEnergy_not_escape_log_window
  refine ⟨C₀, hC₀, fun {a R} ha0 ha hR hlt => ?_⟩
  obtain ⟨S_R, hSR2, hSR_ub, hev_win⟩ := hwin hR
  have hev_high := eventuallyHighConductorPosDef_of_lt_exp_six_mul ha0 ha hR hlt
  refine ⟨S_R, hSR2, hSR_ub, ?_⟩
  filter_upwards [hev_high, hev_win] with N hhighN hwinN c hc1 hc8 z hzne hle0
  refine ⟨?_, hwinN hc1 hc8 hzne hle0⟩
  intro hproj0
  have horth : z ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ := by
    simpa [hproj0] using
      Submodule.sub_starProjection_mem_orthogonal
        (K := conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N) z
  have hpos := hhighN hc1 hc8 horth hzne
  linarith only [hpos, hle0]

/-- Below `criticalNonnegativityThreshold`, the low-packet Schur / polar payment `PolarPaymentAt R A`
holds on every window `A ≥ 0`. -/
theorem polarPaymentAt_of_lt_criticalNonnegativityThreshold {R A : ℝ} (hR : 0 < R) (hA : 0 ≤ A)
    (hlt : (R : EReal) < criticalNonnegativityThreshold) :
    PolarPaymentAt R A := by
  have hnn := eventuallyCriticalNonneg_of_lt_threshold hR hlt
  refine polarPaymentAt_of_eventually_nonneg (one_le_localCriticalCurve R) hR
    (tendsto_localCriticalCurve_ratio hR) ?_ hA
  filter_upwards [hnn, eventually_localCriticalCurve_pow_eight hR] with N hN hpow z
  exact hN (one_le_localCriticalCurve R N) hpow.le z

theorem criticalNonnegativityThreshold_le_highConductorCriticalThreshold :
    criticalNonnegativityThreshold ≤ highConductorCriticalThreshold := by
  rw [highConductorCriticalThreshold_eq_nonnegativityThreshold]
  exact criticalNonnegativityThreshold_le_highConductorNonnegativityThreshold

/-! ### 7. Global equivalences with infinite onset aperture and the Riemann Hypothesis -/

theorem eventuallyCriticalPosDef_of_riemannHypothesis (hRH : RiemannHypothesis) {R : ℝ}
    (_hR : 0 < R) : EventuallyCriticalPosDef R := by
  filter_upwards [eventually_ge_atTop 1] with N hN1 c hc1 _ z hzne
  exact HodgeTheoryWithoutVarieties.completeWeilEnergy_pos_of_riemannHypothesis hRH
    EdgeHodgeTheory.admissible_tiltedUnitSpline (zero_lt_one.trans_le hc1) hN1 hzne

theorem criticalPositivityThreshold_eq_top_of_riemannHypothesis (hRH : RiemannHypothesis) :
    criticalPositivityThreshold = ⊤ := by
  refine (EReal.eq_top_iff_forall_lt _).mpr fun r => ?_
  set R : ℝ := max (r + 1) 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hrR : (r : EReal) < (R : EReal) :=
    EReal.coe_lt_coe_iff.mpr (by dsimp only [R]; linarith [le_max_left (r + 1) 1])
  exact hrR.trans_le
    (le_sSup ⟨R, ⟨hR, eventuallyCriticalPosDef_of_riemannHypothesis hRH hR⟩, rfl⟩)

theorem riemannHypothesis_of_highConductorNonnegativityThreshold_eq_top
    (htop : highConductorNonnegativityThreshold = ⊤) : RiemannHypothesis := by
  refine riemannHypothesis_iff_windowThreshold_eq_top.mpr fun A hA => top_le_iff.mp ?_
  calc (⊤ : EReal)
      = highConductorNonnegativityThreshold := htop.symm
    _ ≤ ⨅ (B : ℝ) (_ : 0 ≤ B), windowThreshold B :=
        highConductorNonnegativityThreshold_le_iInf_windowThreshold
    _ ≤ windowThreshold A := iInf_le_of_le A (iInf_le _ hA)

theorem criticalPositivityThreshold_eq_top_iff_riemannHypothesis :
    criticalPositivityThreshold = ⊤ ↔ RiemannHypothesis :=
  ⟨fun h => riemannHypothesis_of_highConductorNonnegativityThreshold_eq_top
    (top_le_iff.mp (h ▸ (criticalPositivityThreshold_le_highConductorCriticalThreshold.trans
      highConductorCriticalThreshold_le_highConductorNonnegativityThreshold))),
   criticalPositivityThreshold_eq_top_of_riemannHypothesis⟩

theorem criticalNonnegativityThreshold_eq_top_iff_riemannHypothesis :
    criticalNonnegativityThreshold = ⊤ ↔ RiemannHypothesis :=
  ⟨fun h => riemannHypothesis_of_highConductorNonnegativityThreshold_eq_top
    (top_le_iff.mp (h ▸ criticalNonnegativityThreshold_le_highConductorNonnegativityThreshold)),
   fun hRH => top_le_iff.mp
     (criticalPositivityThreshold_eq_top_of_riemannHypothesis hRH ▸
       criticalPositivityThreshold_le_criticalNonnegativityThreshold)⟩

theorem poleOrthogonalCriticalThreshold_eq_top_iff_riemannHypothesis :
    poleOrthogonalCriticalThreshold = ⊤ ↔ RiemannHypothesis :=
  ⟨fun h => riemannHypothesis_of_highConductorNonnegativityThreshold_eq_top
    (top_le_iff.mp (h ▸ (poleOrthogonalCriticalThreshold_le_highConductorCriticalThreshold.trans
      highConductorCriticalThreshold_le_highConductorNonnegativityThreshold))),
   fun hRH => top_le_iff.mp
     (criticalPositivityThreshold_eq_top_of_riemannHypothesis hRH ▸
       criticalPositivityThreshold_le_poleOrthogonalCriticalThreshold)⟩

theorem highConductorCriticalThreshold_eq_top_iff_riemannHypothesis :
    highConductorCriticalThreshold = ⊤ ↔ RiemannHypothesis :=
  ⟨fun h => riemannHypothesis_of_highConductorNonnegativityThreshold_eq_top
    (top_le_iff.mp (h ▸ highConductorCriticalThreshold_le_highConductorNonnegativityThreshold)),
   fun hRH => top_le_iff.mp
     (criticalPositivityThreshold_eq_top_of_riemannHypothesis hRH ▸
       criticalPositivityThreshold_le_highConductorCriticalThreshold)⟩

theorem highConductorNonnegativityThreshold_eq_top_iff_riemannHypothesis :
    highConductorNonnegativityThreshold = ⊤ ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_highConductorNonnegativityThreshold_eq_top,
   fun hRH => top_le_iff.mp
     (criticalPositivityThreshold_eq_top_of_riemannHypothesis hRH ▸
       (criticalPositivityThreshold_le_highConductorCriticalThreshold.trans
         highConductorCriticalThreshold_le_highConductorNonnegativityThreshold))⟩

theorem criticalPositivityThreshold_eq_top_iff_onsetAperture_eq_top :
    criticalPositivityThreshold = ⊤ ↔ onsetAperture zetaZeroConfig = ⊤ :=
  criticalPositivityThreshold_eq_top_iff_riemannHypothesis.trans
    riemannHypothesis_iff_onsetAperture_zeta_eq_top

theorem highConductorCriticalThreshold_eq_top_iff_onsetAperture_eq_top :
    highConductorCriticalThreshold = ⊤ ↔ onsetAperture zetaZeroConfig = ⊤ :=
  highConductorCriticalThreshold_eq_top_iff_riemannHypothesis.trans
    riemannHypothesis_iff_onsetAperture_zeta_eq_top

#print axioms exists_archForm_windowMollify_le_of_gammaLiminf_bound
#print axioms exists_window_sequence_of_gammaLiminf_bound
#print axioms eventually_nonpos_completeWeilEnergy_not_escape_log_window
#print axioms eventually_negative_direction_window_confinement
#print axioms iInf_windowThreshold_ge_exp_six_mul_of_le_onsetAperture
#print axioms no_nonpositive_atomic_sequence_below_windowThreshold
#print axioms highConductorCriticalThreshold_eq_iInf_windowThreshold
#print axioms exp_six_mul_le_highConductorCriticalThreshold
#print axioms log_highConductorCriticalThreshold_ge_six_mul_onsetAperture
#print axioms eventually_lowConductorProjection_and_topWindow_ne_zero_of_nonpos
#print axioms criticalPositivityThreshold_eq_top_iff_riemannHypothesis
#print axioms criticalPositivityThreshold_eq_top_iff_onsetAperture_eq_top

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
