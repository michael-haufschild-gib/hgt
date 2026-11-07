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
open scoped RealInnerProductSpace ENNReal Convolution

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
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
    Nat.le_floor (Real.one_le_rpow hL1 (by norm_num))
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

theorem eventuallyCriticalNonneg_of_lt_threshold {R : ℝ} (hR : 0 < R)
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
  have hm : 0 < ∫ u, tiltedUnitSpline u := integral_tiltedUnitSpline_pos
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
  have hm : 0 < ∫ u, tiltedUnitSpline u := integral_tiltedUnitSpline_pos
  unfold leftSplineMollifier
  rw [integral_const_mul]
  have hneg : (∫ s : ℝ, tiltedUnitSpline (-(s / δ))) = ∫ s : ℝ, tiltedUnitSpline (s / δ) := by
    simpa only [neg_div] using
      MeasureTheory.integral_neg_eq_self (fun s : ℝ => tiltedUnitSpline (s / δ))
  have hdiv := MeasureTheory.Measure.integral_comp_div tiltedUnitSpline δ
  simp only [smul_eq_mul, abs_of_pos hδ] at hdiv
  rw [hneg, hdiv, inv_mul_cancel₀ (mul_pos hδ hm).ne']

theorem norm_paperFT_leftSplineMollifier_le {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ‖paperFT (cx (leftSplineMollifier δ)) r‖ ≤ 1 := by
  refine (norm_paperFT_le (leftSplineMollifier δ) r).trans ?_
  have habs : (∫ s, ‖leftSplineMollifier δ s‖) = ∫ s, leftSplineMollifier δ s :=
    integral_congr_ae (Eventually.of_forall fun s => by
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
  have hone : (1 : ℂ) = ∫ s, cx (leftSplineMollifier δ) s := by
    unfold cx
    rw [integral_complex_ofReal, integral_leftSplineMollifier hδ, Complex.ofReal_one]
  have hsub : (1 : ℂ) - paperFT (cx (leftSplineMollifier δ)) r =
      ∫ s, cx (leftSplineMollifier δ) s * (1 - Complex.exp (Complex.I * (r : ℂ) * (s : ℂ))) := by
    rw [hone, paperFT_def, ← integral_sub hic hker]
    exact integral_congr_ae (Eventually.of_forall fun s => by ring)
  rw [hsub]
  refine (norm_integral_le_of_norm_le (hi.mul_const (|r| * δ))
    (Eventually.of_forall fun s => ?_)).trans ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
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
  exact integral_congr_ae (Eventually.of_forall fun s => by push_cast; rfl)

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
    {G : ℝ → ℝ} (hGm : Measurable G) (hG2 : Integrable fun u => G u ^ 2)
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
    rw [Real.norm_eq_abs, ← Real.rpow_natCast, Nat.cast_two, sq_abs]
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
      unfold HTGeometry.lineConvolution
      have hone : g x = ∫ s, leftSplineMollifier δ s * g x := by
        rw [integral_mul_const, integral_leftSplineMollifier hδ, one_mul]
      have hint1 := HTGeometry.integrable_kernel_mul_sq hρ_cont.aestronglyMeasurable hρ2
        hg_cont.aestronglyMeasurable hg2 x
      have hint2 := (integrable_leftSplineMollifier hδ).mul_const (g x)
      rw [hone, ← integral_sub hint1 hint2]
      exact integral_congr_ae (Eventually.of_forall fun s => by ring)
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
      exact integral_congr_ae (Eventually.of_forall fun s => by ring)
    linarith only [hsub]
  have hgF2 : Integrable fun x => (g x - F x) ^ 2 := by
    refine hFg2.congr (Eventually.of_forall fun x => by ring)
  have hgF_sq : (∫ x, (g x - F x) ^ 2) = ∫ x, (F x - g x) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
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
    rw [integral_add ((hconv_Fg_int.const_mul 3).add (hmid_int.const_mul 3)) (hgF2.const_mul 3),
      integral_add (hconv_Fg_int.const_mul 3) (hmid_int.const_mul 3),
      integral_const_mul, integral_const_mul, integral_const_mul, hgF_sq] at hm
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
    have htail_le : (∫ x in {x : ℝ | R < |x|}, W k x ^ 2) ≤
        Real.exp (-8 * R) * C_t := by
      have hm := setIntegral_mono_on hW2_int.integrableOn
        (hW8_int.const_mul (Real.exp (-8 * R))).integrableOn hmeas_abs hpt
      have htot := setIntegral_le_integral (hW8_int.const_mul (Real.exp (-8 * R)))
        (Eventually.of_forall fun _ => by positivity)
      rw [integral_const_mul] at htot
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
    have hft_Dk : ∀ r, paperFT (cx Dk) r =
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
      by_cases hy : y < a
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr (by linarith only [hy])),
          Set.indicator_of_mem hy]
        congr 1; ring
      · rw [Set.indicator_of_notMem (fun h => hy (by rw [Set.mem_Ioi] at h; linarith only [h])),
          Set.indicator_of_notMem hy]
    have hint : Integrable ((Set.Iio a).indicator fun y => Real.exp (8 * y)) :=
      hfn ▸ (hon.integrable_indicator measurableSet_Ioi).comp_neg
    refine ⟨hint, ?_⟩
    have hneg := MeasureTheory.integral_neg_eq_self
      ((Set.Ioi (-a)).indicator fun x : ℝ => Real.exp (-8 * x))
    rw [hfn] at hneg
    rw [← hneg, MeasureTheory.integral_indicator measurableSet_Ioi,
      integral_exp_mul_Ioi (by norm_num : (-8 : ℝ) < 0) (-a)]
    ring
  have hexp4_sq : ∀ (a y : ℝ),
      ((Set.Iio a).indicator (fun t => Real.exp (4 * t)) y) ^ 2 =
        (Set.Iio a).indicator (fun t => Real.exp (8 * t)) y := by
    intro a y
    by_cases hy : y < a
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
    by_cases hy2 : y < 2
    · dsimp only [g₁, g₂]
      rw [Set.indicator_of_mem hy2, Real.norm_eq_abs, mul_assoc, ← Real.exp_add,
        show -(4 * y) + 4 * y = 0 by ring, Real.exp_zero, mul_one]
    · push Not at hy2
      rw [hy1 (by linarith only [hy2]), norm_zero]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y)
  refine ⟨hFi, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C_tail : ℝ := (4 * M₈ + 1) / 8
  have hCt_pos : 0 < C_tail := by positivity
  set Y : ℝ := max 1 (Real.log (C_tail / (ε / 2) ^ 2) / 8 + 1)
  have hY1 : 1 ≤ Y := le_max_left _ _
  have hY_log : Real.log (C_tail / (ε / 2) ^ 2) / 8 + 1 ≤ Y := le_max_right _ _
  have htail_exp : C_tail * Real.exp (-8 * Y) ≤ (ε / 2) ^ 2 := by
    have h1 : -8 * Y ≤ -Real.log (C_tail / (ε / 2) ^ 2) := by linarith only [hY_log]
    have h2 : Real.exp (-8 * Y) ≤ (ε / 2) ^ 2 / C_tail := by
      calc Real.exp (-8 * Y)
          ≤ Real.exp (-Real.log (C_tail / (ε / 2) ^ 2)) := Real.exp_le_exp.mpr h1
        _ = (C_tail / (ε / 2) ^ 2)⁻¹ := by
            rw [Real.exp_neg, Real.exp_log (div_pos hCt_pos (by positivity))]
        _ = (ε / 2) ^ 2 / C_tail := inv_div _ _
    exact (mul_le_mul_of_nonneg_left h2 hCt_pos.le).trans_eq (mul_div_cancel₀ _ hCt_pos.ne')
  set η_mid : ℝ := (ε / 2) ^ 2 / (Y + 2)
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
  have hdi : Integrable d := by
    simpa only [d, Real.norm_eq_abs] using (hVj_i.sub hFi).norm
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
    rw [integral_add (hVj8.const_mul 2) (hF8.const_mul 2), integral_const_mul,
      integral_const_mul] at hm
    linarith only [hm, hM₈ j, hF8_le]
  have hmid_le : (∫ y, (Set.Icc (-Y) 1).indicator d y) ≤ ε / 2 := by
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
    have hsq_le : (∫ y, (Set.Icc (-Y) 1).indicator d y) ^ 2 ≤ (ε / 2) ^ 2 := by
      have hm := (mul_le_mul_of_nonneg_left hj_L2.le (by linarith only [hY1] : 0 ≤ Y + 1)).trans
        (mul_le_mul_of_nonneg_right (by linarith : Y + 1 ≤ Y + 2) hη_mid.le)
      have hid : (Y + 2) * η_mid = (ε / 2) ^ 2 := by
        dsimp only [η_mid]; field_simp [(by linarith only [hY1] : Y + 2 ≠ 0)]
      linarith only [hcs, hm, hid]
    have hnn := integral_nonneg fun y =>
      Set.indicator_nonneg (fun _ _ => abs_nonneg _) y
    nlinarith only [hsq_le, hnn, hε]
  have htail_le : (∫ y, (Set.Iio (-Y)).indicator d y) ≤ ε / 2 := by
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
      by_cases hy : y < -Y
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_assoc, ← Real.exp_add,
          show -(4 * y) + 4 * y = 0 by ring, Real.exp_zero, mul_one]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
    rw [hmul_eq, hg₁2_eq, hg₂2_eq] at hcs
    have hsq_le : (∫ y, (Set.Iio (-Y)).indicator d y) ^ 2 ≤ (ε / 2) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right
        (hd8_le.trans (by linarith : 4 * M₈ ≤ 4 * M₈ + 1))
        (by positivity : 0 ≤ (1 / 8 : ℝ) * Real.exp (-8 * Y))
      have hid : (4 * M₈ + 1) * ((1 / 8 : ℝ) * Real.exp (-8 * Y)) = C_tail * Real.exp (-8 * Y) := by
        dsimp only [C_tail]; ring
      linarith only [hcs, hm, hid, htail_exp]
    have hnn := integral_nonneg fun y =>
      Set.indicator_nonneg (fun _ _ => abs_nonneg _) y
    nlinarith only [hsq_le, hnn, hε]
  have hsplit_ae : d =ᵐ[volume]
      fun y => (Set.Iio (-Y)).indicator d y + (Set.Icc (-Y) 1).indicator d y := by
    filter_upwards [hF_supp1] with y hyF
    rcases lt_or_ge y (-Y) with hy1 | hy1
    · rw [Set.indicator_of_mem hy1,
        Set.indicator_of_notMem (fun h => not_le.mpr hy1 h.1), add_zero]
    · rcases le_or_gt y 1 with hy2 | hy2
      · rw [Set.indicator_of_notMem (not_lt.mpr hy1),
          Set.indicator_of_mem ⟨hy1, hy2⟩, zero_add]
      · dsimp only [d]
        rw [hsupp1 j y hy2, hyF hy2, sub_self, abs_zero,
          Set.indicator_of_notMem (not_lt.mpr (hy1.trans (by linarith only [hY1, hy2]))),
          Set.indicator_of_notMem (fun h => not_le.mpr hy2 h.2), add_zero]
  have hi_tail : Integrable ((Set.Iio (-Y)).indicator d) := hdi.indicator measurableSet_Iio
  have hi_mid : Integrable ((Set.Icc (-Y) 1).indicator d) := hdi.indicator measurableSet_Icc
  have htot : (∫ y, ‖V j y - F y‖) ≤ ε := by
    have heq : (∫ y, ‖V j y - F y‖) =
        (∫ y, (Set.Iio (-Y)).indicator d y) + ∫ y, (Set.Icc (-Y) 1).indicator d y := by
      have h1 : (∫ y, ‖V j y - F y‖) = ∫ y, d y :=
        integral_congr_ae (Eventually.of_forall fun _ => Real.norm_eq_abs _)
      rw [h1, integral_congr_ae hsplit_ae, integral_add hi_tail hi_mid]
    linarith only [heq, htail_le, hmid_le]
  have h0 : 0 ≤ ∫ y, ‖V j y - F y‖ := integral_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith only [htot, hε, (show ε ≤ ε by rfl)]

