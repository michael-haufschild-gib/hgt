import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.BiScaleUncertainty.DiscrepancyTransformLaw
import GaloisForLFunctions.BiScaleUncertainty.CompactFiniteJumpWeilFormula
import GaloisForLFunctions.BiScaleUncertainty.BandSpectrumZeroWidthLaw
import GaloisForLFunctions.BiScaleUncertainty.PairingRecurrenceLaw
import GaloisForLFunctions.BiScaleUncertainty.KreinIncrementAndChordCascade
import GaloisForLFunctions.BiScaleUncertainty.ProbeResolutionLaw
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampFullWeilSmoothingLimit
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge

/-!
# The zero width bounds the Weil floor in the energy normalisation

A floor for the Weil functional at aperture `A` is a lower bound for `Ẑ(F)` in terms of
the test's mass `autocorr F 0 = ∫F²`.  In that normalisation the implication *width `≤ σ`
⟹ floor at rate `2σ`* needs to control how the off-line zeros sit in a single window,
because the zero side of the explicit formula is a sum over zeros whose local density is
the only thing bounding it.

The prime side needs no such input.  The signed prime–polar pairing of an autocorrelation
is a Stieltjes integral against the normalised Chebyshev error `Ẽ`, whose size is exactly
the width, and the only test datum it costs is the sup of the gauge derivative
`a' − a/2` of the autocorrelation.  Normalising the floor by that datum — an `H¹`-type
quantity — therefore turns the arrow into an unconditional theorem:

`zetaZeroWidth < β` implies `Ẑ(F) ≥ −C (1+A) e^{2βA} (∫F² + D)` for every `C²_c` test
supported in `[−A,A]` whose autocorrelation has gauge derivative bounded by `D`.

No hypothesis on the distribution of the zeros appears.  The two inputs are the exact
Gamma–Lévy form of the Weil functional (the Lévy energy is dropped, being nonnegative)
and generalised von Koch in the Chebyshev gauge.
-/

open MeasureTheory Set
open scoped CompactlySupported

namespace GaloisForLFunctions.SquareRootThreshold

open RHTower.ArchimedeanAnomaly BiScaleUncertainty BiScaleUncertainty.SignedPrimePolar
  BiScaleUncertainty.ChebyshevGauge ArithmeticCriticalityTheory ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-! ## A gauge cutoff beyond the aperture -/

/-- A cutoff index whose gauge length `log(N+2)` exceeds the autocorrelation aperture `2A`. -/
private def gaugeIndex (A : ℝ) : ℕ := ⌈Real.exp (2 * A)⌉₊ + 1

private theorem two_mul_lt_cutoff_gaugeIndex (A : ℝ) : 2 * A < cutoff (gaugeIndex A) := by
  have hc : Real.exp (2 * A) ≤ (⌈Real.exp (2 * A)⌉₊ : ℝ) := Nat.le_ceil _
  have hlt : Real.exp (2 * A) < ((gaugeIndex A + 2 : ℕ) : ℝ) := by
    have : ((gaugeIndex A + 2 : ℕ) : ℝ) = (⌈Real.exp (2 * A)⌉₊ : ℝ) + 3 := by
      simp [gaugeIndex]; ring
    rw [this]; linarith
  have hcut : cutoff (gaugeIndex A) = Real.log ((gaugeIndex A + 2 : ℕ) : ℝ) := rfl
  have := Real.log_lt_log (Real.exp_pos _) hlt
  rw [Real.log_exp] at this
  rw [hcut]; exact this

private theorem cutoff_gaugeIndex_le (A : ℝ) (hA : 0 ≤ A) :
    cutoff (gaugeIndex A) ≤ 2 * A + 4 := by
  have h1 : Real.exp 1 ≤ Real.exp (2 * A + 1) := by
    apply Real.exp_le_exp.mpr; linarith
  have hc : (⌈Real.exp (2 * A)⌉₊ : ℝ) < Real.exp (2 * A) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hE1 : (1 : ℝ) ≤ Real.exp (2 * A) := Real.one_le_exp (by linarith)
  have hle : ((gaugeIndex A + 2 : ℕ) : ℝ) ≤ Real.exp (2 * A + 4) := by
    have hcast : ((gaugeIndex A + 2 : ℕ) : ℝ) = (⌈Real.exp (2 * A)⌉₊ : ℝ) + 3 := by
      simp [gaugeIndex]; ring
    have hgrow : Real.exp (2 * A) * Real.exp 4 ≤ Real.exp (2 * A + 4) := by
      rw [← Real.exp_add]
    have h4 : (5 : ℝ) ≤ Real.exp 4 := by
      have : (5 : ℝ) ≤ Real.exp 2 := by
        have h2 : Real.exp 1 * Real.exp 1 ≤ Real.exp 2 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_gt_d9]
      have hmono : Real.exp 2 ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
      linarith
    rw [hcast]
    nlinarith [Real.exp_pos (2 * A)]
  have hpos : (0 : ℝ) < ((gaugeIndex A + 2 : ℕ) : ℝ) := by positivity
  have hcut : cutoff (gaugeIndex A) = Real.log ((gaugeIndex A + 2 : ℕ) : ℝ) := rfl
  have := Real.log_le_log hpos hle
  rw [Real.log_exp] at this
  rw [hcut]; exact this

/-! ## The Chebyshev-gauge bound for the pairing of an autocorrelation -/

/-- **The prime side costs one gauge derivative.**  For a `C²_c` test supported in
`[−A,A]`, the signed prime–polar pairing of its autocorrelation is bounded by the test
mass and the sup `D` of the gauge derivative of the autocorrelation, weighted by the size
of the normalised Chebyshev error on `[0, 2A+4]`.  The mechanism is the Stieltjes form of
the pairing: no zero-side sum, hence no local density of zeros, enters. -/
private theorem abs_fullPairing_autocorr_le {A C₀ β D : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hC₀ : 0 ≤ C₀)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hsupp : ∀ x : ℝ, A < |x| → F x = 0)
    (hE : ∀ t : ℝ, 0 ≤ t → |normalizedLogError t| ≤ C₀ * Real.exp (β * t))
    (hD : ∀ t : ℝ, |gaugeDerivative (autocorr F) t| ≤ D) :
    |fullPairing (autocorr F)| ≤
      (2 * A + 5) * autocorr F 0 + (2 * A + 4) * (C₀ * Real.exp (β * (2 * A + 4)) * D) := by
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0)
  have ha0 : 0 ≤ autocorr F 0 := RHTower.ArchimedeanAnomaly.autocorr_zero_nonneg F
  set N := gaugeIndex A with hN
  set L := cutoff N with hL
  have hLlt : 2 * A < L := two_mul_lt_cutoff_gaugeIndex A
  have hLle : L ≤ 2 * A + 4 := cutoff_gaugeIndex_le A hA
  have hL0 : 0 ≤ L := by linarith
  -- the autocorrelation vanishes from the gauge length on
  have hazero : ∀ x : ℝ, L ≤ x → autocorr F x = 0 := by
    intro x hx
    refine autocorr_eq_zero_of_far hsupp ?_
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x)]
    linarith
  have haC1 : ContDiff ℝ 1 (autocorr F) :=
    (contDiff_autocorr hF hFc).of_le (by norm_num)
  have hac : Continuous (autocorr F) := haC1.continuous
  -- Stieltjes form of the pairing, with the boundary value killed by the support
  have htrans : fullPairing (autocorr F) = pairing N (autocorr F) :=
    fullPairing_eq_pairing_of_tail _ N hazero
  have hstielt := pairing_eq_stieltjes_gauge (autocorr F) haC1 N
  rw [hazero L le_rfl, mul_zero, add_zero] at hstielt
  -- the gauge integral: `|Ẽ| ≤ C₀ e^{βL}` and `|a' − a/2| ≤ D`
  have hI1 : |∫ t in Icc 0 L, normalizedLogError t * gaugeDerivative (autocorr F) t| ≤
      (C₀ * Real.exp (β * (2 * A + 4)) * D) * L := by
    have hbd : ∀ t ∈ Icc (0:ℝ) L,
        ‖normalizedLogError t * gaugeDerivative (autocorr F) t‖ ≤
          C₀ * Real.exp (β * (2 * A + 4)) * D := by
      intro t ht
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |normalizedLogError t| ≤ C₀ * Real.exp (β * (2 * A + 4)) := by
        refine (hE t ht.1).trans ?_
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith [ht.2])) hC₀
      have h2 : |gaugeDerivative (autocorr F) t| ≤ D := hD t
      calc |normalizedLogError t| * |gaugeDerivative (autocorr F) t|
          ≤ (C₀ * Real.exp (β * (2 * A + 4))) * D :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = C₀ * Real.exp (β * (2 * A + 4)) * D := by ring
    have := norm_setIntegral_le_of_norm_le_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hbd
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have hvol : (volume.real (Icc (0:ℝ) L)) = L := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
    rw [hvol]
  -- the polar integral: the weight is at most one and `|a| ≤ a(0)`
  have hI2 : |∫ t in Icc 0 L, Real.exp (-t / 2) * autocorr F t| ≤ autocorr F 0 * L := by
    have hbd : ∀ t ∈ Icc (0:ℝ) L,
        ‖Real.exp (-t / 2) * autocorr F t‖ ≤ autocorr F 0 := by
      intro t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
      have h2 : |autocorr F t| ≤ autocorr F 0 := abs_autocorr_le_zero hFc hF.continuous t
      calc Real.exp (-t / 2) * |autocorr F t| ≤ 1 * |autocorr F t| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ autocorr F 0 := by rw [one_mul]; exact h2
    have := norm_setIntegral_le_of_norm_le_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hbd
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have hvol : (volume.real (Icc (0:ℝ) L)) = L := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
    rw [hvol]
  rw [htrans, hstielt]
  have hLexp : (0:ℝ) ≤ C₀ * Real.exp (β * (2 * A + 4)) * D := by positivity
  calc |autocorr F 0 - (∫ t in Icc 0 L, normalizedLogError t * gaugeDerivative (autocorr F) t)
          - ∫ t in Icc 0 L, Real.exp (-t / 2) * autocorr F t|
      ≤ |autocorr F 0| +
          |∫ t in Icc 0 L, normalizedLogError t * gaugeDerivative (autocorr F) t| +
          |∫ t in Icc 0 L, Real.exp (-t / 2) * autocorr F t| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ autocorr F 0 + (C₀ * Real.exp (β * (2 * A + 4)) * D) * L + autocorr F 0 * L := by
        rw [abs_of_nonneg ha0]; gcongr
    _ ≤ (2 * A + 5) * autocorr F 0 +
          (2 * A + 4) * (C₀ * Real.exp (β * (2 * A + 4)) * D) := by
        have h1 : (C₀ * Real.exp (β * (2 * A + 4)) * D) * L ≤
            (2 * A + 4) * (C₀ * Real.exp (β * (2 * A + 4)) * D) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right hLle hLexp
        have h2 : autocorr F 0 * L ≤ (2 * A + 4) * autocorr F 0 := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right hLle ha0
        nlinarith

/-! ## The unconditional arrow from the width to the floor -/

/-- **The width bounds the energy-normalised Weil floor, unconditionally.**  For every
`β` above the zero width there is a constant `C` with

`Ẑ(F) ≥ −C (1+A) e^{2βA} (∫F² + D)`

for every `C²_c` test `F` supported in `[−A,A]` whose autocorrelation has gauge derivative
bounded by `D`.  No hypothesis on the local distribution of the off-line zeros is used:
the prime side is read through the Chebyshev gauge, where the width is the whole input. -/
theorem exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt {β : ℝ} (hβ : zetaZeroWidth < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x : ℝ, A < |x| → F x = 0) → ∀ D : ℝ,
      (∀ t : ℝ, |gaugeDerivative (autocorr F) t| ≤ D) →
      -(C * (1 + A) * Real.exp (2 * β * A) * ((∫ x, F x ^ 2) + D)) ≤ fullZeroForm F := by
  have hβ0 : 0 ≤ β := le_trans zetaZeroWidth_nonneg hβ.le
  obtain ⟨C₀, hC₀, hE⟩ :=
    exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound zetaZeroWidth_nonneg hβ
      xiZeroHalfPlaneBound_zetaZeroWidth
  refine ⟨(|Zeta23.EF.gammaBracket 0| + 10 + 8 * C₀) * Real.exp (4 * β), by positivity, ?_⟩
  intro A hA F hF hFc hsupp D hD
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0)
  have ha0 : 0 ≤ autocorr F 0 := RHTower.ArchimedeanAnomaly.autocorr_zero_nonneg F
  have hmass : autocorr F 0 = ∫ x, F x ^ 2 := RHTower.AutocorrelationKrein.autocorr_zero_eq F
  -- the exact Gamma–Lévy form of the Weil functional, with the Lévy energy dropped
  have hJ : IntegrableOn (fun x => (autocorr F 0 - autocorr F x) * archLevySinhWeight x)
      (Ioi 0) := integrableOn_biScaleLevyIntegrand hF hFc
  have hform : fullZeroForm F =
      Zeta23.EF.gammaBracket 0 * autocorr F 0 + biScaleLevyEnergy F
        - 2 * fullPairing (autocorr F) := by
    rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc]
    exact re_weilFullFunctional_eq_of_compact_finite_jump ⟨⟨F, hF.continuous⟩, hFc⟩ hJ
  have hlevy : 0 ≤ biScaleLevyEnergy F := biScaleLevyEnergy_nonneg hFc hF.continuous
  -- the pairing bound in the Chebyshev gauge
  have hpair := abs_fullPairing_autocorr_le hA hβ0 hC₀ hF hFc hsupp hE hD
  have hgamma : -(|Zeta23.EF.gammaBracket 0| * autocorr F 0) ≤
      Zeta23.EF.gammaBracket 0 * autocorr F 0 := by
    have := neg_abs_le (Zeta23.EF.gammaBracket 0)
    nlinarith [abs_nonneg (Zeta23.EF.gammaBracket 0)]
  have hpairle : fullPairing (autocorr F) ≤
      (2 * A + 5) * autocorr F 0 + (2 * A + 4) * (C₀ * Real.exp (β * (2 * A + 4)) * D) :=
    le_trans (le_abs_self _) hpair
  -- the exponential bookkeeping: `e^{β(2A+4)} = e^{4β} e^{2βA}`
  have hexp : Real.exp (β * (2 * A + 4)) = Real.exp (4 * β) * Real.exp (2 * β * A) := by
    rw [← Real.exp_add]; ring_nf
  have hA4 : (2 * A + 5) ≤ 5 * (1 + A) := by linarith
  have hA5 : (2 * A + 4) ≤ 4 * (1 + A) := by linarith
  have hexp1 : (1:ℝ) ≤ Real.exp (2 * β * A) := Real.one_le_exp (by positivity)
  have hexp4 : (1:ℝ) ≤ Real.exp (4 * β) := Real.one_le_exp (by positivity)
  have hepos : (0:ℝ) < Real.exp (2 * β * A) := Real.exp_pos _
  have h4pos : (0:ℝ) < Real.exp (4 * β) := Real.exp_pos _
  rw [hform, ← hmass]
  set T := (1 + A) * (Real.exp (2 * β * A) * (autocorr F 0 + D)) with hT
  have hΩ0 : 0 ≤ |Zeta23.EF.gammaBracket 0| := abs_nonneg _
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hX : 0 ≤ C₀ * (Real.exp (4 * β) * Real.exp (2 * β * A)) * D := by positivity
  -- the pairing bound with the aperture factors separated
  have hbig : 2 * fullPairing (autocorr F) ≤
      10 * ((1 + A) * autocorr F 0) +
        8 * ((1 + A) * (C₀ * (Real.exp (4 * β) * Real.exp (2 * β * A)) * D)) := by
    rw [hexp] at hpairle
    have h1 : (2 * A + 5) * autocorr F 0 ≤ 5 * ((1 + A) * autocorr F 0) := by
      have := mul_le_mul_of_nonneg_right hA4 ha0; linarith
    have h2 : (2 * A + 4) * (C₀ * (Real.exp (4 * β) * Real.exp (2 * β * A)) * D) ≤
        4 * ((1 + A) * (C₀ * (Real.exp (4 * β) * Real.exp (2 * β * A)) * D)) := by
      have := mul_le_mul_of_nonneg_right hA5 hX; linarith
    linarith
  -- three term comparisons against the single quantity `T`
  have hm : autocorr F 0 ≤ Real.exp (2 * β * A) * (autocorr F 0 + D) := by
    have h := le_mul_of_one_le_left (by linarith : (0:ℝ) ≤ autocorr F 0 + D) hexp1
    linarith
  have hmT : autocorr F 0 ≤ T := by
    rw [hT]
    have h := le_mul_of_one_le_left
      (by positivity : (0:ℝ) ≤ Real.exp (2 * β * A) * (autocorr F 0 + D))
      (by linarith : (1:ℝ) ≤ 1 + A)
    linarith
  have hAmT : (1 + A) * autocorr F 0 ≤ T := by
    rw [hT]; exact mul_le_mul_of_nonneg_left hm (by linarith)
  have hADT : (1 + A) * (Real.exp (2 * β * A) * D) ≤ T := by
    rw [hT]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le) (by linarith)
  have hTe : T ≤ Real.exp (4 * β) * T := le_mul_of_one_le_left hT0 hexp4
  have hcmp1 : |Zeta23.EF.gammaBracket 0| * autocorr F 0 ≤
      |Zeta23.EF.gammaBracket 0| * (Real.exp (4 * β) * T) :=
    mul_le_mul_of_nonneg_left (hmT.trans hTe) hΩ0
  have hcmp2 : 10 * ((1 + A) * autocorr F 0) ≤ 10 * (Real.exp (4 * β) * T) := by
    have := hAmT.trans hTe; linarith
  have hcmp3 : 8 * ((1 + A) * (C₀ * (Real.exp (4 * β) * Real.exp (2 * β * A)) * D)) ≤
      8 * (C₀ * (Real.exp (4 * β) * T)) := by
    have hfac : (1 + A) * (C₀ * (Real.exp (4 * β) * Real.exp (2 * β * A)) * D) =
        C₀ * Real.exp (4 * β) * ((1 + A) * (Real.exp (2 * β * A) * D)) := by ring
    have hmono : C₀ * Real.exp (4 * β) * ((1 + A) * (Real.exp (2 * β * A) * D)) ≤
        C₀ * Real.exp (4 * β) * T :=
      mul_le_mul_of_nonneg_left hADT (by positivity)
    rw [hfac]; linarith
  have hgoal : |Zeta23.EF.gammaBracket 0| * autocorr F 0 +
      (10 * ((1 + A) * autocorr F 0) +
        8 * ((1 + A) * (C₀ * (Real.exp (4 * β) * Real.exp (2 * β * A)) * D))) ≤
      (|Zeta23.EF.gammaBracket 0| + 10 + 8 * C₀) * Real.exp (4 * β) * (1 + A) *
        Real.exp (2 * β * A) * (autocorr F 0 + D) := by
    have hexpand : (|Zeta23.EF.gammaBracket 0| + 10 + 8 * C₀) * Real.exp (4 * β) * (1 + A) *
        Real.exp (2 * β * A) * (autocorr F 0 + D) =
        |Zeta23.EF.gammaBracket 0| * (Real.exp (4 * β) * T) + 10 * (Real.exp (4 * β) * T) +
          8 * (C₀ * (Real.exp (4 * β) * T)) := by rw [hT]; ring
    rw [hexpand]; linarith
  linarith [hgamma, hbig, hlevy, hgoal]

/-- **Bounded gauge oscillation discharges the clustering hypothesis.**  On any class of
tests whose autocorrelation has gauge derivative at most `K` times the mass, the floor at
rate `2β` holds for every `β` above the width, in the plain `L²` normalisation and with no
hypothesis on how the off-line zeros are distributed. -/
theorem exists_fullZeroForm_ge_neg_mass_of_zetaZeroWidth_lt {β : ℝ} (hβ : zetaZeroWidth < β)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x : ℝ, A < |x| → F x = 0) →
      (∀ t : ℝ, |gaugeDerivative (autocorr F) t| ≤ K * ∫ x, F x ^ 2) →
      -(C * (1 + A) * Real.exp (2 * β * A) * ∫ x, F x ^ 2) ≤ fullZeroForm F := by
  obtain ⟨C, hC, hfloor⟩ := exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt hβ
  refine ⟨C * (1 + K), by positivity, ?_⟩
  intro A hA F hF hFc hsupp hD
  have h := hfloor A hA F hF hFc hsupp (K * ∫ x, F x ^ 2) hD
  have heq : C * (1 + A) * Real.exp (2 * β * A) * ((∫ x, F x ^ 2) + K * ∫ x, F x ^ 2) =
      C * (1 + K) * (1 + A) * Real.exp (2 * β * A) * ∫ x, F x ^ 2 := by ring
  rw [heq] at h
  exact h

end

end GaloisForLFunctions.SquareRootThreshold
