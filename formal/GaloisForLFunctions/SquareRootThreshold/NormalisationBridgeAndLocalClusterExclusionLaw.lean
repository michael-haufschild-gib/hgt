import GaloisForLFunctions.SquareRootThreshold.TheUnconditionalWeilFloorInTheArchimedeanNormalisation
import GaloisForLFunctions.SquareRootThreshold.TheWidthBoundsTheEnergyNormalisedWeilFloor
import GaloisForLFunctions.SquareRootThreshold.UnsignedDepthSamplingDetectsLocalMass

/-!
# The Three-Normalisation Width Bridge, Aperture-Invariant Depth Sampling, and the Clustering Dichotomy

This module resolves Research Topic 8 of the Square-Root Threshold programme by unifying the three
normalisations of the width-to-floor arrow (archimedean, energy/`H¹`, and `L²`), proving that
unsigned conjugate-difference depth sampling is aperture-invariant and equivalent to local depth-mass
boundedness, and establishing the sub-exponential depth-floor closure and exponential height-escape
laws for the clustering alternative:

1. **The three normalisations of the Weil floor** (`three_normalisation_weil_floor_bridge`):
   - *Archimedean normalisation (unconditional, zero side):* At every aperture `a > 0` and `ε > 0`,
     `Re W_ζ(f, f) ≥ −C e^{(2a + ε)·zetaZeroWidth} ∫ ‖𝓕f(y)‖² log(|y| + 3) dy`
     (`exists_re_W_ge_logWeighted_rate_sharp`).
   - *Energy/`H¹` normalisation (unconditional, prime side in the Chebyshev gauge):* For every
     `β > zetaZeroWidth`, `Ẑ(F) ≥ −C (1 + A) e^{2βA} (∫ F² + D)` for every `C²_c` test supported in
     `[−A, A]` with `|gaugeDerivative (autocorr F) t| ≤ D`
     (`exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt`), and `Ẑ(F) ≥ −C(1 + K)(1 + A)e^{2βA} ∫ F²`
     whenever `|gaugeDerivative (autocorr F) t| ≤ K ∫ F²`
     (`exists_fullZeroForm_ge_neg_mass_of_zetaZeroWidth_lt`).
   - *`L²` ground-energy normalisation (under local depth-mass bound):* Under
     `OffLineDepthLocallyBounded W`, `μ(A) ≥ −depthFloorConst W A.1` at every aperture `A` and
     `polarGroundEnergyRate = zetaZeroWidth`
     (`neg_depthFloorConst_le_ccmRestrictedWeilGroundEnergy`,
     `polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineDepthLocallyBounded`).

2. **Aperture-invariance of unsigned depth sampling and single-aperture sufficiency**
   (`exists_unsignedDepthSamplingBound_iff_forall_aperture`,
   `polarGroundEnergyRate_eq_zetaZeroWidth_of_unsignedDepthSamplingBound`,
   `polarGroundEnergyRate_eq_zetaZeroWidth_or_forall_aperture_unsignedDepthSampling_unbounded`):
   Because `exists_unsignedDepthSamplingBound_iff` equates `(∃ B ≥ 0, UnsignedDepthSamplingBound a B)`
   at any fixed positive aperture `a` to the aperture-independent property
   `∃ W, OffLineDepthLocallyBounded W`, boundedness of unsigned conjugate-difference sampling at a
   *single* positive aperture `a₀` is equivalent to boundedness at *every* positive aperture `a`,
   and suffices to force `polarGroundEnergyRate = zetaZeroWidth`.

3. **Sub-exponential depth-floor closure and exponential height escape of high-depth-mass windows**
   (`exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_subexponential_depthFloor`,
   `polarGroundEnergyRate_eq_zetaZeroWidth_of_subexponential_depthFloor`,
   `exists_superexponential_depthFloor_of_lt`,
   `div_sq_lt_card_of_window_depthMass_gt`,
   `exp_depthMass_lt_height_of_window_depthMass_gt`,
   `polarGroundEnergyRate_eq_zetaZeroWidth_or_high_depthMass_window_escape`):
   Any aperture-dependent depth-floor factor `W(A) = o(e^{εA})` in
   `−depthFloorConst (W A.1) A.1 ≤ ccmRestrictedWeilGroundEnergy A` already forces
   `polarGroundEnergyRate = zetaZeroWidth`; contrapositively, `zetaZeroWidth < polarGroundEnergyRate`
   requires super-exponential failure of the depth floor and forces unit windows `[T − 1, T + 1]`
   of arbitrarily large squared depth mass `> W`, multiplicity `> W / zetaZeroWidth²`, and
   exponential height `180 |T| > exp(W / (40 · zetaZeroWidth²))` (`|T| ≥ 4`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real FourierTransform CompactlySupported

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.CCMParityQuartet
  GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
  GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory

/-! ## 1. The three normalisations of the Weil floor -/

/-- **The three-normalisation Weil floor bridge.**
1. *Archimedean normalisation (unconditional):* for every `a > 0` and `ε > 0`, `Re W_ζ(f, f)` is
   bounded below at exponential rate `(2a + ε) · zetaZeroWidth` against the archimedean weight
   `∫ ‖𝓕f(y)‖² log(|y| + 3) dy`.
2. *Energy/`H¹` normalisation (unconditional):* for every `β > zetaZeroWidth` and `K ≥ 0`, `Ẑ(F)`
   is bounded below at exponential rate `2βA` against `∫ F²` on all `C²_c` tests supported in
   `[−A, A]` with `|gaugeDerivative (autocorr F) t| ≤ K ∫ F²`.
3. *`L²` ground-energy normalisation (under local depth-mass bound):* whenever
   `OffLineDepthLocallyBounded W` holds, `μ(A) ≥ −depthFloorConst W A.1` for every `A` and
   `polarGroundEnergyRate = zetaZeroWidth`. -/
theorem three_normalisation_weil_floor_bridge :
    (∀ {a ε : ℝ}, 0 < a → 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
        (∀ t : ℝ, a < |t| → f t = 0) → Integrable (𝓕 f) →
        Integrable (fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) →
        -(C * Real.exp ((2 * a + ε) * zetaZeroWidth) *
            ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
          (Zeta23.zetaZeroConfig.W f f).re) ∧
    (∀ {β K : ℝ}, zetaZeroWidth < β → 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : ℝ, 0 ≤ A → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x : ℝ, A < |x| → F x = 0) →
        (∀ t : ℝ, |gaugeDerivative (RHTower.ArchimedeanAnomaly.autocorr F) t| ≤ K * ∫ x, F x ^ 2) →
        -(C * (1 + A) * Real.exp (2 * β * A) * ∫ x, F x ^ 2) ≤ fullZeroForm F) ∧
    (∀ {W : ℝ}, OffLineDepthLocallyBounded W →
      (∀ A : SuzukiPositiveAperture, -(depthFloorConst W A.1) ≤ ccmRestrictedWeilGroundEnergy A) ∧
        polarGroundEnergyRate = zetaZeroWidth) :=
  ⟨fun ha hε => exists_re_W_ge_logWeighted_rate_sharp ha hε,
    fun hβ hK => exists_fullZeroForm_ge_neg_mass_of_zetaZeroWidth_lt hβ hK,
    fun hW => ⟨neg_depthFloorConst_le_ccmRestrictedWeilGroundEnergy hW,
      polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineDepthLocallyBounded hW⟩⟩

/-! ## 2. Aperture-invariance of unsigned depth sampling and single-aperture sufficiency -/

/-- **Unsigned conjugate-difference sampling is aperture-invariant.** Boundedness of
`UnsignedDepthSamplingBound` at a *single* positive aperture `a₀` is equivalent to boundedness at
*every* positive aperture `a`, and to `∃ W, OffLineDepthLocallyBounded W`. -/
theorem exists_unsignedDepthSamplingBound_iff_forall_aperture (a₀ : SuzukiPositiveAperture) :
    (∃ B : ℝ, 0 ≤ B ∧ UnsignedDepthSamplingBound a₀ B) ↔
      (∀ a : SuzukiPositiveAperture, ∃ B : ℝ, 0 ≤ B ∧ UnsignedDepthSamplingBound a B) := by
  rw [exists_unsignedDepthSamplingBound_iff a₀]
  constructor
  · intro hW a
    exact (exists_unsignedDepthSamplingBound_iff a).mpr hW
  · intro hall
    exact (exists_unsignedDepthSamplingBound_iff a₀).mp (hall a₀)

/-- **Unsigned depth sampling at one aperture forces the `L²` ground-energy exponent to equal the
zero width.** If `UnsignedDepthSamplingBound a₀ B` holds at one positive aperture `a₀`, then
`polarGroundEnergyRate = zetaZeroWidth` and `μ(A)` obeys a pure exponential floor at every rate
`σ > zetaZeroWidth`. -/
theorem polarGroundEnergyRate_eq_zetaZeroWidth_of_unsignedDepthSamplingBound
    {a₀ : SuzukiPositiveAperture} {B : ℝ} (hB : UnsignedDepthSamplingBound a₀ B) :
    polarGroundEnergyRate = zetaZeroWidth ∧
      ∀ σ : ℝ, zetaZeroWidth < σ → ∃ C : ℝ, ∀ A : SuzukiPositiveAperture,
        -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A := by
  obtain ⟨W, hW⟩ := exists_offLineDepthLocallyBounded_of_unsignedDepthSamplingBound hB
  exact ⟨polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineDepthLocallyBounded hW,
    fun σ hσ => exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_offLineDepthLocallyBounded hW hσ⟩

/-- **The unsigned-sampling dichotomy across all apertures.** Either
`polarGroundEnergyRate = zetaZeroWidth`, or at *every* positive aperture `a` and for *every* bound
`B : ℝ`, `UnsignedDepthSamplingBound a B` fails. -/
theorem polarGroundEnergyRate_eq_zetaZeroWidth_or_forall_aperture_unsignedDepthSampling_unbounded :
    polarGroundEnergyRate = zetaZeroWidth ∨
      ∀ (a : SuzukiPositiveAperture) (B : ℝ), ¬ UnsignedDepthSamplingBound a B := by
  by_cases h : ∃ (a : SuzukiPositiveAperture) (B : ℝ), UnsignedDepthSamplingBound a B
  · obtain ⟨a, B, hB⟩ := h
    exact Or.inl (polarGroundEnergyRate_eq_zetaZeroWidth_of_unsignedDepthSamplingBound hB).1
  · right
    intro a B hB
    exact h ⟨a, B, hB⟩

/-! ## 3. Sub-exponential depth-floor closure and exponential height escape of clustering windows -/

/-- **Pure exponential floors at every rate `σ > zetaZeroWidth` from a sub-exponential depth-floor
factor.** If `-(depthFloorConst (W A.1) A.1) ≤ ccmRestrictedWeilGroundEnergy A` for a function
`W : ℝ → ℝ` with `W(A) ≤ C₀ e^{εA}` for every `ε > 0`, then at every rate `σ > zetaZeroWidth` the
ground energy satisfies `-(C e^{2σA}) ≤ ccmRestrictedWeilGroundEnergy A`. -/
theorem exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_subexponential_depthFloor
    (W : ℝ → ℝ)
    (hfloor : ∀ A : SuzukiPositiveAperture,
      -(depthFloorConst (W A.1) A.1) ≤ ccmRestrictedWeilGroundEnergy A)
    (hsubexp : ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ A : ℝ, 0 ≤ A → W A ≤ C₀ * Real.exp (ε * A))
    {σ : ℝ} (hσ : zetaZeroWidth < σ) :
    ∃ C : ℝ, ∀ A : SuzukiPositiveAperture,
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A := by
  set δ := (σ - zetaZeroWidth) / 2 with hδ
  have hδ0 : 0 < δ := by linarith
  obtain ⟨C₀, hC₀0, hWle⟩ := hsubexp (2 * δ) (by positivity)
  refine ⟨(12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * π) * C₀, fun A => ?_⟩
  refine le_trans ?_ (hfloor A)
  apply neg_le_neg
  have hA : 0 < A.1 := A.2
  have hpoly := sq_mul_linear_le_exp hδ0 hA.le
  have hWA := hWle A.1 hA.le
  have hsplit : Real.exp (2 * σ * A.1) =
      Real.exp (2 * δ * A.1) * Real.exp (2 * zetaZeroWidth * A.1) * Real.exp (2 * δ * A.1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hδ]
    ring
  unfold depthFloorConst
  rw [hsplit]
  have h1 : A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
      Real.exp (2 * zetaZeroWidth * A.1)) * W A.1 ≤
      A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
        Real.exp (2 * zetaZeroWidth * A.1)) * (C₀ * Real.exp (2 * δ * A.1)) :=
    mul_le_mul_of_nonneg_left hWA (by positivity)
  have h2 : A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
      Real.exp (2 * zetaZeroWidth * A.1)) * (C₀ * Real.exp (2 * δ * A.1)) ≤
      ((12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * δ * A.1)) *
        (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
          (C₀ * Real.exp (2 * δ * A.1))) := by
    calc A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
          Real.exp (2 * zetaZeroWidth * A.1)) * (C₀ * Real.exp (2 * δ * A.1))
        = (A.1 ^ 2 * (2 * A.1 + 2 * π)) *
            (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
              (C₀ * Real.exp (2 * δ * A.1))) := by ring
      _ ≤ ((12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * δ * A.1)) *
            (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
              (C₀ * Real.exp (2 * δ * A.1))) :=
          mul_le_mul_of_nonneg_right hpoly (by positivity)
  calc A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
        Real.exp (2 * zetaZeroWidth * A.1)) * W A.1
      ≤ ((12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * δ * A.1)) *
          (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
            (C₀ * Real.exp (2 * δ * A.1))) := h1.trans h2
    _ = (12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * π) * C₀ *
          (Real.exp (2 * δ * A.1) * Real.exp (2 * zetaZeroWidth * A.1) *
            Real.exp (2 * δ * A.1)) := by ring

/-- **Sub-exponential depth-floor closure of the ground-energy rate.** Whenever the
aperture-dependent depth-floor factor `W(A)` grows sub-exponentially in `A`,
`polarGroundEnergyRate = zetaZeroWidth`. -/
theorem polarGroundEnergyRate_eq_zetaZeroWidth_of_subexponential_depthFloor
    (W : ℝ → ℝ)
    (hfloor : ∀ A : SuzukiPositiveAperture,
      -(depthFloorConst (W A.1) A.1) ≤ ccmRestrictedWeilGroundEnergy A)
    (hsubexp : ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ A : ℝ, 0 ≤ A → W A ≤ C₀ * Real.exp (ε * A)) :
    polarGroundEnergyRate = zetaZeroWidth := by
  refine le_antisymm ?_ zetaZeroWidth_le_polarGroundEnergyRate
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨C, hC⟩ :=
    exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_subexponential_depthFloor W hfloor hsubexp
      (show zetaZeroWidth < zetaZeroWidth + ε by linarith)
  refine csInf_le bddBelow_polarGroundEnergyRates
    ⟨by linarith [zetaZeroWidth_nonneg], C, 0, fun A _ => ?_⟩
  exact (hC A).trans (ccmRestrictedWeilGroundEnergy_le_polar A)

/-- **Super-exponential depth-floor obstruction when `zetaZeroWidth < polarGroundEnergyRate`.** If
the ground-energy rate strictly exceeds the zero width, then there is an exponential rate `ε > 0`
such that for every `C₀ ≥ 0`, some aperture `A` violates the depth floor with factor
`C₀ e^{ε A}`. -/
theorem exists_superexponential_depthFloor_of_lt
    (hlt : zetaZeroWidth < polarGroundEnergyRate) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ A : SuzukiPositiveAperture,
      ccmRestrictedWeilGroundEnergy A < -(depthFloorConst (C₀ * Real.exp (ε * A.1)) A.1) := by
  set δ := (polarGroundEnergyRate - zetaZeroWidth) / 4 with hδ
  have hδ0 : 0 < δ := by linarith
  refine ⟨2 * δ, by positivity, fun C₀ hC₀0 => ?_⟩
  by_contra h
  push Not at h
  set C := (12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * π) * C₀ with hC
  have hbound : ∀ A : SuzukiPositiveAperture,
      -(C * Real.exp (2 * (zetaZeroWidth + 2 * δ) * A.1)) ≤
        ccmRestrictedWeilGroundEnergy A := by
    intro A
    refine le_trans ?_ (h A)
    apply neg_le_neg
    have hA : 0 < A.1 := A.2
    have hpoly := sq_mul_linear_le_exp hδ0 hA.le
    have hsplit : Real.exp (2 * (zetaZeroWidth + 2 * δ) * A.1) =
        Real.exp (2 * δ * A.1) * Real.exp (2 * zetaZeroWidth * A.1) *
          Real.exp (2 * δ * A.1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    unfold depthFloorConst
    rw [hsplit, hC]
    calc A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
          Real.exp (2 * zetaZeroWidth * A.1)) * (C₀ * Real.exp (2 * δ * A.1))
        = (A.1 ^ 2 * (2 * A.1 + 2 * π)) *
            (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
              (C₀ * Real.exp (2 * δ * A.1))) := by ring
      _ ≤ ((12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * δ * A.1)) *
            (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
              (C₀ * Real.exp (2 * δ * A.1))) :=
          mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = (12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * π) * C₀ *
            (Real.exp (2 * δ * A.1) * Real.exp (2 * zetaZeroWidth * A.1) *
              Real.exp (2 * δ * A.1)) := by ring
  have hle : polarGroundEnergyRate ≤ zetaZeroWidth + 2 * δ :=
    csInf_le bddBelow_polarGroundEnergyRates
      ⟨by linarith [zetaZeroWidth_nonneg], C, 0, fun A _ =>
        (hbound A).trans (ccmRestrictedWeilGroundEnergy_le_polar A)⟩
  linarith

/-- Any finite set of copies carrying squared depth mass `> W` (`0 < zetaZeroWidth`) has
cardinality strictly exceeding `W / zetaZeroWidth²`. -/
theorem div_sq_lt_card_of_window_depthMass_gt {W : ℝ} (hσ : 0 < zetaZeroWidth)
    (s : Finset XiZeroCopy) (hW : W < ∑ q ∈ s, (xiSpectralPoint q).im ^ 2) :
    W / zetaZeroWidth ^ 2 < s.card := by
  rw [div_lt_iff₀ (sq_pos_of_pos hσ)]
  calc W < ∑ q ∈ s, (xiSpectralPoint q).im ^ 2 := hW
    _ ≤ ∑ _q ∈ s, zetaZeroWidth ^ 2 := Finset.sum_le_sum fun q _ => sq_im_xiSpectralPoint_le q
    _ = s.card * zetaZeroWidth ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Exponential height lower bound for high-depth-mass unit windows.** Any unit window
`[T − 1, T + 1]` at height `|T| ≥ 4` carrying squared off-line depth mass `> W`
(`0 < zetaZeroWidth`) must lie at height `180 |T| > exp(W / (40 · zetaZeroWidth²))`. -/
theorem exp_depthMass_lt_height_of_window_depthMass_gt {T W : ℝ} (hσ : 0 < zetaZeroWidth)
    (hT : 4 ≤ |T|) (s : Finset XiZeroCopy) (hs : ∀ q ∈ s, |(xiSpectralPoint q).re - T| ≤ 1)
    (hW : W < ∑ q ∈ s, (xiSpectralPoint q).im ^ 2) :
    Real.exp (W / (40 * zetaZeroWidth ^ 2)) < 180 * |T| := by
  have hsum := sum_sq_im_xiSpectralPoint_window_le hT s hs
  have hlt : W < 40 * zetaZeroWidth ^ 2 * Real.log (180 * |T|) := hW.trans_le hsum
  have hdiv : W / (40 * zetaZeroWidth ^ 2) < Real.log (180 * |T|) := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have h180 : 0 < 180 * |T| := by linarith
  calc Real.exp (W / (40 * zetaZeroWidth ^ 2))
      < Real.exp (Real.log (180 * |T|)) := Real.exp_lt_exp.mpr hdiv
    _ = 180 * |T| := Real.exp_log h180

/-- **The sharp clustering and exponential height-escape dichotomy.**
Either `polarGroundEnergyRate = zetaZeroWidth`, or `0 < zetaZeroWidth < polarGroundEnergyRate` and:
1. at every positive aperture `a`, `UnsignedDepthSamplingBound a B` fails for all `B : ℝ`;
2. there is `ε > 0` such that no sub-exponential factor `C₀ e^{εA}` bounds the depth floor across
   all apertures; and
3. for every `W : ℝ`, there exist a height `T` and a finite set `s` of copies in `[T − 1, T + 1]`
   with squared depth mass `> W`, cardinality `> W / zetaZeroWidth²`, and (whenever `4 ≤ |T|`)
   `exp(W / (40 · zetaZeroWidth²)) < 180 |T|`. -/
theorem polarGroundEnergyRate_eq_zetaZeroWidth_or_high_depthMass_window_escape :
    polarGroundEnergyRate = zetaZeroWidth ∨
      (0 < zetaZeroWidth ∧ zetaZeroWidth < polarGroundEnergyRate ∧
        (∀ (a : SuzukiPositiveAperture) (B : ℝ), ¬ UnsignedDepthSamplingBound a B) ∧
        (∃ ε : ℝ, 0 < ε ∧ ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ A : SuzukiPositiveAperture,
          ccmRestrictedWeilGroundEnergy A < -(depthFloorConst (C₀ * Real.exp (ε * A.1)) A.1)) ∧
        (∀ W : ℝ, ∃ T : ℝ, ∃ s : Finset XiZeroCopy,
          (∀ q ∈ s, |(xiSpectralPoint q).re - T| ≤ 1) ∧
          W < ∑ q ∈ s, (xiSpectralPoint q).im ^ 2 ∧
          W / zetaZeroWidth ^ 2 < s.card ∧
          (4 ≤ |T| → Real.exp (W / (40 * zetaZeroWidth ^ 2)) < 180 * |T|))) := by
  rcases eq_or_lt_of_le zetaZeroWidth_le_polarGroundEnergyRate with heq | hlt
  · exact Or.inl heq.symm
  · right
    have hσ : 0 < zetaZeroWidth := by
      rcases eq_or_lt_of_le zetaZeroWidth_nonneg with h0 | hpos
      · exfalso
        have hRH : RiemannHypothesis := riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr h0.symm
        have hp0 : polarGroundEnergyRate = 0 :=
          riemannHypothesis_iff_polarGroundEnergyRate_eq_zero.mp hRH
        linarith
      · exact hpos
    have hno_uds : ∀ (a : SuzukiPositiveAperture) (B : ℝ), ¬ UnsignedDepthSamplingBound a B := by
      intro a B hB
      exact hlt.ne' (polarGroundEnergyRate_eq_zetaZeroWidth_of_unsignedDepthSamplingBound hB).1
    refine ⟨hσ, hlt, hno_uds, exists_superexponential_depthFloor_of_lt hlt, fun W => ?_⟩
    obtain ⟨T, s, hs, hW⟩ := exists_window_depthMass_gt_of_zetaZeroWidth_lt_polarGroundEnergyRate hlt W
    exact ⟨T, s, hs, hW, div_sq_lt_card_of_window_depthMass_gt hσ s hW,
      fun hT => exp_depthMass_lt_height_of_window_depthMass_gt hσ hT s hs hW⟩

end GaloisForLFunctions.SquareRootThreshold
