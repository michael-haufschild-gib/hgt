import GaloisForLFunctions.RHTower.PerronMellinSeamResidue

/-!
# Canonical Perron--Mellin seam

An additive defect in `L²` is not chosen structure.  Whenever the carrier's negative line is square
integrable, its canonical defect relative to a normalized Mellin source trace is the `L²` class of
the carrier line minus that trace.  This module constructs the class, weakens cross-line coherence to
the eventual form actually consumed by the contour, and eliminates the defect hypothesis from the
arithmetic-recovery theorem.

The resulting seam coordinate is source-gauge invariant: subtracting two different admissible Sonin
sources changes the `L²` defect, but their normalized Perron coordinates converge to the same
Dirichlet coefficient beyond both physical radii.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal Topology

/-- The canonical `L²` class of a negative carrier line when it is square-integrable, extended by
zero away from that domain.  Only eventual square-integrable depths are consumed below. -/
def negativeLineLp (F : ℂ → ℂ) (M : ℕ) : SoninL2 := by
  classical
  exact if h : MemLp (fun t : ℝ => F (↑(-(M : ℝ)) + ↑t * I)) 2 volume then
      h.toLp (fun t : ℝ => F (↑(-(M : ℝ)) + ↑t * I))
    else 0

/-- The canonical additive cross-line defect: carrier line minus normalized weighted source trace. -/
def canonicalCrossLineMellinDefect
    (F : ℂ → ℂ) (g : SoninL2) (τ : ℝ)
    (hsupp : HasAELowerSupport (fun t => g t) τ) (M : ℕ) : SoninL2 :=
  negativeLineLp F M - negativeMellinL2Trace g τ hsupp M

/-- The additive defect at a fixed line is unique as an `L²` class.  Thus whenever it exists, it is
forced by the carrier and source rather than chosen auxiliary data. -/
theorem crossLineMellinDefectAt_unique
    {F : ℂ → ℂ} {g : SoninL2} {τ : ℝ}
    {hsupp : HasAELowerSupport (fun t => g t) τ}
    {Δ₁ Δ₂ : ℕ → SoninL2} {M : ℕ}
    (h₁ : HasCrossLineMellinDefectAt F g τ hsupp Δ₁ M)
    (h₂ : HasCrossLineMellinDefectAt F g τ hsupp Δ₂ M) :
    Δ₁ M = Δ₂ M := by
  apply Lp.ext
  filter_upwards [h₁, h₂] with t h₁t h₂t
  exact add_left_cancel (h₁t.symm.trans h₂t)

/-- At every square-integrable depth, canonical subtraction supplies the local additive defect
identity almost everywhere. -/
theorem hasCrossLineMellinDefectAt_canonical
    {F : ℂ → ℂ} {g : SoninL2} {τ : ℝ}
    (hsupp : HasAELowerSupport (fun t => g t) τ) {M : ℕ}
    (hline : MemLp (fun t : ℝ => F (↑(-(M : ℝ)) + ↑t * I)) 2 volume) :
    HasCrossLineMellinDefectAt F g τ hsupp
      (canonicalCrossLineMellinDefect F g τ hsupp) M := by
  classical
  have hlineAE : (fun t => negativeLineLp F M t) =ᵐ[volume]
      fun t => F (↑(-(M : ℝ)) + ↑t * I) := by
    simpa only [negativeLineLp, dif_pos hline] using hline.coeFn_toLp
  filter_upwards [hlineAE,
    Lp.coeFn_sub (negativeLineLp F M) (negativeMellinL2Trace g τ hsupp M)] with
      t hline_t hsub
  rw [canonicalCrossLineMellinDefect, hsub, Pi.sub_apply, hline_t]
  ring

/-- Eventual square-integrability constructs the eventual cross-line defect interface canonically. -/
theorem hasEventuallyCrossLineMellinDefect_canonical
    {F : ℂ → ℂ} {g : SoninL2} {τ : ℝ}
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (hlines : ∀ᶠ M : ℕ in atTop,
      MemLp (fun t : ℝ => F (↑(-(M : ℝ)) + ↑t * I)) 2 volume) :
    HasEventuallyCrossLineMellinDefect F g τ hsupp
      (canonicalCrossLineMellinDefect F g τ hsupp) := by
  filter_upwards [hlines] with M hM
  exact hasCrossLineMellinDefectAt_canonical hsupp hM

/-- Differentiability supplies measurability, so the existing flank-energy interface discharges
eventual square-integrability of the carrier lines. -/
theorem eventually_memLp_negativeLine_of_flankL2Energy
    {F : ℂ → ℂ} {B : ℕ → ℝ} (hF : Differentiable ℂ F)
    (henergy : HasPerronCarrierFlankL2Energy F B) :
    ∀ᶠ M : ℕ in atTop,
      MemLp (fun t : ℝ => F (↑(-(M : ℝ)) + ↑t * I)) 2 volume := by
  filter_upwards [henergy] with M hM
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => F (↑(-(M : ℝ)) + ↑t * I)) :=
    (hF.continuous.comp (by fun_prop)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq_norm hmeas).2 hM.1

/-- **Canonical seam coefficient recovery.**  Flank `L²` energy constructs the cross-line defect
internally; its normalized Perron coordinate converges to the Dirichlet coefficient beyond the
source radius.  No defect or coherence Prop remains. -/
theorem soninPerronCanonicalSeamCoefficient_tendsto_coefficient_of_flankL2Energy
    {F : ℂ → ℂ} {q c δ : ℝ} {coeff : ℕ → ℂ} {B : ℕ → ℝ}
    {n : ℕ} (hq : 0 < q) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier q)
    (henergy : HasPerronCarrierFlankL2Energy F B)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδn : δ < (n : ℝ))
    (hgap : q⁻¹ < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ => perronMellinSeamCoefficient
      (canonicalCrossLineMellinDefect F (logEvenUnitary f) (Real.log q)
        (logEvenUnitary_hasAELowerSupport hq f hf)) M n δ) atTop
      (𝓝 (coeff n)) := by
  have hdef := hasEventuallyCrossLineMellinDefect_canonical
    (logEvenUnitary_hasAELowerSupport hq f hf)
    (eventually_memLp_negativeLine_of_flankL2Energy hF henergy)
  exact soninPerronMellinSeamCoefficient_tendsto_coefficient_of_eventuallyDefect
    hq f hf hdef hhorizontal hc0 hsum hF hFeq hn hδ0 hδ1 hδn hgap

/-- **Source-gauge invariance of the canonical arithmetic seam.**  Two Sonin sources subtracted
from the same carrier give asymptotically equal normalized seam coordinates beyond both reciprocal
cutoffs.  The recovered arithmetic coordinate belongs to the carrier, not the chosen source. -/
theorem soninPerronCanonicalSeamCoefficient_twoSource_sub_tendsto_zero
    {F : ℂ → ℂ} {q₁ q₂ c δ : ℝ} {coeff : ℕ → ℂ} {B : ℕ → ℝ}
    {n : ℕ} (hq₁ : 0 < q₁) (f₁ : evenSubspace)
    (hf₁ : f₁ ∈ evenCentralSoninCarrier q₁)
    (hq₂ : 0 < q₂) (f₂ : evenSubspace)
    (hf₂ : f₂ ∈ evenCentralSoninCarrier q₂)
    (henergy : HasPerronCarrierFlankL2Energy F B)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδn : δ < (n : ℝ))
    (hgap₁ : q₁⁻¹ < perronSupportScaleAt n δ)
    (hgap₂ : q₂⁻¹ < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ =>
      perronMellinSeamCoefficient
          (canonicalCrossLineMellinDefect F (logEvenUnitary f₁) (Real.log q₁)
            (logEvenUnitary_hasAELowerSupport hq₁ f₁ hf₁)) M n δ -
        perronMellinSeamCoefficient
          (canonicalCrossLineMellinDefect F (logEvenUnitary f₂) (Real.log q₂)
            (logEvenUnitary_hasAELowerSupport hq₂ f₂ hf₂)) M n δ) atTop (𝓝 0) := by
  have h₁ := soninPerronCanonicalSeamCoefficient_tendsto_coefficient_of_flankL2Energy
    hq₁ f₁ hf₁ henergy hhorizontal hc0 hsum hF hFeq hn hδ0 hδ1 hδn hgap₁
  have h₂ := soninPerronCanonicalSeamCoefficient_tendsto_coefficient_of_flankL2Energy
    hq₂ f₂ hf₂ henergy hhorizontal hc0 hsum hF hFeq hn hδ0 hδ1 hδn hgap₂
  simpa using h₁.sub h₂

end RHTower
