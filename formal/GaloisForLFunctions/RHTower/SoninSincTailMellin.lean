import GaloisForLFunctions.RHTower.SoninDecayTailMellin

/-!
# The Mellin tail of the sinc kernel

`fourierBandIndicator a` decays like `1/(π|t|)`, so `SoninDecayTailMellin` applies verbatim: its
Mellin tail

`sincMellin a s = ∫_a^∞ (fourierBandIndicator a)(t) · t^{-s} dt`

converges absolutely and is holomorphic on the whole half-plane `Re s > 0`.  This is the explicit
half of the Mellin transform of a vector of the extended Sonine space `L_a`.

## Main results

* `integrableOn_sincMellin`, `norm_sincTail_le`
* `differentiableOn_sincMellin` — holomorphy on `Re s > 0`
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The sinc kernel as a plain function. -/
def soninSincKernel (a : ℝ) : ℝ → ℂ := fun t => ((fourierBandIndicator a : SoninL2) : ℝ → ℂ) t

theorem aestronglyMeasurable_soninSincKernel (a : ℝ) :
    AEStronglyMeasurable (soninSincKernel a) volume :=
  Lp.aestronglyMeasurable _

/-- The Mellin tail of the sinc kernel. -/
def sincMellin (a : ℝ) : ℂ → ℂ := fun s => decayTailMellin (fourierBandIndicator a) a s

theorem sincMellin_eq (a : ℝ) (s : ℂ) :
    sincMellin a s = ∫ t in Ioi a, soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s) := rfl

theorem integrableOn_sincMellin {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) {T : ℝ}
    (haT : a ≤ T) :
    IntegrableOn (fun t : ℝ => soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s)) (Ioi T) volume :=
  integrableOn_decayTail (hasInverseDecay_fourierBandIndicator ha) (lt_of_lt_of_le ha haT) hs

/-- **The uniform tail bound.** -/
theorem norm_sincTail_le {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) {T : ℝ} (haT : a ≤ T) :
    ‖∫ t in Ioi T, soninSincKernel a t * ((t : ℝ) : ℂ) ^ (-s)‖
      ≤ (1 / Real.pi) * (T ^ (-s.re) / s.re) :=
  norm_decayTail_le (hasInverseDecay_fourierBandIndicator ha) (lt_of_lt_of_le ha haT) hs

/-- **The Mellin tail of the sinc kernel is holomorphic on the right half-plane.** -/
theorem differentiableOn_sincMellin {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ (sincMellin a) {s : ℂ | 0 < s.re} :=
  differentiableOn_decayTailMellin (hasInverseDecay_fourierBandIndicator ha) ha

end RHTower

end
