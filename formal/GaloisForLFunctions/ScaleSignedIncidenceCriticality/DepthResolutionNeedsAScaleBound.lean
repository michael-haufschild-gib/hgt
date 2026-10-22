import GaloisForLFunctions.ScaleSignedIncidenceCriticality.OneApertureResolvesOnlyTheScalesBelowTwiceIt

/-!
# Depth resolution needs a scale bound

The level certificate of aperture `a` resolves the depth sharply — but only on data of a *known*
scale: the computation `min ½ (depthResolution L η)` fixes `L` first. This module varies both
coordinates and finds that the gain disappears entirely.

The data are now pairs `(L, δ)`: a lattice of spacing `2π/L` and depth `δ`. The same reading, the
level-`η` Weil floor on aperture `a`, is **automatic** on every datum whose scale satisfies
`2a ≤ L` (`scaleDepthReading_of_dense`), since such a lattice is Weil-positive at aperture `a`.
Hence (`resolutionLimit_sdDepth_scaleDepthReading`)

`resolutionLimit sdDepth (scaleDepthReading a η) = ½`

for every aperture and every level: with the scale free, the trivial bound returns.

`theDepthNeedsAScaleBound` puts the two computations side by side. The gain of a trans-Nyquist level
certificate is not a property of the certificate; it is a property of the certificate *together with*
a bound on the scale of the data it is applied to. Reading the deficit finely is not enough — one
must also know that the configuration is not denser than the aperture can follow.

The consequence for `ζ` is the sharp form of "every scale, not almost every". The zeros of `ζ` grow
denser with the height, so for any fixed aperture the configuration eventually has `2a ≤ L` and
falls into the automatic region: a fixed aperture is blind above some height
(`everyFixedApertureIsEventuallyBlind`). A mechanism must therefore let its aperture grow with the
density it addresses; no single certificate, at any level, covers all heights.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The two-coordinate data -/

/-- A lattice datum with both coordinates free: scale `L` and depth `δ`. -/
def ScaleDepthDatum : Type := {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2}

/-- The scale coordinate. -/
def sdScale (p : ScaleDepthDatum) : ℝ := p.1.1

/-- The depth coordinate: the invariant RH is about. -/
def sdDepth (p : ScaleDepthDatum) : ℝ := p.1.2

/-- The configuration of the datum. -/
noncomputable def sdConfig (p : ScaleDepthDatum) : ZeroConfig :=
  offLineLatticeConfig p.2.1 p.2.2.1 p.2.2.2

/-- The level-`η` Weil floor on aperture `a`, now read on both coordinates. -/
def scaleDepthReading (a η : ℝ) (p : ScaleDepthDatum) : Prop :=
  WeilFloorAtLevel (sdConfig p) a η

/-! ### 2. Dense data satisfy the certificate automatically -/

/-- **The automatic region.** A datum whose scale satisfies `2a ≤ L` is Weil-positive at aperture
`a`, hence has a floor at every nonnegative level, whatever its depth. -/
theorem scaleDepthReading_of_dense {a η : ℝ} (hη : 0 ≤ η) (p : ScaleDepthDatum)
    (hp : 2 * a ≤ sdScale p) : scaleDepthReading a η p := by
  intro f hf hfs _ _
  have hpos : 0 ≤ ((sdConfig p).W f f).re :=
    (offLineLattice_weil_positive_iff p.2.1 p.2.2.1 p.2.2.2 a).mpr
      (by simp only [sdScale] at hp; linarith) f hf hfs
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  nlinarith

/-! ### 3. With the scale free the limit is trivial again -/

/-- **Depth resolution collapses without a scale bound.** At every aperture and every level, the
resolution limit of the depth on the two-coordinate family is the trivial `½`: the dense end of the
family carries the maximal depth and satisfies the certificate for free. -/
theorem resolutionLimit_sdDepth_scaleDepthReading {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η)
    {p₀ : ScaleDepthDatum} (hp₀ : scaleDepthReading a η p₀) :
    resolutionLimit sdDepth (scaleDepthReading a η) p₀ = 1 / 2 := by
  have hbdd : BddAbove (sdDepth '' shadow (scaleDepthReading a η) p₀) :=
    ⟨1 / 2, by rintro x ⟨p, -, rfl⟩; exact p.2.2.2⟩
  refine le_antisymm (csSup_le (shadow_image_nonempty sdDepth (scaleDepthReading a η) p₀) ?_) ?_
  · rintro x ⟨p, -, rfl⟩
    exact p.2.2.2
  · set p₁ : ScaleDepthDatum := ⟨(2 * a, 1 / 2), by linarith, by norm_num, le_rfl⟩ with hp₁
    have hdense : 2 * a ≤ sdScale p₁ := le_rfl
    have hmem : p₁ ∈ shadow (scaleDepthReading a η) p₀ :=
      propext (iff_of_true (scaleDepthReading_of_dense hη p₁ hdense) hp₀)
    exact le_csSup hbdd ⟨p₁, hmem, rfl⟩

/-! ### 4. A fixed aperture is eventually blind -/

/-- **Every fixed aperture is eventually blind.** For any aperture and level, every datum of scale
at least `2a` lies in the automatic region, so the certificate distinguishes none of them: it says
nothing about configurations denser than its own aperture can follow. -/
theorem everyFixedApertureIsEventuallyBlind {a η : ℝ} (hη : 0 ≤ η) :
    ∀ p q : ScaleDepthDatum, 2 * a ≤ sdScale p → 2 * a ≤ sdScale q →
      scaleDepthReading a η p = scaleDepthReading a η q := fun p q hp hq =>
  propext (iff_of_true (scaleDepthReading_of_dense hη p hp)
    (scaleDepthReading_of_dense hη q hq))

/-- **The depth needs a scale bound.** At a known scale a level certificate resolves the depth to
`min ½ (depthResolution L η)`; with the scale free the same certificate resolves nothing. The gain
belongs to the pair (certificate, scale bound), not to the certificate. -/
theorem theDepthNeedsAScaleBound {L a η : ℝ} (hL : 0 < L) (ha : L / 2 < a) (haL : a ≤ L)
    (hη : 0 ≤ η) {d₀ : DepthDatum} (hd₀ : levelReading hL a η d₀)
    {p₀ : ScaleDepthDatum} (hp₀ : scaleDepthReading a η p₀) :
    resolutionLimit depth (levelReading hL a η) d₀ = min (1 / 2) (depthResolution L η) ∧
      resolutionLimit sdDepth (scaleDepthReading a η) p₀ = 1 / 2 :=
  ⟨resolutionLimit_depth_levelReading hL ha haL hη hd₀,
    resolutionLimit_sdDepth_scaleDepthReading (by linarith) hη hp₀⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
