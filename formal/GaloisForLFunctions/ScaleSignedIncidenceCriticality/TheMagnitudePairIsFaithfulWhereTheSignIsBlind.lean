import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheDepthIsTheCompleteDilationInvariant
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThreeBandsDefeatTheMass

/-!
# The magnitude pair is faithful where the sign is blind

Everything the programme proved blind is a *sign*: the certificate at an aperture, at a level, in any
unit, with any auxiliary bounded datum, over any family. Everything the band inversions compute is a
*magnitude*. This module puts the two readings side by side on the same data and computes both
resolution limits.

On the two-coordinate lattice family `ScaleDepthDatum`:

* the level certificate at any aperture and level has resolution limit `½` for the depth
  (`resolutionLimit_sdDepth_scaleDepthReading`, recalled here as `theSignIsBlind`) — the trivial
  bound, no information at all;
* the pair of ground energies at aliasing indices two and three has resolution limit exactly the
  depth (`resolutionLimit_sdDepth_bandPairReading`) — its shadow is a single depth, so floor and
  limit coincide and the reading is *faithful*.

`theDichotomyOfSignAndMagnitude` states both at once. This is the sharpest form of the field's
central fact. The blindness theorems are not about the Weil form being a weak object; they are about
*which functional of it is read*. Its sign at one aperture carries no depth information in any unit;
two of its magnitudes carry all of it. A closing mechanism must therefore be a size estimate, and
the field now says exactly which sizes: the ground energies at the first two aliasing indices above
Nyquist.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The magnitude-pair reading -/

/-- The reading that returns the two ground energies just above the Nyquist aperture. -/
noncomputable def bandPairReading (p : ScaleDepthDatum) : ℝ × ℝ :=
  (bandEnergy (sdScale p) (sdDepth p) 2, bandEnergy (sdScale p) (sdDepth p) 3)

/-- **The shadow of the magnitude pair is a single depth.** -/
theorem sdDepth_eq_of_mem_shadow_bandPair {p q : ScaleDepthDatum}
    (h : q ∈ shadow bandPairReading p) : sdDepth q = sdDepth p := by
  have hq : (0 : ℝ) < sdScale q := q.2.1
  have hqd : (0 : ℝ) < sdDepth q := q.2.2.1
  have hp : (0 : ℝ) < sdScale p := p.2.1
  have hpd : (0 : ℝ) < sdDepth p := p.2.2.1
  have h2 : bandEnergy (sdScale q) (sdDepth q) 2 = bandEnergy (sdScale p) (sdDepth p) 2 :=
    congrArg Prod.fst h
  have h3 : bandEnergy (sdScale q) (sdDepth q) 3 = bandEnergy (sdScale p) (sdDepth p) 3 :=
    congrArg Prod.snd h
  simp only [bandEnergy] at h2 h3
  exact depth_determined_by_two_bands hq hqd hp hpd h2 h3

theorem bddAbove_sdDepth_shadow (p : ScaleDepthDatum) :
    BddAbove (sdDepth '' shadow bandPairReading p) := by
  refine ⟨1 / 2, fun x hx => ?_⟩
  obtain ⟨e, -, rfl⟩ := hx
  exact e.2.2.2

/-! ### 2. The magnitude pair is faithful -/

/-- **The magnitude pair resolves the depth exactly.** -/
theorem resolutionLimit_sdDepth_bandPairReading (p : ScaleDepthDatum) :
    resolutionLimit sdDepth bandPairReading p = sdDepth p := by
  refine le_antisymm ?_ (le_resolutionLimit (bddAbove_sdDepth_shadow p))
  refine (certifies_iff_resolutionLimit_le (bddAbove_sdDepth_shadow p)).mp fun e he => ?_
  exact le_of_eq (sdDepth_eq_of_mem_shadow_bandPair he)

/-- Floor and limit coincide: the reading is informative for the depth. -/
theorem resolutionFloor_eq_resolutionLimit_bandPairReading (p : ScaleDepthDatum) :
    resolutionFloor sdDepth bandPairReading p = resolutionLimit sdDepth bandPairReading p := by
  refine (resolutionFloor_eq_resolutionLimit_iff ?_ (bddAbove_sdDepth_shadow p)).mpr
    fun e he => sdDepth_eq_of_mem_shadow_bandPair he
  refine ⟨0, fun x hx => ?_⟩
  obtain ⟨e, -, rfl⟩ := hx
  exact e.2.2.1.le

/-! ### 3. The dichotomy -/

/-- The sign side, recalled: at every aperture and level the certificate's limit is the trivial
`½`. -/
theorem theSignIsBlind {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η) {p : ScaleDepthDatum}
    (hp : scaleDepthReading a η p) :
    resolutionLimit sdDepth (scaleDepthReading a η) p = 1 / 2 :=
  resolutionLimit_sdDepth_scaleDepthReading ha hη hp

/-- **The dichotomy of sign and magnitude.** On the same family, the certificate's sign resolves
nothing and the two ground-energy magnitudes resolve the depth exactly. -/
theorem theDichotomyOfSignAndMagnitude {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η)
    {p : ScaleDepthDatum} (hp : scaleDepthReading a η p) :
    resolutionLimit sdDepth (scaleDepthReading a η) p = 1 / 2 ∧
      resolutionLimit sdDepth bandPairReading p = sdDepth p ∧
      resolutionFloor sdDepth bandPairReading p = resolutionLimit sdDepth bandPairReading p :=
  ⟨theSignIsBlind ha hη hp, resolutionLimit_sdDepth_bandPairReading p,
    resolutionFloor_eq_resolutionLimit_bandPairReading p⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
