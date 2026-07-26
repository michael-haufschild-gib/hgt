/-
The line of symmetry's slice of the exponent-pair region, and the record lattice.

Every landmark pair lies on the line `λ = κ + 1/2`, where the subconvexity exponent is `κ` itself.
The two trivial pairs `(0, 1)` and `(1/2, 1/2)` lie off that line, on opposite sides, and their
midpoint

    **(1/4, 3/4)**

is on it, with `μ = 1/4` — the convexity bound.  So the line's slice of the region runs from the
record `(13/84, 55/84)` up to `(1/4, 3/4)`, and the van der Corput tower's exponents
`μ_k = 1/4 - k/(2N_k)` converge exactly to the far endpoint.

Separately, three of the four landmark exponents lie on a common lattice.  Over the denominator
`168 = lcm(6, 56, 84)`:

    Weyl `1/6`              = **28/168**
    Bombieri–Iwaniec `9/56` = **27/168**
    Bourgain `13/84`        = **26/168**

three consecutive multiples of `1/168`; Huxley's `32/205` lies strictly between the second and third
at `26.2244…/168`, off the lattice since `205 = 5·41` is coprime to `168`.  This is recorded as an
observation about four numbers, not as a structural law.
-/
import GaloisForLFunctions.HTGeometry.VanDerCorputTowerClosedForm

namespace HTGeometry

/-! ### The line's slice -/

/-- The first trivial pair. -/
def trivialPairA : ℚ × ℚ := (0, 1)

/-- The second trivial pair. -/
def trivialPairB : ℚ × ℚ := (1 / 2, 1 / 2)

/-- **Neither trivial pair lies on the line of symmetry, and they lie on opposite sides.** -/
theorem trivial_pairs_off_line :
    epDisplacement trivialPairA.1 trivialPairA.2 = 1 / 2 ∧
      epDisplacement trivialPairB.1 trivialPairB.2 = -(1 / 2) := by
  constructor
  · unfold epDisplacement trivialPairA; norm_num
  · unfold epDisplacement trivialPairB; norm_num

/-- Their midpoint. -/
def convexityPair : ℚ × ℚ := (1 / 4, 3 / 4)

/-- **The midpoint of the two trivial pairs is `(1/4, 3/4)`.** -/
theorem convexityPair_is_midpoint :
    mixFst trivialPairA.1 trivialPairB.1 (1 / 2) = convexityPair.1 ∧
      mixSnd trivialPairA.2 trivialPairB.2 (1 / 2) = convexityPair.2 := by
  constructor
  · unfold mixFst trivialPairA trivialPairB convexityPair; norm_num
  · unfold mixSnd trivialPairA trivialPairB convexityPair; norm_num

/-- **It lies on the line of symmetry.** -/
theorem convexityPair_on_line :
    epDisplacement convexityPair.1 convexityPair.2 = 0 := by
  unfold epDisplacement convexityPair; norm_num

/-- **And its exponent is the convexity bound.** -/
theorem convexityPair_mu : epMu convexityPair.1 convexityPair.2 = 1 / 4 := by
  unfold epMu convexityPair; norm_num

/-- **The tower's exponents converge to it**: they increase and stay below `1/4`. -/
theorem tower_converges_to_convexityPair :
    towerMu 1 < towerMu 4 ∧ towerMu 4 < epMu convexityPair.1 convexityPair.2 := by
  rw [convexityPair_mu]
  obtain ⟨h1, -, -, h4⟩ := towerMu_values
  rw [h1, h4]
  constructor <;> norm_num

/-- **The line's slice runs from the record to the convexity pair.** -/
theorem line_slice_endpoints :
    epMu bourgainKappa bourgainLambda = bourgainTheta ∧
      epMu convexityPair.1 convexityPair.2 = 1 / 4 ∧
      bourgainTheta < 1 / 4 := by
  refine ⟨bourgain_pair_mu, convexityPair_mu, ?_⟩
  unfold bourgainTheta; norm_num

/-! ### The record lattice -/

/-- The common denominator of three of the four landmark exponents. -/
def recordLatticeDen : ℚ := 168

/-- **Weyl, Bombieri–Iwaniec and Bourgain are three consecutive multiples of `1/168`.** -/
theorem record_lattice :
    weylKappa = 28 / recordLatticeDen ∧
      biKappa = 27 / recordLatticeDen ∧
      bourgainKappa = 26 / recordLatticeDen := by
  refine ⟨?_, ?_, ?_⟩
  · unfold weylKappa recordLatticeDen; norm_num
  · unfold biKappa recordLatticeDen; norm_num
  · unfold bourgainKappa recordLatticeDen; norm_num

/-- **Huxley's exponent lies strictly between the second and third, off the lattice.** -/
theorem huxley_between :
    bourgainKappa < huxleyPairKappa ∧ huxleyPairKappa < biKappa := by
  constructor
  · unfold bourgainKappa huxleyPairKappa; norm_num
  · unfold huxleyPairKappa biKappa; norm_num

/-- Its position on the lattice scale, as a rational multiple of `1/168`. -/
theorem huxley_lattice_position :
    huxleyPairKappa * recordLatticeDen = 5376 / 205 := by
  unfold huxleyPairKappa recordLatticeDen; norm_num

/-- **The century's progress, in lattice units**: from `28` to `26`, with the Lindelöf target at
`0`. -/
theorem lattice_progress :
    weylKappa * recordLatticeDen = 28 ∧
      bourgainKappa * recordLatticeDen = 26 ∧
      (0 : ℚ) * recordLatticeDen = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold weylKappa recordLatticeDen; norm_num
  · unfold bourgainKappa recordLatticeDen; norm_num
  · ring

/-- **Two units gained, twenty-six remaining.** -/
theorem lattice_ledger :
    (weylKappa - bourgainKappa) * recordLatticeDen = 2 ∧
      bourgainKappa * recordLatticeDen = 26 := by
  constructor
  · unfold weylKappa bourgainKappa recordLatticeDen; norm_num
  · unfold bourgainKappa recordLatticeDen; norm_num

end HTGeometry
