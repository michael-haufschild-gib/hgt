import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheApertureLadderIsStrictYetEveryStageIsTrivial
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.AsymptoticNodeReadingsCannotResolveNodePositivity
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.StructuralFlagReadingsCannotResolveCriticality

/-!
# The wall gates of a resolving reading

Explicit pairs of data carry the whole admissibility problem. Each pair is **identified** by the
natural reading of one face of the critical-line problem and must be **separated** by any reading
that resolves that face:

| Gate | Pair | Identified by |
| --- | --- | --- |
| temperedness | `ζ(s−¼)ζ(s+¼)` against `ζ²` | the structural flags |
| node criticality | the prime powers with and without `4` | every asymptotic (density) reading |
| trans-Nyquist | a depth-`½` lattice against the on-line lattice | positivity at any one aperture |
| no finite carrier | one off-line pair above height `T` | the divisor truncated at height `T` |
| parity | the damped Möbius weight against its parity twin | the Ramanujan amplitudes |

`theWallGates` states both halves of the first four rows at once, under RH on the two faces whose
positive side is RH itself; the parity row is `parityWallGate` in
`AmplitudeReadingsCannotResolveTheReceiver`, of the same shape.

This is the admissibility checklist of the field as a theorem: a proposed mechanism presented as a
reading `r` is inadmissible unless `r` separates each pair, and each separation is a concrete
inequality of readings, not a methodological remark. The pairs are independent data — they live on
three different classes of data (shifts, node sets, configurations) and move three different
invariants.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

universe u

/-! ### 1. The depth-`½` pair above a height -/

/-- The on-line lattice with one reflected pair of depth `½` inserted above height `T`. -/
noncomputable def halfPairAbove {L : ℝ} (hL : 0 < L) (T : ℝ) : TemperedZeroConfig :=
  latticeWithPairAbove hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl T

theorem width_halfPairAbove {L : ℝ} (hL : 0 < L) (T : ℝ) : width (halfPairAbove hL T) = 1 / 2 :=
  width_latticeWithPairAbove_half hL T

theorem heightReading_halfPairAbove {L : ℝ} (hL : 0 < L) (T : ℝ) :
    heightReading T (halfPairAbove hL T) = heightReading T (onLineLattice hL) :=
  heightReading_isolatedPairConfig hL _ _ T

/-! ### 2. The gates -/

/-- **The wall gates.** For each face: the pair is identified by the natural reading of that face,
and every reading that resolves the face separates the pair. -/
theorem theWallGates (hRH : RiemannHypothesis) :
    -- Gate 1 — temperedness: the shifted pair wears all the structural flags of `ζ`.
    (structuralFlags (1 / 4) = structuralFlags 0 ∧
      ∀ (O : Type u) (r : ℝ → O), Resolves r PairZerosOnLine → r (1 / 4) ≠ r 0) ∧
    -- Gate 2 — node criticality: deleting the node `4` is a finite modification.
    ((∀ (O : Type u) (r : Set ℕ → O), AsymptoticReading r →
        r (deleteNode 4 {n | IsPrimePow n}) = r {n | IsPrimePow n}) ∧
      ∀ (O : Type u) (r : Set ℕ → O), Resolves r ZeroPoleBlindPositiveOn →
        r (deleteNode 4 {n | IsPrimePow n}) ≠ r {n | IsPrimePow n}) ∧
    -- Gate 3 — trans-Nyquist: at every aperture a depth-`½` lattice is certified positive.
    (∀ (L : ℝ) (hL : 0 < L) (a : ℝ), 0 < a → ∃ Z : TemperedZeroConfig,
      width Z = 1 / 2 ∧ aperturePositivity a Z ∧ aperturePositivity a (onLineLattice hL) ∧
        ∀ (O : Type u) (r : TemperedZeroConfig → O), Resolves r (fun W => width W = 0) →
          r Z ≠ r (onLineLattice hL)) ∧
    -- Gate 4 — no finite carrier: one pair above the height leaves the truncated divisor fixed.
    (∀ (L : ℝ) (hL : 0 < L) (T : ℝ),
      heightReading T (halfPairAbove hL T) = heightReading T (onLineLattice hL) ∧
        ∀ (O : Type u) (r : TemperedZeroConfig → O), Resolves r (fun W => width W = 0) →
          r (halfPairAbove hL T) ≠ r (onLineLattice hL)) := by
  have hzero : PairZerosOnLine 0 := pairZerosOnLine_zero_of_riemannHypothesis hRH
  have hnode : ZeroPoleBlindPositiveOn {n | IsPrimePow n} :=
    riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mp hRH
  refine ⟨⟨structuralFlags_eq (by norm_num), fun _ _ hres heq =>
      not_resolves_of_pair heq hzero not_pairZerosOnLine_quarter hres⟩,
    ⟨fun _ _ hr => invisible_deleteNode_of_asymptoticReading hr 4 _,
      fun _ _ hres heq => not_resolves_of_pair heq hnode
        (not_zeroPoleBlindPositiveOn_deleteNode (by decide : IsPrimePow 4) _) hres⟩,
    fun L hL a ha => ?_, fun L hL T => ⟨heightReading_halfPairAbove hL T, fun _ _ hres heq => ?_⟩⟩
  · obtain ⟨Z, hw, hpos⟩ := exists_width_eq_half_aperturePositivity ha
    refine ⟨Z, hw, hpos, aperturePositivity_onLineLattice hL a, fun _ _ hres heq => ?_⟩
    refine not_resolves_of_pair heq (width_onLineLattice hL) ?_ hres
    rw [hw]
    norm_num
  · refine not_resolves_of_pair heq (width_onLineLattice hL) ?_ hres
    rw [width_halfPairAbove hL T]
    norm_num

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
