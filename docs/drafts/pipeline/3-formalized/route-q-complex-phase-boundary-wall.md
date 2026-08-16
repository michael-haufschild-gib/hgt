# Route Q: complex-phase boundary wall

Status: `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Question

Can complex coefficients repair Route Q's real boundary-packet obstruction?  More precisely, can
one replace the target-aligned fusion `b₊ + b₋` by `α b₊ + β b₋`, retain nonnegative Xi--Weil
energy, and let `(α, β)` converge to `(1, 1)` as separated source packets converge to the two
boundary vectors?

## Exact theorem

Let `w` be the Xi--Hurwitz orientation vector, let `e` be its absolute companion, let
`b₊ = (w + e) / 2`, `b₋ = (w - e) / 2`, and put

`E = ||w||² = -Q(w)`.

The orientation and absolute channels are Hilbert-orthogonal, and the boundary axes are also
Hilbert-orthogonal with `||b₊||² = ||b₋||² = E / 2`.  For every `α, β : ℂ`,

`Q(α b₊ + β b₋) = -Re(conj(α) β) E`.

If RH is false, then `E > 0`, so nonnegative energy is equivalent to
`Re(conj(α) β) ≤ 0`.  Every such pair obeys the sharp coefficient wall

`1 ≤ |α - 1|² + |β - 1|²`,

and consequently the exact Hilbert-space distance formula gives

`E / 2 ≤ ||α b₊ + β b₋ - w||²`.

The coefficient constant is attained, for example, at `(α, β) = (0, 1)`.  Thus complexification
enlarges the null cone but no nonnegative complex-phase fusion can approach the target-aligned
orientation vector off RH.

The sequential form is stronger than a static coefficient calculation.  For arbitrary complex
sequences `αₙ → 1`, `βₙ → 1` and arbitrary separated packet sequences converging to `b₊`, `b₋`,
the fused Xi--Weil energy converges to `-E` and is eventually strictly negative off RH.

## Conjecture loop

### Q-CP1 — complex phases may repair real fusion

Conjecture: the real two-axis obstruction is an artefact of restricting boundary coefficients to
`ℝ`; relative complex phase may retain nonnegative energy while reconstructing orientation.

Result: partially true, then false in the needed form.  Complex coefficients enlarge the
nonnegative cone from opposite real signs to the Hermitian half-space
`Re(conj(α) β) ≤ 0`, but target alignment is `(1, 1)`, where the incidence is strictly positive.

### Q-CP2 — adaptive phases may evade the static obstruction

Conjecture: packet-dependent phases might remain in the nonnegative cone for every finite packet
while converging to `(1, 1)` only in the boundary limit.

Result: false.  The coefficient half-space has squared Euclidean distance exactly one from
`(1, 1)`, producing the sharp Hilbert gap `E / 2`.  Independently, continuity of the packet fusion
energy forces convergence to `-E`, hence eventual negativity off RH.

### Q-CP3 — a phase repair can supply Route Q's missing fixed channel

Conjecture: the doubled or majorant construction can be implemented after the boundary split by a
complex phase choice.

Result: false for every target-convergent phase rule.  Such a rule changes coefficient incidence,
not source geometry, and must cross the positive-incidence region before reaching orientation.

Positive survivor: any viable Route Q repair must be source-native and alter the target geometry
before boundary splitting.  Post-split scalar phases, including packet-dependent complex phases,
cannot provide a cofinal positive channel.

## Higher principle

Null directions need not be cofinal directions.  Complexification can enlarge a null cone without
making it approach a distinguished negative vector.  Here a Hermitian incidence invariant creates
a quantitative phase gap: target alignment lies a fixed positive distance beyond every
nonnegative boundary fusion.  Route Q therefore needs a new source-defined channel, not a more
flexible scalar recombination of the existing two channels.

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationBoundaryComplexPhaseWall.lean`

Principal declarations:

- `xiWeilHilbertQuadratic_boundaryComplexCoordinates`
- `one_le_boundaryComplexCoefficient_displacement`
- `boundaryComplexCoefficient_displacement_sharp`
- `norm_sq_boundaryComplexCoordinates_sub_orientation`
- `orientationEnergy_div_two_le_norm_sq_boundaryComplexCoordinates_sub_orientation_of_nonnegative_of_not_rh`
- `xiWeilHilbertQuadratic_boundaryComplexCoordinates_nonnegative_iff_of_not_rh`
- `eventually_xiSeparatedBoundaryPacket_complexPhaseFusionEnergy_neg_of_not_rh`

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

Verification performed:

- `lake env lean GaloisForLFunctions/RHTower/XiHurwitzOrientationBoundaryComplexPhaseWall.lean`
- `lake build Mathlib.Analysis.InnerProductSpace.l2Space` for the missing prerequisite `.olean`
- `lake build GaloisForLFunctions.RHTower.XiHurwitzOrientationBoundaryComplexPhaseWall`
- scratch `#print axioms` audit: capstones use only `propext`, `Classical.choice`, and `Quot.sound`
- forbidden-token scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`

No umbrella or full-project build was run.

## External novelty audit

Targeted primary-source search found related Weil-form and Hilbert-space treatments, including:

- Masatoshi Suzuki, *The screw line of the Riemann zeta-function and its applications*,
  arXiv:2209.04658.
- Masatoshi Suzuki, *On the Hilbert space derived from the Weil distribution*, arXiv:2301.00421.
- Masatoshi Suzuki, *Aspects of the screw function corresponding to the Riemann zeta function*,
  arXiv:2206.03682.
- Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- Alain Connes and Caterina Consani, *The Scaling Hamiltonian*, arXiv:1910.14368.

No searched source contained this Xi--Hurwitz boundary-coordinate law, its sharp coefficient
distance-one wall, or the adaptive separated-packet complex-phase no-go.  This is not an external
priority claim; novelty remains unverified pending specialist review.

## Remaining open core

This theorem eliminates scalar complex-phase repair only.  It does not construct the source-native
fixed majorant or doubled adjoint channel needed by Route Q, and it does not prove RH.
