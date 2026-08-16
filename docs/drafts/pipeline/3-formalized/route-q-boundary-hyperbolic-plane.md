# Route Q exact boundary hyperbolic plane

- **ID:** `route-q-boundary-hyperbolic-plane`
- **Stage:** 3-formalized
- **Type:** THEOREM / exact boundary-cone classification
- **Routes:** Q primary
- **Source:** Xi--Hurwitz orientation carrier and separated continued prime--Gamma packets

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Theorem Q-HYP

Let `w` be Xi--Hurwitz orientation vector, `e` its reflection-even absolute companion, and

```text
b₊=(w+e)/2,    b₋=(w-e)/2,    E=||w||^2.
```

The two exact null-boundary witnesses satisfy

```text
b₊+b₋=w,       b₊-b₋=e,
J b₊=-b₋,      J b₋=-b₊,
2||b₊||^2=E,   2||b₋||^2=E.
```

Their full real two-coordinate span has exact Weil quadratic law

```text
Q(alpha b₊ + beta b₋) = -alpha beta E.                    (1)
```

If RH is false, `E>0`, hence:

- same-sign coordinates are exactly negative;
- opposite-sign coordinates are exactly positive;
- coordinate axes are complete null cone in this plane.

For arbitrary separated-packet reconstructions `P_n -> b₊`, `Q_n -> b₋`, scaled fusion energies
converge to right side of `(1)`. Off RH, every same-sign fusion is eventually strictly negative
and every opposite-sign fusion eventually strictly positive, regardless of diagonal packet-energy
behavior.

Statements are unconditional closed Lean theorems. Sign classifications use `not RH` only as a
local implication premise via already-proved equivalence `not RH <-> E>0`; no added axiom or RH
assumption enters corpus.

## Theorem Q-TRANSVERSE

Let `J` be Xi reflection and let `z` be real-orthogonal to both canonical boundary axes `w,e`.
Then the boundary plane and transverse sector decouple exactly:

```text
Q(alpha b₊ + beta b₋ + z) = -alpha beta E + Q(z).          (2)
```

Writing fixed and anti-fixed transverse channel energies through `z+Jz` and `z-Jz`, nonnegative
source fusion forces the sharp budget

```text
4 alpha beta E + ||z-Jz||^2 <= ||z+Jz||^2.                (3)
```

Thus fixed transverse energy must pay both full hyperbolic target defect and every anti-fixed
transverse contribution. In particular a fixed transverse vector orthogonal to `e` gives exact
energy `||z||^2-E` in orientation direction, while an anti-fixed vector orthogonal to `w` gives
`-E-||z||^2` and can never repair false-RH negativity.

## Heavy conjecture loop

### Q-H1 — exact boundary multiplicity is only phase nonuniqueness

**Conjecture.** Two closest null witnesses merely show metric projection is nonunique; their span
carries no sharper source information.

**Attack.** Compute reflection action on each boundary and expand Weil quadratic form on arbitrary
real coordinates. Boundary nullity kills diagonal terms while reflected exchange fixes cross term.

**Verdict:** false. Expansion collapses to exact hyperbolic law `(1)`.

### Q-H2 — two positive-side boundary reconstructions can fuse toward orientation target

**Conjecture.** Since genuine separated packets approach both boundaries from positive source
energy, adding the two sequences may reconstruct `w=b₊+b₋` without further arithmetic input.

**Attack.** Set `alpha=beta=1` in `(1)`. Limit energy is `-E`, strictly negative off RH. Continuity
makes every sufficiently late same-sign packet fusion negative independently of how each diagonal
energy tends to zero.

**Verdict:** false. Positive diagonal saturation does not control mixed incidence and cannot fuse
toward target within source-positive cone.

### Q-H3 — rescaling boundaries can repair same-phase fusion

**Conjecture.** Unequal positive coefficients may keep fusion nonnegative while retaining both
orientation components.

**Attack.** `(1)` depends only on coefficient product. Every nonzero same-sign pair is negative off
RH; magnitude does not change cone component.

**Verdict:** false. Entire same-sign quadrant is forbidden asymptotically.

### Q-H4 — opposite phase is useless because it moves away from target

**Conjecture.** Opposite-sign fusion is only another negative result and supplies no lawful design
constraint.

**Attack.** Exact sign classification shows opposite-sign quadrant is precisely positive cone in
boundary plane. It exposes missing quantity: a successful source-first selector approaching
orientation direction must contribute a transverse mixed-incidence term that compensates the
fixed `-alpha beta E` boundary-plane defect.

**Verdict:** positive survivor. Route Q needs transverse compensation outside diagonal boundary
saturation, not stronger approximation to either boundary ray.

### Q-H5 — arbitrary transverse mass can repair target fusion

**Conjecture.** Once packets carry any nonzero component outside boundary plane, its norm can be
used as undirected compensation for same-sign target fusion.

**Attack.** Polarize `Q` against boundary coordinates and decompose transverse Krein energy into
fixed/anti-fixed reflection channels. Orthogonality removes only mixed boundary terms, giving
`(2)`; Clifford balance converts nonnegativity into `(3)`.

**Verdict:** false. Anti-fixed mass worsens defect. Only fixed transverse channel can compensate,
and its required squared norm is quantitatively at least hyperbolic defect plus anti-fixed cost.

## Higher universal principle

**Null source rays can have a hyperbolic mixed defect invisible to diagonal approximation, and its
repair is reflection-polarized.** Each
boundary phase is individually approachable from positive source chamber, yet their target-aligned
fusion crosses into negative cone because cross incidence survives while diagonal energies vanish.
This is source-selection obstruction, not approximation obstruction.

Consequently Route Q must retain a mixed theta/prime--Gamma incidence coordinate before Hilbert
closure. Any construction recording only two diagonal source energies, distances to boundary, or
independent packet convergence has discarded exactly the compensation it needs.

## Positive survivor and remaining bridge

Strongest survivor is exact lower-dimensional target law `(1)`, full transverse law `(2)`, and
channel budget `(3)`. A lawful Q advance must build, from finite source data, one cofinal selector
converging toward `w` whose fixed transverse channel pays full orientation defect and every
anti-fixed contribution. Mere transverse norm or unpolarized mixed incidence is insufficient.
Existing equivalent formulation remains cofinal nonnegative recurrence along one unconditional
separated reconstruction of `w`; Q-HYP explains why independent boundary saturation cannot prove
that recurrence.

This does not prove such compensation exists and does not prove RH.

## External novelty audit

Prior Route-Q audit covers Suzuki's Weil-distribution Hilbert spaces, screw-line norm criteria, and
model-space formulations. Targeted corpus/literature collision searches found no external theorem
identifying Xi--Hurwitz exact boundary witnesses as a hyperbolic plane whose arbitrary separated
prime--Gamma packet reconstructions have forced eventual fusion sign. No external priority claim is
made; novelty remains unverified.

## Gates

- [x] 0 -> 1: boundary-flatness and source-fusion conjectures attacked
- [x] 1 -> 2: dependency-closed proof and prior novelty audit integrated
- [x] 2 -> 3: unconditional Lean proof, direct check, exact leaf build, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Modules:

- `formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationBoundaryHyperbolicPlane.lean`;
- `formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationBoundaryTransverseCompensation.lean`.

Capstones:

- `xiHurwitzOrientationBoundaryPlus_sub_boundaryMinus`;
- `xiWeilLineConj_boundaryPlus` and `xiWeilLineConj_boundaryMinus`;
- `two_mul_norm_sq_xiHurwitzOrientationBoundaryPlus` and its minus analogue;
- `xiWeilHilbertQuadratic_boundaryCoordinates`;
- three off-RH cone classification equivalences;
- `tendsto_xiSeparatedBoundaryPacket_scaledFusionEnergy`;
- eventual negative/positive scaled-fusion theorems;
- `xiWeilHilbertQuadratic_boundaryCoordinates_add_transverse`;
- `four_mul_orientationEnergy_add_oddChannel_le_evenChannel_of_transverse_weil_nonnegative`;
- fixed- and anti-fixed orientation compensation corollaries.

Module passed direct `lake env lean` and exact leaf `lake build`. Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Targeted forbidden declaration scan is clean.
Module is imported by `RHTower.lean`; no umbrella or full-project build was run.

## Log

- 2026-08-16 — Exact reflection exchange and half-energy norms proved.
- 2026-08-16 — Boundary-coordinate hyperbolic quadratic law proved.
- 2026-08-16 — Off-RH null/positive/negative cone classification proved.
- 2026-08-16 — Eventual sign for arbitrary scaled separated-packet fusions proved.
- 2026-08-16 — Exact transverse decoupling and sharp fixed-versus-anti-fixed channel budget proved.
