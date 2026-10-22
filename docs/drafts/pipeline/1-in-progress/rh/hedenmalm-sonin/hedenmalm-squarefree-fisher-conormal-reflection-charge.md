# Hedenmalm squarefree Fisher conormal reflection charge

- **Label:** `P-G137`
- **Route:** P
- **Parents:** `P-G136`, `HedenmalmGammaSewnSquarefreeFisherConormalResidue`, `XiReflectionSelfIntersectionCharge`
- **Stage:** 1-in-progress
- **Type:** theorem (Lean) / source-intrinsic quantization / exact global bridge
- **Status:** `[PAPER-PROVED] [LEAN EXACT BUILD GREEN] [NOT RH]`

## Conjecture tested

P-G136 proves continuous Cartan/Weyl defect cannot see discrete Xi collision charge near critical
wall. Test whether squarefree Fisher conormal residue supplies missing integer intrinsically.

Use fixed source chart

```text
sigma = 2, epsilon = 1, u_rho = rho - 2.
```

Define source multiplicity as analytic order of squarefree boundary overlap at `u_rho`. Define
window charge as twice sum of squared source multiplicities over strict-right strip zeros.

## Required theorem package

1. Source multiplicity equals full Xi analytic multiplicity throughout strict-right strip.
2. Punctured Fisher quotient residue at every such zero equals twice source multiplicity.
3. Global source charge equals `xiReflectionSelfIntersectionCharge` coefficient-for-coefficient.
4. Same strict-two endpoint follows, while honest boundary records missing unconditional source
   estimate rather than relabeling it RH.

## Heavy conjecture loop

### P-G137.A — source overlap order crosses quantization wall

The affine squarefree overlap already carries complete Xi divisor order. Fixed chart must preserve
that order without horizontal normalization or prime-scale division.

**Proved.** The fixed chart has source analytic order exactly equal to Xi analytic order throughout
strict-right strip. No horizontal normalization enters definition.

### P-G137.B — Fisher residue generates integer locally

At each strict-right zero, logarithmic Fisher quotient must have simple-pole residue exactly twice
source multiplicity.

**Proved.** At every source zero, punctured Fisher quotient tends to `2m`, where `m` is source
overlap order. Integer multiplicity is generated as logarithmic conormal residue.

### P-G137.C — local residues globalize to reflection charge

Squared source multiplicities over finite right-window support must equal canonical reflection
self-intersection charge exactly.

**Proved.** Strict-right source support defined by zeros of squarefree partition is finite in every
height window and exactly equals strict-right Xi support. Twice sum of squared source overlap orders
over that source-defined support equals `xiReflectionSelfIntersectionCharge`.

## Non-theatre gate

Card succeeds only if source overlap supplies multiplicity, Fisher quotient realizes it as local
residue, and finite-window sum matches existing discrete reflection charge exactly. Merely defining
source multiplicity using `analyticOrderAt xi`, or restating RH endpoint, does not count.

## Gates

- [x] 0 → 1: source chart and exact coefficient target fixed
- [x] 1 → 2: dependency-closed paper proof
- [ ] 2 → 3: Lean module, exact build, lint, axiom audit, umbrella wiring
- [ ] 3 → 4: publication-ready extraction

## Honest boundary

P-G137 is not RH. Even if exact source representation is proved, unconditional strict-two control
still requires source-only conservation, positivity, or cancellation law bounding squared conormal
residue charge.

## Positive survivor

Route P now has a genuinely source-defined discrete charge: its support uses squarefree-partition
zeros and its weight uses squarefree-overlap order. Fisher residue produces twice that order
locally, and exact global comparison recovers canonical reflection self-intersection. P-G136's
quantization wall is crossed by source meromorphy, not by singular post-processing of a continuous
Weyl defect.

New open core is narrower and source-side: prove an unconditional conservation, positivity, or
cancellation law forcing this squarefree Fisher charge below two on cofinal height windows.

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmSquarefreeFisherConormalReflectionCharge.lean`

Headline declarations:

- `hedenmalmSquarefreeRightSourceZeros_eq`;
- `hedenmalmSquarefreeConormalMultiplicity_eq_xi`;
- `tendsto_hedenmalmSquarefreeFisherQuotient_residue_eq_two_mul_sourceMultiplicity`;
- `hedenmalmSquarefreeFisherReflectionCharge_eq`.

## Log

- 2026-08-13 — opened after P-G136 proved singular quantization is necessary and identified
  logarithmic residue/order current as viable producer.
- 2026-08-13 — source support, source multiplicity, local Fisher residue, and global exact charge
  bridge paper-proved and formalized; direct `lake env lean` green.
- 2026-08-13 — umbrella import wired; exact leaf build passed (`12970/12970`) after restoring one
  missing shared dependency artifact; headline declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`. Lint and final umbrella build remain pending.
