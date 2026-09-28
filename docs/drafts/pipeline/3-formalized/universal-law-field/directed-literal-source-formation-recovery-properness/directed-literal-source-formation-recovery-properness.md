# Directed literal-source formation/recovery properness

- **ID:** ULF-DLSFRP-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `SourceFormationHarmonicMechanics` + `BilateralPrimeAnglePacketSewing` +
  `LiteralSourceAdmissibleRankGaugeObstruction`
- **Statement:** On the directed source-rank history, actual marked formation and its exact rank
  recovery are jointly polynomially moderate exactly at unit character norm.

## Big-picture law and RH closure

Algebraic reconstruction is not enough: an information-neutral recovery may be exponentially
ill-conditioned in the source topology.  Literal source formation exposes the missing law without
passing to a bilateral completion.  Its marked response transports by `z^m`; the unique rank
normalization already constructed transports reciprocally by `z^-m`.  Either directed history is
moderate in one radial chamber.  Requiring **formation and recovery to inhabit the same admissible
source category** forces their common boundary `|z|=1`.

This is a joint properness law, not another scalar selector.  Exact reconstruction supplies the
conservation identity, while simultaneous admissibility prevents hiding exponential work in either
encoder or decoder.

Exact RH closure: for any nontrivial zero `rho` and prime `p`, put
`z=p^(1/2-rho)`.  If pre-divisor literal formation proves polynomial rank bounds for both the
actual marked source history and its canonical information-neutral recovery, then the theorem gives
`|z|=1`, hence `Re rho=1/2`.  Global joint properness for every divisor copy implies RH.  Remaining
producer is precisely those two bounds from one occurrence-independent source topology.

## Corpus audit

- `complexCharacterEdge z m=z^m(1-z)` is actual coherent execution of one marked source edge.
- `rankTwelveLiteralSourceMarkedExecution_eq` identifies it with every normalized depth-12 source
  channel at rank `12+j`.
- `rankAnchoredComplexCharacterEdge_eq` gives exact recovery
  `(z^-1)^m complexCharacterEdge z m=1-z`.
- `hardyPositiveHalf` is the zero-extended directed history `e>=0 -> z^(-e)`;
  `bilateralModerate_hardyPositiveHalf_iff` classifies it by `1<=|z|`.
- `hardyHalves_both_moderate_iff` classifies bilateral sewing, but compares positive and negative
  orientations of one eigenhistory rather than actual formation with its recovery on the same
  directed ranks.
- `ConstitutiveCanonicalCoinducedReporter` proves algebraic exact recovery always exists and leaves
  topological admission open.  `ConstitutiveFormationDepthProperness` proves abstract expanding-orbit
  properness but does not instantiate the literal marked edge/recovery pair.
- Search found no joint moderation theorem for `complexCharacterEdge z m` and `(z^-1)^m`, and no
  actual depth-12 formation/recovery properness square.

## Definitions

Let `H_+(z)` denote the positive Hardy history, extended by zero to negative ranks.  For `z != 0`,
define

`R_z = H_+(z)`

and

`F_z = (1-z) H_+(z^-1)`.

`R_z` is forward rank recovery.  `F_z` is forward marked formation.  At every natural rank `m`,

`R_z(m)=(z^-1)^m`,

`F_z(m)=z^m(1-z)=e_m(z)`.

Thus at rank `12+j`, `F_z` is the actual normalized depth-12 marked source execution.

## Theorem

Let `z != 0`.

1. **Literal identification:** for every `m in N`,
   `R_z(m)=(z^-1)^m` and `F_z(m)=complexCharacterEdge z m`.
2. **Joint reconstruction:** `R_z(m)F_z(m)=1-z` for every `m`.
3. **Actual-source square:** for every prime `p` and grade `j`,
   `F_z(12+j)=A_(p,j)(z)` and `R_z(12+j)A_(p,j)(z)=1-z`.
4. **Recovery chamber:** `R_z` is polynomially moderate iff `1<=|z|`.
5. **Formation chamber:** `F_z` is polynomially moderate iff `|z|<=1`.
6. **Joint properness:** `F_z` and `R_z` are both polynomially moderate iff `|z|=1`.
7. **Half-density selection:** for `p>=2`, joint properness at
   `z=p^(1/2-s)` holds iff `Re s=1/2`.

## Proof

On nonnegative integer `m`, the positive Hardy history is `H_+(z)(m)=z^(-m)`, proving the formula
for `R_z`.  Applying this to `z^-1` and using `z != 0` gives

`F_z(m)=(1-z)(z^-1)^(-m)=(1-z)z^m=e_m(z)`.

Multiplication by `R_z(m)` cancels `z^m`, proving item 2.  Existing literal source execution gives
`A_(p,j)(z)=e_(12+j)(z)`, proving item 3.

The positive-Hardy moderation theorem gives item 4.  For item 5, if `z=1`, then `F_z=0` and the
claim is immediate.  If `z!=1`, multiplication by nonzero constant `1-z` preserves and reflects
polynomial moderation, so `F_z` is moderate iff `H_+(z^-1)` is.  By item 4 this is equivalent to

`1<=|z^-1|`,

which, since `z!=0`, is equivalent to `|z|<=1`.  Intersecting items 4 and 5 proves item 6.  Finally,
`|p^(1/2-s)|=1` iff `Re s=1/2`, proving item 7. `[PROVED HERE]`

## Hostile assessment

- **New narrowing:** replaces bilateral-admission premise by two source-native directed bounds:
  actual formation plus its already forced recovery.
- **Not RH:** exact recovery does not prove its own continuity.  Assuming both bounds at Xi zeros is
  equivalent to selection.
- **Killed:** “information-neutral” as sufficient physical admissibility.  Algebraic recovery can
  preserve every datum while exporting exponential cost into the decoder.
- **Positive survivor:** selection is condition-number symmetry of a generated formation/recovery
  pair.  Neither leg alone selects; their exact reciprocal conservation plus common bornology does.
- **Required producer:** construct one pre-divisor source norm/bornology in which both actual marked
  formation and canonical recovery are continuous with polynomial rank control.  Separate,
  zero-dependent norms would make the theorem circular.

## Gates

- [x] 0 -> 1: big-picture law, corpus audit, and exact RH closure stated
- [x] 1 -> 2: dependency-closed proof; `[PROVED HERE]`
- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.DirectedLiteralSourceFormationRecoveryProperness`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only
  and module-only build pass; axioms `[propext, Classical.choice, Quot.sound]`
- [ ] 3 -> 4: publication-ready extraction


## Lean certificate

Module `GaloisForLFunctions.HTGeometry.DirectedLiteralSourceFormationRecoveryProperness` (13 constants, axiom audit clean).

| Claim | Lean declaration |
|-|-|
| 1. literal identification of `R_z`, `F_z` | `literalSourceForwardRecoveryHistory_nat`, `literalSourceForwardFormationHistory_nat` |
| 2. `R_z(m) F_z(m) = 1 - z` | `literalSourceForwardRecovery_mul_formation_nat` |
| 3. actual-source square | `literalSourceForwardFormationHistory_rankTwelve`, `literalSourceForwardRecovery_mul_rankTwelveLiteralSourceMarkedExecution` |
| 4. recovery chamber `1 ≤ ‖z‖` | `bilateralModerate_literalSourceForwardRecoveryHistory_iff` |
| 5. formation chamber `‖z‖ ≤ 1` | `bilateralModerate_literalSourceForwardFormationHistory_iff` |
| 6. joint properness `‖z‖ = 1` | `literalSourceForwardFormationRecovery_jointModerate_iff` |
| 7. half-density selection `Re s = 1/2` | `literalSourceHalfDensityFormationRecovery_jointModerate_iff` |

## Log

- 2026-09-01 — directed joint formation/recovery properness law isolated and paper proof closed.
- 2026-09-01 — Lean literal-source identities, chamber laws, and exact target audit passed.
- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
