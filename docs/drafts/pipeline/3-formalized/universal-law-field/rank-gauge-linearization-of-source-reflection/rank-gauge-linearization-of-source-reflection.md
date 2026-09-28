# Rank-gauge linearization of literal-source reflection

- **ID:** ULF-RGLSR-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `SourceFormationHarmonicMechanics` + `LiteralSourceReflectionDeterminantCocycle`
- **Statement:** Canonical rank normalization makes every marked source edge equal to `1-z` and
  conjugates its functional-equation multiplier from an odd rank-dependent power to `-z^-1`.

## Big-picture law and RH closure

Universal formation geometry must live on gauge classes of marked source execution, not raw
coordinates of a rank-dependent frame.  A rate that changes after multiplication of rank `m` by
the already present character monomial `z^-m` is not curvature, holonomy, or noncompactness; it is
connection coefficient in a chosen trivialization.

The previously proved quadratic reflection exponent would close RH only if literal pre-divisor
formation forced that raw frame and a subquadratic bound in it.  This theorem shows the exponent is
removed by the source's own rank normalization.  Therefore that proposed closure is invalid.
The surviving classifier is gauge-normal reflection weight `-z^-1`: for every nonempty block its
norm is one exactly when `|z|=1`.  To close RH, a future law must either prove this residual character
unitary from literal arithmetic, or construct a mixed additive/multiplicative invariant that no
source-legal rank gauge can remove.

## Corpus audit

- `complexCharacterEdge z m = z^m-z^(m+1)` and
  `complexCharacterEdge_succ` expose `z^m` as predictable rank transport.
- `rankTwelveSource_character_execution` identifies this edge with the actual two marked
  coefficients of each normalized depth-12 source channel.
- `complexCharacterEdge_inv_eq_reflectionMultiplier_mul` gives raw reflection multiplier
  `-(z^-1)^(2m+1)` and its quadratic block accumulation.
- `deningerExponentExceptionalLineReflectionCoefficient_eq_gaugeCoboundary` independently proves
  that a literal reflection coefficient can be pure two-sheet gauge and hence carry no horizontal
  holonomy.
- `rankOnePicardClass_eq_one_iff_coboundary` records the general corpus rule that coboundary
  representatives have trivial rank-one class.
- Search found no existing theorem normalizing `complexCharacterEdge` by `z^-m`, no pointwise
  conjugation of its odd-power multiplier, and no literal-source block linearization.

## Definitions

For `z != 0` and rank `m`, define

`e_m(z) = z^m-z^(m+1)`,

`a_m(z) = (z^-1)^m e_m(z)`,

`c_m(z) = -(z^-1)^(2m+1)`, and `r(z)=-z^-1`.

For the actual depth-12 source channel `A_(p,j)(z)`, define

`A^a_(p,j)(z)=(z^-1)^(12+j) A_(p,j)(z)`.

## Theorem

Let `z != 0`.

1. **Rank normal form:** `a_m(z)=1-z`; hence `a_m(z)` is independent of `m`.
2. **Gauge-normal reflection:** `a_m(z^-1)=r(z)a_m(z)`.
3. **Exact multiplier conjugation:** `z^m c_m(z) z^m=r(z)`.
4. **Linear block law:** for every `M,n`,
   `product_(j<n) a_(M+j)(z^-1)=r(z)^n product_(j<n) a_(M+j)(z)`.
5. **Quadratic-to-linear coboundary identity:** if
   `G_(M,n)(z)=product_(j<n) z^(M+j)`, then
   `G_(M,n)(z) C_(M,n)(z) G_(M,n)(z)=r(z)^n`, where `C` is the raw quadratic
   block multiplier.
6. **Literal-source normal form:** for every prime `p`,
   `A^a_(p,j)(z)=1-z`, and its reflected blocks obey item 4 independently of `p,M`.
7. **Residual phase classifier:** if `n>0`, `|r(z)^n|=1` iff `|z|=1`.  For
   prime-radial `z=p^nu`, this is equivalent to `nu=0`.

## Proof

Factor `e_m(z)=z^m(1-z)`.  Since `z != 0`,

`a_m(z)=(z^-1)^m z^m(1-z)=1-z`,

proving item 1.  Applying item 1 at `z^-1` gives

`a_m(z^-1)=1-z^-1=-z^-1(1-z)=r(z)a_m(z)`,

which is item 2.

For item 3, split `2m+1=m+1+m` and cancel the two pairs
`z^m(z^-1)^m=1`; the sole uncancelled factor is `-z^-1`.  Multiplying item 2
over `j=0,...,n-1` proves item 4.  Multiplying item 3 over the same block and
using commutativity regroups the two gauge products around the raw multiplier,
proving item 5.  Thus the raw exponent `n(2M+n)` differs from the invariant
linear exponent `n` by exact change of rank frame.

For item 6, `rankTwelveSource_character_execution` substitutes
`A_(p,j)(z)=e_(12+j)(z)` into item 1 and then item 4.  Finally,
`|r(z)^n|=|z|^(-n)`.  A nonzero natural power of a nonnegative real is one
exactly when its base is one, giving item 7.  At `z=p^nu`, positivity and
injectivity of real exponentiation for prime `p>1` give `p^nu=1` iff `nu=0`.
`[PROVED HERE]`

## Hostile assessment

- **Killed:** quadratic growth as gauge-invariant reflection curvature, conditioning, or selection
  pressure.
- **Why:** a source-visible monomial rank gauge converts it exactly to linear growth.
- **Positive survivor:** unique rank-independent normal form of the marked edge and constant
  residual FE character `-z^-1`; unit norm remains exact critical-line classifier.
- **Open core:** derive residual unitarity before Xi specialization, or find mixed cross-effect
  invariant under all source-legal rank gauges.  One-leg determinant growth cannot do this.

## Gates

- [x] 0 → 1: exact RH closure and failure mechanism stated; corpus search completed
- [x] 1 → 2: dependency-closed algebraic proof; `[PROVED HERE]`
- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.LiteralSourceReflectionRankGaugeLinearization`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only
  build pass; axioms `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4: publication-ready extraction


## Lean certificate

Module `GaloisForLFunctions.HTGeometry.LiteralSourceReflectionRankGaugeLinearization` (20 constants, axiom audit clean).

| Claim | Lean declaration |
|-|-|
| 1. rank normal form | `rankAnchoredComplexCharacterEdge_eq`, `rankAnchoredComplexCharacterEdge_rank_independent` |
| 2. gauge-normal reflection | `rankAnchoredComplexCharacterEdge_inv_eq` |
| 3. multiplier conjugation | `complexCharacterEdgeReflectionMultiplier_rankGaugeConjugation` |
| 4. linear block law | `prod_rankAnchoredComplexCharacterEdge_inv_eq` |
| 5. quadratic-to-linear coboundary | `reflectionBlockMultiplier_rankGaugeConjugation` |
| 6. literal-source normal form | `rankTwelveLiteralSourceRankAnchoredExecution_eq`, `prod_rankTwelveLiteralSourceRankAnchoredExecution_inv_eq` |
| 7. residual phase classifier | `norm_rankAnchoredReflectionBlockMultiplier_eq_one_iff`, `primeRadial_norm_rankAnchoredReflectionBlockMultiplier_eq_one_iff` |

## Log

- 2026-09-01 — hostile audit found raw quadratic exponent is rank-gauge artefact; paper proof closed.
- 2026-09-01 — Lean formalization and target-only build passed.
- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
