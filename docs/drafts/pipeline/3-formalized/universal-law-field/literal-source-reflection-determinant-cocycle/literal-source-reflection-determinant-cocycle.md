# Literal-source reflection determinant cocycle

- **ID:** ULF-LSRDC-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `LiteralSourceDeterminantRankTower` + `SourceFormationHarmonicMechanics`
- **Statement:** Functional-equation inversion acts on each canonical new-channel execution by an
  exact odd-power multiplier; accumulated multiplier across `n` source ticks has quadratic exponent.

## Big-picture law and RH closure

Rank-growing source formation creates one pointed determinant increment per tick.  Functional
equation does not act on abstract rank index: source tower is parameter-free.  Nontrivial action
appears only when canonical new-channel generator is executed by a spectral character `z`.  Higher
law sought here is therefore not determinant holonomy of bare tower, but cocycle of **marked source
execution** under inversion `z ↦ z^-1`.

For prime-radial character `z=p^nu`, unit norm of any nonempty accumulated cocycle is equivalent to
`nu=0`.  Under existing identification `nu = 1/2-Re(rho)`, a pre-divisor theorem forcing unit-norm
source reflection transport would close RH through existing horizontal-charge receivers.

This card proves exact cocycle and classifier in the raw source-rank frame, not unit-norm premise.
`RankGaugeLinearizationOfSourceReflection` subsequently proves its quadratic exponent is conjugated
to a linear exponent by source-visible rank normalization; quadratic rate is therefore not an
invariant selector.  Corpus also warns that
information-neutral FE recovery is not defect-neutral and that finite reflected source displacement
collapses cofinally off line with divergent inverse conditioning.  Thus unit norm cannot be inferred
from involutivity, common recovery, or ordinary completion.

## Corpus audit

- `rankTwelveSource_character_execution`: actual channel `j+1` executes as
  `complexCharacterEdge z (12+j)`.
- `LiteralSourceDeterminantRankTower`: channel `j+1` is canonical generator of a new pointed
  one-dimensional quotient increment.
- `involutiveFormationLift_informationNeutral`: FE lift through common recovery preserves KL work
  but explicitly does not annihilate endpoint separation.
- `countermodel_functional_equation_neutral`: involution can preserve observer/recovery and act by
  `-1` on nonzero formation charge.
- `tendsto_completeResolutionReflectionSourceDisplacement_zero`: ordinary cofinal `l1` topology
  erases finite off-line displacement while inverse conditioning diverges.
- Corpus search found no theorem for inverse reflection of `complexCharacterEdge` or quadratic
  accumulated exponent below.

## Definitions

For `z ≠ 0` and source exponent edge `m`, put

`e_m(z)=z^m-z^(m+1)`,

`c_m(z)=-(z^-1)^(2m+1)`.

For a block starting at `M` with length `n`, put

`C_(M,n)(z)=product_(j=0)^(n-1) c_(M+j)(z)`.

The actual depth-12 channel execution at prime `p` is

`A_(p,j)(z)=a_(j+1)(p^(12+j)) z^(12+j)
             +a_(j+1)(p^(13+j)) z^(13+j)`.

## Theorem

Let `z ≠ 0`.

1. **One-tick reflection law:**
   `e_m(z^-1)=c_m(z)e_m(z)`.
2. **Quadratic accumulation:**
   `C_(M,n)(z)=(-1)^n (z^-1)^(n(2M+n))`.
3. **Block reflection law:**
   `product_j e_(M+j)(z^-1)
      =(-1)^n (z^-1)^(n(2M+n)) product_j e_(M+j)(z)`.
4. **Literal-source law:** for every prime `p`, the same formula holds with
   `e_(12+M+j)` replaced by actual `A_(p,M+j)`.
5. **Phase classifier:** if `n>0`,
   `norm(C_(M,n)(z))=1 ↔ norm(z)=1`.
6. **Prime-radial prediction:** for prime `p` and real `nu`, if `n>0`,
   `norm(C_(M,n)(p^nu))=1 ↔ nu=0`.

## Proof

For item 1,

`e_m(z^-1)=z^-m-z^-(m+1)=z^-(m+1)(z-1)`

`= -z^-(2m+1) z^m(1-z)=c_m(z)e_m(z)`.

For item 2, multiply itemwise.  Signs give `(-1)^n`.  Exponents add, and

`sum_(j=0)^(n-1) (2(M+j)+1)=2nM+n^2=n(2M+n)`.

Item 3 follows by multiplying item 1 over block and applying item 2.

For item 4, `rankTwelveSource_character_execution` identifies actual marked two-coefficient
execution exactly with `e_(12+j)(z)` in both orientations.  Substitute item 3 with base `12+M`.
No quotient functional is asserted: execution is coordinate of canonical marked new-channel
representative, not a map descending through arbitrary quotient representatives.

For item 5, item 2 and multiplicativity of norm give

`norm(C_(M,n)(z))=norm(z)^(-n(2M+n))`.

When `n>0`, exponent `n(2M+n)` is positive.  Since `norm(z)>0`, a positive real number has a
nonzero natural power equal to one exactly when base equals one.  Inversion preserves equality to
one, proving item 5.

For item 6, `p>1` and `norm(p^nu)=p^nu`; strict injectivity of real exponentiation at base
`p != 1` gives `p^nu=1 ↔ nu=0`.  Combine with item 5.  `[PROVED HERE]`

## Hostile assessment

- Exact source-specific law fuses rank creation, prime-edge execution, FE inversion, and cofinal
  accumulation.
- It predicts quadratic reflection conditioning only in the raw rank frame; exact rank-gauge
  linearization proves this rate is not invariant.
- It remains a faithful coordinate of horizontal grade, not source proof of grade zero.
- FE involutivity only pairs cocycle with inverse and is compatible with every nonzero grade.
- Any claimed RH use must independently prove unit norm or subquadratic conditioning from literal
  pre-divisor completion; assuming it is circular.

## Gates

- [x] 0 → 1: source-pure definitions; corpus audit; exact RH closure and circularity boundary
- [x] 1 → 2: complete dependency-closed proof; `[PROVED HERE]`
- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.LiteralSourceReflectionDeterminantCocycle`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only
  pass; axioms `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4: publication-ready extraction


## Lean certificate

Module `GaloisForLFunctions.HTGeometry.LiteralSourceReflectionDeterminantCocycle` (16 constants, axiom audit clean).

| Claim | Lean declaration |
|-|-|
| 1. one-tick law | `complexCharacterEdge_inv_eq_reflectionMultiplier_mul` |
| 2. quadratic accumulation | `complexCharacterEdgeReflectionBlockMultiplier_eq` |
| 3. block law | `prod_complexCharacterEdge_inv_eq_reflectionBlockMultiplier_mul` |
| 4. literal-source law | `rankTwelveLiteralSourceMarkedExecution_eq`, `prod_rankTwelveLiteralSourceMarkedExecution_inv_eq` |
| 5. phase classifier | `norm_complexCharacterEdgeReflectionBlockMultiplier_eq_one_iff` |
| 6. prime-radial prediction | `primeRadial_norm_reflectionBlockMultiplier_eq_one_iff` |

## Log

- 2026-09-01 — conjectured from literal rank tower; corpus search negative; hostile scope narrowed
  from quotient functional to marked canonical generator; paper proof closed.
- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
