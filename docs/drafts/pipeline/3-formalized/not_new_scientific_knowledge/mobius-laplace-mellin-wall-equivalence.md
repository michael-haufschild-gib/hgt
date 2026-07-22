# Möbius–Laplace Mellin wall is exactly RH

## Status

Stage 3 — formalized in Lean 4.

## Claim

`[PAPER-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]` `MobiusLaplaceMellinContinuationWall` is equivalent to
`RiemannHypothesis`.

## Why this claim matters

The existing Lean interface proves wall-to-RH and decay-to-wall. The converse tests whether the
wall contains a source theorem beyond the standard zero-free analytic quotient
`Gamma(s) * (s - 1) / zetaResidueUnit(s)`.

## Corpus audit

- `[CORPUS]` `MobiusLaplaceCriterionFrontier.lean` proves the discrete Laplace transform's Mellin
  identity on `Re(s) > 1`, the decay-to-continuation bridge, wall-to-RH, and decay-to-RH.
- `[CORPUS]` `mobius-half-unit-exponential-moment-rh-law.md` records the equivalent weighted
  `L²` hierarchy and its missing critical `1/2` gain.
- `[CORPUS]` `baez-duarte-critical-mobius-beta-wavelet-law.md` records the exact sequential
  wavelet form and the still-open arithmetic cancellation.

## Literature audit

- `[LITERATURE]` Báez-Duarte's general Möbius-convolution criterion gives RH-equivalent
  `epsilon`-loss estimates and shows an exact critical estimate can force stronger boundary-zero
  restrictions: <https://arxiv.org/abs/math/0504402>.
- `[LITERATURE]` Liflandsky proves the exact bound
  `Phi(x) = O(x^(-1/2))` implies RH and obtains a converse only with additional hypotheses:
  <https://arxiv.org/abs/2607.09797>.
- `[LITERATURE]` Classical Lambert/Möbius inversion gives
  `sum_{k >= 1} Phi(k x) = exp(-x)`; in critical log coordinates its multiplier is
  `zeta(1/2 + i t)`, so inversion is the same critical reciprocal-zeta obstruction.

## Paper-proof obligations

1. Forward implication: cite the dependency-closed corpus theorem.
2. Under RH, prove `zetaResidueUnit` is nonzero on `Re(s) > 1/2`.
3. Define `G(s) = Gamma(s) * (s - 1) / zetaResidueUnit(s)` and prove it analytic on that half-plane.
4. Verify the wall identity by cancellation.

## Hostile-review questions

- Does the quotient construction assume more than RH? It should not: Gamma is analytic on the
  right half-plane and RH supplies denominator nonvanishing.
- Is the wall an independent continuation theorem? No if the converse closes.
- Does this prove the Laplace decay? No; decay remains strictly stronger and source-side.

## Dependency-closed paper proof

### Forward implication

`mobiusLaplaceMellinContinuationWall_implies_riemannHypothesis` is an unconditional corpus theorem.

### Reverse implication

Assume RH. For `Re(s)>1/2`, set

`G(s) = Gamma(s) * (s - 1) / zetaResidueUnit(s)`.

The residue unit is nonzero throughout this half-plane. At `s=1` it equals `1`. Away from `1`, it
equals `(s-1) zeta(s)`. RH gives `xi(s) != 0` on the right half-plane; since `Re(s)>0` and `s!=1`,
the standard Xi/zeta zero equivalence gives `zeta(s)!=0`. Thus both factors are nonzero.

Gamma is analytic because `Re(s)>0`; `s-1` is entire; the residue unit is analytic at every point.
The analytic quotient theorem therefore makes `G` analytic on the right half-plane. Multiplication
by the nonzero denominator gives

`G(s) * zetaResidueUnit(s) = Gamma(s) * (s - 1)`,

which is exactly the wall.

### Dependency audit

Uses RH only through right-half Xi nonvanishing, the corpus Xi/zeta zero equivalence, analyticity of
Gamma on `Re(s)>0`, and the already proved global local analyticity of `zetaResidueUnit`. No decay,
Mellin transform, boundary estimate, simple-zero assumption, or zero-sum hypothesis is used.

## Hostile-review verdict

`[CIRCULAR AS RH SOURCE]`. The wall is the canonical RH-defined analytic quotient. It cannot be
counted as continuation progress unless its witness is constructed independently of RH.

## Expected classification

Classification: `[PAPER-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [CIRCULAR AS RH SOURCE]`.
Positive survivor: the only open content in the requested Möbius lane is a quantitative boundary
estimate or an independently derived continuation, not existence of the RH-defined quotient.

## Lean formalization

- `zetaResidueUnit_ne_zero_of_riemannHypothesis`
- `mobiusLaplaceMellinContinuationWall_of_riemannHypothesis`
- `mobiusLaplaceMellinContinuationWall_iff_riemannHypothesis`
- Targeted verification: `lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceCriterionFrontier.lean`
