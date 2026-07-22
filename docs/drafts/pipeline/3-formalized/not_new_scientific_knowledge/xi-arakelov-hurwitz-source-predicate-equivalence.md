# Xi/Arakelov–Hurwitz source predicate is exactly RH

## Status

Stage 3 — formalized in Lean 4.

## Claim

`[PAPER-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]` The formal predicate
`XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter` is equivalent to
`RiemannHypothesis`.

## Why this claim matters

The existing Lean interface proves the forward implication. The converse determines whether the
algebraic-character condition is an independently producible source theorem or an RH-shaped
certificate whose right-half quantifier becomes empty under RH.

## Corpus audit

- `[CORPUS]` `XiArakelovHurwitzDependenceCollision.lean` proves dependence is exactly equality of
  the monodromy scalar and transfers algebraic dependence to algebraicity of the Arakelov coordinate.
- `[CORPUS]` `XiArakelovHurwitzAlgebraicityCollision.lean` proves joint algebraicity forces a
  right-half Xi divisor point to be real, contradicting the open-strip zero-free theorem.
- `[CORPUS]` `XiHurwitzFEAnchorCircuitCollision.lean` proves the fixed half-anchor circuit is
  independent at every Xi zero and the FE/Schwarz dependence condition is pointwise equivalent to
  the critical-line equation.
- `[CORPUS]` Existing Arakelov-power and finite-atlas cards identify no arithmetic source provider.

## Literature audit

- `[LITERATURE]` Lagarias–Rains establish the two-variable Arakelov zeta framework and functional
  equation, but no algebraicity theorem for individual zeta zeros:
  <https://arxiv.org/abs/math/0104176>.
- `[LITERATURE]` Gun–Murty–Rath emphasize that the algebraic nature of nontrivial zeta zeros remains
  unknown: <https://doi.org/10.2140/ant.2018.12.1653>.
- `[LITERATURE]` Gelfond–Schneider supplies the transcendence collision used by the corpus; it does
  not supply algebraicity of either coordinate.

## Paper-proof obligations

1. Forward implication: cite the dependency-closed corpus theorem.
2. Reverse implication: under RH, show no `XiDivisorSupport` point has real part greater than `1/2`;
   eliminate the universal predicate's input by contradiction.
3. Audit subtype coercions and the bridge from divisor support to `xi rho = 0`.

## Hostile-review questions

- Is the reverse implication merely classical vacuity? Yes; that is the classification's point.
- Does the predicate encode any source-side construction? No.
- Can a fixed half-anchor repair it? No; the corpus proves unconditional independence.
- Can FE/Schwarz dependence repair it? No; that condition is already RH pointwise.

## Dependency-closed paper proof

### Forward implication

`riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter`
is an unconditional corpus theorem.

### Reverse implication

Assume RH. Let `rho : XiDivisorSupport` and suppose `1/2 < Re(rho)`. Divisor-support membership
gives `xi(rho) = 0`. The real-part inequality gives `rho ∈ rightHalf`. The right-half zero-free
form of RH contradicts those two facts. Hence there is no input to the universal source predicate,
so its algebraicity and dependence conclusion follows by false elimination.

### Dependency audit

Uses only the definition of the predicate, `xi_eq_zero_of_mem_divisor_support`, and
`rh_iff_xi_ne_zero_right`. No algebraicity, choice, anchor construction, or unproved analytic
claim enters the reverse implication.

## Hostile-review verdict

`[CIRCULAR AS RH SOURCE]`. Both directions are exact. The reverse direction proves the requested
right-half algebraic dependence has no source content under RH: its domain is empty.

## Expected classification

Classification: `[PAPER-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [CIRCULAR AS RH SOURCE]`.
Strongest positive survivor: exact no-go theorem that this algebraic-character interface is a
certificate equivalent to RH, not an independent route to RH.

## Lean formalization

- `xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter_of_riemannHypothesis`
- `xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter_iff_riemannHypothesis`
- Targeted verification: `lake env lean GaloisForLFunctions/RHTower/XiArakelovHurwitzDependenceCollision.lean`
