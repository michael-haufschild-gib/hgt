# Route-P irregular-RH full-carrier weak-trace no-go

- **ID:** IRH-P-FULL-WEAK-TRACE-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** full all-depth Route-P prime-harmonic balanced `det₂` carrier; irregular-RH Fredholm transport
- **Statement:** Full Route-P carrier is weak Schatten-one, so no bounded channel mixing followed by a Schatten-one correction can relocate it to ordered Xi reciprocal spectrum.

## Goal

Remove depth-zero caveat from basis-independent mixing obstruction. Classify complete
prime-by-depth Stokes operator, including every positive-depth mode, at exact operator-ideal scale.

## Gates

- [x] 0 → 1 in-progress: full source operator and channel class fixed; no Xi-derived source data
- [x] 1 → 2 fully-proven: complete paper proof below; `[PROVED HERE]`; no open dependency
- [x] 2 → 3 formalized: Lean theorem, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone note and external novelty review pending

## Audit

- `[CORPUS]` `routePPrimitiveGammaJuliaLogBalancedOperator` is literal all-depth balanced
  genus-one Stokes carrier with multipliers `±8w(p,e)`.
- `[CORPUS]` `routePPrimitiveGammaJuliaDepthZeroSignedOperator_memWeakSchattenClass_one`
  proves signed `e=0` face with multipliers `±2/p` lies in weak `S₁`.
- `[CORPUS]` `summable_routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight` proves
  `sum_{p,k>=0} w(p,k+1)<infinity`; divergence is completely localized at depth zero.
- `[CORPUS]` `realSummableDiagonalOperator_memSchattenClass_one` promotes an absolutely
  summable real diagonal to a Schatten-one operator.
- `[CORPUS]` `lpScalarInjection` and `lpCoordinatePullback` give bounded zero-extension and
  restriction along an injective coordinate map.
- `[CORPUS]` Searches for `RouteP balanced operator depth zero projection tail`, `RouteP full
  weak Schatten`, and `RouteP positive depth tail trace class` found components above but no
  full-carrier weak-ideal theorem or Xi relocation consequence.
- `[LITERATURE]` Bertola's Malgrange/IIKS construction and Bothner's Hankel-composition RH
  construction use Fredholm trace-class corrections. Regularized `det₂` theory permits a
  Hilbert--Schmidt base, but does not make trace-class perturbations cross weak-ideal boundaries.
- `[LITERATURE]` Targeted searches for irregular-RH, Hilbert--Schmidt `det₂`, weak trace class,
  and zeta prime spectra found no all-depth Route-P/Xi comparison.
- `[NOVELTY STATUS]` `[BRIDGE]`: standard ideal mechanics plus corpus-specific all-depth Stokes
  decomposition; closes exact internal open core without external-priority claim.

## Exact claim

Let `B` be full Route-P balanced operator on

```text
H_P = ell²(Fin 2 × (Primes × Nat)),
```

with diagonal `±8w(p,e)`. Let `X` be ordered signed Xi reciprocal operator on signed-prime
Hilbert space `H_X`. Then

```text
B ∈ S_{1,∞},
for every bounded A : H_P → H_X and C : H_X → H_P,
X - A B C ∉ S₁.
```

All quantifiers are unconditional. `A,C` may be non-diagonal, non-unitary, and infinite rank.

## Complete paper proof `[PROVED HERE]`

Embed signed prime indices into full prime-depth indices by

```text
inl p ↦ (0,(p,0)),
inr p ↦ (1,(p,0)).
```

Let `J : H_X→H_P` be zero-extension and `Q=J* : H_P→H_X` coordinate restriction. Both are
bounded. If `P₀` is signed depth-zero Route-P operator, then

```text
D₀ = J P₀ Q
```

is exactly full carrier restricted to `e=0`. Since `P₀∈S_{1,∞}` and weak `S₁` is preserved by
bounded left/right composition, `D₀∈S_{1,∞}`.

Let `R=B-D₀`. It is diagonal, vanishes at `e=0`, and has entries `±8w(p,e)` for `e>=1`. Therefore

```text
sum_{orientation,p,e} |R(orientation,p,e)|
  = 16 sum_{p,e>=1} w(p,e)
  = 16 sum_{p,k>=0} w(p,k+1)
  < infinity.
```

Last inequality is corpus theorem
`summable_routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight`. Absolute diagonal
factorization makes `R∈S₁`, hence `R∈S_{1,∞}`. Additivity yields

```text
B = D₀+R ∈ S_{1,∞}.
```

For arbitrary bounded `A,C`, ideal property gives `ABC∈S_{1,∞}`. If
`X-ABC∈S₁`, then it also lies in weak `S₁`, and additivity would force

```text
X = ABC + (X-ABC) ∈ S_{1,∞},
```

contradicting `xiOrderedSignedPrimeOperator_not_memWeakSchattenClass_one`.

## Hostile audit

- Positive-depth escape: closed. Entire `e>=1` sector is Schatten-one and cannot alter weak
  boundary set by `e=0` face.
- Cross-space mixing: closed for arbitrary bounded `A,C`; unitary transport and reordering are
  special cases.
- Non-diagonal/infinite-rank escape: closed within additive Schatten-one correction class.
- Source purity: all source weights are literal Route-P `w(p,e)`; Xi appears only in target
  weak-ideal theorem.
- Genus-two escape: survives. A Hilbert--Schmidt but non-trace-class correction can change weak
  boundary and belongs naturally to regularized `det₂`, not ordinary Fredholm determinant.
- Nonlinear monodromy escape: survives. No claim concerns nonlinear transformation of Stokes data.

## No-go closure

- **Exact killing theorem/mechanism:** Complete all-depth Route-P carrier has weak-`S₁` density;
  positive-depth Stokes modes add only trace-class mass. Bounded channel mixing and trace-class
  Fredholm corrections preserve weak-`S₁`, while Xi lies outside it.
- **Strongest positive survivor:** `[BRIDGE] [PROVED HERE]` A viable irregular-RH weld must use a
  genuinely genus-one correction outside `S₁`, or replace Route-P base by a wild source already
  carrying logarithmically enhanced `log(n)/n` density. Positive Stokes depth cannot supply it.
- **New insight:** Missing Xi arithmetic density is not hidden in neglected positive-depth modes.
  It must enter at principal wild face or through non-Fredholm `det₂`-scale transport.
- **Status:** formalized in
  `RoutePPrimitiveGammaJuliaLogFullWeakTraceNoGo.lean`; exact-target build and new-declaration
  axiom audit pass.

## References

- Marco Bertola, SIGMA 13 (2017), 046, https://doi.org/10.3842/SIGMA.2017.046
- Thomas Bothner, arXiv:2205.15007, https://arxiv.org/abs/2205.15007

## Log

- 2026-08-24 — corpus/literature audit, exact all-depth conjecture, hostile audit, and complete
  proof; moved to `2-fully-proven`.
- 2026-08-24 — formalized full-carrier decomposition, trace-class positive-depth tail,
  weak-`S₁` membership under arbitrary bounded channel mixing, and Xi trace-class relocation
  no-go; direct Lean check and exact-target build pass; all new theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`; moved to `3-formalized`.
