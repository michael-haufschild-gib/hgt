# Finite-dimensional linear holographic locality tradeoff universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED]`

## Lean-derived conjecture

Every finite-dimensional law space carrying a represented degree-`d` scalar law (`d ≥ 3`) has a
linear-width holographic completion with:

- exact algebraic-dependence horizon equal to the scalar-law zero locus;
- injective exterior derivation symbol;
- exact detector width `d(2r+1)`, where `r` is law-space dimension.

But for the same completion in its canonical finite coordinates, every membrane-local
presentation of valence at most `Δ` must cover every law-space two-plane and therefore obey

`choose r 2 ≤ #H * choose Δ 2`.

Thus linear global holographic width and quadratic bounded-locality channel demand coexist in one
universal theorem.

## Corpus inputs

- `finiteDimensionalLinearHolographicCompletion_fieldHorizon_and_maximalPrincipalSymbol`
- `finiteDimensionalLinearHolographicCompletionCoordinate_card`
- `linearWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent`
- `membranePairComplete_of_principalBracketPair_linearIndependent`
- `holographicLocality_choose_bound`

## New connector

Finite-dimensional completion transports a universal linear-width detector through a chosen
basis, while the locality theorem only sees finite coordinate supports. Applying locality before
the final coordinate transport exposes the cost hidden by the coordinate-free completion:
bounded membrane valence cannot inherit its linear channel count.

No numerical computation is used.

## Novelty protocol

Literature search was deferred until the theorem passed

`lake env lean GaloisForLFunctions/HTGeometry/FiniteDimensionalLinearHolographicLocalityTradeoffUniversalityLaw.lean`.

Nearest sources found:

- Gordon, Kuperberg, Patashnik, and Spencer, *Asymptotically optimal covering designs*,
  arXiv:math/9511224, gives the classical `choose(v,t)/choose(k,t)` covering lower bound;
- Nelson and Nguyễn, *Sparsity lower bounds for dimensionality reducing maps* and later work on
  sparsity/dimension tradeoffs study locality costs for linear embeddings;
- Almheiri, Dong, and Harlow, *Bulk Locality and Quantum Error Correction in AdS/CFT* and
  single-shot holographic-compression work study holography/local recovery in different models.

No source found joins a finite-dimensional degree-`d` scalar-law zero-locus horizon, injective
exterior derivation symbol, exact detector width `d(2r+1)`, and the bounded-membrane pair-covering
inequality for the identical completed principal symbol.

## Lean target

`formal/GaloisForLFunctions/HTGeometry/FiniteDimensionalLinearHolographicLocalityTradeoffUniversalityLaw.lean`
