# Splitting over positive power-series loops

- **Stage:** 3-formalized
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](../1-in-progress/garland-loop-eisenstein-over-q.md)
- **Target:** An injective homomorphism `SL₂(F[[X]]) → LoopSL2 F` lifting the
  coefficientwise inclusion, agreeing with both canonical integral root groups.

## Scope and evidence

The formal Laurent central extension and degree action are constructed. The
next group input is its splitting over the positive power-series subgroup.
Liu, *Eisenstein Series on Loop Groups*, §3.1, discusses this splitting:
<https://arxiv.org/abs/1103.4212>. This is known mathematics. Corpus searches
found the tame-symbol residue formulas and finite elementary factorizations;
none constructs this positive-loop splitting. No loop Iwasawa theorem or
integrable highest-weight representation was found in the corpus.

## Algebraic construction to formalize

Let `O=F[[X]]`, `K=F((X))`. For `g=[[a,b],[c,d]]∈SL₂(O)`, its bottom row is
unimodular, so `c` or `d` is a unit of `O`. Define

`κ(g)=T(c,d)` if `c≠0` and `d∈Oˣ`, and `κ(g)=1` otherwise.

Here nonzero series are viewed as units of `K`, and `T` is the constructed
Laurent tame symbol. The proposed lift is `(g,κ(g))` in multiplicative central
coordinates. For `c∈Oˣ` its value is one, including when `d∈Oˣ` because both
integer valuations then vanish.

To prove multiplicativity, prove compatibility with right multiplication by
each elementary root matrix, then use elementary generation over the local
ring. This checks the actual cocycle; no splitting identity is postulated.

### Upper-root multiplication

Right multiplication by `U(s)`, `s∈O`, preserves `c` and replaces `d` by
`d+cs`. Its Kubota factor is one because the `x` coordinate is unchanged.
If `c` is a unit, both correction factors are one. Otherwise `d` and `d+cs`
are units with the same residue, so `T(c,d+cs)=T(c,d)`. The case `c=0` has
both correction factors one. Thus the lift respects right upper roots.

### Lower-root multiplication

Right multiplication by `L(s)` preserves `d` and replaces `c` by `c'=c+ds`.
If `d` is a unit and `c,c',s` are nonzero, the needed symbol identity is

`T(c'/c,c'/s)=T(c'/c,d)`.

Indeed put `u=c/c'`; then `1-u=ds/c'`, and the quotient of the two sides is
`T(u⁻¹,(1-u)⁻¹)=1` by Steinberg. This is exactly the ratio
`κ(gL(s))/κ(g)`. When `c=0` or `c'=0`, the same identity follows from the
opposite-pair symbol and triviality on two units of `O`; when `s=0` it is
the identity element.

If `d` is not a unit, `c,c'` are units with equal residue. Thus `c'/c` has
residue one and valuation zero. Its tame symbol with every Laurent unit is
one, so the Kubota factor and both correction factors are one.

### Generation and exactness

If `c∈Oˣ`, matrix multiplication gives
`g=U(a/c)W(c)U(d/c)`. If `d∈Oˣ`, it gives
`g=U(b/d)D(d⁻¹)L(c/d)`. The Weyl word and the unit diagonal are products of
integral upper/lower root matrices, by the proved relative Weyl identity at
symbol level and its underlying matrix identity. These factorizations prove
elementary generation with no Euclidean algorithm. Compatibility with right
root multiplication therefore gives the homomorphism law. Projection recovers
the original matrix, hence injectivity. Both root subgroups have correction
one, giving the required agreement with the canonical root splittings.

## Status

Dependency-closed paper argument and Lean implementation complete.
The splitting is an input to the positive Iwahori subgroup and completion
comparison. It does not supply Iwasawa coordinates, arithmetic-series
convergence, or unfolding.

Current Lean modules under `HTGeometry/LoopEisenstein/`:

- `PowerSeriesTameSymbol`: symbol laws, power-series residue formula,
  triviality on principal units, and equality for equal residues. Compiles.
- `PowerSeriesSL2`: injective Laurent inclusion, four elementary factors,
  unimodularity after reduction, and bottom-row shear formulas. Compiles.
- `PowerSeriesRowCorrection`: explicit correction, upper invariance, principal
  ratios, and all three lower-shear symbol identities. Compiles.
- `PowerSeriesKubota`: actual matrix/cocycle comparison and lower invariance.
  Compiles without warnings, including both zero-entry cases.
- `PositiveLoopSplitting`: explicit section, elementary compatibility,
  multiplicativity by four-factor generation, injective homomorphism, and both
  root restrictions. All five final direct source checks passed without
  warnings. Transitive axiom audit passed.

The corpus result `FiniteRingSl2.exists_four_factors` applies because
`PowerSeries F` is local and its maximal spectrum is finite. Its source was
read and its transitive axioms checked: only the three standard Lean axioms.
No finiteness assumption on the coefficient field is used.

The saved [transitive axiom audit](garland-positive-loop-splitting-audit.txt)
contains only `propext`, `Classical.choice`, and `Quot.sound` for all principal
declarations. Every final source check used `lake --old env lean` on the
individual module. All five modules are wired into the umbrella; no umbrella
build was run. The `PositiveLoopSplitting` olean is emitted only for the new
`PositiveIwahori` consumer.
