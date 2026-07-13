# Rectangular Gamma--polar cancellation and bounded source law

- **ID:** `rectangular-gamma-polar-cancellation-source-bound-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH VALUE RELATION
- **Scientific status:** `[FORMALIZED IN LEAN] [AXIOM-CLEAN] [NOT AN RH PROOF]`
- **Statement:** For every fixed positive rectangular width, the normalized archimedean bottom
  value minus the elementary polar square is uniformly bounded over all separated apertures.
  Consequently RH is equivalent to uniform boundedness, and to eventual all-epsilon one-sided
  subpower lower control, of the corresponding finite prime--polar source values.

## Main law

For every `L > 0`, the finite prime--polar source satisfies

```text
RH iff exists C >= 0, forall a >= L, |source(L,a)| <= C.       (1)
```

It also satisfies the eventual all-epsilon one-sided form

```text
RH iff exists N, forall epsilon > 0, exists C >= 0,
  forall n >= N, 0 <= source(L, log(n)/2) + C*n^epsilon.       (2)
```

There is no named proposition interface, test-function hypothesis, archimedean hypothesis, or
zero datum in either statement.

## Exact Gamma--polar identity

For `A_(L,a)(t)` equal to `rectangularTwoEdgeAutocorrelation L a t`, Gauss's digamma integral and
sharp Fourier inversion give

```text
normalizedBottomArch(L,a) - 2 polarFeature(L,a)^2
 = 2 integral_0^infinity
     [exp(-2t) A_(L,a)(0) - exp(-t/2) A_(L,a)(t)]
       /(1-exp(-2t)) dt
   - (gamma + log pi) A_(L,a)(0).                            (3)
```

For `a >= L >= 0`, the four-tent law reduces on `t >= 0` to two fixed self-overlap tents and one
moving cross tent.  Here `A_(L,a)(0)=2L`, while the moving tent is bounded by `min(L,t)`.  Hence
the Gamma--polar correction is bounded by an explicit nonnegative constant depending only on
`L`, uniformly in `a`.

Combining `(3)` with

```text
Weil(L,a) = -2 primeAutocorrelation(L,a) + normalizedBottomArch(L,a)
source(L,a) = -2 primeAutocorrelation(L,a) + 2 polarFeature(L,a)^2
```

gives the exact source law

```text
Weil(L,a) = source(L,a) + GammaCorrection(L,a).               (4)
```

Under RH the reciprocal-square spectral estimate bounds `Weil(L,a)` uniformly in `a`; hence the
source is uniformly bounded.  Conversely, boundedness of the source bounds the sampled Weil
values and the transverse-growth theorem returns RH.  The same bounded correction transfers the
all-epsilon lower criterion without changing its exponent or quantifier pattern.

The source is also exactly a fixed completed critical-Mellin adjacent-block value plus a
width-dependent constant.  Thus `(2)` is equivalent to

```text
exists N, forall epsilon > 0, exists C >= 0, forall n >= N,
  0 <= criticalMellinAdjacentBlock(L, log n) + C*n^epsilon.
```

This is the sole RH-bearing value estimate left by the rectangular formula.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/XiGuinandWeilRectangularGammaCancellation.lean` proves the
exact Gamma integral, its integrability, and its aperture-uniform bound.  The capstone
`formal/GaloisForLFunctions/RHTower/XiGuinandWeilRectangularGammaPolarSourceLaw.lean` proves:

- `xiWeilPolarization_rectangular_eq_primePolarSource_add_gammaCorrection`;
- `rectangularWeil_subpowerLower_iff_primePolarSource`;
- `riemannHypothesis_iff_rectangularPrimePolarSource_uniformlyBounded`;
- `riemannHypothesis_iff_exists_eventually_rectangularPrimePolarSource_subpowerLower`;
- `riemannHypothesis_iff_exists_eventually_criticalMellinAdjacentBlock_subpowerLower`.

The module builds under the project toolchain.  `#print axioms` reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; there are no project axioms, `sorry`, `admit`,
`opaque`, or `unsafe` declarations in the result.

## Relation to the sharp dyadic window

A positive finite-width increment law is available: increasing `(L,x)` to `(L+h,x+h)` adds at
least `h` times every von-Mangoldt atom already in the closed multiplicative shell.  This gives a
value-only majorant for the sharp dyadic window.  The positive formulation of the remaining
constraint is that a successful sharp transfer must retain cancellation at the local slope or
positive-excess-energy level; a scalar first secant has cost `h*sqrt(n) + 1/h`.

The formal sharp-window stack reduces the pointwise target further.  It is enough to prove, for
every `epsilon > 0`, absolute convergence of

```text
sum_n positiveExcess(n) / n^(1+epsilon),
```

where `positiveExcess(n)` is the positive part of the amount by which the dyadic weighted prime
window exceeds its square-root main term.  This is weaker than pointwise all-epsilon control and
is exactly the positive backward-variation energy of the completed critical-Mellin error.

## Gates

- [x] exact Gauss/Fubini identity and uniform tent majorant
- [x] aperture-uniform Gamma--polar correction bound
- [x] exact prime--polar source decomposition
- [x] direct uniform-boundedness equivalence with RH
- [x] direct all-epsilon source and adjacent-block equivalences with RH
- [x] axiom audit and focused module build
- [ ] sharp-window completion: formal RH Chebyshev error or an equally strong local value relation
- [ ] RH

## Literature boundary

Gauss's integral representation of the digamma function is classical (DLMF 5.9.12).  Schoenfeld's
conditional estimate `|psi(x)-x| <= sqrt(x) log(x)^2/(8 pi)` is an explicit form of the classical
von Koch consequence of RH.  The scientific content here is the exact rectangular Gamma--polar
source decomposition and its direct bounded-source RH law, not either classical ingredient.
