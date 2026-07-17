# Von Mangoldt--Gamma factorial normalization positivity no-go

- **ID:** `von-mangoldt-gamma-factorial-normalization-positivity-no-go`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** POSITIVE NO-GO (Lean), NORMALIZATION OBSTRUCTION
- **Scientific status:** `[PROVED] [LEAN-VERIFIED] [ROUTE KILL] [NOT AN RH PROOF]`
- **Parent:** `von-mangoldt-gamma-cofinal-pointed-ward-euler-germ.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaFactorialNormalizationNoGo.lean`

## Theorem

Let `m_k(x)` be the cofinal pointed von Mangoldt--Gamma raw moment.  For every natural shift `r`
and finite exponent packet `a_i`, Lean constructs the literal source Gram

```text
G_(r,x)(i,j)=m_(r+a_i+a_j)(x)                            (1)
```

and proves

```text
x>0 -> G_(r,x)>=0.                                       (2)
```

This is first proved at finite aperture by absorbing `log(n)^r` into the nonnegative source
weight, then passed to the cofinal limit entrywise.  In particular, the first unnormalized odd
trace block

```text
R_x=[[m_1,m_3],[m_3,m_5]]                                (3)
```

is positive semidefinite for every `x>0`.

Define the literal first factorial trace normalization

```text
F([[a,b],[c,d]])=[[a,b/3!],[c/3!,d/5!]].                (4)
```

The normalized block is therefore

```text
F(R_x)=[[m_1,m_3/6],[m_3/6,m_5/120]].                   (5)
```

The cofinal Euler-germ identification from the parent theorem gives the exact determinant law

```text
det F(R_x)
 = vonMangoldtNormalizedFirstHankelDet(x+1).             (6)
```

The existing far-right theorem proves that the right side is eventually strictly negative.
Consequently Lean proves the exact no-go

```text
eventually in x:
  R_x>=0 and F(R_x) is not positive semidefinite.         (7)
```

All claims are unconditional.

## RH consequence

The direct positivity arrow

```text
positive pointed Gamma--Euler source Gram
  -> factorially normalized trace-Hankel positivity
```

is false for the actual infinite von Mangoldt source, already in the first two-by-two block and
already arbitrarily far inside the absolute-Euler half-plane.  This is stronger than failure at
the critical boundary: the normalization loses positivity before inverse half-translation begins.

Therefore the source reconstruction proved by the parent card cannot be fed directly into the
existing normalized Xi Hankel endpoint.  A viable RH proof must change the middle arrow in one of
two substantive ways:

1. construct a coupled Gamma/polar/Mellin completion whose cross terms correct `(5)` before the
   factorial projection; or
2. prove a different positive critical realization whose relation to Xi is not the entrywise
   factorial map `(4)`.

Adding more raw source moments, taking a compact completion, or invoking positivity of each
finite Bianchi Gram cannot repair `(7)` by itself.

## Anti-theatre and novelty gate

This theorem does not produce RH positivity; it kills a tempting but invalid transport.  The
linear-algebra mechanism is classical, and the negative determinant was already known in the
corpus.  The useful new corpus fact is the exact juxtaposition with the now-formalized cofinal raw
source Gram and the explicit positivity-destroying map `(4)`.  It is classified as a route-killing
bridge, not new scientific knowledge.

## Lean certificate

Principal declarations:

- `finiteVonMangoldtGammaShiftedRawGram_apply`;
- `finiteVonMangoldtGammaShiftedRawGram_posSemidef`;
- `tendsto_finiteVonMangoldtGammaShiftedRawGram_apply`;
- `infiniteVonMangoldtGammaShiftedRawGram_posSemidef`;
- `infiniteVonMangoldtGammaFirstRawTraceGram_posSemidef`;
- `infiniteVonMangoldtGammaFirstFactorialTraceGram_eq_normalize`;
- `det_infiniteVonMangoldtGammaFirstFactorialTraceGram_eq_normalized`;
- `infiniteVonMangoldtGammaFirstFactorialTraceGram_eventually_not_posSemidef`;
- `vonMangoldtGammaFirstFactorialNormalize_eventually_destroys_posSemidef`.

Verification:

- exact target build passed;
- axiom audit: `propext`, `Classical.choice`, and `Quot.sound` only;
- no numerical computation;
- no target Xi positivity or RH hypothesis.

## Gates

- [x] general shifted raw source Gram constructed
- [x] finite and cofinal shifted Gram positivity
- [x] unnormalized odd trace block positivity
- [x] literal factorial trace-normalization map isolated
- [x] exact determinant identification with the analytic Euler theorem
- [x] eventual strict negative determinant
- [x] eventual failure of positive semidefiniteness
- [x] direct source-to-normalized-Hankel route killed
- [ ] coupled pre-normalization correction
- [ ] alternative positive critical realization
- [ ] RH
