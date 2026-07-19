# Xi Transverse Aperture Projective Tangent Ultrametric

- **ID:** `xi-transverse-aperture-projective-tangent-ultrametric`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / positive survivor of the naive true-aperture completion
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW STRUCTURAL KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** transverse Xi shift defects; cofinite prime shift--jet asymptotic scale;
  transverse prime-source Hilbert metric; all-valuation-layer rank
- **Lean target:** `RHTower/XiTransversePrimeSourceProjectiveTangent.lean`

## Headline theorem

For a positive integral aperture `a` and prime `p`, put

```text
f_a(p)=p^(-a),
T_a(p)=log(p)(1-f_a(p)).                                  (1)
```

Here `T_a` is the prime layer of the actual transverse Xi source
`Lambda(n)(1-n^(-a))`.  For any two positive distinct apertures `a,b`, define the projective
ratio

```text
R_(a,b)(p)=T_a(p)/T_b(p)=(1-f_a(p))/(1-f_b(p)).           (2)
```

Then, along the cofinite filter on the primes,

```text
R_(a,b)(p) -> 1,                                          (3)
```

but the first renormalized projective defect is nonzero and exact:

```text
(R_(a,b)(p)-1)/f_min(a,b)(p)
  -> -1,  if a<b,
  -> +1,  if b<a.                                         (4)
```

Thus the ordinary projective boundary forgets the aperture, whereas its first tangent recovers
both the smaller aperture and the orientation of the pair.  The projective contact grade is

```text
v(a,b)=min(a,b).                                           (5)
```

It obeys the non-Archimedean triangle inequality

```text
v(a,c) >= min(v(a,b),v(b,c)).                              (6)
```

On prime-power valuation layer `e`, the shift is replaced by `(e+1)a`, so the exact contact grade
is

```text
v_e(a,b)=(e+1)min(a,b),                                    (7)
```

with the same orientation.  Consequently the all-valuation transverse aperture carries a
self-similar projective tangent ultrametric even though every finite source packet carries a
strictly positive Hilbert Gram.

## Proof

Because `a>0`, the established prime shift asymptotic-scale theorem gives

```text
f_a(p)->0.                                                 (8)
```

Hence `(1-f_a)/(1-f_b)->1`, proving `(3)`.  If `a<b`, direct algebra gives

```text
(R_(a,b)-1)/f_a
  = (f_b/f_a-1)/(1-f_b).                                  (9)
```

The shift-scale theorem gives `f_b/f_a->0`, while `f_b->0`, so `(9)` tends to `-1`.  If `b<a`,

```text
(R_(a,b)-1)/f_b
  = (1-f_a/f_b)/(1-f_b),                                  (10)
```

which tends to `+1`.  These are `(4)` and `(5)`.  Equation `(6)` is the elementary identity
boundary

```text
min(a,c) >= min(min(a,b),min(b,c)).                        (11)
```

At layer `e`, the prime-power identity for the transverse source replaces `f_a` by
`f_((e+1)a)`.  Applying `(4)` to the scaled apertures proves `(7)`.

## What this changes about the true-aperture metric

The existing Hilbert theorem says that, after deleting any finite prime set, one can choose a
finite prime packet whose shift--jet evaluation Gram is positive definite.  That is a rank
statement.  Equations `(3)`--`(7)` show that it is not a uniform tail-coercivity statement:
zeroth-order aperture columns become projectively collinear on the prime boundary.  Their inverse
Gram directions can become large only by resolving the renormalized defect grades `(5)`--`(7)`.

This supplies the strongest positive statement exposed by the naive completion no-go:

```text
finite positive Hilbert rank + ordinary tail completion
  = projective collapse with a nondegenerate graded tangent boundary. (12)
```

The correct infinite aperture object therefore cannot be the unrenormalized Hilbert limit alone.
It must retain the projective tangent filtration, or an equivalent jet/valuation renormalization.

## RH impact and exact remaining bridge

For the Xi Euler-ray response, Lean now proves that an off-line squared-zero orbit has a negative
three-node determinant and that the rest of the divisor can mask it only below a finite positive
reweighting threshold.  The transverse source family is the actual safe-side translation defect
of the completed logarithmic derivative, so it is a natural candidate source for such an
amplifier.

This theorem rules out obtaining that amplifier from ordinary cofinite-prime Hilbert separation:
the raw aperture rays collapse.  It also identifies the only live source residue: the graded
projective tangent `(4)`, replicated at the accelerated grades `(7)`.  What remains is an
unconditional source-to-zero response map proving that one of these renormalized tangent grades
acts with unbounded relative weight on a transverse squared-zero orbit while preserving the
critical-line positive sector.  Neither finite differential independence nor positive finite
Grams supplies that map.

Accordingly this card is not an RH proof.  Its candidate-new content is the exact coexistence and
classification of finite Hilbert rank, boundary projective collapse, oriented first defect, and
valuation-self-similar ultrametric in the actual Xi transverse source.  The elementary exponential
limit ingredients themselves are not claimed as new.

## Brownian--Laplace factorization of the true aperture

The contact kernel `min(a,b)` is not an analogy imposed after the fact.  It is the canonical
preimage Hilbert metric of the actual source columns.  Put `r=e+1` and `L=log p`.  The prime-power
coefficient is

```text
Lambda(p^r)(1-p^(-ra))=L(1-exp(-raL)).                   (13)
```

Since `rL>0`, exact integration gives

```text
[Lambda(p^r)(1-p^(-ra))]/[rL^2]
  =[1-exp(-raL)]/[rL]
  =integral_0^a exp(-rLt)dt.                             (14)
```

Thus, after its forced clock normalization, every transverse shift column is the Laplace image at
rate `r log p` of the interval vector

```text
h_a(t)=1_[0,a](t).                                       (15)
```

These source vectors satisfy

```text
<h_a,h_b>_(L2(0,infinity))=min(a,b).                     (16)
```

Equations `(14)`--`(16)` identify the projective contact grade `(5)` with a canonical positive
Hilbert kernel.  Valuation does not alter the source metric: it only accelerates the Laplace
sampling rate from `log p` to `r log p`.  The finite prime-source Gram is therefore a sampled
Laplace image of one Brownian/Cameron--Martin aperture geometry, rather than an unrelated family
of existential positive matrices.

There is an exact cross-corpus match.  The established anti-causal Xi boundary relative trace is

```text
Delta_ell(u)=integral_0^infinity min(t,u)|ell(t)|^2dt.    (17)
```

Its kernel is the same interval Gram `(16)`.  Consequently the source and zero-side consumers now
share one explicit Hilbert skeleton:

```text
transverse prime source
  -- valuation-scaled Laplace sampling --> Brownian aperture metric
  -- completed source-to-Hardy map      --> Xi relative-trace metric. (18)
```

The remaining RH theorem is no longer “find some completion.”  It is to construct the second
arrow from the completed Euler--Gamma source and prove it is nonexpansive against the Euler-pole
four-unit boundary density.  In the notation of the relative-trace card, the exact target is

```text
Delta_Xi(u)<=4(1-exp(-u))+o(u),   u->0+.                 (19)
```

The Brownian--Laplace factorization proves the source and target metrics are compatible in shape;
it does not prove the contraction `(19)`.  Its candidate-new status concerns this exact
source-specific identification with the projective contact filtration and the Xi relative-trace
consumer.  The Laplace primitive and Brownian covariance separately are classical.

## Lean status

`XiTransversePrimeSourceProjectiveTangent.lean` formalizes:

1. cofinite projective collapse of every positive aperture pair;
2. the exact `-1/+1` first-defect limits at grade `min(a,b)`;
3. the non-Archimedean grade inequality and valuation-layer scaling;
4. the canonical Brownian metric and strict two-node determinant;
5. the complex interval-Laplace primitive; and
6. the normalized prime-power identity `(14)` for the actual transverse Xi arithmetic source.

The direct source check and narrow module build pass.  `#print axioms` for the principal collapse,
first-defect, Brownian metric, Laplace factorization, and valuation-layer theorems reports only
`propext`, `Classical.choice`, and `Quot.sound` (the purely arithmetic grade inequality omits
`Classical.choice`).

## Gates

- [x] 0 -> 1: exact source coefficients and the completion ambiguity identified
- [x] 1 -> 2: projective collapse, first defect, ultrametric law, valuation scaling, and
      Brownian--Laplace factorization proved
- [x] 2 -> 3: Lean module checks and standard axiom audit
- [ ] 3 -> 4: external novelty audit and source-to-zero tangent realization
