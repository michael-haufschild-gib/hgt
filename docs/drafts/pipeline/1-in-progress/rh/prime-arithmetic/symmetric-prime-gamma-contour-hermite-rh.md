# Symmetric prime--Gamma contour Hermite positivity implies RH

- **ID:** symmetric-prime-gamma-contour-hermite-rh
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** top-down Lean-corpus synthesis
- **Statement:** Nonnegativity of the translated finite Hermite tests against the continued prime--Gamma source trace on admissible rational symmetric rectangles, for integer polynomials only, forces RH.

## Formal status

`[PROVED IN LEAN, CONDITIONAL]` Lean proves the chain

```text
integer Hermite positivity on admissible rational prime--Gamma rectangles
  -> finite translated trace--Hankel positivity for every enclosed Xi packet
    -> every enclosed centered Xi zero is real
      -> RH.
```

The formal capstone is

```text
riemannHypothesis_of_countableSymmetricPrimeArchTraceHankelNonnegative
```

in

```text
GaloisForLFunctions.RHTower.XiGuinandWeilFiniteHermiteCriterion.
```

## Goal

Prove directly from the analytically continued prime--Gamma source that, for every admissible
symmetric rectangle with rational `R,c`

```text
[-R,R] x [-c,c],     R > 0,  0 < c < 1/2,
```

and every integer polynomial `P`,

```text
Re ((2*pi*i)^(-1) * integral_(boundary rectangle)
  (R + 1 + z) * P(R + 1 + z)^2
    * continuedPrimeArchSourceRelativeTrace(z) dz) >= 0.
```

This is a countable family of source inequalities.  The translation `R+1` is geometric, not
spectral: every real point of the rectangle is sent into the strictly positive real axis with at
least unit room.  The condition mentions no Xi zero, zero enumeration, real-rootedness assertion,
reciprocal-zero measure, or limiting divisor sum.

## Exact value relation

For every admissible rectangle, the existing Guinand--Weil contour theorem identifies the
normalized source integral exactly with

```text
sum_(alpha in enclosed distinct XiC zeros)
  ord_alpha(XiC) * (R + 1 + alpha) * P(R + 1 + alpha)^2.
```

The rectangle is symmetric, so its finite Xi packet is closed under conjugation.  The generic
finite theorem

```text
finite_shifted_traceHankel_nonneg_implies_real
```

translates the packet by `R+1`, applies the already formalized finite trace--Hankel converse, and
forces every enclosed `alpha` to have zero imaginary part.

The value relation now has its own theorem surface:

```text
normalized_symmetricPrimeArchHermiteContour_eq_closedRectangleTraceHankel.
```

At each fixed finite packet, coefficient continuity, rational density, and quadratic homogeneity
prove that integer-polynomial positivity implies real-polynomial positivity.  Thus no uncountable
coefficient family is hidden in the criterion.  Lean also strengthens the rectangle selector:
the admissible avoiding contour can always be chosen with rational `R,c`.

Lean also proves unconditionally that every multiplicity copy of the Xi divisor is strictly
inside some such admissible symmetric rectangle.  The selection avoids only the finitely many
real and imaginary coordinates of XiC zeros in one larger compact box; the selected contour and
the hypothesis itself remain source-defined.

## Named open core

`[OPEN CORE]` Prove

```text
XiCountableSymmetricPrimeArchTraceHankelNonnegative.
```

This is a countable family of finite source-contour inequalities indexed by
`(R,c,P) in Q x Q x Z[X]`.  No passage to an infinite Hankel cone, no tightness or
moment-determinacy theorem, and no cofinal limit is required.  A useful attack must produce the
sign from the continued prime and Gamma boundary values themselves, for example by an edgewise
positive decomposition or a coefficient identity.  Replacing the contour by the Xi zero sum and
invoking real-rootedness would be circular.

## Non-redressing audit

- The hypothesis is stated entirely using rational finite rectangles, integer polynomial
  coefficients, and `continuedPrimeArchSourceRelativeTrace`.
- The test is entire and fixed before the Xi divisor in the rectangle is extracted.
- The source-to-zero equality is a proved value relation, not the definition of the source
  integral.
- The argument uses no asymptotic rectangular test `Q_{L,n}` and no subpower lower bound.
- It uses no infinite-support moment representation or RH-equivalent limiting measure.
- The remaining source inequality is stronger than the target statement that the enclosed roots
  are real; its proof cannot select or inspect those roots.
- Countability is proved by coefficient-density and rational-contour selection theorems, not
  postulated as a sequential encoding of the Xi divisor.
- `[NOVELTY UNVERIFIED]` No new-scientific-knowledge claim is made for this conditional bridge.

## Census audit residue

The height-adaptive DISC objects `discCensusH`, `windowDepth`, `V`, and `valMeasure` are presently
divisor-fed: each is defined from local Xi orders or an Xi-zero finset.  The completed-SEM contour
index is source-defined, but its current RH interface centers the contour at a selected Xi zero.
Therefore that census branch has no independent source producer in the current corpus.

The positive obligation extracted from that no-go is exactly a global source boundary value before
divisor selection.  The Guinand--Weil rectangle theorem supplies such a value.  The finite Hermite
route uses it without asking the source to reproduce a target-defined dyadic census.

## Gates

- [x] 0 -> 1 in-progress: source-pure finite condition and exact attack surface identified
- [ ] 1 -> 2 fully-proven: prove the prime--Gamma contour Hermite inequality
- [ ] 2 -> 3 formalized: formalize the unconditional source sign and close RH
- [ ] 3 -> 4 publication-ready: standalone proof and literature audit

## Lean surface

```text
finite_shifted_traceHankel_nonneg_implies_real
finite_shifted_traceHankel_nonnegative_of_int
finite_shifted_traceHankel_int_nonneg_implies_real
symmetricRectangleLower
symmetricRectangleUpper
XiSymmetricRectangleExplicitAdmissible
exists_admissible_symmetric_rectangle_containing_xiZeroCopy
exists_admissible_rational_symmetric_rectangle_containing_xiZeroCopy
xiSymmetricRectangleHermiteTest
xiSymmetricRectangleHermiteTest_analyticOnNhd
normalized_symmetricPrimeArchHermiteContour_eq_closedRectangleTraceHankel
XiSymmetricPrimeArchTraceHankelNonnegative
XiCountableSymmetricPrimeArchTraceHankelNonnegative
symmetricRectangleZeros_conj_closed
riemannHypothesis_of_symmetricPrimeArchTraceHankelNonnegative
riemannHypothesis_of_countableSymmetricPrimeArchTraceHankelNonnegative
```

## Verification

- [x] exact module build
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint
- [x] generated index refresh

## Log

- 2026-07-13 -- top-down census audit found the global Guinand--Weil rectangle value relation;
  translated the finite Hermite converse to its source contour and formalized the conditional RH
  chain.
- 2026-07-13 -- compressed the source family to rational rectangles and integer polynomials;
  formalized the exact contour value relation, the coefficient-density transfer, the rational
  cofinal selector, and the countable conditional RH capstone.
