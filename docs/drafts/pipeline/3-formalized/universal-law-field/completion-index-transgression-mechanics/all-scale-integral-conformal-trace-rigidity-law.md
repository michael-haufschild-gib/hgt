# All-scale integral conformal-trace rigidity

- **ID:** `ULF-ICTR-1`
- **Stage:** 3-formalized
- **Type:** unconditional source-model rigidity theorem
- **Lean:** `GaloisForLFunctions.HTGeometry.AllScaleIntegralConformalTraceRigidity`; verified

## 1. Higher-law interpretation

The functional equation does not merely exchange two normalized reciprocal weights.  Before
half-density normalization it pairs two formation orientations at every positive integer scale
`n`.  For horizontal grade `a=2 Re(s)-1`, their squared weights are

`n^(1+a)` and `n^(1-a)`.

Their product is always `n^2`.  Thus functional-equation reflection fixes an integral determinant
line independently of `a`.  If this orientation doublet is the complexification of a finite
integral formation correspondence, its trace must also be integral.  Keeping the natural scale,
rather than dividing it away, turns that integrality into a selector.

## 2. Exact theorem

For `b in [0,1)`, define

`T_b(n)=n^(1+b)+n^(1-b)` for `n in N`.

### Theorem ICTR-1 — all-scale trace rigidity

The following are equivalent:

1. `T_b(n)` is an integer for every `n in N`;
2. `b=0`.

Equivalently, for every real grade `a`,

`|a|<1` and `T_|a|(n)` is integral for every `n`

if and only if `a=0`.

At every positive integer scale there is also the exact conservation law

`n^(1+b) n^(1-b)=n^2`.

The same classification holds for the parity-retaining supertrace

`S_b(n)=n^(1+b)-n^(1-b)`:

`S_b(n)` is integral for every `n` iff `b=0`.

Its proof is identical after replacing the lower-order plus sign by a minus sign.

## 3. Proof

The reverse implication is immediate: `T_0(n)=2n`.

Assume `0<b<1`.  Extend the trace to positive real `x` and take its second unit finite
difference

`C_b(x)=T_b(x+2)-2T_b(x+1)+T_b(x)`.

The general real-power finite-difference theorem already proved in the corpus gives

`Delta^2 x^beta ~ beta(beta-1)x^(beta-2)`.

Apply it to `beta_+=1+b` and `beta_-=1-b`.  The first contribution is asymptotic to

`(1+b)b x^(b-1)`,

whereas the second is asymptotic to

`-(1-b)b x^(-b-1)`.

Because `-b-1<b-1`, the second term is lower order.  Therefore

`C_b(x) ~ (1+b)b x^(b-1)`.

The leading coefficient is positive and `b-1<0`, so `C_b(n)` is eventually positive and tends to
zero.  Hence eventually `0<C_b(n)<1`.

If every `T_b(n)` were integral, every integer second difference `C_b(n)` would be integral.  No
integer lies strictly between zero and one.  Contradiction.  QED.

## 4. Corpus fusion

This theorem uses four independent organs without restating any route endpoint.

1. Functional equation and Schwarz reflection supply the two orientations `1+a` and `1-a`.
2. Formation mechanics supplies every natural integer scale, not only a prime or a fitted
   subsequence.
3. Multiplicative collision fibres are finite permutation histories, so an integral or virtual
   integral categorical trace is source-natural.
4. Polynomial-power finite-difference asymptotics detect the nonintegral residual curvature.

There is a stronger exact ledger behind these four shadows.  Put `u=b log n` and

`E=n exp(u)`, `O=n exp(-u)`.

Then

`trace=E+O=2n cosh(u)`,

`supertrace=E-O=2n sinh(u)`,

`det=EO=n^2`,

`supertrace/trace=tanh(u)`,

`2n/trace=sech(u)`,

`trace^2-supertrace^2=4n^2`.

Thus fixed mixed inertia, Hodge-sign sinh, positive cosh defect, likelihood contrast, visibility,
and rapidity are not analogies.  They are exact quotients of one parity-graded formation ledger.

The normalized Lorentz-lattice theorem sees only reciprocal eigenvalues `n^a,n^-a` and therefore
must manufacture a lattice after dividing by `n`.  ICTR-1 shows that the discarded common factor
is the arithmetic datum that can do the selection.

## 5. Exact RH boundary

ICTR-1 is not RH by itself.  A finite integral matrix independent of the spectral character cannot
work: scalar extension cannot make its trace depend on `s`; putting character-valued entries in
the matrix makes its source trace character-valued rather than integral.  The viable source must be
infinite/pro-integral before completion.

The theorem would close RH if the corpus constructs, before Xi-zero specialization, an integral
Frobenius--Verschiebung formation superobject such that:

1. integral operators satisfy `F_n V_n=n` before analytic completion;
2. the even/odd doublet is `F_n^2` and `V_n^2`;
3. on a completed character of real part `sigma`, the two eigenvalues are `n^(2sigma)` and
   `n^(2-2sigma)`;
4. a source-proved Fredholm/properness law identifies analytic supertrace with the stabilized
   integral Lefschetz supertrace for every `n`.

Then supertrace ICTR-1 forces `a=2sigma-1=0` for every occurrence; the corpus' exact grade
equivalence gives RH.

The construction may not define the completion from a zero, assume trace comparison, or choose a
lattice after complexification.  Those are the old receiver in new notation.  Integral provenance
must come from literal finite formation histories; spectral dependence may enter only through an
analytic completion/character.  Existing genuine-positive Artin no-gos make the super/Krein
grading mandatory rather than optional.

## 6. Positive survivor if realization fails

Even without the source correspondence, ICTR-1 proves a sharp classification: no noncritical
strip grade can have an all-natural-scale integral unnormalized paired trace.  Any failed
realization must identify exactly which formation operation destroys integrality or the spectral
identification; weakening to prime-only or normalized traces discards the theorem's selector.

## Log

- 2026-09-02 -- derived after fresh audit killed rooted completion, label retention, and
  transition-energy relabelings; dependency-closed paper proof completed.
