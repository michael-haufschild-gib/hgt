# Route R cross-prime Stokes/Calkin pre-quotient comparison

- **ID:** `route-r-cross-prime-stokes-calkin-prequotient-comparison`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / NO-FACTORISATION
- **Parent:** `route-r-cross-prime-stokes-calkin-compression-landing.md`
- **Status:** `[PAPER-PROVED] [PRE-QUOTIENT COMPARISON EXISTS] [CORONA DESCENT IMPOSSIBLE]
  [LEAN DEFERRED DURING REFACTOR] [NOT RH]`
- **Statement:** Localized two-prime Stokes curvature admits a coefficient-faithful comparison
  from the actual finite Calderon--Witt cross-prime source span to the fixed Sonin Calkin class.
  This comparison cannot factor through the singular-corona quotient or through any continuous
  Hausdorff completion that kills the old oriented source boundary.

## Goal

Decide whether the scalar curvature/compression landing can be promoted to a literal source
comparison whose existing source exactness would force compactness.  The comparison must use the
actual ordered cross-prime Milnor-incidence atoms and the fixed Sonin compression.  It may not
replace the finite `(2,3)` atom by the full-support horizon or assume compactness of its image.

## Universal localized curvature

Let `x,y` be independent invertible prime-character variables.  Away from the two Cartier walls
`x=1` and `y=1`, put

```text
Omega(x,y) = (y-1)/(x-1) - (x-1)/(y-1).
```

Reflection sends `(x,y)` to `(x^-1,y^-1)`.  Direct reduction gives

```text
Delta(x,y)
  = Omega(x,y)-Omega(x^-1,y^-1)
  = (y-x) * ((y-1)/(y*(x-1)) + (x-1)/(x*(y-1)))
  = N(x,y)/(x*y*(x-1)*(y-1)),                              (1)

N(x,y) = (y-x) * (x*(y-1)^2 + y*(x-1)^2).                  (2)
```

Proof of `(1)` uses

```text
Omega(x^-1,y^-1)
  = x*(y-1)/(y*(x-1)) - y*(x-1)/(x*(y-1)),
```

followed by collecting the two differences.  Clearing denominators gives `(2)`.  Thus the class
is defined in the localization

```text
C[x^+-1,y^+-1, (x-1)^-1, (y-1)^-1].
```

On the common modular character curve

```text
x=p^(-a),  y=q^a,
```

`Delta(x,y)` is exactly `Delta_pq(a)` from the parent card.  The one-parameter continuation at
`a=0` is zero, but `(1)` is not regular as a two-variable source function across the Cartier
normal-crossing divisor: neither `x-1` nor `y-1` divides `N`.  The common modular curve is
therefore load-bearing; ordinary two-variable scalar base change cannot retain the central atom.

## Actual arithmetic pre-quotient comparison

The corpus supplies the exact source presentation needed here:

1. ordered distinct-prime indices
   `DeningerCalderonWittCrossPrimePacketIndex`;
2. linearly independent actual Gamma--Milnor witnesses;
3. a canonical equivalence between their algebraic span and finitely supported ordered-pair
   coefficients;
4. exact recovery of every coefficient by the normalized arithmetic packet coordinate.

For a finite prime set `P`, send a zero-diagonal ordered coefficient matrix `A` to the Calkin class
of the literal finite Sonin Euler Gram

```text
A |-> [sum_(p,q in P) A_pq G_pq].                            (3)
```

The finite-prime shell estimate recovers every off-diagonal entry from distance to compact
operators.  Hence `(3)` is injective.  Passing over the directed union of finite supports gives a
coefficient-faithful linear comparison on the complete algebraic cross-prime source span.  On the
`(2,3)` atom with coefficient `Delta_23(a)`, it is precisely the fixed Calkin class constructed in
the parent card, and it is nonzero for `a!=0`.

This is the maximal honest source lift currently available: it is algebraic, pre-quotient, and
retains prime/depth provenance.

## Exact no-factorisation theorem

Let `S_alg` be the actual finite arithmetic source span, `H_pkt` its `ell^2` packet completion,
`q_cor : H_pkt -> H_pkt/S_alg` the singular-corona projection, and `e_23` the actual `(2,3)` source
atom.  Then

```text
q_cor(e_23)=0,                                               (4)
```

whereas for every nonneutral grade

```text
CalkinComparison_a(e_23) != 0.                              (5)
```

Therefore no linear map from the singular corona to the Calkin target can factor the comparison:
if `CalkinComparison_a = F o q_cor`, equations `(4)` and `(5)` contradict each other.

The Hausdorff/continuous alternative is even stronger.  `S_alg` is dense in `H_pkt`; the corpus
proves every continuous observation on `H_pkt` vanishing on `S_alg` is zero.  Consequently no
bounded comparison can simultaneously

1. descend the old oriented boundary, which kills all of `S_alg`, and
2. retain either the finite `(2,3)` atom or the nonzero full-support horizon.

The algebraic singular corona retains the horizon only by being non-Hausdorff, but necessarily
kills the finite atom required by the fixed compression landing.  The two receivers cannot be
identified.

## Conjecture / proof-or-failure loop

### C1 -- localized curvature descends through the singular corona

`[FALSIFIED]`.  Corona projection kills the literal finite atom while the Calkin comparison is
injective on it off-neutral.  This is an algebraic contradiction, not a missing continuity proof.

### C2 -- replace singular corona by the Hilbert completion

`[FALSIFIED]`.  Finite arithmetic packets are dense.  Every continuous comparison that kills the
old source boundary is identically zero and therefore cannot retain the fixed Calkin class.

### C3 -- use an operator-norm summable all-prime tail to cancel the finite Calkin atom

`[FALSIFIED BY EXISTING LEAN THEOREM]`.
`coefficients_eq_zero_of_summableEvenDilationGramAggregate_isCompact` proves entrywise Calkin
injectivity for every absolutely operator-norm summable all-prime Gram.  Norm-summable tails cannot
cancel one nonzero finite coefficient modulo compact operators.

### C4 -- retain the comparison before quotienting

`[PROVED]`.  Finite-support arithmetic coefficient recovery followed by finite Sonin Calkin
injection gives the coefficient-faithful comparison `(3)`.

### C5 -- source exactness then forces compactness

`[FALSIFIED]`.  The comparison in C4 is deliberately pre-quotient.  Existing exactness kills the
old oriented boundary, not the retained cross-prime atom.  Factoring through the quotient needed
to infer compactness is exactly what C1--C3 exclude.

## Frontier effect

The literal rational-adelic operator-lift question is closed, but it does not close RH.  Route R
now has a sharp local/global fracture:

```text
actual finite source atom
  -- coefficient-faithful --> fixed nonzero Calkin class off-neutral
  -- singular-corona class --> 0.
```

Thus no existing Stokes/Koszul exactness theorem can annihilate the fixed compression class.  Any
surviving producer must add a genuinely new, non-norm-summable and non-corona multi-place law that
uses the actual Xi zero equation.  It must prove compactness of the pre-quotient Calkin image
without declaring the retained arithmetic atom a boundary.  A bounded completion, algebraic
corona factorisation, or norm-summable all-prime correction is dependency-closed dead.

This removes a false source-exactness shortcut and narrows the open theorem to one precise
category: a cutoff-dependent/unbounded Poisson self-product comparison whose finite coefficient
is recovered only after global renormalization.  Existence and compactness of that comparison
remain unproved.

## Lean reuse plan after refactor

No Lean code is written during the shared refactor.  Later formalization should reuse:

- `DeningerCalderonWittAllCrossPrimeIncidenceKoszul` for ordered indices, witnesses, and exact
  coefficient recovery;
- `DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion` for the Finsupp/source-span
  equivalence and density;
- `DeningerCalderonWittCrossPrimeSingularCorona` for `(4)` and horizon survival;
- `SoninEulerFiniteGramLower` for finite coefficient-faithful Calkin injection;
- `XiPrimeSeamSummableCalkinAggregate` for the norm-summable no-cancellation theorem.

Required new formal content is only the finite-support matrix adapter, universal rational identity
`(1)`--`(2)`, and the two no-factorisation corollaries.

## Log

- 2026-08-11 -- C1--C3 falsified, C4 proved, C5 falsified.  Literal source comparison exists only
  before quotienting; no existing exactness or norm-summable completion can force its compactness.
