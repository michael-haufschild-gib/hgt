# Route R cross-prime Stokes/Calkin pre-quotient comparison

- **ID:** `route-r-cross-prime-stokes-calkin-prequotient-comparison`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / NO-FACTORISATION
- **Parent:** `route-r-cross-prime-stokes-calkin-compression-landing.md`
- **Status:** `[PAPER-PROVED] [PRE-QUOTIENT COMPARISON EXISTS] [CORONA DESCENT IMPOSSIBLE]
  [LEAN-PROVED FOR FIXED (2,3) ATOM] [FULL MATRIX ADAPTER OPEN] [NOT RH]`
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

### C3b -- use a conditionally operator-norm convergent coherent tail

`[LEAN-PROVED] [FALSIFIED]`.  Absolute summability is unnecessary.  Let `A : N x N -> C` have
zero diagonal, let `T_N(A)` be its `N x N` Sonin Gram rectangle, and suppose `T_N(A)` converges in
operator norm to a compact operator `K`.  Fix `i != j`.  For every
`N >= max(i,j)+1`, the finite shell estimate applied to `T_N(A)-K` gives

```text
|A_ij| <= ||T_N(A)-K||.
```

The right side tends to zero, hence `A_ij=0`; diagonal entries vanish by hypothesis.  Therefore
`A=0`.  In particular, no coherent rectangular exhaustion retaining a nonzero `(2,3)` coefficient
can have any compact operator-norm limit, regardless of conditional cancellation or ordering
inside each rectangle.

This proof uses only the already proved finite coefficient estimate and norm convergence.  It does
not use absolute summability, interchange an infinite sum with a shell limit, or assume a Calkin
series exists.

### C3c -- use cutoff-dependent compact counterterms with no compact limit

`[LEAN-PROVED] [FALSIFIED]`.  Even convergence of the compact counterterms is unnecessary.  Let
`K_N` be an arbitrary compact operator at stage `N`; impose no uniform norm bound and no convergence
on `(K_N)`.  If

```text
||T_N(A)-K_N|| -> 0,
```

then for every fixed `i != j` and all sufficiently large `N`, the same finite shell estimate gives

```text
|A_ij| <= ||T_N(A)-K_N||.
```

Hence `A_ij=0`, and a zero diagonal again gives `A=0`.  Thus no cutoff-dependent family of compact
counterterms can asymptotically erase a retained coherent finite coefficient in operator norm.
The counterterms may vary arbitrarily and diverge; compactness at each individual cutoff is enough.

### C3d -- require compact approximation only along a subsequence or recurrent cutoffs

`[LEAN-PROVED] [FALSIFIED]`.  The finite estimate is stronger than an asymptotic theorem.  For
each fixed `i != j`, once `N >= max(i,j)+1`, every compact operator `K` satisfies

```text
|A_ij| <= ||T_N(A)-K||.                                     (6)
```

Thus a nonzero retained coefficient gives one uniform positive Calkin gap at every sufficiently
large cutoff.  There cannot even be frequently many stages admitting compact `K_N` with error
strictly below `|A_ij|`; in particular, no subsequence has compact-approximation error tending to
zero.  This closes liminf-zero, recurrent, and cofinal-subnet variants without assuming a global
limit.

### C3e -- let the coefficient matrix vary and recover the atom only after renormalization

`[LEAN-PROVED] [FALSIFIED]`.  Let `A_N` be an arbitrary coefficient matrix at cutoff `N`; no
coherence, summability, boundedness, or common ordering is assumed.  Suppose one selected
off-diagonal coefficient converges,

```text
(A_N)_ij -> c,
```

and there are arbitrary compact counterterms `K_N` with

```text
||T_N(A_N)-K_N|| -> 0.
```

For every sufficiently large `N`, finite shell recovery gives

```text
|(A_N)_ij| <= ||T_N(A_N)-K_N||.
```

The squeeze theorem makes the left side tend to zero, while coefficient convergence makes it tend
to `|c|`; uniqueness of limits gives `|c|=0`, hence `c=0`.  Therefore a finite-stage Sonin Gram
renormalization cannot both recover a nonzero physical atom asymptotically and become compact in
Calkin norm.  This includes cutoff-dependent scaling and noncoherent coefficient repair.

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
surviving producer must add a genuinely new, non-operator-norm-convergent and non-corona multi-place law that
uses the actual Xi zero equation.  It must prove compactness of the pre-quotient Calkin image
without declaring the retained arithmetic atom a boundary.  A bounded completion, algebraic
corona factorisation, coherent operator-norm convergent all-prime correction, or
cutoff-dependent compact operator-norm renormalization, or finite-Gram coefficient recovery only
after global renormalization is
dependency-closed dead.

### C3f -- weaken the landing topology to strong or weak operator convergence

`[LEAN-PROVED] [FALSIFIED AS A COMPACTNESS PRODUCER]`.  Let `T` be any bounded operator on a
Hilbert space and `b` a Hilbert basis.  Its finite column truncations

```text
T_s x = sum_(i in s) <b_i,x> T b_i
```

have finite-dimensional range and are compact.  The Hilbert-basis expansion of `x`, followed by
continuity of `T`, gives `T_s x -> T x` for every `x` as finite sets increase.  Therefore every
bounded operator—compact or not—is a strong operator limit of compact operators; consequently it
is also a weak operator limit of compacts.

Applying this to the fixed Route-R Stokes--Sonin commutator at any nonzero grade gives an explicit
noncompact operator with compact finite-stage approximants converging strongly.  Strong/weak
compact approximability is therefore horizontal-blind and cannot imply physical compactness.
Combined with C3b--C3e, the topology dichotomy is exact:

```text
operator norm / Calkin norm : coefficient-faithful, but retained atom forbids compact approach;
strong / weak operator      : compact approach always exists, even off-neutral.
```

Hence changing only the convergence topology cannot create the missing producer.

Formalized in
`RHTower/RouteRStrongCompactApproximationBlindness.lean`: Lean constructs the finite Hilbert-basis
truncation net for every bounded Hilbert-space operator, proves every stage compact and proves
pointwise strong convergence.  For Route R it combines this with the fixed `(2,3)` compactness
criterion to exhibit, at every positive aperture and nonzero grade, a noncompact physical receiver
which is the strong pointwise limit of compact operators.  Targeted module build and axiom audit are
green; all five public theorems use only `[propext, Classical.choice, Quot.sound]`.

### C3g -- replace norm/strong by an arbitrary operator topology

`[LEAN-PROVED] [BRIDGE] [FALSIFIED AS A COMPACTNESS PRODUCER]`.  Let `C` be the compact ideal in
the fixed physical operator space and give that space any topology `tau`.  If `C` is `tau`-closed,
then `closure_tau(C) subset C`; consequently no noncompact receiver can be a `tau`-limit of compact
stages.  Applied to the actual `(2,3)` receiver, for every positive aperture and nonzero grade no
topology can simultaneously preserve compactness under limits and supply compact approximation.

`RouteROperatorTopologyCompactnessDichotomy.lean` proves this without assuming a named topology.
It also proves norm compact-approximability is exactly compactness, hence exactly neutral grade on
the fixed receiver and globally exactly RH.  Together with C3f, this closes every topology-only
repair, not just the norm/strong/weak examples.  A surviving handoff must add source-specific
tightness or prove physical compactness directly.

### C3h -- add collective compactness to the strong approximation

`[LEAN-PROVED] [POSITIVE SURVIVOR]`.  Pointwise convergence upgrades to compactness whenever every
stage maps the unit ball into one common compact subset of physical Hilbert space; individual stage
compactness is unnecessary.  Consequently, at positive aperture and every nonzero grade, Route R's
canonical compact Hilbert-basis truncations escape every compact set: for each compact `C` some
stage and some unit vector have image outside `C`.

`RouteRStrongApproximationCompactEscape.lean` proves the general common-envelope theorem, the
explicit escape law, and the exact classification

```text
collectively compact strong approximation of fixed receiver
  iff receiver compact
  iff horizontal grade = 0.
```

Globally the collective property is equivalent to RH.  Thus source-specific tightness is not a
hidden weaker repair: it is the exact geometric content still missing, and nonneutral atom manifests
as unavoidable physical compact escape.  The canonical net is now classified exactly as well: it
has one common compact unit-ball envelope iff the grade is zero; at zero its receiver and every
truncation are literally zero.

This removes a false source-exactness shortcut and narrows the open theorem to one precise
category: a cutoff-dependent/unbounded Poisson self-product comparison whose finite coefficient
is recovered only after global renormalization.  Existence and compactness of that comparison
remain unproved.

## Lean realization

`RHTower/RouteRCrossPrimeStokesCalkinPrequotientNoGo.lean` now constructs the literal `(2,3)`
Calderon--Witt source atom and its coefficient-one pre-quotient comparison with the fixed
Stokes--Sonin commutator.  Lean proves that the atom has zero singular-corona class, noncompact
physical image at every nonzero grade, and no linear factorization through the singular corona
even modulo compact operators.  The stronger general finite-support matrix adapter remains open.

The realization reuses:

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
- 2026-08-13 -- Fixed `(2,3)` atom, coefficient-one pre-quotient comparison, off-neutral
  noncompactness, and exact/mod-compact singular-corona no-factorization formalized in
  `RHTower/RouteRCrossPrimeStokesCalkinPrequotientNoGo.lean`; targeted build and axiom audit green.
- 2026-08-13 -- C3b paper proof removes absolute summability: any coherent rectangular Sonin Gram
  exhaustion converging in operator norm to a compact operator has every coefficient zero.
- 2026-08-13 -- C3b formalized in
  `RHTower/RouteRNormConvergentCalkinCoefficientRigidity.lean`; targeted build and axiom audit
  green.  The theorem recovers each off-diagonal coefficient separately before deriving global
  zero-matrix rigidity.
- 2026-08-13 -- C3c paper proof removes convergence and boundedness of the compact counterterm:
  arbitrary stage-dependent compact subtraction cannot make a retained coherent coefficient tend
  to zero in operator norm.
- 2026-08-13 -- C3c formalized in the same norm-convergent rigidity module; targeted build and
  axiom audit green.  Lean permits arbitrary compact `K_N` with neither convergence nor a uniform
  norm bound.
- 2026-08-13 -- C3d paper proof extracts the strongest positive survivor: an eventual uniform
  Calkin gap equal to every retained coefficient modulus, against every stage-dependent compact
  counterterm.
- 2026-08-13 -- C3d formalized: Lean proves the eventual all-compact lower bound and excludes
  frequently recurring compact approximations below the retained coefficient modulus.  Targeted
  build and axiom audit green.
- 2026-08-13 -- C3e paper proof allows a completely varying coefficient matrix and proves every
  asymptotically recovered coefficient is zero under stagewise compact Calkin-norm approximation.
- 2026-08-13 -- C3e formalized.  Lean accepts arbitrary cutoff matrices and compact counterterms,
  proves the varying coefficient lower bound, and forces every recovered limit to zero.  Targeted
  build and axiom audit green.
- 2026-08-13 -- C3f paper proof identifies the complementary topology no-go: every bounded
  operator is a strong limit of compact Hilbert-basis truncations, including Route R's explicitly
  noncompact off-neutral commutator.
- 2026-08-13 -- C3f formalized in `RouteRStrongCompactApproximationBlindness`; module wired into
  `RHTower.lean`, targeted build green, axiom audit only
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-13 -- C3g arbitrary-topology dichotomy formalized in
  `RouteROperatorTopologyCompactnessDichotomy`; topology-only compactness production is now
  dependency-closed, with targeted build and axiom audit green.
- 2026-08-13 -- C3h positive survivor formalized in
  `RouteRStrongApproximationCompactEscape`: actual nonneutral strong truncations escape every
  common compact unit-ball envelope. Targeted build and axiom audit green.
