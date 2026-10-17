# Complete positivity classification of prime-Burnol evolution

Status: STOPPED AFTER USER CLEARED GOAL. CANDIDATE 16, NOT COUNTED.
Verified count remains 15/100. Paper construction and attacks below;
exact Lean formalization and final significance audit are unfinished.

## Exact target and significance

For every `BurnolAccretiveSymbol` psi, classify preservation of the physical
nonnegative cone by its entire strongly continuous contractive evolution:

    (for every t >= 0, psi.evolution(t) preserves nonnegativity)
      iff
    there exists a unique BurnolLevyData D such that
      psi(z) = D.exponent(z) for every Re z > 0.

This covers the full accretive holomorphic prime calculus, including unbounded
generators and infinite jump activity. Equality is on the right half-plane;
arbitrary values of a symbol outside that domain are not classified.
The positivity hypothesis defines the class being classified. No RH, source
admission, or unproved positivity of an actual Xi source is assumed.

Contribution 9 classifies bounded generators by finite jump measures.
Contribution 11 realizes every accretive holomorphic exponent without
classifying positivity. Contribution 14 constructs every Levy datum, including
infinite activity, and identifies its inverse domain, but does not prove this
converse. A unique representation of the whole positive evolution class
would remove that gap. Count at most ONE structural contribution, including
all measure, finite-difference, endpoint, uniqueness and operator helpers.

## Local-corpus comparison

Direct Lean inspection:

- `PrimeBurnolPositiveMeasureClassification` classifies each bounded positive
  eigenoperator by one finite positive shift measure, with norm equal to mass.
- `PrimeBurnolGeneratorMeasure` and `PrimeBurnolFiniteJumpClassification`
  assume a bounded generator. Their scalar correction uses its operator norm,
  which is unavailable for the unbounded class.
- `PrimeBurnolAccretiveEvolution` constructs the contraction and its exact
  eigenaction at every complex rate in the right half-plane.
- `PrimeBurnolLevySymbol`, `PrimeBurnolLevyEvolution`, and
  `PrimeBurnolLevyAsymptotics` construct the data class, prove positivity, and
  recover killing and drift by endpoint limits. No converse or full control
  measure uniqueness appears in these statements.
- `HTGeometry/HausdorffMomentTheorem`, from the CDD moment machinery, gives a
  unique finite positive interval measure for every completely monotone
  sequence. `InfinitesimalCompleteMonotonicity` extracts exponent differences
  by differentiation at time zero, but its existing application is bounded.
- `HTGeometry/HalfLineLaplaceTomography` determines finite half-line measures
  from positive integer Laplace samples alone, without knowing total mass.
  This removes the need for boundary analytic interpolation or a bounded
  exponent assumption.
- `LevyLaplaceKernel`, `LevyLaplaceExponent`, and `LevyLaplaceLimits` already
  supply integrable analytic kernels and endpoint estimates for every finite
  control measure. These are construction inputs, not the missing converse.

The first documented deep search completed over an inventory of 61,624 Lean
files and 1,085,147 declarations. Snapshot age and unmeasured semantic coverage
were reported. Its 20 candidate lemmas and 20 source arguments were inspected:
most were irrelevant; its only ingredient set restated the existing forward
construction. No proof ideas were returned. Research prose is excluded as
mathematical evidence. A second focused search also completed, over 61,626
Lean files and 1,085,172 declarations, with the same coverage limitations.
Its 20 candidate lemmas and 20 source arguments were inspected; finite-
difference sampling was relevant, but the only proposed ingredient set was
an unrelated alternating-series argument. No proof ideas were returned.
There is no exhaustive semantic or external novelty claim.

## Dependency-closed paper construction

1. **Positive time measures.** For each t>=0, the existing bounded positive
   operator classifier gives a unique finite positive measure mu_t on [0,infty)
   whose shift mixture equals the actual operator. Contractivity gives
   mu_t(total)<=1. Its Laplace value at every x>0 is exp(-t psi(x)). These
   values are real nonnegative for every positive t; differentiation at t=0
   gives Im psi(x)=0. Accretivity gives psi(x)>=0.

2. **An interval moment sequence including killing.** Define a(0)=0 and
   a(n)=psi(n) for positive integers. Push mu_t forward by h -> exp(-h), then
   add mass 1-mu_t(total) at interval endpoint 0. This is a probability measure
   with moments exp(-t a(n)) for EVERY n, including zero. Thus all its signed
   finite differences are nonnegative. Differentiate each finite difference
   at t=0 from the right. Since every positive-order difference of the
   constant sequence is zero, the resulting sequence

       m(n) = a(n+1)-a(n)

   is completely monotone. Hausdorff determinacy gives a unique finite
   positive interval measure sigma with m(n)=integral u^n d sigma.

3. **Separate both endpoints before changing variables.** Set

       killing = sigma({0}),   drift = sigma({1}).

   On 0<u<1 put h=-log(u)>0 and

       w(u) = h / ((1+h)(1-u)).

   Define the Levy control eta as the pushforward of w times the interior
   restriction of sigma by u -> h. It has no zero atom. Since
   1-exp(-h) >= h/(1+h), 0<w(u)<=1; eta is finite even when the jump measure
   eta(dh)*(1+h)/h has infinite mass. Thus these data satisfy every field of
   the existing `BurnolLevyData` structure.

4. **Exact integer exponent identity.** For every integer n>=1, telescoping
   and a finite geometric sum give

       a(n) = sum_(j=0)^(n-1) m(j)
            = killing + n*drift
              + integral_(0,1) (1-u^n)/(1-u) d sigma
            = D.exponent(n).

   Endpoint u=0 contributes killing once; u=1 contributes n times drift.
   No finiteness of the unweighted jump measure is used.

5. **Integer observations identify the full evolution.** D already has a
   positive evolution and hence finite shift measures nu_t. At every positive
   integer n the two Laplace transforms agree by step 4. Positive-integer
   Laplace tomography gives mu_t=nu_t, hence equality of the actual bounded
   operators for every t. Their complex-rate eigenvectors are nonzero, so
   exp(-t psi(z))=exp(-t D.exponent(z)) for every Re z>0 and t>=0.
   Differentiation at t=0 yields equality of the exponents on that domain.
   This argument proves the full domain identity without claiming integer
   samples determine an arbitrary holomorphic function.

6. **Uniqueness of all data.** Existing endpoint laws recover killing as
   lim_(x down to 0) psi(x), and drift as lim_(x -> infinity) psi(x)/x.
   After subtracting both, equal holomorphic jump exponents have equal
   derivatives. For h>0 their derivative kernel is (1+h) exp(-z h).
   The finite positive tilted controls (1+h) exp(-h) eta(dh) therefore have
   identical nonnegative integer Laplace transforms. Finite-measure
   determinacy identifies them; the strictly positive finite density can be
   divided out. The zero-atom restriction removes the kernel's invisible
   endpoint. Thus eta, drift and killing are all unique. The existing forward
   positivity theorem proves the reverse implication.

## Attacks and precise limits

- Setting the artificial a(0)=0 is deliberate. It is not a claim that
  psi(0)=0 or that the evolution preserves mass. The added interval atom at
  zero records killing; omitting it would incorrectly exclude killed flows.
- Compact endpoint 1 records drift. Folding it into the logarithmic interior
  measure would create an undefined zero-shift quotient and lose drift.
- No bounded-generator norm, finite jump mass, uniform continuity in operator
  norm, derivative of the semigroup on the whole Hilbert space, or analytic
  continuation across Re z=0 is available or needed.
- Positive integer interpolation alone is false for unrestricted holomorphic
  functions. The proof uses positive finite-measure determinacy at each time.
- No arbitrary C0 semigroup outside the established accretive holomorphic
  prime calculus is included unless its reduction to that calculus is proved.
- Physical positivity is cone preservation, not self-adjointness, positivity
  of a quadratic form, or positivity reflection by an inverse.
- Routine consequences of this classification are not additional counts.

## Formal work and verification plan

First verify exact Mathlib APIs in /tmp, then implement the infinitesimal
Hausdorff sequence, logarithmic interval control, integer identity, positive
time-measure extraction, full operator identity and control uniqueness in
small leaves. One owned foreground Lean process; targeted final checks using
`lake --old env lean -j 1`; no umbrella build or heartbeat increase. Audit
all public axiom lists, exact signatures and definitions; verify source hashes,
objects, umbrella imports, index and lint. Count only after the complete
classification and final independent significance review pass.

## Stopped checkpoint

The user cleared the goal before formal implementation. No new repository
Lean file or umbrella import was added for this candidate. One /tmp scratch
passed `lake --old env lean -j 1` (exit 0, one style warning). It proved the
natural-index finite-difference derivative at time zero, complete monotonicity
of exponent increments from all-time exponential Hausdorff positivity, and
existence/uniqueness of their compact Hausdorff measure. No axiom audit ran;
these helpers are not counted. A separate logarithmic-coordinate/weight
draft was written but never compiled. Both scratch drafts and owned search
artifacts were removed after saving this checkpoint. No owned process remains.

Resume only on a new user instruction. The principal classification,
measure construction, full half-plane identity and data uniqueness remain
unproved in Lean; the paper argument above is the continuation point.
