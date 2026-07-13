# Universal classification of positive Hedenmalm theta forms

- **ID:** `hedenmalm-universal-positive-form-classification`
- **Stage:** 1-in-progress
- **Type:** THEOREM / COMPLETE NATURAL-CATEGORY HILBERT--POLYA CLASSIFICATION
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:**
  - `hedenmalm-cyclic-null-form-nonclosability.md`;
  - `../3-formalized/not_new_scientific_knowledge/hedenmalm-spectral-orientation-classification.md`;
  - `../2-fully-proven/new_scientific_knowledge/hedenmalm-theta-pair-divisor-supported-metric-law.md`.

## Target theorem

Let `Q` be a jointly continuous nonnegative sesquilinear form on complex Schwartz space. Assume
that the Hedenmalm momentum operator is symmetric for `Q` and that the normalized theta source `k`
is null. Then there should exist a unique positive Borel measure `mu` of temperate growth such that

```text
Q(u,v)=integral_R hat(u)(t) conjugate(hat(v)(t)) dmu(t),
```

and necessarily

```text
mu=sum_(gamma in R:Xi(gamma)=0) c_gamma delta_gamma,
c_gamma>=0.
```

Consequently every such nonzero form is purely singular relative to ordinary Lebesgue `L^2`: its
ordinary-`L^2` radical image is dense and proper, its induced ordinary-`L^2` quotient seminorm is
zero, and it is not sequentially closable.  Conversely every positive temperate atomic weight on
the real `Xi` divisor gives such a form.

For the Hedenmalm eigenfunction family, strict positivity on every nonzero divided eigenstate
should force every centered zero to be real and every analytic multiplicity to be one. Thus the
classification separates the unconditional theorem from the still-open orientation producer:

```text
all natural positive theta metrics
  = positive atomic weights on the real Xi divisor;

a conservative natural theta metric
  => RH plus simplicity.
```

## Proved components

1. The actual normalized theta source is translation-cyclic in ordinary `L^2`.
2. Every nonzero nonnegative momentum-symmetric theta-null Schwartz form is purely
   ordinary-`L^2` singular and nonclosable.
3. The entire temperate spectral-measure subclass is faithful and classified exactly:
   theta nullity is equivalent to real-divisor support, and nullity plus ordinary-`L^2`
   closability is equivalent to the measure being zero.
4. Positive divisor-supported weights symmetrize the centered spectral coordinate; strict
   positivity on every Hedenmalm eigenfunction forces RH and simplicity.

## Open core

The missing implication is the classical Bochner--Schwartz converse in the exact formal category:

```text
jointly continuous + nonnegative + simultaneous-translation invariant
  => unique positive temperate spectral measure.
```

Momentum symmetry already implies simultaneous-translation invariance.  The corpus contains the
constructive measure-to-form direction but not the converse.  Mathlib also explicitly records that
the Schwartz kernel theorem is future work.  No representation measure may be introduced as an
assumption in the target theorem or final paper.

## Formalization route

1. Curry a continuous Schwartz sesquilinear form into continuous tempered distributions.
2. Prove compact spectral locality directly from symmetric functional calculus, without a
   Schwartz kernel theorem.
3. Extend strict quadratic-packet locality to arbitrary disjoint compact supports and construct
   the resulting positive order-zero distribution. The locality half is complete; the order-zero
   distribution remains open.
4. Apply Riesz--Markov/positive-distribution representation to recover the unique temperate
   measure and invoke the already formalized theta
   support, atomicity, radical, and nonclosability theorems.
5. Audit the divided-eigenstate conservativity statement for multiplicities without assuming
   simplicity.

Step 1 is complete in
`formal/GaloisForLFunctions/SchwartzSesquilinearTempered.lean`: the fixed-second-argument
functional is constructed as an actual tempered distribution, momentum symmetry is proved to be
its derivative intertwining law, and translations act contragrediently on the test and parameter
arguments. The module builds exactly and is axiom-clean.

The spectral transfer needed for Step 2 is also complete in
`formal/GaloisForLFunctions/SchwartzSpectralPullbackForm.lean`.  It constructs the Fourier-pulled
form, proves that nonnegativity survives the pullback, identifies physical momentum with exact
multiplication by `2*pi*t`, and propagates symmetry to every power of that spectral coordinate.
The kernel-free algebraic core of compact-support locality is now complete.  For any symmetric
continuous multiplier `A`, if `A^n f -> 0` and the second packet has inverse-power factors
`h_n -> 0` with `A^n h_n=g`, continuity forces `Q(f,g)=0`.  The concrete positive quadratic
separator

```text
A_(lambda,C)(t)=C^(-1)(1+(2*pi*t-lambda)^2)
```

is proved symmetric directly from momentum symmetry.  The complete analytic compact-packet
contraction theorem is now formalized.  Faà di Bruno expresses every derivative of the `n`th
separator power as a finite sum of terms

```text
n.descFactorial(k) q^(n-k),   0 ≤ q < 1,
```

and each term tends to zero.  Uniform compact support lifts the resulting derivative estimates to
every polynomially weighted Schwartz seminorm.  The reciprocal multiplier

```text
C/(1+(2*pi*t-lambda)^2)
```

is proved temperate, its powers converge on every compact outer packet, and it is an exact
inverse-power factor.  Hence a momentum-symmetric continuous form makes every strict inner packet
orthogonal to every compact outer packet.  No Schwartz kernel theorem or representation measure
is assumed.

Arbitrary compact locality is now complete without a finite partition. Urysohn separation and
Weierstrass approximation produce one real polynomial `P` near zero on the first compact spectral
packet and near two on the second. The positive functional-calculus separator

```text
A_P(t)=(1+P(2*pi*t)^2)/2
```

is symmetric, temperate, and globally invertible; its direct powers contract the first packet and
the reciprocal powers contract the second. Therefore any two Schwartz maps with disjoint compact
spectral supports are orthogonal for the pulled form. The remaining Step 3 obligation is exactly
the positive order-zero distribution construction, followed by Riesz--Markov representation.

## Significance gate

The Bochner--Schwartz theorem itself is classical infrastructure.  Publication-level significance
must come from the complete classification of Hedenmalm's 2026 theta inner-product problem and the
forced pure singularity of every nonzero natural metric.  Until the converse is formalized and a
primary-literature audit finds no existing classification, the package remains below 90/100.

## Preliminary literature boundary

Targeted searches locate the classical Bochner--Schwartz and positive-form representation
literature, but no paper applying it to Hedenmalm's June 2026 theta pair, no classification of his
sesquilinear-form search, and no pure ordinary-`L^2` singularity theorem for the normalized theta
source.  Because the parent preprint is only weeks old, this absence is provisional rather than a
completed novelty certificate.  The classical representation theorem must be credited as
infrastructure; only the source-specific classification can carry scientific novelty.
