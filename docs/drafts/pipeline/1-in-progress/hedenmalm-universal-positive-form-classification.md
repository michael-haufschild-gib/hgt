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
2. Construct the difference-variable positive-definite tempered distribution using a formal
   Schwartz factorization/kernel theorem.
3. Prove the Bochner--Schwartz representation theorem for that distribution.
4. Recover the unique measure representation of `Q` and invoke the already formalized theta
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
The next named lemma is the compact-support locality theorem: disjoint spectral supports must be
orthogonal for the pulled form.

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
