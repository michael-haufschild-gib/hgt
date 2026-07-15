# Finite observable/Koopman hypertranscendence boundary

- **ID:** `finite-observable-koopman-hypertranscendence-boundary`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM, `[GENERAL HT]`, `[ML/AI BRIDGE]`, `[POSITIVE ESCAPE LAW]`
- **Scientific status:** `[LEAN-VERIFIED] [STANDARD FINITE-RANK PARENT THEORY] [NOT AN RH PROOF]`
- **Formal module:**
  `formal/GaloisForLFunctions/HTGeometry/FiniteObservableKoopmanBoundary.lean`

## Result

Let `V` be a finite-dimensional complex linear space of complex-valued clock observables.  Say
that it is an exact infinitesimal invariant model when

```text
g in V  implies  deriv(g) in V.                           (1)
```

Lean proves that if `f in V`, then every derivative observable `f^(n)` lies in `V`.  Finite
dimension forces a nontrivial linear relation among these jets, hence there is a polynomial
`L != 0` such that

```text
L(D)f=0.                                                   (2)
```

Consequently

```text
f in V and D(V) subset V  implies  f is differentially algebraic.  (3)
```

In particular, if `f` is hypertranscendental, then

```text
f notin V                                                  (4)
```

for every finite-dimensional derivative-invariant observable space `V`.

## Positive escape law

The useful positive form removes the invariant-space premise entirely.  For every finite-
dimensional observable space `V` and every hypertranscendental `f`, Lean proves

```text
there exists n such that f^(n) notin V.                    (5)
```

Thus an HT clock has an observable tower that escapes every fixed finite feature dictionary.  A
finite learned model may be approximate, but exact derivative closure has a certified failure at
some observable depth.  This is the nontrivial positive statement retained from the finite-model
no-go.

## ML/AI relation

Finite Koopman, EDMD, and learned latent-linear methods seek a finite dictionary spanning an
invariant or nearly invariant observable subspace.  Equation `(3)` identifies the exact-
realization boundary for complex clock functions: exact infinitesimal closure is a differential-
algebraic certificate.  Equation `(5)` gives the HT-side escape certificate.

This is not merely a neural-network name attached to an old theorem.  The module adds the missing
finite-submodule interface, constructs the nonzero constant-coefficient annihilator from finite
rank, proves the DA classification, and exposes the universal derivative-escape consumer.  It
composes with `FiniteGibbsDifferentialBoundary.lean`, whose earlier result characterized infinite
constant-coefficient spectral complexity by linear independence of the derivative observables.

## Clock interpretation

Although Koopman methods originate in dynamical systems, the Lean theorem uses no state trajectory
or temporal propagator.  Differentiation is the clock readout ordering the observable jet family.
Hypertranscendence is detected by the impossibility of placing all those readouts into one finite
closed observation space.  This is exactly “observability structure of a clock, not temporal
evolution.”

## Relation to existing corpus boundaries

- `FiniteGibbsDifferentialBoundary.lean` excluded finite exponential spectra and identified
  derivative-observable linear independence.  The new module upgrades this from a particular
  spectral basis to every finite-dimensional derivative-invariant observable subspace.
- `finite-spectral-hankel-dimension-boundary.md` excludes fixed-width moment/spectral models by
  Hankel singularity.  The present theorem is complementary: it acts directly on arbitrary
  function-space dictionaries and produces a differential annihilator.
- `hypertranscendental-clock-observable-boundary.md` gives the algebraic jet-field erosion law.
  Equation `(5)` is its analytic linear-observable counterpart.

## Genetics/genomics relation

Finite gene-regulatory and learned genomic latent models often use finite feature dictionaries,
but no biology-specific exact closure premise was found that strengthens `(1)`.  The corpus already
contains the exact Price selection-covariance and size-bias response laws in
`NormalizedMomentQuantumVariance.lean`.  Those were retained as existing direct applications; no
duplicate genetics wrappers were added.

The next potentially useful genomics target is therefore not another covariance identity.  It is a
source-defined theorem that a concrete gene-regulatory observable dictionary is exactly closed, or
a quantitative lower bound on its unavoidable closure residual.  Neither is asserted here.

## RH impact

This theorem does not locate zeta zeros.  Its immediate RH value is architectural and negative-
positive:

1. any exact finite learned/Koopman latent model for an HT source is impossible;
2. the positive successor is an unbounded observable-rank or nonvanishing closure-residual theorem;
3. an RH route cannot outsource the missing source orientation to a fixed finite AI feature model;
4. ML may still search for approximate source inequalities, but a rigorous route must prove a
   source-uniform residual/gap rather than exact finite closure.

For the present RHTower, the source-specific orientation/sign theorem remains the hard part.  The
new result prevents a finite latent redressing of that problem and gives a precise research route:
quantify how the prime--Gamma derivative observables escape learned finite dictionaries, then test
whether that escape lower bound feeds an existing Gram/Hankel or orientation consumer.

## Verification

- the one missing exact module cache was built;
- the touched file passed a direct Lean check;
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`;
- the repository formal lint gate passes;
- no numerical computation, full project build, or concurrent Lean process was run.

## Literature

- S. L. Brunton, B. W. Brunton, J. L. Proctor, and J. N. Kutz, *Koopman Invariant Subspaces and
  Finite Linear Representations of Nonlinear Dynamical Systems for Control*, PLOS ONE 11 (2016),
  e0150171.  Finite exact representations arise by restricting the Koopman operator to invariant
  observable subspaces: <https://pmc.ncbi.nlm.nih.gov/articles/PMC4769143/>.
- B. Lusch, J. N. Kutz, and S. L. Brunton, *Deep learning for universal linear embeddings of
  nonlinear dynamics*, Nature Communications 9 (2018), 4950.  Neural architectures learn Koopman
  eigenfunction coordinates and finite latent linear representations:
  <https://www.nature.com/articles/s41467-018-07210-0>.
- N. Takeishi et al., *Neural Tangent Kernels and Fisher Information Matrices for Simple ReLU
  Networks with Random Hidden Weights*, for the NTK/Fisher lane audited but not wrapped because its
  Gram content is already present: <https://arxiv.org/abs/2507.18555>.

## Gates

- [x] finite derivative-invariant observable-space interface
- [x] propagation of membership through every derivative observable
- [x] finite rank forces a nonzero constant-coefficient annihilator
- [x] finite exact observable closure implies differential algebraicity
- [x] HT excludes every finite exact invariant observable model
- [x] HT derivative tower escapes every finite-dimensional observable space
- [ ] quantitative source-uniform escape residual for prime--Gamma observables
- [ ] feed such a residual into an existing strict Gram/Hankel or orientation theorem
- [ ] RH
