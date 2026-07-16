# Source-gauge observability trichotomy and compact wall

- **ID:** `source-gauge-observability-trichotomy`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Register:** `[BRIDGE] [PARENT FUNCTIONAL ANALYSIS] [FOUNDATIONAL HT USE] [NOT A NOVELTY CLAIM]`
- **Statement:** For a bounded source boundary and reporter, the reporter restricted to the
  residual source gauge lies in exactly one of three phases: exact blindness, normalized
  approximate blindness, or stable anti-Lipschitz separation. If the residual gauge is
  infinite-dimensional, every compact injective reporter lies in the approximate-blind phase.

## The theorem

Let `Q:E -> B` be a bounded complex-linear source boundary, let `R:E -> F` be a bounded reporter,
and put

```text
G=ker Q,              A=R|G.                                (1)
```

Then

```text
(Q,R) injective  <->  A injective.                           (2)
```

If `A` is injective between complex Banach spaces, Lean proves the exact closed-range law

```text
exists u_n, ||u_n||=1 and A u_n -> 0
  <-> range(A) is not closed.                                (3)
```

Together with the Banach inverse theorem this gives the exhaustive alternatives

```text
exact blind:       (Q,R) is not injective;
approximate blind: (Q,R) is injective and unit gauges become invisible;
stable:            (Q,R) is injective and A is anti-Lipschitz. (4)
```

On Hilbert completions the residual Gram operator

```text
Delta=A^* A >= 0                                             (5)
```

is injective exactly when `(Q,R)` is injective.

The compact strengthening is:

```text
dim G=infinity, R compact, (Q,R) injective
  -> exists u_n in G, ||u_n||=1 and R u_n -> 0.              (6)
```

Indeed, an injective compact operator with closed range would make the identity on its domain
compact and hence force that domain to be finite-dimensional.

## Positive successor

Equation `(6)` rules out stable reconstruction by compact or smoothing reporters on an
infinite-dimensional source gauge. The maximal positive conclusion is exact:

> A stably conservative normalization must contain a noncompact transverse reporter with a
> uniform lower observability bound on the normalized residual gauge.

This is stronger than the common-kernel criterion. Trivial common kernel gives only algebraic
injectivity; it does not exclude normalized gauges whose observation energy tends to zero.

## Novelty gate

Closed-range criteria, approximate versus exact observability, observability Gramians, and the
compact-operator obstruction are standard functional analysis and control theory. The theorem is
therefore not new scientific knowledge. Its value is architectural: it identifies the precise
operator that a genuine HT theory must construct and the noncompactness property any stable
source normalization must possess.

Candidate novelty is moved to
`../../1-in-progress/hypertranscendental-conservativity-spectrum.md`: construct the operator
canonically for a natural HT source, prove all endogenous finite-window reporters compact, and
construct a natural transverse noncompact channel.

## Lean certificate

`formal/GaloisForLFunctions/HTGeometry/SourceGaugeObservabilitySpectrum.lean` proves:

- `hasApproximateUnitKernel_iff_not_isClosed_range`;
- `finiteDimensional_of_compact_injective_isClosed_range`;
- `compact_injective_hasApproximateUnitKernel`;
- `residualGaugeReporter_isCompact`;
- `prod_injective_iff_residualGaugeReporter_injective`;
- `sourceGaugeObservability_trichotomy`;
- `compact_sourceGaugeReporter_hasApproximateUnitKernel`;
- `residualGaugeGram_positive`;
- `prod_injective_iff_residualGaugeGram_injective`.

The certificate has no `sorry`, `admit`, project axiom, opaque postulate, unsafe declaration, or
numerical computation.

## Gates

- [x] exact common-kernel gate strengthened to closed-range observability
- [x] normalized approximate-null equivalence proved
- [x] exact/approximate/stable trichotomy proved
- [x] compact reporter wall proved
- [x] positive noncompact transverse requirement isolated
- [x] Hilbert Gram positivity and injectivity equivalence proved
- [x] external parent theory identified
- [x] formalized in Lean
