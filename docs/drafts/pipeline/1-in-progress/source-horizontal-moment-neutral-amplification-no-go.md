# Source-horizontal moment-neutral amplification and rank--trace no-go

- **ID:** `source-horizontal-moment-neutral-amplification-no-go`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / LEAN-IN-PROGRESS / FALSIFIED RH HANDOFF
- **Source:** `claude-zeta23-rank-trace-audit.md`; `rh-current-frontier-map.md`;
  `formal/GaloisForLFunctions/RHTower/SourceZeroHorizontalCarrier.lean`
- **Statement:** Every off-line source-horizontal Xi copy admits arbitrarily large packets of
  distinct prime-labelled hyperbolic blocks with arbitrarily small average Frobenius-square cost,
  but each nonzero block also adds one positive-index unit. Claude's rank--trace inequality prices
  that unit by `c^2`, so this amplification weakens rather than contradicts the certificate.

## Goal

Test the proposed producer: amplify one retained off-line source class into arbitrarily many
independent hyperbolic blocks while keeping prime-side first and second moments sublinear, then use
the finite Weil rank--trace inequality to force a contradiction.

## Gates

- [x] 0 -> 1 in-progress: exact source coefficients, finite packet, moment budget, and rank--trace
  sign audited.
- [ ] 1 -> 2 fully-proven: independent paper audit of every matrix-normalization convention and
  completed local Lean theorem.
- [ ] 2 -> 3 formalized: targeted module elaboration, module build, lint, and axiom audit pass.
- [ ] 3 -> 4 publication-ready: integrate no-go and positive survivor into RH frontier paper.

## Heavy conjecture loop

### C0 -- raw moment-neutral index amplification

**Frozen conjecture.** For an off-line multiplicity copy `q`, choose arbitrarily many distinct
ordinary primes `p`. Attach the hyperbolic blocks

```text
H(a_p) = [[0,a_p],[a_p,0]],
a_p = sourceZeroHorizontalPrimeCarrier(q,p).
```

Require exact prime labels, the fixed multiplicity copy, reflection `a_p -> -a_p`, raw inertia one
per block, zero trace, and sublinear Frobenius-square growth.

**Verdict: PROVED, but it is not an RH producer.** Off line, every `a_p` is nonzero and the corpus
proves `a_p -> 0` along the cofinite prime filter. Hence for every packet size `k` and every
`eta>0`, one can choose `k` distinct primes with `2 a_p^2 < eta`. The direct sum has signature
`(k,k)`, trace zero, and Frobenius square below `eta k`. Reflection negates every amplitude and
does not change the budget. Thus the requested raw moment-neutral amplification already exists.

### C1 -- rank--trace contradiction from C0

**Frozen conjecture.** Feed the amplified off-line block family into the paper's rank--trace
inequality while retaining the original one-zero off-line count.

**Verdict: FALSIFIED.** In the paper's notation,

```text
||P+Q||_F^2 >= c tr(P) + ... + 2c tr(Q) - c^2 b,
```

where `b` bounds the positive index of `Q`. Each nonzero hyperbolic block contributes one positive
eigenvalue, so `k` independent blocks force `b >= k`; `b` cannot remain the original divisor-pair
count. In the equivalent certificate form the allowance is `+c^2 b`. Increasing raw off-line
index therefore weakens the estimate. The external artifact also formalizes equality models, so
no strengthening using only the same trace, Frobenius square, and index can reverse this price.

### C2 -- uniformly visible amplification

**Frozen conjecture.** Keep each amplified block above a fixed spectral threshold `delta>0` while
retaining sublinear Frobenius growth.

**Verdict: FALSIFIED.** The eigenvalues of `H(a)` are `+|a|,-|a|` and
`||H(a)||_F^2=2a^2`. Therefore

```text
2 delta^2 * #{j : |a_j| >= delta} <= sum_j ||H(a_j)||_F^2.
```

Consequently `k` uniformly visible blocks cost at least `2 delta^2 k`. Sublinear second moment can
amplify only spectrally collapsing blocks. This is the finite-dimensional Schatten/eigenvalue-count
wall, not an artifact of tensoring.

### C3 -- bounded coefficient-faithful spectral quantization

**Frozen conjecture.** Apply a bounded source-derived map which sends every nonzero `a_p` to a
fixed-size projection or involution, then use C2.

**Verdict: FALSIFIED.** Since `a_p -> 0`, every bounded continuous functional-calculus operation
vanishing at zero also tends to zero. Mapping all nonzero `a_p` to fixed size requires the
discontinuous sign/support projection, equivalently unbounded normalization by `1/|a_p|`. The
corpus's fixed-ideal Gamma normalizer theorem classifies that singular operation: forward and
reflected domains coexist exactly at neutral grade. Assuming their coexistence at an Xi divisor is
already equivalent to RH, so quantization relocates the missing producer instead of proving it.

## No-go closure

- **Exact killing theorem/mechanism:** raw inertia has no spectral scale; rank--trace charges each
  positive-index unit independently of amplitude. Uniformly visible inertia has an unavoidable
  linear Frobenius cost.
- **Strongest positive survivor:** off-line source coefficients give arbitrarily large independent,
  label-faithful hyperbolic packets with arbitrarily small average second moment. More generally,
  second moments control only thresholded inertia, never raw inertia. The exact source Schatten
  phase diagram records how fast the blocks collapse.
- **New insight:** moment-neutral amplification is not missing—it is already realized by the source
  prime tail. What is missing is a source law preventing spectral collapse, or equivalently a
  legitimate two-sided unbounded normalization. That is the same simultaneous-orientation/domain
  producer already isolated by Route R.
- **Status:** packet theorem and thresholded inequality are dependency-closed on paper. Lean
  formalization is in progress. Rank--trace sign and tightness are checked against the pinned
  external `zeta-23-lean` artifact.

## External novelty audit

The thresholded inequality is a standard Schatten/eigenvalue-counting principle. The new content
is its coefficient-faithful application to the corpus's actual source-horizontal prime carrier and
the resulting correction of the proposed rank--trace handoff. No external source found a mechanism
that makes raw scale-free inertia contradict a second-moment estimate.

## Log

- 2026-08-10 -- C0 proved on paper; C1--C3 falsified; exact positive survivor and corrected open
  producer isolated.
