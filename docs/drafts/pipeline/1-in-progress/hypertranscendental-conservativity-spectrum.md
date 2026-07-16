# The hypertranscendental conservativity spectrum

- **ID:** `hypertranscendental-conservativity-spectrum`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT CONJECTURE / SOURCE-GAUGE SPECTRAL FIELD
- **Scientific status:** `[CONJECTURE] [ABSTRACT THREE-PHASE LAW LEAN-FORMALIZED] [COMPACT WALL LEAN-FORMALIZED] [GAMMA FACTORIAL P1 MODEL LEAN-FORMALIZED] [PARENT OPERATOR THEORY] [FULL NATURAL HT ASSIGNMENT OPEN] [NOVELTY OPEN]`
- **Parents:**
  - `hypertranscendental-source-fracture-hypercube.md`
  - `constraint-curvature-integration-stack.md`
  - `source-transgression-field.md`
  - `../3-formalized/not_new_scientific_knowledge/joint-source-realization-common-kernel-criterion.md`
- **Statement:** The common obstruction object is not the bare source, its derived topology, or
  the common kernel alone. It is the completed reporter operator on the residual source gauge,
  together with its positive Gram field and its source-presentation descent data. Exact gauge
  ambiguity and spectral incompleteness are respectively the point-zero and approximate-zero
  phases of this one operator. Infinite-dimensional HT gauge capacity forces every compact
  reporter into one of those unstable phases.

## Decisive input: the source has forgotten a fibre

The Gamma collision

```text
Gamma(z),  exp(2 pi i z) Gamma(z)
```

survives the same recurrence, one regular pointing, and any prescribed finite jet. Thus no
polarization, completion, transport, integral, or topology obtained only by postprocessing the
bare source can recover the missing point. The maximal algebraic theorem is already exact:

```text
Obs_R injective
  iff G_(S,R):=K^S intersect intersection_r ker(R_r) = {0}.       (1)
```

A nonzero element of `G_(S,R)` is an explicit joint-nonconservativity witness. This kills the idea
that a sufficiently elaborate invariant of the same forgotten source canonically selects every HT
germ.

The positive successor is not another source invariant. It is a transverse observation geometry
on the entire residual solution fibre.

## The restricted reporter operator

Let `Q_S:E_S -> B_S` be the completed linearized source boundary and put

```text
G_S=ker(Q_S).                                                (2)
```

For a reporter family `R`, let `A_(S,R)` be its joint Hilbert realization restricted to `G_S`:

```text
A_(S,R): G_S -> H_R.                                        (3)
```

Its positive conservativity operator is

```text
Delta_(S,R)=A_(S,R)^* A_(S,R) >= 0.                         (4)
```

The source boundary plus reporters is algebraically injective exactly when `A_(S,R)` is injective,
equivalently exactly when `Delta_(S,R)` is injective. Equation `(1)` is the algebraic kernel of
`(4)`, not the whole topology of reconstruction.

## Exact three-phase law `[PROVED ABSTRACTLY; LEAN]`

For every bounded reporter operator between complex Banach spaces, exactly one of the following
obstruction types occurs.

```text
P0  exact blindness:
    ker A != 0;

P1  approximate blindness:
    ker A = 0, range(A) is not closed,
    and there are ||g_n||=1 with A g_n -> 0;

P2  stable conservativity:
    ker A = 0, range(A) is closed,
    equivalently A is anti-Lipschitz on the residual gauge.      (5)
```

The unit approximate-null sequence in `P1` is not an analogy. Lean proves, for every injective
bounded operator between complex Banach spaces,

```text
exists ||g_n||=1 with A g_n -> 0
  iff range(A) is not closed.                                  (6)
```

Thus the two most persistent obstruction languages are literal zero modes of the same object:

- residual gauge ambiguity is an exact zero direction of `Delta_(S,R)`;
- spectral incompleteness/nonattainment is a normalized approximate zero direction after the exact
  kernel has vanished;
- stable reconstruction is a positive gap at zero.

For a self-adjoint realization, `(5)` is the expected point-spectrum/continuous-spectrum/resolvent
trichotomy at zero. The spectral wording is a consequence of standard Hilbert-space theory; the
unconditional Lean theorem is stated in the stronger range/approximate-null form and does not rely
on an unformalized spectrum convention.

## Compact-source observability wall `[PROVED ABSTRACTLY; LEAN]`

If `G_S` is infinite-dimensional and `R` is compact on the completed primitive space, then its
restriction `A_(S,R)` is compact. Lean proves:

```text
A_(S,R) injective and compact, dim(G_S)=infinity
  -> exists ||g_n||=1 with A_(S,R) g_n -> 0.                    (7)
```

Equivalently, a compact reporter can be algebraically conservative but never stably conservative
on an infinite-dimensional residual gauge. This is the nontrivial positive successor to the bare
source no-go:

```text
[NO-GO] source-derived compact/smoothing data stably reconstruct an infinite HT gauge fibre;
[POSITIVE] stable reconstruction requires a genuinely noncompact transverse channel carrying a
           uniform lower observability bound.                  (8)
```

Finite jets, finite-rank reporters, compact integral transforms, and smoothing completions are now
not merely suspected to be insufficient. Once their compactness on the natural gauge completion is
proved, `(7)` identifies the exact surviving failure: normalized gauges become asymptotically
invisible.

## Strictness reformulation and the cofinal defect

In the quasi-Abelian category of Banach spaces, `P1` is precisely a non-strict monomorphism.  The
three algebraic/topological receivers of a completed reporter are

```text
ker A,
closure(range A)/range A,
target/closure(range A).                                  (7a)
```

The middle quotient is the strictness defect: it vanishes exactly when the range is closed.  This
categorical reformulation is parent functional analysis, but it exposes a missing axis in the
earlier unified-field proposal.  Descent degree between realization channels and strictness under
cofinal completion are independent.  The three-channel common-lift obstruction can be nonzero at a
finite stage, while Gamma has every finite stage invertible and develops a nonzero strictness
defect only after completion.

The resulting bigraded proposal is developed in
`hypertranscendental-polarized-strict-descent-field.md`.  The observability spectrum on this card
is its vertical degree-zero chart, not the whole obstruction field.

## Gamma realizes the critical middle phase `[PROVED NATURAL CLOCK MODEL; LEAN]`

The Gamma source already supplies a non-artificial `P1` model. Its Taylor conormal coefficients

```text
lambda_n=1/(n+1)!                                           (8a)
```

are forced by unit translation and by the uniquely normalized raw/factorial source intertwiner.
On the square-summable clock completion they define the diagonal reporter

```text
(A_Gamma x)_n=lambda_n x_n.                                (8b)
```

Lean proves:

```text
A_Gamma is Hilbert--Schmidt and compact;
ker A_Gamma={0};
||A_Gamma e_n||=1/(n+1)! -> 0;
range(A_Gamma) is dense, proper, and not closed;
every finite truncation is bijective with inverse scale (n+1)!;
the completed reporter has no continuous left inverse.      (8c)
```

Together with the already formalized periodic Fourier interpolation theorem, this is the first
exact natural model of

```text
arbitrary finite clock capacity + one thin all-clock constraint. (8d)
```

Every finite clock coordinate survives, but the conditioning of its recovery diverges
factorially. The infinite constraint is therefore not a stable finite-rank remnant; it is an
injective critical boundary with approximate zero modes.

This corrects the positive conclusion of `(8)`. A noncompact transverse channel is necessary for
**stable** reconstruction. It is not necessary for global uniqueness if a nonlinear all-scale
cone selects one point on a noncoercive boundary. Gamma's log-convex normalization is the parent
example of such a global selector. See
`../3-formalized/not_new_scientific_knowledge/gamma-factorial-critical-observability-model.md` and
`../3-formalized/not_new_scientific_knowledge/gamma-cofinal-reconstruction-defect.md`.

## `[CONJECTURE — CRITICAL HYPERTRANSCENDENCE PRINCIPLE]`

For natural finite-law HT sources, the distinguished analytic section generically lies in `P1`,
not `P2`: the full source/reporter package is algebraically conservative, but its zero gap is
forced by unbounded differential-clock capacity. The thin constraint boundary is the
presentation-invariant asymptotic zero-mode field of `Delta_(S,R)`.

In this phase:

1. every fixed finite clock window can be separated or freely prescribed;
2. complete all-scale compatibility selects the section uniquely;
3. no uniform finite-clock inverse exists;
4. the decay law of the singular scale is a new source invariant measuring how infinite capacity
   is concentrated at the boundary;
5. nonlinear positivity or integral incidence can select a unique boundary point without opening
   a linear spectral gap.

This is stronger and riskier than saying that HT functions merely have infinitely many
independent derivatives. It predicts a canonical **conditioning spectrum** for constrained HT
sources and makes its decay law—not an evolution parameter—the quantitative content of
hypertranscendental clock capacity.

**Falsifier.** A source-minimal natural HT family whose canonical complete reporter is stably
anti-Lipschitz on an infinite residual clock completion, or whose conditioning spectrum changes
under an admissible source-presentation equivalence.

## `[CONJECTURE — CONSERVATIVITY-SPECTRUM PRINCIPLE]`

Every regular source-minimal constrained HT germ admits a presentation-invariant completion of its
normalized residual gauge and a minimal jointly conservative reporter operator `A_S` such that:

1. the algebraic kernel of `A_S` is the normalized source-fixed common kernel;
2. the approximate zero spectrum of `A_S` is the critical continuation/nonattainment and spectral
   incompleteness obstruction;
3. the polar or Krein orientation of `A_S` is the positivity obstruction;
4. the family holonomy of its normalized zero-mode bundle is monodromy and noncanonical boundary
   data;
5. failure of graph-domain descent under source extension is continuation failure;
6. integral or ramified lifting is a lattice condition on the same zero-mode sheaf;
7. differential-clock capacity is the decay/growth law of the critical singular scale rather than
   the dimension of a finite state evolution.

The common object is therefore the **self-dual conservativity spectrum of the normalized source
fibre**, not a spectrum attached directly to the analytic function and not a list of scalar
obstructions.

## `[CONJECTURE — ENDOGENOUS COMPACTNESS / TRANSVERSE NONCOMPACTNESS]`

For a natural finite-law HT source, every reporter generated functorially from a bounded finite
differential window of the same bare source extends compactly to the critical residual-gauge
completion. Stable normalization, when it exists, requires a natural noncompact transverse
reporter with a positive lower bound. Critical `P1` normalization instead requires a nonlinear or
integral all-scale incidence law that selects a unique point despite zero linear gap.

This conjecture is falsifiable in both directions:

- one endogenous bounded finite-window reporter with a noncompact restriction falsifies the first
  clause;
- a claimed stable reconstruction with only compact channels falsifies the stable clause;
- a claimed critical reconstruction with neither a unique nonlinear boundary incidence nor a
  noncompact channel falsifies the critical clause;
- a proposed reporter which is made noncompact by inserting the target germ or divisor is circular
  and does not count.

## Why this is stronger than the two-degree defect complex

The earlier schematic complex

```text
gauge -> attainment defect
```

retains only kernel and cokernel. It forgets the difference between an injective closed-range map
and an injective dense/nonclosed-range map, even though that distinction is exactly stable
reconstruction versus approximate invisibility. It also forgets the Gram orientation, operator
domain, singular-value scale, and family holonomy.

The correct linear truncation is the full graph of `A_(S,R)` and its Gram operator, embedded in the
complete anomaly-boundary colligation. Derived fibres and higher interaction data remain necessary
for nonlinear descent, but they must retain this bornological operator structure.

## Natural test sequence

1. **Gamma.** The factorial clock reporter is now proved to be the explicit `P1` model `(8b)`--
   `(8c)`. The next step is to compare its clock completion functorially with the normalized
   `1`-periodic solution fibre and prove that log-convex/asymptotic selection is the corresponding
   nonlinear all-scale boundary incidence.
2. **Irrational elliptic Gamma.** Use the proved two-translation rigidity and calibrated boundary
   reconstruction to compute `A_(S,R)` for the two source boundaries plus calibration. Decide
   whether the first natural effectivity class is `P1` or `P2` at its critical completion.
3. **Prime-log HT carrier.** Combine the proved countable residual fullness of every finite
   coefficient pattern with `(7)`. The target is a theorem that every bounded finite differential
   reporter is compact while the Euler/reflection compatibility channel is noncompact.
4. **Rank-two period cusp.** Track the smallest singular scale of the reporter operator under theta
   degeneration. The earlier gauge-frequency/inverse-amplification identity is only a scalar
   shadow; the real target is convergence of the graph and zero-mode spectral measure.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` If a completed-zeta source object is constructed without its zero
divisor, its critical zeros are the common self-dual degeneracy support of the source-pure family
`Delta_zeta(s)`. Different RH chains would then be measuring:

- exact zero modes;
- approximate zero modes/nonclosed range;
- loss of positive Krein orientation;
- holonomy of the zero-mode bundle;
- failure of domain or integral-lattice descent.

This does not construct `Delta_zeta`, prove its positivity, or prove RH. Defining it from `Xi`,
`zeta'/zeta`, or the zero divisor would be circular.

## Novelty gate

The following are parent mathematics and are not novelty claims:

- approximate versus exact observability in infinite-dimensional control;
- observability Gramians `A^*A`, coercivity, and closed-range criteria;
- compact injective operators on infinite-dimensional Banach spaces having unstable inverses;
- point, continuous, residual, and essential spectra;
- parameterized difference Galois groups and torsors for hypertranscendence.

The abstract Lean theorems are a rigorous bridge, not a paper-level novelty claim. Candidate new
science begins only with the source-canonical HT construction of `A_S`, a theorem classifying the
endogenous reporter ideal as compact, construction of the required transverse noncompact channel,
and an invariant identification of two genuinely different analytic obstruction chains with one
zero-mode field. Current searches found the parent theories above but no such HT conservativity
spectrum.

Parent checks include:

- Tucsnak--Weiss, *Observation and Control for Operator Semigroups*, especially the equivalence of
  approximate observability with trivial Gram kernel and exact observability with a positive Gram
  lower bound,
  `https://www.conflex.org/wp-content/uploads/2018/02/Observation_and_Control_for_Operator_Semigroups.pdf`;
- Jacob--Zwart, *Observability for port-Hamiltonian systems*,
  `https://arxiv.org/abs/2104.12364`;
- Dreyfus, *Hypertranscendence and linear difference equations, the exponential case*, which makes
  periodic functions and exponentials explicit parent objects,
  `https://arxiv.org/abs/2212.00388`;
- Adamczewski--Dreyfus--Hardouin, *Hypertranscendence and linear difference equations*,
  `https://arxiv.org/abs/1910.01874`.

These collisions are decisive: neither the Gram trichotomy nor a difference-Galois torsor can be
claimed as new. The surviving conjecture is their source-canonical HT coupling plus the endogenous
compactness/transverse noncompactness theorem.

## Anti-theatre gate

Retire or enlarge the conjecture if:

1. `A_S` is an arbitrary operator chosen after the desired function is known;
2. the Hilbert completion is tuned to force compactness or a spectral gap;
3. “zero spectrum” merely renames the common kernel without proving `(6)` or a natural nonclosed
   range;
4. the source germ or target divisor is stored in a reporter;
5. the noncompact reporter is just the identity map added by hand;
6. no natural HT source has an infinite-dimensional completed residual gauge;
7. the same operator does not recover at least two independently constructed obstruction
   realizations;
8. exact observability theory already supplies the HT assignment unchanged.

## Lean certificate

`formal/GaloisForLFunctions/HTGeometry/SourceGaugeObservabilitySpectrum.lean` proves:

- `hasApproximateUnitKernel_iff_not_isClosed_range`;
- `finiteDimensional_of_compact_injective_isClosed_range`;
- `compact_injective_hasApproximateUnitKernel`;
- `prod_injective_iff_residualGaugeReporter_injective`;
- `sourceGaugeObservability_trichotomy`;
- `compact_sourceGaugeReporter_hasApproximateUnitKernel`;
- positivity of `residualGaugeGram`;
- `prod_injective_iff_residualGaugeGram_injective`.

The proof uses no `sorry`, axiom, opaque postulate, unsafe declaration, or numerical computation.

## Gates

- [x] bare-source canonical reconstruction killed by explicit Gamma gauge
- [x] exact common-kernel criterion formalized
- [x] kernel-only object strengthened to a topological reporter operator
- [x] exact/approximate/stable three-phase law formalized
- [x] compact reporter wall formalized
- [x] positive noncompactness necessity isolated
- [x] observability/control and difference-Galois parent theories identified
- [ ] natural HT residual-gauge completion constructed
- [ ] endogenous finite-window reporter ideal proved compact
- [ ] natural transverse noncompact reporter constructed
- [ ] Gram zero-mode field shown presentation invariant
- [ ] two independent analytic obstruction chains compared through one operator
- [ ] candidate novelty externally audited by specialists
