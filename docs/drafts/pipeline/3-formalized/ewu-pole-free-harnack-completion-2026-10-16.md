# EWU: remove the pole-free extension defect

Status: formalized; targeted `.olean` builds and direct Lean audits passed. Evidence comes from Lean source and the corpus search tool. No external search, numerical experiment, or novelty audit.

## Verified starting point

`EvenSectorPoleWeightUniqueness` already proves exact signed evenization, absolute Dirichlet convergence from even pole-free positivity, and source uniqueness for every finite pole weight. Repeating that result would not advance this task.

`EvenSectorPolarRigidity` and `EvenSectorPoleFreeLogThreshold` still need an arithmetic lower-floor hypothesis to extend pole-free positivity to the full even cone. `CHMDStage7HyperbolicCoshFactorizationAndEvenSubblindDecomposition` isolates the negative double-pole obstruction. The new absolute convergence theorem removes its convergence premise, but does not by itself remove its Abel-limit premise.

## Conjecture loop

1. Automatic finite-pole extension from positivity on a codimension-one kernel. Rejected as an abstract argument: positivity on that kernel does not control a mixed term against its null vectors. A pole-value/first-jet defect can be invisible on pole-free autocorrelations. Arithmetic structure must do additional work.
2. Use the signed Toeplitz estimate alone to remove the double-pole term. Not established: its dyadic absolute mass scale still permits a logarithmic mean source and hence a double pole. A structural cancellation or rigidity identity is needed, not a better constant.
3. Exact hyperbolic window identities alone do not eliminate the defect. `WeilWorkExposingRayCoshDoubling.exists_positive_linear_cosh_doubling` supplies an explicit repeated-pole survivor. Pairwise real-axis recurrence is the wrong information to iterate.
4. **Succeeded, Lean verified:** retain all frequency twists of the detuned packet, then use holomorphy to eliminate the invisible pole direction. No Laurent expansion is needed.
5. **Succeeded, Lean verified:** the same source extends automatically to every compact complex test. The even pole-free and full Weil source sets are exactly equal, and every source is canonical on `n >= 2`.

## Dependency-closed paper proof for conjecture 4

For a source in the even pole-free cone, detuned reflection gives the signed real multiplicative Toeplitz inequality. Apply it to real and imaginary parts of an arbitrary complex coefficient sequence and add. The real part of each complex correlation is exactly the sum of those two real correlations, and their masses add to the complex squared norm. Thus every unitary logarithmic character is available, with a constant independent of its frequency.

Insert `c(m)=m^(-1/2) exp(i t log m)` below the cutoff. The resulting signed harmonic density is at most `C(1+log N)^2`, uniformly in every real `t`. The existing signed cumulative Laplace identity, absolute convergence already proved from detuning, and the residue-one harmonic factor give `s Re F(s+it) <= M` for all sufficiently small positive `s` and every `t`, where `F(z)=sum_{n>=2} lam(n)n^(-1-z)` is holomorphic for `Re z>0`.

The decisive analytic mechanism is local Harnack propagation with a freely chosen anchor. Suppose `Re F(z)<=M/Re z` on `0<Re z<r`, with `M>=0`. Fix `0<d<r/2` and `0<s<d`. On the disc centered at `d` with radius `d-s/2`, the holomorphic function `G(z)=2M/s-F(z)` has nonnegative real part. The corpus Harnack inequality at `s` has factor `4(d-s)/s <= 4d/s`. Writing `A=|Re F(d)|` yields

`-s^2 Re F(s) <= 8 M d + 4 d s A + s^2 A`.

Choose the anchor `d` small first, then let `s` tend to zero. This proves that the negative quadratic boundary defect vanishes. The original upper bound also makes the positive quadratic defect vanish. There is no meromorphic continuation, residue, coefficient sign, numerical calculation, or assumed Abel limit in this argument.

The existing sharp untwisted even density ceiling and Abel correction now extend pole-free positivity to the actual pole-weight-one even functional. Existing even-to-full positivity then gives full positivity for the same arithmetic source. The intended main result is this exact automatic completion of the test cone, not another RH equivalence or a conditional receiver with a new analytic premise.

### Proof attacks

- The generic codimension-one counterexample does not have the uniform all-frequency arithmetic ceiling; it cannot refute this argument.
- A negative double pole has positive real part of quadratic size on slanted approaches, violating that ceiling. The Harnack proof covers nonmeromorphic defects too.
- The anchor is fixed before `s` tends to zero. Its possibly large value `F(d)` is finite by absolute convergence and is multiplied by terms tending to zero.
- The Harnack disc stays entirely in the convergence half-plane and inside the strip on which the uniform ceiling holds.
- Complex characters are obtained by adding two legitimate even real packet inequalities; no unsupported parity-preserving modulation is assumed.

## Formal implementation

- `HTGeometry/HolomorphicQuadraticBoundary.lean`: the generic one-sided holomorphic boundary theorem is compiled, with no heartbeat changes.
- `RHTower/EvenSectorTwistedAbel.lean`: complex detuned Toeplitz forms, every logarithmic twist, and the uniform vertical Abel ceiling are compiled.
- `RHTower/EvenSectorPolarCompletion.lean`: actual L-series holomorphy, exact twisted real-part identity, quadratic defect removal, automatic pole completion, full test-cone completion, and canonical source identification. Compiled and directly audited.
- `WeilWorkExposingRayCriticalTwists.positive_twisted_harmonic_bound` was made public so the existing generic character argument can be reused without duplicating its proof.

The new unconditional capstone is `evenPolar_sourceCone_eq_full_sourceCone`. Its statement has no premises. It identifies the actual arithmetic source sets; it does not assert their nonemptiness or add an RH equivalence.

## Final verification

- Targeted foreground builds used `lake --old build` for the three new leaves and the reused character lemma's module. All completed successfully. No umbrella or full build was run.
- Final `lake env lean` audits of `HolomorphicQuadraticBoundary.lean`, `EvenSectorTwistedAbel.lean`, `EvenSectorPolarCompletion.lean`, and `WeilWorkExposingRayCriticalTwists.lean` all exited zero with no output, errors, or warnings.
- A separate `/tmp` audit checked eight key declarations with `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`. No added axioms, admitted proofs, computational certificates, or heartbeat overrides.
- All three new leaves are wired into their theorem-area umbrellas. `scripts/formal_tools.py index` refreshed generated declaration indexes and the search database.
- `scripts/formal_tools.py lint` found one unrelated concurrent wiring error: `RHTower.PaperThetaSpatialSolvability` was not reachable from its umbrella. The EWU modules are reachable. Existing large-file warnings were outside this contribution.
- The earlier requested `CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion` is already wired; its `.olean` is newer than its source.

## Frontier change and limitation

Previously, pole-free completion required an external lower floor or the absence of a negative double pole. The new proof derives the missing boundary cancellation from the cone's arithmetic structure itself. This is a completion of the actual test cone, followed by source classification, rather than an additional condition awaiting a proof.

No existence theorem for this cone is claimed. In particular, the contribution does not prove RH. The next unresolved burden is to produce a source in the identified cone or establish its prime-blind positivity by a new construction.

## Work plan

Read the exact CHMD/even-cone identities and use corpus-wide mechanism searches; iterate paper conjectures and attacks. Formalize only a dependency-closed proof that advances the route. Build leaves serially in the foreground with `lake --old`; final audits with `lake env lean`. Wire completed leaves, refresh index, lint, audit axioms in `/tmp`, and remove owned scratch files. Preserve concurrent changes.
