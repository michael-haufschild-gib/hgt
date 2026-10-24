# Q-III: escape states, repairing ideals, and the Kronecker curve

- **ID:** q-iii-escape-state-classification
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-2410/opus.md`, §3 Q-III and §2.1.
- **Statement:** Classify actual normalized receiver escape modules, their signed data, annihilator hulls, and indices; determine whether their generators come from the translated off-line zero hull on the Kronecker curve.

## Goal

Full answer to Q-III, unconditional Lean proofs of the answer and its corollaries,
and applications wherever they advance the research corpus. Partial structural
lemmas do not complete this goal. No use of the hgtl7 skill, numerical experiments,
new analytic assumptions, or unproved interfaces.

## Completion requirements

- [ ] Classify the actual limits from `exists_cofactorGram_limit`, including
  antipodality, pole trace, and forcing split.
- [ ] Construct their critical Wiener algebra modules and prove cyclicity.
- [ ] Establish the repairing-ideal/annihilator bridge and exact hull relation.
- [ ] Decide Kronecker-curve generation and translated-zero-hull containment.
- [ ] Establish the correct index formula, including multiplicities and possible
  infinite-dimensional cases.
- [ ] Audit the proposed exponent law and moving-translation covariance.
- [ ] Audit white-noise and golden-datum calibrations and formalize their exact
  positive conclusions.
- [ ] Formalize all resulting corollaries and relevant cross-programme applications.
- [ ] Check each new module with `lake --old env lean`, inspect transitive axioms,
  wire umbrellas without compiling them, remove own scratch artifacts.

## Approach

Search the corpus before mathlib; inspect source statements rather than relying
on report prose. Alternate precise conjectures, dependency-closed paper proofs,
Lean proofs, and revised conjectures informed by counterexamples. Preserve the
distinction between arbitrary PSD dilation kernels and actual receiver limits.

## Current evidence and conjectures

The report has been read in full. Its module construction, exponent law, and
white-noise exclusion are explicitly marked unproved. Initial search locates
the existing cofactor covariance and obstruction-hull infrastructure. Several
unrelated worktree edits predate this task and are being preserved.

1. **C1:** Every paid finitely supported convolution has zero normalized Gram
   norm along every escaping receiver subsequence. Check the exact receiver and
   convolution conventions before attempting its closure in the Wiener norm.
2. **C2:** The hull of an individual escape module is contained in the paid
   ideal hull; equality need not follow from this inclusion.
3. **C3:** The report's regular-variation scaling requires a separate proof of
   asymptotic pronic dilation, not merely the existing contraction inequality.

## Paper proof: repairing kernels and bounded dilation

For a real critical Wiener kernel `g` and a weight `c` with absolutely summable
mean, write `m_g = sum g(n)/n`, `m_c = sum c(n)/n`, and
`D_g A_c(n) = sum_{j <= n} g(j) A_c(floor(n/j))`. The already proved exact
convolution identity is

`A_(g*c) = D_g A_c + m_c A_g`.

The correction has uniformly bounded pronic norm, at most
`|m_c| (sqrt(2)+1) sum |g(j)|/sqrt(j)`. Both triangle inequalities therefore
prove, without an analytic premise, that `g*c` is paid exactly when `D_g A_c`
has bounded pronic norm. If the actual receiver energy tends to infinity,
divide the square of that bound by receiver energy. Every paid kernel has
zero normalized dilation energy. For finite kernels, pass the finite Gram
sum to any common subsequential limit to obtain a null vector.

**Status:** Dependency-closed paper proof. The full source-side Lean module
`ArithmeticDefectRigidity/RepairingKernelsVanishOnEscape.lean` passed its first
check. Two deprecated finite-sum spellings and one unused simp argument were
then cleaned up. Final check and transitive axiom audit remain pending.

## Index audit

`AnIndexFormulaForTheActualReceiver.lean` proves hull equality only above the
zero width, where both hulls are empty. Its all-damping TFAE includes emptiness,
so it does not establish the requested below-width formula.

`UnpayabilityCarriesMultiplicity.lean` proves that the logarithmic smooth power
and smooth power have the same hull, but strictly different paid ideals; the
first ideal is non-radical and its quotient has rank at least two. Consequently
hull containment cannot by itself identify an escape-module index with paid
ideal codimension. Next conjecture to test: leading escape normalization loses
lower logarithmic orders, requiring a filtration of escape scales to recover
multiplicity. This is presently a conjecture, not a proved counterexample for
the actual Möbius receiver.

An additional index distinction needs formal audit. AOT uses algebraic
`Module.rank` for general quotients, while the escape space also has a Hilbert
dimension. For a closed operator kernel, the Wiener quotient is Banach. It
cannot have countably infinite Hamel dimension: a countable algebraic basis
would express it as the union of proper finite-dimensional closed subspaces,
each with empty interior, contradicting Baire. Thus a literal cardinal equality
between its algebraic codimension and a countably infinite zero set would be
the wrong infinite-dimensional index convention. This does not prove that the
actual infinite branch occurs. The Baire argument and its application remain
to be formalized; finite-dimensional multiplicity issues remain separate.

## Cross-programme applications to pursue

The source-side bridge consumes THIM's exact convolution identity and sharp
pronic dilation estimate, and adds annihilator information to ADR's existing
compactness theorem. The complex two-component version directly consumes AOT's
actual `paidIdeal`, without changing its definition.

After the Wiener representation is formalized, its unit action should transport
escape modules across the actual Möbius–Liouville unit orbit. If `u` is a Wiener
unit, then `pi(u)v_1` is nonzero and cyclic. Convolution changes the receiver by
the dilation `D_u` plus a bounded correction, so its limiting Gram kernel is
the Gram of this new cyclic vector, normalized by `||pi(u)v_1||²`. This predicts
isomorphic modules, not just the already known equality of paid ideals and
hulls. This application remains unformalized and is part of the original goal.

## Antipodality audit and positive survivor

The assertion that white noise should violate antipodality is not justified by
the reported Gram axioms. For any positive kernel realized by vectors `v_j`,
adjoin the vector `r = -v_1`. This preserves the entire original kernel and
gives residual mass one and pairing `-1` when `K(1,1)=1`. Thus antipodality
alone cannot exclude any normalized positive cofactor kernel, including the
white-noise kernel. This does not claim the extension realizes the actual
moving cofactor residual or its pole trace.

**Positive survivor, paper proof:** The antipodal positive extension is unique.
If `||r||² = ||v_1||² = 1` and `<r,v_1> = -1`, positivity gives
`||r+v_1||² = 0`, hence `r=-v_1` and every residual covariance is forced to be
`-K(1,j)`. An antipodal coordinate supplies no independent Gram information;
the remaining content must be the source-defined realization of that coordinate
by the moving cofactor sum and its renormalization. Lean formalization pending.

The reusable Hilbert realization exists in
`HTGeometry/PosSemidefKernelGram.lean` (`KernelPre`, `KernelHilbert`,
`KernelHilbert.inner_vector`); positivity operations and Gram realization are in
`HTGeometry/PSDKernelOperations.lean`.

## Module bridge: dependency-closed paper argument

Complexify a real limiting kernel and use its Gram Hilbert realization. The
packet dilation inequality makes `v_j -> v_(p*j)` well-defined on the quotient
by null vectors, with operator norm at most `1/sqrt(p)`. Extend by continuity.
The resulting operators commute, multiply according to the integer monoid,
and the vector `v_1` is cyclic. The absolutely convergent operator series
`pi(a) = sum a_n V_n` is a unital contractive representation of the critical
Wiener algebra. Its kernel is a proper closed ideal.

For infinite kernels, finite-packet convergence alone is insufficient. The
required uniform estimate follows by Minkowski and sharp dilation contraction:
`||D_g A||_T <= ||g||_W sqrt(E_T)`. Approximate a paid kernel `a` by its finite
truncations `a_N`. Their normalized norms differ from the norm of `D_a A` by
at most `||a-a_N||_W`, uniformly in the horizon. The latter normalized norm
tends to zero by the repairing-kernel theorem. Passing first to the fixed
finite-packet limit and then to `N -> infinity` gives `pi(a) v_1 = 0`.
Commutativity and cyclicity give `pi(a)=0`. Hence
`P(c) <= ker(pi)` and `h(ker(pi)) <= h(P(c))`.

This establishes the paper argument for A1–A2, but neither equality of the
ideals nor identification with the translated zero hull follows. Lean status:
the source-side bounded-dilation and vanishing lemmas passed Lean; Hilbert
operators and cyclicity are drafted; Wiener series and ideal inclusion remain
pending.

Implementation route for infinite repair annihilation: for finite Wiener
truncations `a_N`, the normalized source maps are uniformly bounded in the
Wiener norm. The triangle inequality gives a uniform tail error bounded by
`||a-a_N||_W`. Finite Gram convergence identifies the limiting norm of `a_N`;
source payment makes the normalized norm of `a` vanish. Hence
`||pi(a_N)v_1|| <= ||a-a_N||_W` (or a harmless fixed multiple when treating
real and imaginary parts separately). Passing to `N -> infinity` proves
`pi(a)v_1=0`. Finite truncations need not themselves be paid; no density of
finite repairing kernels is being assumed.

For the operator series, `WienerAlgebraAt.hasSum_pointMass` is already proved.
First define the bounded linear series map `a -> sum a_n V_n`. Its value on
each point mass is `V_n`. Extend the multiplicativity of point masses twice
using this convergent series and continuity of multiplication. This avoids
re-proving an infinite Dirichlet-convolution rearrangement.

## Moving-translation refinement to test

The proposed `k = O(sqrt(E))` translation scale may itself be invisible. The
actual prefix has increments bounded by one. If its elementary sublinearity
`A(n)/n -> 0` is established, dominated convergence against the summable
pronic weights gives

`sum_{n >= 1} (A(n+k)-A(n))^2 / (n(n+1) k^2) -> 0`.

For each fixed `n`, the numerator divided by `k^2` tends to zero; the unit
increment bound dominates it by one. Splitting bounded and large `k` then
shows that every moving translation with bounded `k^2/E` disappears on
escape, even without `k -> infinity`. Thus a nonzero successor displacement
would require an unbounded ratio to `sqrt(E)`. The sublinearity input follows from the existing all-damping hyperbola bound
with `D=n`. A complete paper proof is recorded in
`../2-fully-proven/square-root-energy-translations-still-disappear.md`; Lean
verification remains pending.

A quantitative candidate is `|A(n)| <= C_epsilon n^(1-epsilon)`. Splitting the
pronic sum at `n=k` would give displacement energy `O(k^(2-2epsilon))`.
Its source bound and the uniform estimate both require proof before use.

## Dilation scaling audit

The exact pronic fibre identity proves, at a complete block horizon,
`<D_p v,D_p w>_(p*M+p-1) = (1/p) <v,w>_M` for zero-origin rows.
At arbitrary horizons there is one incomplete fibre. For the actual source,
the bound `|A(n)| <= n` bounds its energy uniformly, so it disappears on
escape. This suggests an exact *transport between limit states* under horizon
rescaling. Regular variation of receiver energy would determine the diagonal
`K(p,p)`, but does not alone identify the mixed Gram limits at `T` and `T/p`.
The stronger all-packet homogeneity asserted in A3 therefore needs its own
invariance proof. No assumption of that invariance will be added.

Potential positive replacement: logarithmically average the horizon states.
If the scalar energy ratios are regularly varying, transport gives
`K_T(pj,pk) = p^(-1-alpha) K_(T/p)(j,k) + o(1)`. Averaging in `dT/T`
makes the fixed translation `log T -> log T - log p` negligible at the ends,
so every averaged limit is homogeneous. This would classify an averaged state,
not every individual subsequential state from the original theorem. No actual
regular-variation premise has been proved, and this replacement is not yet a
Lean theorem or a completed no-go.

## Alternative intrinsic annihilator construction

For a fixed cofinal horizon sequence, define the vanishing kernels to be the
complex Wiener kernels whose real and imaginary dilation energies, divided by
receiver energy, tend to zero. The uniform dilation bound and exact composition
identity make this a closed ideal. The identity kernel has normalized energy
one, so the ideal is proper. On escape it contains every paid kernel. This
constructs a nonempty hull contained in the obstruction hull directly from
the actual receiver, even before identifying it with the kernel of the Gram
Hilbert representation. The identification still requires uniform finite
approximation. This route is a paper-level alternative, not yet formalized.

For the Hilbert route, the existing `KernelPre` is a seminormed coefficient
space. A bounded pushforward of finite coefficients therefore extends through
`ContinuousLinearMap.completion`; this avoids choosing representatives in the
nullspace quotient. The kernel pullback identity is already proved as
`kernelForm_mapDomain`. The remaining generic construction and its norm bound
are being prepared as reusable kernel geometry.

## Golden calibration audit

The exact golden datum in `FakeCurvesAndTheWindowLaw.lean` is a curve datum at
`q = 5` with normalized eigenvalues `phi` and `phi^-1`.
`TheGoldenCurveIsABeurlingSystem.lean` realizes its point counts by nonnegative
integer prime multiplicities at generalized norms `5^d`. This does not yet
specify an integer-prefix receiver of the type used by `cofactorGram`.
Constructing its escape module therefore needs an explicit source and horizon
measure, followed by a proved comparison with the golden zeta datum. Merely
substituting its two eigenvalues into a rank-two kernel would not discharge
that realization step.

## Full signed covariance consequence to formalize

The already proved bound on `A + renormalizedCofactor` gives more than its
pairing with `A`: Cauchy--Schwarz and sharp dilation show that its normalized
pairing with each fixed `D_j A` vanishes. The residual mass tends to one and
all mixed residual covariances are therefore forced by the original kernel.
The generic uniqueness theorem for the antipodal extension records exactly
this rigidity. Its actual-source realization remains to be packaged and
checked; no additional independent signed Gram coordinates survive.

## Verification state

| Module | Kernel check | Axiom audit | Final source check/import |
|---|---|---|---|
| `RepairingKernelsVanishOnEscape` | Passed, olean exists | Standard axioms only | Pending |
| `AntipodalKernelExtension` | Passed, olean exists | Standard axioms only | Pending |
| `RealPositiveKernelComplexification` | Passed, olean exists | Standard axioms only | Pending |
| `BoundedKernelReindexing` | Passed, olean exists | Standard axioms only | Pending |
| `TheCofactorLimitCarriesACyclicDilationAction` | Two representation errors fixed; retry pending | Pending | Pending |
| `WhiteNoiseAndAntipodalEscapeData` | Source audit running, session `70238` | Running | Pending |
| `BoundedMultiplicativeSequencesActOnWienerAlgebras` | Draft | Pending | Pending |
| `TheCofactorLimitIsAWienerModule` | Initial definition only | Pending | Pending |

The standard axioms reported are `propext`, `Classical.choice`, and `Quot.sound`.
The translation proof remains in `/tmp/qiii_translation_check.lean`, pending its
first check before transfer into the corpus. No new umbrella imports yet.

## Gates

- [x] 0 → 1: question and required distinctions recorded.
- [ ] 1 → 2: complete classification with no open mathematical dependency.
- [ ] 2 → 3: Lean proofs and axiom audits for every required result.

## Current verification handoff

- `BoundedKernelReindexing` and `RepairingKernelsVanishOnEscape` both passed
  their corrected olean checks. Their oleans now exist; preserve them.
- The targeted source/kernel axiom audit completed: every printed theorem
  depends only on `propext`, `Classical.choice`, and `Quot.sound`. Its nonzero
  exit came solely from speculative API names that do not exist.
- Active compiler: `/tmp/qiii_white_noise_audit.lean`, session `70238`.
  This checks white-noise source, prints axioms, and probes further APIs.
- The actual Hilbert action check found an unexpanded `vector` definition in
  cyclicity and `RCLike.re` blocking complex-energy simplification. Both were
  corrected. Its olean was not generated; the corrected retry remains pending.
  `TheCofactorLimitIsAWienerModule.lean` now imports it.
- Existing new oleans also include `AntipodalKernelExtension`,
  `RealPositiveKernelComplexification`, and dependency
  `CountableCofactorCovariancesHaveACommonLimit`.
- `TheCofactorLimitCarriesACyclicDilationAction` and
  `WhiteNoiseAndAntipodalEscapeData` remain unverified. The latter has a
  source-plus-axioms scratch copy at `/tmp/qiii_white_noise_audit.lean`.
- New draft `ArithmeticOrientationTheory/BoundedMultiplicativeSequencesActOnWienerAlgebras.lean`
  integrates arbitrary weighted multiplicative sequences by norm-convergent
  point-mass series. It has not been checked.
- Complete translation proof scratch: `/tmp/qiii_translation_check.lean`;
  not yet checked. No translation Lean module has been added yet.
- Pending scratch bodies: `/tmp/qiii_wiener_action_body.lean` (actual Wiener
  representation, closed/proper annihilator, nonempty hull) and
  `/tmp/qiii_banach_countable_check.lean` (Baire countable algebraic span).
  Neither has been checked or transferred.
- No new umbrella imports yet. Final source-only checks and axiom audits remain
  required. Use targeted audits, not `scripts/check_axioms.sh` (full umbrella,
  missing `--old`).
- Own temporary files are prefixed `/tmp/qiii`; remove after their information
  is consumed. Preserve other agents' work and compiler processes.

## Infinite-repair bridge: scalar covariance route

An alternative to a two-parameter energy approximation is now identified.
For each fixed cofactor `j`, pair the full kernel action against `D_j A`.
Its coefficient series is uniformly dominated by the Wiener summands through
`|K_T(n,j)| <= n^(-1/2) j^(-1/2)`. Dominated convergence therefore passes every
Wiener kernel through the common Gram limit. A paid kernel has pairing tending
to zero by its bounded source norm and Cauchy--Schwarz. Hence its limiting
vector is orthogonal to every Gram vector and is zero by density; commutativity
and cyclicity then make the entire operator zero. This bypasses any assumption
that finite paid kernels are dense. The proof is not yet formalized.

A relevant reusable corpus result is
`HTGeometry.tendsto_of_dense_of_uniform_bound` in `StrongConvergenceDense.lean`.
A concurrently present module `BiarithmeticGeometry/PaidKernelsVanishOnEscape.lean`
also proves source-side payment annihilation. The current ADR module additionally
proves the generic boundedness equivalence and finite common-limit consequences;
no changes to the concurrent module have been made.

## Log

- 2026-10-25 — Read attachment and full report; began source audit and corpus searches.

## Source-documentation correction

The comments in `ArithmeticOrientationTheory/AnIndexFormulaForTheActualReceiver.lean`
claimed a complete resolution despite stating only the above-width zero-index
formula. Those comments now state the proved range and the remaining below-width
question. The all-damping TFAE explicitly includes hull emptiness; it does not
identify hull equality alone with RH. No theorem in that module was changed.

## Further distinctions to preserve

The current chosen-kernel Hilbert construction realizes one actual common limit.
A full answer must cover every actual limit; a choice construction is not itself
a classification. The source-side finite repair theorem already quantifies over
all common limits.

For A3, the missing mixed-horizon invariance is presently a proof gap, not a
counterexample to regular-variation homogeneity. A no-go requires a proved
counterexample and a positive survivor.
