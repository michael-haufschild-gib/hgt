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
only the source-side bounded-dilation and vanishing lemmas are currently
drafted; Hilbert operators, Wiener series, and ideal inclusion remain pending.

## Scaling audit: next conjecture

The exact pronic fibre identity proves, at a complete block horizon,
`<D_p v,D_p w>_(p*M+p-1) = (1/p) <v,w>_M` for zero-origin rows.
At arbitrary horizons there is one incomplete fibre. For the actual source,
the bound `|A(n)| <= n` bounds its energy uniformly, so it disappears on
escape. This suggests an exact *transport between limit states* under horizon
rescaling. Regular variation of receiver energy would determine the diagonal
`K(p,p)`, but does not alone identify the mixed Gram limits at `T` and `T/p`.
The stronger all-packet homogeneity asserted in A3 therefore needs its own
invariance proof. No assumption of that invariance will be added.

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

- Missing dependency `CountableCofactorCovariancesHaveACommonLimit.olean` was
  generated successfully with the permitted single-module command.
- The `/tmp/qiii_bridge_check.lean` declaration check completed. Required finite
  sums, support, limit, complex conjugation, and inner-product names were
  confirmed; deliberately queried unused alternatives were absent.
- Draft new files: `ArithmeticDefectRigidity/RepairingKernelsVanishOnEscape.lean`,
  `HTGeometry/AntipodalKernelExtension.lean`, and
  `ArithmeticDefectRigidity/WhiteNoiseAndAntipodalEscapeData.lean`.
- `RepairingKernelsVanishOnEscape.lean` passed its first check; warning cleanup
  is complete. Final verification and transitive axiom audit remain pending.
- Added draft `HTGeometry/RealPositiveKernelComplexification.lean`, splitting
  complex energies into their real and imaginary parts. White-noise positivity
  now uses this generic bridge.
- Generic bounded coefficient pushforward and completion are being checked in
  `/tmp/qiii_kernel_check.lean` before transfer to the corpus.
- Umbrella imports and axiom audits remain pending successful final checks.

## Gates

- [x] 0 → 1: question and required distinctions recorded.
- [ ] 1 → 2: complete classification with no open mathematical dependency.
- [ ] 2 → 3: Lean proofs and axiom audits for every required result.

## Log

- 2026-10-25 — Read attachment and full report; began source audit and corpus searches.
