# Route L source-selected completion attack

- **ID:** L-SOURCE-COMPLETION-2026-09-10
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; no RH proof claimed
- **Source:** [current frontier](rh-current-frontier-map.md), route L
- **Statement:** Find a source-derived completion/domain law that identifies the literal degree-six BV–Green boundary with the fixed physical readout, preserving arithmetic provenance and multiplicity.

## Proof chain and obstruction

Completed Green/BV source → source-to-fixed-physical comparison → zero reflected conormal boundary → critical-line placement for every Xi divisor copy → RH.

The existing normalized pair-cyclic reader kills the source boundary. Its agreement with the fixed physical reader remains unproved. Continuous faithful Hausdorff descent of the actual Big-Witt rows is already equivalent to RH. Merely changing the target type, admitting multivalued linear maps, or asserting cyclicity does not produce agreement.

## Plan

1. Audit the literal source rows and degree-six boundary against full-corpus hybrid, deep, and proof-method searches.
2. Test source-selected domain changes and singular completion against explicit source witnesses; prove or reject each precise candidate before pivoting.
3. Formalize only dependency-closed results, verify in scratch with sequential foreground Lean, then run a scoped final module audit. Record remaining gaps explicitly.

## Evidence and working state

- Existing exact degree-six comparison: `RouteRDegreeSixBVGreenPhysicalCyclicDescentWall.lean`.
- Existing Hausdorff classifier: `XiGammaSixWoldJordanHausdorffMultifibreDescentNoGo.lean`.
- Completed corpus requests: normalized cyclic source / physical boundary; singular domain change; closability and quadratic-energy graph methods; coherent covariance; theta prime sampling. Coverage limits are recorded below.
- Broad arXiv searches requested June–September 2026 papers using descent, monodromy, dissipation, and renormalization. Results so far are mostly older or unrelated; no unverified external mechanism is assumed.
- No new Lean declarations or numerical experiments at initialization.

## Gates

- [x] Exact target and known obstructions stated
- [ ] Source-derived cyclic-to-fixed-physical comparison proved on paper
- [ ] Unconditional closed Lean proof of RH

## Conjecture / proof / pivot loop

### C1: retain the missing energy by completing its graph

For the actual finite Big-Witt packet space `D`, let `i : D → X` be admission into the existing one-leg graph, and let `E_A` be the literal prime-labelled reporter with coefficient `A/p`. Define the proposed enlarged source domain as the closure of `{(i(d), E_A(d)) : d ∈ D}` in `X × ℂ`. This is a concrete domain change, not an assumed physical comparison.

**Paper result:** if `A ≠ 0`, this closure is the entire product. An annihilator `(x,y)` with `y ≠ 0` would express `E_A` as a bounded functional of `i(d)`. That supplies the continuous descent already proved equivalent to `A=0`, a contradiction. Hence `y=0`; density of `i(D)` forces `x=0`. The corpus graph-saturation theorem now gives full-product closure. At `A=0` the energy coordinate is identically zero, so the closure is proper.

**Consequence:** graph completion admits every complex output above every source vector when the retained coefficient is nonzero. It constructs a domain with a continuous energy projection, but supplies no physical selection. The strongest survivor is this exact saturation dichotomy, now [formalized and audited](../3-formalized/route-l-energy-graph-saturation.md). This rejects C1 as a producer, not route L as a whole.

### C2: choose the minimum-energy point in the enlarged fibre

The full-product conclusion makes the minimum of `|z|²` in every fibre zero. This selects `(x,0)` regardless of `A`; actual fixed-prime rows still carry `A/p`. Thus minimization erases the very reporter it was meant to preserve. It cannot establish agreement with the original fixed physical readout. A useful variational replacement needs an independent arithmetic restriction on the admissible fibre before minimizing.

### C3: source-derived noncommuting relaxation

The broad search found Wang–Lu, [*Slow is fast: raising barriers to accelerate thermal relaxation*](https://arxiv.org/html/2607.11877v1), submitted 13 July 2026. Its equations (1)–(4) use reversible edge generators with a common independently specified equilibrium, and time ordering changes finite-time decay by rotating modes. **Transfer candidate only:** source operations might restrict the enlarged fibre dynamically. The paper supplies no Big-Witt arithmetic generator, invariant physical readout, or equilibrium identification. None is assumed here. Those three obligations must be derived before claiming a comparison.

**Attempted transfer:** use trace-preserving transitions between the normalized fixed-left rows as reversible channels. These transitions preserve source trace one but change the retained reporter from `A/p` to `A/r`. Requiring reporter preservation for distinct primes forces `A=0`; allowing it to change loses the desired equality with the fixed physical reader. The finite reversible-chain corpus likewise takes its stationary distribution and detailed balance as input (`ReversibleKilledWalk.lean`); it does not construct them from the arithmetic source. A general scheduling theorem is therefore insufficient. The remaining dynamic candidate needs extra literal theta/arithmetic information beyond this free-parameter packet family.

### C4: restrict to positive packets before completing

The existing counter-witnesses are already positive: each raw row coefficient is `1/(p*r)>0`, and its normalizing trace is positive. Distinct fixed-left rows converge to the same singular vector while retaining `A/p` and `A/r`. Positivity alone therefore does not make the completed readout unique. This uses the existing `deningerBigWittWoldFixedLeftRightEdgeWeight_pos`, `deningerBigWittWoldFixedLeftRightEdgeMass_pos`, the normalized-row convergence theorem, and the exact reporter evaluation; it is not a new independent obstruction. Full complex-product saturation is asserted only for the linear graph, not for the positive cone. A complete classification of the positive-cone fibre has not been proved here.

## C5: retain each left-prime marginal before completion

Candidate domain: retain the entire finite left-prime marginal, rather than its scalar total, and complete with a norm admitting the reciprocal-prime covector. This domain is defined before Xi specialization. Fixed-prime rows then have distinct retained marginals, so the old common-limit argument does not apply to this new domain. This construction alone would only preserve the reporter; it would not annihilate the degree-six boundary.

The next finite source test uses the **actual** coherent right-leg packet, whose coefficient is `conj(a(p)-a(q))`. Its total trace is zero by antisymmetry. Its prime-weighted readout instead has the exact proposed formula

`E_c(R(a,S)) = |S| sum_(p∈S) c(p)conj(a(p)) - (sum_(p∈S)c(p))(sum_(p∈S)conj(a(p)))`.

This is a covariance, not automatic zero. Testing the source supported at one of two distinct primes shows that annihilation for every `a,S` forces `c` constant; constants suffice. For `c(p)=A/p`, this is exactly `A=0`. Scratch Lean verified this formula and its full annihilator classification; the axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The scoped module audit passed; see the [formalized covariance card](../3-formalized/route-l-coherent-marginal-covariance.md). It tests the proposed domain against literal coherent source packets before any singular limit. No assertion that arbitrary test profiles are Xi-selected profiles is made.

### C6: use the literal theta half-density connection to gain a summable source domain

The corpus supplies the actual source connection, not an invented regularizer:
`thetaMovingHorizonConnection = d/dL + 1/2`. Its exact Ward-profile identity
in `HedenmalmThetaMovingHorizonCovariantHardyGreenRegularization.lean` removes
the flat mode and retains an exponentially twisted tail. For the Route L carrier,
`thetaGammaSixWoldHorizontalCarrier p q` is the fixed theta amplitude times
`2 * sourceHorizontalWoldPrimeClockUniversalProfile(rate q)`.

**Attempt:** apply this connection before prime sampling, obtain a summable
source, and infer that the original harmonic coefficient vanishes.

**Failure:** the connection annihilates `K exp(-L/2)` for every scalar `K`.
The regularized source therefore omits the exact coefficient read by the original
physical marginal. Summability after this operation does not imply summability
of the original carrier or identify its readout. This is an application of the
already formalized flat-mode connection identity, not a new RH criterion.

A second literal source mechanism is the corrected two-collar Meyer–Poisson
regulator (`DeningerMeyerSecondaryPoissonRegulator.lean`): each component of a
genuine Poisson boundary is zero by reflection. Its domain admission is therefore
unconditional. Raw prime sampling cannot replace it: the existing Fourier-fixed
Hermite boundary probe has strictly positive raw values at every prime
(`DeningerRationalWittPoissonBoundarySamplingObstruction.lean`). The unresolved
step is equality of this corrected source regulator with the existing physical
reader on the full completed Green boundary, including the omitted flat mode.
Neither source identity alone gives that equality.

## Search coverage (details)

The completed hybrid request reported 722,314 indexed declarations and 706,071 ready method descriptions, but incomplete source/compiler and semantic coverage. The two broad deep requests returned partial results after deadlines; the method-oriented request reported a local semantic-runtime deadline. Their candidate lemmas, source arguments, and proposed ingredient sets were inspected. Generic boundary and limit candidates did not provide physical agreement. Lexical graph search found the applicable `GraphSaturationCore` theorem and a separate cofinal vertical-fibre principle in `CompleteResolutionCofinalConditioningLaw`; their actual source was read. No whole-corpus completeness claim is made.

The subsequent theta/sampling deep request reported 722,323 indexed declarations and partial coverage after its deadline. Its proposed periodicity ingredient does not supply prime-domain admission or physical-reader agreement. Direct source inspection instead identified the flat-mode connection identity and the secondary Meyer–Poisson boundary regulator used in C6. Broad arXiv searches for screening, rigidity, and sampling with recent-date preferences returned mostly older or unrelated papers; no new source bound was obtained from them.

## Verified checkpoint and next mathematical target

Both new modules passed sequential scratch checks, axiom audits, and their scoped
final builds. The final repository lint passed. Both imports are wired into
`RHTower`; no umbrella build was run and no owned Lean process remains.

The comparison and RH gates remain open. The next direct target is the exact
difference between the corrected two-collar source regulator and the fixed
Burnol/Deninger reader on the full completed Green boundary, with the flat mode
and coherent compensation retained. A vanishing statement for only the corrected
regulator, or an estimate only after removing the flat mode, does not close this
step. The completed graph and finite marginal classifications prevent repeating
those two unsuccessful producers.

## Continuation: literal Mellin cancellation and prime escape

**C7 attempted producer:** use `M(Zf)(rho)=zeta(rho)M(f)(rho)=0` at an
actual zero to annihilate the physical Green Wronskian. Source inspection found
that the relevant Gaussian value is `exp((rho-1/2)^2/(4*pi))`, nowhere zero.
It is evaluation of a nonzero Meyer quotient class, not the transform of a
Poisson boundary. Its two-source Wronskian is already exactly the physical
fracture times a positive Gaussian square. The boundary factorization cannot
be substituted for that quotient-class identity. The source-observer splitting
also retains an explicit boundary-sensitive Green term. No annihilation of
that term follows from Mellin boundary cancellation alone.

**C8 candidate:** choose the prime-domain completion using only positive raw
source rows, while allowing the left prime to escape. The trial cutoff for row
`n` is the least prefix whose trace exceeds `(n+1)(C+1)`, where `C` is the norm
of the literal raw horizon. This uses no Xi point or energy parameter. The
normalized packet then has trace one, ambient norm at most `1/(n+1)`, and
reporter `A/p_n`. Therefore it should converge to the same nonzero singular
source while its energy tends to zero for **every** `A`. Scratch Lean and axiom audits verified positivity, trace one, the reciprocal norm
bound, escape of every bounded left-prime range, and both limits. This constructs a source-only zero-output sequence but
shows exactly why its existence cannot establish the fixed-reader agreement:
the same prescription works at nonzero free coefficient too.


**C8 positive survivor, general bound:** for any finite packet with nonnegative
real coefficients, let `H_B` be its mass on left primes at most `B`. For `A≥0`,
`(A/B) H_B ≤ Re E_A` by comparing reciprocal weights on that range. Consequently,
when `A>0`, any sequence of such packets with `E_A→0` must have `H_B→0` for every
positive finite `B`. This is the precise retention obstruction for the proposed
source-selected zero-output exhaustion; it is stronger than inspecting one
chosen sequence. Scratch Lean and axiom audits verified the bound and consequence. The [formalized result](../3-formalized/route-l-prime-escape-retention.md) passed its scoped final module audit and repository lint.
A literal arithmetic comparison would need to establish both vanishing readout
and a retained nonzero finite-range mass in the same source construction. The
fixed-prime rows establish retention; the new escape sequence establishes a
zero-output limit. Combining those properties remains unproved.

### Continuation search audit

Deep source/method queries covered secondary Poisson/physical comparison,
Mellin/Green cancellation, positive fibres, diagonal limits, and mass tightness.
Returned candidates included the actual Meyer–Poisson regulator and Mellin
factorization, Gaussian nonvanishing, and generic Cauchy selection. Their source
statements were checked where used. The proposed Fourier-to-adjoint transfer
still requires equality of different operators and is not a proof. All requests
reported partial source/compiler or semantic coverage; some reached deadlines.

Broad arXiv terms included sewing, resonance, compactification, and trace.
[Jin et al.](https://arxiv.org/abs/2607.29464) was submitted in July 2026 but
reports a 2025 robotics publication: its alignment uses a known length ratio,
so it supplies no independent matching law here.
[Zhang et al.](https://arxiv.org/abs/2608.26219), August 2026, uses learned priors
for sparse field reconstruction; those priors are not an arithmetic uniqueness
theorem. Neither paper is imported as a mathematical premise.


### Continuation checkpoint, 2026-09-11

`XiGammaSixWoldJordanPrimeEscape` passed scratch Lean, the listed axiom audits,
and its scoped module build. Lint and scoped whitespace checks passed. The
source-only cutoff, positivity, graph limit, energy limit, and general finite
prime retention bound are now formal. The proof-chain gap remains the same
arithmetic comparison: vanishing physical readout and retained source mass
have not been obtained together. C7 did not close it; C8 explains why a selected
zero-output limit alone is insufficient. Route L and the RH goal remain open.

## C9: signed coherent correction and retained marginals

The positivity assumption in C8 does not cover the complete signed Frobenius
right-leg source. Test whether coherent corrections repair the missing physical
comparison without changing the retained prime data.

For a profile supported at one prime `p`, the complete right-leg packet on
`{p} union T`, divided by `|T|`, is the signed star
`C = |T|^-1 sum_(q in T) (e_(p,q)-e_(q,p))`. Its trace is zero and its weighted
readout is `A/p - (A/|T|) sum_(q in T) 1/q`. Thus the finite covariance identity
permits a readout shift; it does not force cancellation. The proposed vanishing
Hilbert-norm sequence of larger stars is not yet Lean-verified. In particular,
these fixed-anchor corrections change the marginal at `p` and cannot be called
prime-data-preserving.

The next conjecture is a quantitative replacement: reciprocal readout is stable
under convergence of every left-prime marginal if their total variation remains
bounded. A correction supported above `B` should satisfy
`|E_A(c)| <= |A|/B * variation(c)`. Nonzero cancellation from an escaping tail
would therefore require diverging variation. First prove the exact finite
marginal factorization and estimate, then the convergence statement, and check
whether the actual coherent source supplies the required control. Here variation
means the sum of absolute marginal coefficients; it is not a consequence of the
algebraic BV name. No boundedness or source agreement is assumed for RH.

The transfer idea is the dual-observable estimate in
[Fahli–Galichon, Optimal Transport in Economics](https://arxiv.org/abs/2609.06277),
submitted 5 September 2026, sections 2.2 and 2.5.1: constraints on marginals and
cost must accompany a proposed transport. The paper supplies no arithmetic
comparison. All claims below must be proved from the literal finite source.

### C9 proof outcome

Scratch Lean now verifies the exact left-prime marginal factorization and signed
tail bound. More strongly, for every real weight tending to zero outside finite
prime sets, a uniformly variation-bounded sequence converging coefficientwise
to a finite target marginal preserves the weighted readout. The theorem applies
directly to the existing edge reporter with weights `A/p`; this is a nontrivial
positive comparison law, not an asserted property of the Green/BV source.

The actual coherent marginal is
`|S| conj(a(p)) - sum_(q in S) conj(a(q))` within `S`. Its vanishing is equivalent
to vanishing of the entire coherent packet. For every retained pair,
`|S| |a(p)-a(q)| <= variation(marginal)`. Thus a uniform bound over all unscaled
complete coherent packets exists exactly for constant profiles. C9's raw
uniform-bound producer fails; the survivor is the exact growth law together
with continuity for controlled marginal limits. Both are scratch-verified in
`XiGammaSixWoldJordanSignedMarginal`; final audits are recorded on the
[proof card](../3-formalized/route-l-signed-marginal-stability.md).

The method searches returned generic dominated-convergence proposals with no
applicable majorant. The corpus's positive marked-variation transport law needs
an admitted mass-preserving source envelope; no such envelope was found here.
Its physical-endpoint response normalization retains a separate unproved signed
budget. The proposed star Hilbert-limit construction remains unformalized and
is not used in the proved results. Next test the source-selected diagonal and
punctured compensator with their original normalization, using their exact
marginals and the variation estimate. RH and source-to-physical agreement remain
open.

### Next finite-source test: normalized coherent stars

The normalization test itself is now scratch- and axiom-audited:
`|S| |z(a(p)-a(q))| <= variation(marginal(z R(a,S)))`. Uniformly bounded variation
on growing sets forces every fixed normalized edge amplitude to vanish, even
for varying profiles. This retains the normalization but does not annihilate
aggregated marginal energy. The next construction tests that surviving aggregate.

For a fixed prime `p`, take the indicator profile `a=1_{p}` on a finite set `S`
containing `p`, with `N=|S|`, and normalize the complete packet by `1/N`.
The exact marginal formula predicts `m(q)=1_{q=p}-1_S(q)/N`. Its total trace is
zero while its marginal variation is `2(1-1/N)<=2`. As `S` grows cofinally,
the marginal should tend coefficientwise to `delta_p`, and the proved continuity
law should give reciprocal energy tending to `A/p`. The proposed Hilbert norm
square is `2(N-1)/N^2`, giving zero ambient and one-leg graph limits.

These simultaneous limits are a conjecture awaiting the explicit packet/norm
Lean proof. They would show why uniform marginal variation alone does not make
the reader continuous in the old graph topology: the retained marginal limit
would be `delta_p`, not zero. They would not contradict the new controlled
marginal theorem. Vanishing of each individual normalized edge does not imply
vanishing of its aggregated physical readout. The test must keep this distinction
and the actual complete coherent packet, rather than replacing it by an arbitrary
trace-zero difference of unrelated rows.

Search lead: `GaloisForLFunctions.HTGeometry.finite_weighted_hilbert_dispersion`
in `formal/GaloisForLFunctions/HTGeometry/FiniteHilbertDispersion.lean:103` gives
the finite weighted Hilbert variance identity; its source was read. The deep
query also found `HilbertMetric.sum_pairwise_norm_sub_sq_eq_two_card_mul_centered`.
Both require an actual edge-admission/norm bridge before use. Search result:
`/tmp/route_l_coherent_variance_search.json`, partial coverage. No applicability
claim or extra module build has been made for these variance leads.

### C9 verified checkpoint, 2026-09-11

`XiGammaSixWoldJordanSignedMarginal` passed scratch Lean, the capstone axiom
audits, its single-module final build, repository lint and scoped whitespace
checks. The axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`. The `RHTower` import is wired; no umbrella build was run and no
owned Lean process remains. The signed reader-continuity law, exact complete
coherent growth classification and normalized edge bound are formal. The next
explicit coherent-star norm/marginal construction remains unproved. Source-to-
physical agreement and RH remain open.

### C10 in progress: complete star, not an arbitrary trace-zero packet

The working scratch file is `/tmp/route_l_coherent_star.lean`. It defines the
star as `|S|^-1 R(1_p,S)`, develops the exact coefficient and Hilbert double-sum
identity, and derives the marginal `delta_p - uniform(S)`. The proposed growing
family uses `S_n = {p} union {first n primes}`, independent of `A` and Xi zeros.
The intended capstone retains complete-coherent membership, trace zero,
variation at most two, zero graph limit, marginal limit `delta_p`, and energy
limit `A/p` in one actual sequence. Scratch elaboration is still in progress;
none of these C10 additions has been promoted to the repository Lean tree yet.

Broad condensation/screening searches found
[Bertolini et al.](https://arxiv.org/abs/2607.16099), submitted July 17 and revised
August 6, 2026. Its cubic-anomaly construction produces extended symmetries and
projective charges associated with linked operator configurations. The source
characteristic class and discrete torsion remain inputs. It does not establish
agreement with the existing arithmetic physical reader. The norm-method deep
query returned partial coverage and unrelated quaternion/product examples;
the finite edge proof is being built from the literal source and checked Finsupp
and finite-sum APIs instead.


### C10 scratch verification and actual correction, 2026-09-11

The full scratch file now passes Lean. The promoted module is
`XiGammaSixWoldJordanCoherentStar`; its final single-module build and axiom audit
are pending. No source-to-physical comparison or RH theorem is claimed.

For `S_n={p} union {first n primes}`, the actual complete coherent sequence
`u_n=|S_n|^-1 R(1_p,S_n)` satisfies simultaneously:

- trace zero and marginal variation at most two at every finite stage;
- exact marginal `delta_p-uniform(S_n)`;
- exact squared ambient norm `2(|S_n|-1)/|S_n|^2`;
- ambient and one-leg graph limits zero;
- each marginal coefficient tends to `delta_p`;
- the existing reciprocal reporter tends to `A/p` for every free real `A`.

The normalized packet is itself a complete coherent packet, with the conjugate
scalar included in its profile. This is not an arbitrary trace-zero difference.
The finite edge sum was evaluated directly, including the off-diagonal subtype;
its squared norm is the full double sum of squared profile differences.

For the genuine normalized row `r_(a,n)` at `p=nthPrimeSubtype a`, the same
module proves its exact marginal is `delta_p`. The actual correction
`g_n=r_(a,n)-u_n` therefore has marginal `uniform(S_n)`, variation exactly one,
trace one, and the same nonzero singular graph limit as the original row.
Every fixed-prime marginal and its reciprocal energy tend to zero. The
cancellation is possible because it discards the retained point mass. The
construction asserts no nonnegativity of every corrected edge coefficient.

**Conjecture failed:** complete-coherent membership, zero graph limit, and a
uniform marginal-variation bound would make a correction physically invisible.
**Positive survivor:** all limiting data and the exact source-row correction
are explicit; bounded variation preserves the reader only after the correct
marginal limit is identified. The old graph limit does not identify it.

The correction deep/method search reported partial coverage (324 stale files)
and returned abstract closure subtraction, Roos coherent-representative
obstructions, and unrelated Lorentz bounds. None supplies the missing actual
physical comparison. Broad compensation/tightness searches found
[Slote, Volberg and Zhang](https://arxiv.org/abs/2608.04411), submitted August 5
and revised August 6, 2026. The paper compares quantum operator and product
norms using explicit tensor constructions. Its introduction and the tensor
recursion were read; no applicable identification with this arithmetic reader
was found or assumed.

### C11 next source-domain attack: nonnegative coherent repair

The signed star correction leaves open whether nonnegativity of the corrected
**edge packet**, inherited from the literal positive raw source, forces prime
retention. The source coefficients have now been read directly:
`r_(a,n)(p,q)=1/(p*q*M_n)` on the actual row prefix, zero elsewhere, where
`M_n` tends to infinity. This is an available source law, not a guessed decay.

Candidate: for every complete coherent `R(b,S)` such that
`g_n=r_(a,n)-R(b,S)` has real nonnegative coefficients on every ordered edge,
the mass removed from the left prime `p` is at most `1/(p*M_n)`.

Paper argument to formalize: positivity on both orientations between two
non-anchor primes forces the coherent profile to be constant there. The
remaining correction is a real nonnegative star amplitude `t`. If a star edge
leaves the actual row support, positivity forces `t=0`. Otherwise, for every
leaf `q`, `t <= 1/(p*q*M_n)`. With `k` leaves and largest prime `Q`, distinct
positive integer labels imply `k<=Q`, hence `k*t <= 1/(p*M_n)`. The bound tends
to zero, so the corrected source must retain its anchor marginal. This would
exclude energy cancellation by positive complete coherent repairs of the fixed
actual row. It would not prove that the missing cyclic/physical comparison
has such a positive repair, nor would it prove RH.

C11 is not yet Lean-verified. Its deep search returned only generic weighted
structures and unrelated reciprocal identities; a broader matrix-support method
query is running. The next proof should instantiate the literal row coefficient
and all ordered-edge positivity conditions, not add the retention conclusion
as a premise.


### C10 final verified checkpoint

`XiGammaSixWoldJordanCoherentStar` passed the final single-module build
(only its own Lean compile child ran), the `/tmp` axiom audit of all 28 theorems,
repository lint and scoped whitespace checks. Every axiom list contains only
`propext`, `Classical.choice`, and `Quot.sound`. The umbrella import is wired;
no umbrella or full build ran. All owned Lean processes completed.
The [formal card](../3-formalized/route-l-complete-coherent-star.md) records the
exact positive survivor and failed invisibility inference. The broader C11
matrix-support method query also returned partial, inapplicable results; no
retrieved statement was used as an assumed arithmetic bridge. C11 remains the
next proof attack; physical-reader agreement and RH remain open.


### C11 scratch proof, with a stronger positivity statement

`/tmp/route_l_positive_repair.lean` now develops the actual finite source bound.
The proof needs only nonnegative **real parts** of corrected edge coefficients;
it does not need to assume those coefficients are real. Both edge orientations
force equal real profile values away from the anchor. Counting distinct positive
integer prime labels below the largest leaf bounds the removed real mass by
`K_n=(1/p)/M_n`. The fixed row support and coefficient estimate are instantiated
from the literal source definitions. Scratch verification of the complete chain
is still running.

The proposed positive survivor includes
`1-K_n <= Re marginal(g_n)(p) <= 1`, hence convergence to one, and
`(A/p)(1-K_n) <= Re E_A(g_n)` for `A>=0`.
Thus `A>0` would give an eventual floor `A/(2p)` and exclude zero energy.
This derives retention from the finite source and the specified positive-repair
domain; it does not establish that the missing physical comparison has a
repair in that domain.

Broad rigidity searches found two primary-source leads in the requested date
range. [Wu, September 9](https://arxiv.org/abs/2609.10523) uses a variable
reference curvature in divergence identities; its derivative contribution
allows monotonicity of prescribed data to enter the sign argument. The
introduction and reference identity were read. [Marques–Neves–Sun, August 15](https://arxiv.org/abs/2608.15376)
prove local stable-norm rigidity of flat tori, with an extra volume condition
in codimension one; their explicit three-dimensional family shows that
condition cannot be omitted. The introduction, stated rigidity/counterexample,
and proof discussion were read. Their uniformity obstacle and extra retained
invariant are methodological leads, not established arithmetic hypotheses.
Neither paper supplies the fixed-reader comparison.

### C12 stress test of the single-complete restriction

A finite sum of complete coherent packets need not be one complete packet.
The C11 positive domain must therefore be tested under additive assembly.
Candidate: transpose every ordered edge of the genuine fixed-left positive row.
The transposed row is positive with trace one; the difference between the
original and transposed rows is a finite sum of two-point complete coherent
packets. Its right-prime marginal should lose each fixed prime as `M_n` grows,
and the reciprocal output should tend to zero because its numerator contains
summable reciprocal prime squares. Swapping edge indices preserves the ambient
norm, so the singular graph limit should be unchanged.

This is a concrete source-only test, not an assertion that the source cyclic
reader agrees with the fixed physical reader. If verified, it would show that
positivity and finite coherent additive assembly still allow escape, even though
one complete coherent repair forces retention. A corpus/deep-method query on
Finsupp transposition and `lp` reindexing is running. C12 is not yet formal.


### C11 final verified checkpoint, 2026-09-11

`XiGammaSixWoldJordanPositiveCoherentRepair` passed full scratch Lean, its
targeted final build, the `/tmp` axiom audit of all 16 theorems, and repository
lint. Only `propext`, `Classical.choice` and `Quot.sound` occur. Its umbrella
import is wired; no full or umbrella build ran. C11 build/check processes have
completed. The exact quantitative retention and energy statements, including
the weaker nonnegative-real-part condition, are recorded on the
[formal card](../3-formalized/route-l-positive-coherent-retention.md).

C12 is now being checked in `/tmp/route_l_transpose_repair.lean`: edge swap,
linear packet transposition, trace and ambient norm preservation, an exact
two-point coherent packet identity, and the finite coherent-sum decomposition
of `f-transpose(f)`. The corpus reindex query found the actual unitary
`RHTower.lpReindexEquiv` in `EulerSquarefreeDyadicAffineProjection.lean`; its
source was read. The scratch uses the same equivalence/tsum norm mechanism
directly, avoiding an unrelated module import. No C12 theorem is promoted yet.
Physical-reader agreement and RH remain unproved.

### C12 actual-source energy identity and boundary, scratch audit

The scratch now includes the literal transposed normalized row, its nonnegative
real coefficients, trace one, zero ambient limit, unchanged singular graph
limit, and anchor marginal exactly zero at every stage. Its repair has the
exact finite decomposition

`f-transpose(f) = sum_(i in support f) R(conj(f(i))*1_(left(i)), {left(i),right(i)})`.

The source energy mechanism is now explicit. For the raw row `v_(a,n)`,

`E_A(transpose(v_(a,n))) = A*p*||admission(v_(a,n))||^2`.

Indeed its weight is `w_k=1/(p*q_k)`, and `(A/q_k)*w_k=A*p*w_k^2`.
The admitted raw norm squared is exactly `sum_k w_k^2`. The existing uniform
raw-horizon bound then gives, for the normalized transposed row,

`|E_A(g_n)| <= |A|*p*||rawHorizon||^2/M_n -> 0`.

No numerical summation, prime asymptotic, or new summability assumption is used.
The already proved positive head-mass law then gives escape from every bounded
prime range. C11 also forces the new repair to be eventually unequal to **any**
single complete coherent packet: such a representation would force its zero
anchor marginal to be at least `1-K_n>0`.

The full scratch check, including the last norm inequality and head-mass
consequence, is running. These C12 results are not yet promoted. They identify
why one joint finite coherence condition cannot be replaced by separate local
coherence of finitely many summands. Neither the positive transposition nor
its zero-energy limit identifies the original fixed physical marginal.

### Next candidate: quantitative cost of approximate positivity

After the exact C11/C12 boundary is audited, test a joint complete repair whose
corrected edge real parts have small total negative mass `delta`, rather than
being pointwise nonnegative. For `k` leaves, write their anchor amplitudes
`t_j=Re(b(p)-b(j))` and removed mass `rho=sum_j t_j`. The negative leaf-to-leaf
mass controls half the sum of pairwise amplitude differences, hence
`sum_j |t_j-rho/k| <= 2*delta/k`. At least half the distinct positive labels
lie above `k/2`, where the original row coefficient is at most `2*K_n/k`.
Their outgoing negative mass suggests `rho <= 2*K_n+6*delta`, with the empty
and one-leaf cases treated separately. If formalized, a source-derived
`delta_n -> 0` would retain the anchor and an energy floor even under
approximate positivity. This bound is a new conjecture; the actual source
negative-mass estimate and physical comparison are not supplied by it.


### C13 paper refinement before formalization

The initial `2*K_n+6*delta` candidate can be sharpened on paper. Separate the
negative real mass on outgoing anchor edges (`D_out`) from that on leaf-to-leaf
edges (`D_leaf`); these edge sets are disjoint, so `D_out+D_leaf<=delta`.
For `k>=2`, select exactly `m=ceil(k/2)` leaves whose positive integer labels
are at least `m`. Such a set exists by counting the labels below `m`. Their
original reciprocal row mass is at most `K_n`, and `m/k>=1/2`.

The pairwise identity gives
`sum_j |t_j-rho/k| <= 2*D_leaf/k`. If `rho>0`, the selected outgoing edges
therefore give
`rho/2 <= K_n+D_out+2*D_leaf/k`.
Since `k>=2`, this yields the stronger candidate

`rho <= 2*K_n+2*delta`.

For `rho<=0`, the upper bound is immediate. For zero or one leaf, the direct
outgoing coefficient bound handles the case. This paper argument retains the
specific half-sized selected set; merely saying that many labels are large
would not bound their total original mass by `K_n` without that selection.
No optimal-constant claim is made. A deep/method query on finite mean deviation,
pairwise differences and disjoint negative-part sums has been started at
`/tmp/route_l_negative_mass_repair_search.json`. The new bound is not yet
Lean-verified, and no actual source negative-mass estimate is assumed.


### C12 final verified checkpoint, 2026-09-11

`XiGammaSixWoldJordanTransposeRepair` passed full scratch Lean, its targeted
final build, the `/tmp` axiom audit of all 21 theorems, and repository lint.
All axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
Its umbrella import is wired; no full or umbrella build ran. All owned Lean
build/check processes completed. The [formal card](../3-formalized/route-l-positive-transpose-assembly.md)
records the exact quadratic energy identity, positive source escape, finite
coherent-sum decomposition, and eventual failure of one complete coherent
representation. The frontier map and route-neutral joint-consistency ledger
entry are updated. No physical-reader agreement or RH proof has been produced.
The next unproved mathematical target is C13's quantitative negative-mass cost.


The C13 deep/method query completed with partial coverage. Its leading hits
were negative-part notation, generic finite-mean definitions, a Hilbert
orthogonality lemma and unrelated deviation observables; the proposed ingredient
set does not prove the required real absolute-deviation bound. No retrieved
candidate is being treated as that bound. The next turn should broaden toward
finite `L1` dispersion and prove the selected-half counting lemma directly from
the actual Finset APIs. All search and owned Lean processes from C11/C12 are
terminal; no background Lean work remains.

### C13 direct cut-balance pivot

Avoid the auxiliary absolute mean-deviation theorem. Let `L` be the `k`
leaves, and select `m=ceil(k/2)` leaves `T` with labels at least `m`.
The complete-potential identity directly gives

`m*rho - k*sum_(q in T) t_q = sum_(q in T) sum_(j in L) (t_j-t_q) <= D_leaf`.

The selected outgoing edges give `sum_T t <= K_n+D_out`. Thus
`m*rho <= k*(K_n+D_out)+D_leaf <= k*(K_n+delta) <= 2*m*(K_n+delta)`.
For nonempty `L`, `m>=1`; division proves `rho<=2*K_n+2*delta` without a
sign case for `rho`. The empty case is exact zero. The only combinatorial
input is distinct positive integer labels, proved by a finite injection.
The remaining source step is to account for the two disjoint sets of negative
edges inside the literal corrected packet's total negative real mass.
This is a proof target, not an assumed physical-source bound.

The second deep/method query (`finite subset sum cut balance potential
difference negative part`) completed with partial coverage: 706091 method
records ready, 778 stale. Subset-sum greedy lemmas were retrieved, but do not
supply the exact half-sized set. The actual `Finset.exists_subset_card_eq`,
cardinal filter partition and nonnegative subset-sum APIs are being used.

### C13 source refinement and literature audit

The direct cut proof now has a matching lower removal bound. Incoming
leaf-to-anchor edges have corrected real value `t_q`, so their negative mass
gives `-rho<=delta`. Together the proposed literal-row retention interval is

`1-2*(K_n+delta_n) <= Re(m_(g_n)(p)) <= 1+delta_n`.

The reciprocal reader also admits the signed comparison
`Re E_A(g) >= (A/p)*Re(m_g(p))-(A/2)*delta(g)` for `A>=0`, because every prime
label is at least two. Thus negative mass tending to zero would retain the
anchor limit one and exclude vanishing positive reciprocal energy. Conversely,
for the unit reciprocal reader, the exact finite cost inequality is

`1-2*K_n-p*Re E_1(g_n) <= (2+p/2)*delta_n`.

If that reader tends to zero, this forces `delta_n>=1/(p+4)` eventually,
without assuming the negative mass has a limit. This specializes to the
explicit C10 coherent-star corrected row: its marginal variation is one and
its energy vanishes, but its total negative edge mass cannot tend to zero.
These statements are in the current scratch audit; none supplies a bound on
the original physical comparison's negative mass.

The weighted-negative-part deep/method query completed with partial coverage
(706091 ready method records, 778 stale). Actual `TopSumMajorization` and
`PoissonJensenUpperBound` source proofs were read. The former requires signed
partial-sum control, which is not supplied here; the latter proves generic
positive-part subadditivity. The retrieved Suzuki negative-mass method starts
from a zero-negative-mass premise. It is not a producer for this source.

Broad one-word searches used `dissipation`, `gluing`, `truncation`, `balance`
and `coercivity`, preferring June–September 2026. Primary-source checks:

- [Evangelatos–Haiden, 21 August 2026](https://arxiv.org/html/2608.21201v1),
  Lemma 3.2 and Theorem 3.5: a uniform complex phase sector of width below pi
  bounds cancellation, and a phase gap for glued semistable objects proves a
  support property. The proof keeps the extension datum and proves a common
  sector for all component factors. A sector condition on our repaired edge
  coefficients alone cannot restore prime retention: C12's transposed row has
  positive real coefficients and still escapes. The useful remaining question
  is quantitative control of joint coherence, not an assumed sector bound.
- [da Silveira Dias, 25 July 2026](https://arxiv.org/html/2607.22965v1),
  Section 5: a modified rational gluing constructs an anti-symplectic involution
  on the relative dual Hamiltonian space. No identification with the fixed
  Burnol/Deninger reader was found; its involution is not substituted for ours.
- [Tao et al., 20 August 2026](https://arxiv.org/html/2608.19694v1), Section III:
  the model introduces phase-selective jump operators; the stationary channel
  depends on this additional choice. The subsequent numerical evidence is not
  a source theorem for route L and is not used in Lean.

The next candidate is quantitative distance from joint complete coherence.
C12 proves exact nonmembership eventually. C13 suggests a stronger invariant:
if the positive transposed repair were within vanishing full edge `L1` distance
of one complete packet, that error would bound both negative mass and anchor
error, contradicting the retention interval. The expected source estimate is
`distance >= (1-2*K_n)/3`. This new conjecture remains unproved.

### C13 scratch passed; C14 source-distance attack

All 17 C13 theorems now pass the full `/tmp/route_l_negative_repair.lean`
check. The module `XiGammaSixWoldJordanNegativeMassRepair` is wired and its
targeted final build is running; axiom and lint audits remain. No numerical
experiments, added assumptions or new axioms were used.

For C14 let `h` be a nonnegative-real target packet with zero anchor marginal,
`u=(r_(a,n)-h)-R(b,S)` the error from one complete coherent correction, and
`V(u)=sum_(i in support u) norm(u(i))` the **full edge** variation. Then
`r_(a,n)-R(b,S)=h+u`, so `delta(h+u)<=V(u)` by coefficientwise positivity.
Its anchor real marginal is at most `V(u)` because the target anchor is zero.
The C13 lower retention bound therefore yields `1-2*K_n<=3*V(u)`.

The actual positive transposed row supplies such a target. Thus the expected
distance bound is uniform over every `b,S` at a fixed stage, and eventually
at least `1/6` simultaneously for all complete packets. This strengthens
eventual exact nonmembership to exclusion of approximation in full edge `L1`.
The scratch `/tmp/route_l_coherent_distance.lean` contains this argument;
it has not yet been checked while the C13 final build occupies the single
owned Lean process. This does not exclude approximation in weaker norms or
identify the fixed physical comparison.

### C13 final verified checkpoint

The targeted `XiGammaSixWoldJordanNegativeMassRepair` build passed, all 17
theorems passed the `/tmp` axiom audit with only `propext`, `Classical.choice`
and `Quot.sound`, and repository lint passed. The formal card, frontier and
route-neutral total-sign-error constraint are updated. C13's Lean processes
are terminal. C14's full scratch check is now the only owned Lean process.
Physical-reader agreement and RH remain unproved.

### C14 final verified checkpoint

All seven C14 theorems passed scratch Lean. The targeted final module build
also passed, including removal of one unnecessary `simpa`, and repository
lint passed. All seven theorem axiom audits passed with only `propext`,
`Classical.choice`, and `Quot.sound`. The exact source lower
distance is `(1-2*K_n)/3`; the eventual `1/6` margin is uniform over every
complete profile and finite prime set. No closure of the class in a weaker
graph topology is asserted.

The renewed physical-agreement deep/method query completed with partial
coverage (706094 ready method records, 778 stale). It retrieved the actual
`DeningerBurnolConormalRadialTopBoundaryComparison` and
`DeningerOrdinaryIntegerBVGreenStokesRadialComparison` source identities;
their relevant proofs were read. Exact multiplicity makes the leading
conormal jet nonzero. The actual reflected norm-square defect equals
`n*(B_n(s)-B_n(1-star(s)))`, where the literal boundary evaluator is
`B_n(s)=n^-1*(1-gain_n(s)^-1)`. These identities retain the defect; the
retrieved method's proposed curvature transfer does not prove it zero.

The next direct comparison attempt must keep that original `B_n` term and
the full coherent compensation. Neither replacing it by the normalized
cyclic trace nor invoking aligned phases of the positive transposed target
establishes equality. C13/C14 now quantify two costs a candidate must address:
total negative mass and error from joint complete coherence in full edge
variation. They do not prove that the actual physical construction has either
required bound. The goal remains active and RH unproved.



Both C13/C14 formal cards and umbrella imports are wired. No full or umbrella
build ran. All owned Lean, search and lint processes from this turn completed.
The next work must attack the original physical boundary comparison, with
these source costs retained rather than assumed to vanish.

### C15 cutoff reader: existing positive survivor located, no duplicate module

The direct source test was the diagonal cutoff of the original operator
`[S_n^*,Q*S_n]=n^-1*Q-P_n*Q`. Source search located the exact answer already
formalized in `RouteRDegreeSixBVGreenNeutralFinitePart.lean`: the cutoff is
`(H_N-H_(floor(N/n)))/n`, its limit is `log(n)/n`, and this is the neutral
Bockstein derivative of `n^-1*(1-exp(-a*log n))`. At degree six it is strictly
positive. Thus ordinary cyclic cancellation does not survive this finite-part
reader. No duplicate proof or weaker substitute is being added. The distinct
prime-sparse Dixmier result was also read; it concerns a different diagonal
and makes the normalized residue blind at every Xi copy.

The harmonic/trace deep and method query reported partial coverage and missed
this exact module among its leading hits; exhaustive targeted `rg` located
it. The actual-source query retrieved the known Gaussian Green/Wronskian
comparison, whose factor is the physical fracture times a positive Hodge
factor. Its proposed identity-lift boundary argument does not annihilate that
factor. Neither retrieval suggestion supplies a new vanishing theorem.

### C16 candidate: construct the physical reader from convergent weighted diagonals

The next source-defined reader weights the actual diagonal coefficient
`d_k(T)` by `k^(1-2*sigma)`. On `Q`, the trace is the positive partition sum
`Z_sigma=sum_(k>=1) k^(-2*sigma)`, convergent for `sigma>1/2`. On `P_n Q`,
reindexing multiples gives `n^(-2*sigma)*Z_sigma`. Consequently the normalized
reader should evaluate the actual boundary to

`1/n-n^(-2*sigma) = (1/n)*(1-gain_n(s)^-1)` when `sigma=Re(s)`.

This is a proposed actual operator-to-physical comparison in the convergence
chamber, including nonneutral parameters. It is not cyclic: the two products
have normalized values `1/n` and `n^(-2*sigma)`. The task is to prove the
admitted diagonal domain, linear reader, source normalization, multiples law
and exact physical evaluation, rather than define a zero output. No claim of
ordinary cyclicity, a global reflected normal domain, or RH is made.

Corpus sources read: `ZetaTwoShiftContraction` contains the needed positive
weights, but its summability theorem uses the stronger condition `sigma>1`;
`AbelianZetaGas/KMSState` constructs a different gas algebra with an explicit
modular exchange, not an untwisted trace. The new reader must be checked on the
literal ordinary-integer BV--Green operator.

Further exhaustive source search located `DeningerGammaSixGreenGibbsPhysicalReader`.
Its shell Gibbs formula and its equality with the degree-six physical scalar
are already formal. C16 therefore does not claim that scalar identity as a new
mechanism. The remaining test is the **literal ordinary-integer operator
domain and its exchange law for every admitted operator**, at every positive
integer dilation.

#### C16 paper proof and current scratch target

Put `m_sigma(k)=k^(-2*sigma)` and
`d_sigma,k(T)=m_sigma(k)*k*(T e_k)(k)`. Let `D_sigma` be exactly the submodule
where this complex diagonal family is summable. Summation is a linear
functional on `D_sigma`; normalization is defined only with a proof of
`sigma>1/2`, not by dividing a totalized divergent sum.

On the literal reciprocal Green operator `Q`, the summands are `m_sigma(k)`.
The p-series criterion proves `Q in D_sigma iff sigma>1/2`. For `P_n Q`, they
are the restriction of the same mass to multiples of `n`. The injective
reindexing `k=n*j` and multiplicativity of real powers give exactly
`sum_(n|k) m_sigma(k)=m_sigma(n)*Z_sigma`. Thus the normalized boundary value
is the existing physical value, and is nonzero throughout the convergence
chamber for `n>=2`.

The stronger survivor applies to every `T in D_sigma`. Both `S_n^* T S_n`
and `T P_n` are admitted: their diagonals are a rescaled injective subsequence
and a restriction of the original summable diagonal. Reindexing proves

`Trace_sigma(S_n^* T S_n) = [n*m_sigma(n)]^-1 * Trace_sigma(T P_n)`.

The multiplier is exactly the fixed half-density gain
`exp((2*sigma-1)*log n)`. This is a source-derived weighted exchange law,
not ordinary cyclicity. Reflection sends `sigma` to `1-sigma`; no reflected
pair of these domains admits `Q`. The physical comparison is established
on the convergence chamber by this paper proof; its cyclic extension across
the excluded wall is not established. All 30 theorems now pass in
`/tmp/route_l_gibbs_reader.lean` without warnings. The
[finished module and paper proof](../3-formalized/route-l-gibbs-operator-domain.md)
are wired into `RHTower.lean`. The targeted final build passed, only the new
module was built, all 30 axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`, and repository formal lint passed.
No umbrella build or numerical experiment was run; no owned Lean process
remains. C16 closes the source-domain and weighted-exchange statements,
not cyclic-to-fixed-physical agreement or RH.

Lean also proves the stronger actual-chain admission statement. For every
`n!=1`, `S_n^*` and `Q S_n` both have zero diagonal and belong to `D_sigma`
for every real `sigma`, whereas `S_n^* Q S_n=n^-1 Q` belongs exactly for
`sigma>1/2`. In particular, the two factors are readable at the critical
parameter and their product is not. Admitting the factors cannot justify
cyclicity on that missing product.

The Gibbs/normal-domain and exchange deep searches report partial coverage.
Their leading method hits mostly concern different gas algebras, finite
matrix reindexing, or computational normal forms. Targeted source search
supplies the actual Wold/Green identities; mathlib's p-series, indicator and
injective-sum lemmas supply the analytic steps. No retrieved proposal is
being used as an unchecked theorem.

#### Broad recent-paper tests

Broad searches used `transgression`, `anomaly`, `reciprocity`, and `excision`.
[Niu--Bi--van Wyk, August 2026](https://arxiv.org/html/2608.30778v1) obtains a
positive response matrix from an explicit matched-adjoint transport law;
conservation alone does not supply that law. This does not prove the missing
arithmetic reader matching. [Vu et al., September 2026](https://arxiv.org/html/2609.04169v1)
derives response-rank restrictions from reciprocal symmetric stiffness, with
no identification of the present operator domain.

[Zheng--Huang, August 2026](https://arxiv.org/html/2608.09776v1), Appendix B,
retains endpoint contractions in its exact transgression; local Hamiltonian
exactness is an additional condition. [Song--Wang, August 2026](https://arxiv.org/html/2608.19539v1),
Section 5.2, retains an explicit boundary term in the triangle identity.
These tests support tracking the comparison boundary and its domain; they
provide no vanishing theorem for the fixed Burnol/Deninger reader.

### C17 source-tail test: ordinary trace-class repair is already excluded

The next candidate was to restore ordinary trace admission by retaining the
complete source tail omitted from a principal Green model. The actual-source
files settle that specific test already. In
`DeningerGammaSixFullSourcePrincipalClass`, the complete tensor square is the
nonzero principal tensor plus its exact leading--tail, tail--leading and
tail--tail remainder. That remainder is rectangular trace class, but the
complete source is not: the canonical bounded leading-tensor reader recovers
the non-trace-class principal shell operator. Subtracting the trace-class
remainder would otherwise make that principal operator trace class.

The positive survivor is the existing exact weak-trace principal class and
the `DeningerGammaSixSingularGreenStokesCoface` identity: the full Wold coface
equals the remainder's Wold coface and is ordinary rectangular trace class.
Those statements are already formalized; no duplicate module is added.
They do not exclude every weighted diagonal or singular completion, and do
not identify a cyclic reader with the fixed physical one. The full-source
remainder deep/method query reported partial coverage and mostly unrelated
remainders; the conclusions here use the literal source definitions and
existing theorems read directly.

### C18 proved: recover the full diagonal from all divisibility readouts

The sharper tail test keeps the fixed Gibbs reader and allows an arbitrary
summable diagonal correction to `Q`, including signed corrections. The
question is whether the corrected source can kill all ordinary-integer
Wold boundaries in the convergence chamber. C16's exchange law says this
would make every nontrivial divisibility readout of the corrected source
zero, since the physical multiplier is nontrivial there.

Proposed arithmetic reconstruction: a summable complex family on positive
integers is determined by its sums on all divisibility sets. In particular,
if every sum on multiples of `n>=2` is zero, the family is supported at the
unit. This would force any such corrected Green diagonal to vanish at every
integer at least two, requiring correction `-1/k` on that entire tail.
That correction is not summable. The positive survivor sought is the exact
diagonal reconstruction/classification, rather than only a failed repair.

The proof test uses that divisibility sets form an intersection-stable
family and generate all singletons; summability permits bounded indicator
limits. No positivity or unproved Möbius-series interchange is assumed.
The reconstruction and actual-reader application are now formalized.
They concern the specified diagonal reader, not equality of full operators
or an RH proof.

The measure-theoretic reconstruction step is now checked in scratch. The
sets `{k : n divides k}` are a pi-system (intersection uses the least common
multiple). Their generated sigma-algebra contains every singleton: the
complete divisibility pattern of `k` identifies it by divisibility
antisymmetry. A summable complex family defines a countably additive vector
measure against counting measure. The pi-lambda induction therefore makes
zero divisibility sums imply zero vector measure and zero coefficients.
Subtracting its total mass at the unit gives the nontrivial-multiples
classification. Application to the C16 weighted diagonal and fixed Wold
exchange law proves exact unit-diagonal classification and excludes every
summable diagonal correction to `Q` satisfying all-integer pair cyclicity.
All 12 theorems passed scratch, the targeted final module build, the complete
axiom audit (only standard Lean foundations), and formal lint; the module
is wired into `RHTower`. [Dependency-closed proof and audit](../3-formalized/route-l-cyclic-diagonal-reconstruction.md).

The search for nonlinear source comparison retrieved
`ThetaCuspHawkingBMVacuumDifferentiableNonlinearEvolutionNoGo`. Its proof
was read: a prescribed differentiable vacuum first variation inherits the
source's covariance, so merely calling the comparison nonlinear does not
remove a linearized obstruction. It constructs no new route-L landing.
The top-jet search mostly returned other source families; their reconstruction
or positivity hypotheses do not identify this fixed physical reader.
The divisibility deep/method query was also partial. Its
`CofinalUnitProfileResidue.HasReferenceResidue.of_summable_sub` and residue
uniqueness methods confirm the summable-difference step used after arithmetic
reconstruction; no unproved divisor-weighted summability is needed.

The new broad searches used `regeneration`, `modular`, `isometry`, `holonomy`,
and `coercivity`. Most hits were unrelated. The
[August 2026 Markovian holonomy universality theorem](https://arxiv.org/html/2608.15923v1)
requires the same boundary conjugacy data, a fixed infinitesimal Fourier
symbol, and uniform spectral summability (A3); its stable graph theorem
retains marked loop type. Those are additional comparison obligations,
not consequences of gluing alone. The
[June 2026 discrete Carroll BF construction](https://arxiv.org/html/2606.25499v1)
retains physical boundary holonomies after bulk flatness and imposes further
boundary constraints for its conformal reduction. The
[August 2026 holonomy-signature classification](https://arxiv.org/html/2608.01444v1)
uses a dictionary with primitive differentials and a stratum nonemptiness
theorem. None supplies the missing arithmetic reader identification.

### C19 proved: prime-only incidence control

C18 requires every integer divisibility test, including composite labels.
The next test asks whether even prime tests exclude a summable diagonal
repair to the literal Green operator in the fixed Gibbs chamber. This is
not inferred from C18: prime divisibility sets alone are not an
intersection-stable generating family.

The proposed positive estimate is a uniform column bound, for every `a>0`,
`sum_(p prime, p|k) (p/k)^a <= C_a`. For `r` distinct prime divisors, each
cofactor contains `r-1` integers at least two, giving the bound
`r * (2^(-a))^(r-1)`. Summability of a geometric series with its linear
weight would give a uniform constant. An absolutely summable correction
would then have summable prime incidence outputs. Prime cyclicity of
`Q+R`, however, would force the output at `p` to equal a nonzero constant
times `1/p`, contradicting the proved prime harmonic divergence.

The finite uniform column bound has passed Lean in scratch. Distinct prime
factors are relatively prime, so their product divides the integer; deleting
one factor bounds each cofactor below by `2^(r-1)`. The chosen finite budget
is the convergent series `sum_(j>=0) (j+1)*(2^(-a))^j`. Its full nonnegative
matrix majorant, exact connection to actual Gibbs products, and the
prime-only correction obstruction are now checked. This tests the fixed normal reader and correction class, not all
possible singular source comparisons.

The C19 prime-incidence deep/method search was partial (706108 ready methods,
779 stale). `Sieve.RoughCountTuran.sum_indicator_pair_le` supplied the checked
pairwise-prime coprimality mechanism. `RouteRCofinalSieveHarmonicResidue`
retains harmonic divergence after deleting any finite prime head. The
column/cofactor search mostly returned finite matrix cofactors and unrelated
entries; no infinite arithmetic column estimate was imported from those hits.
The actual proof uses the full prime product and a geometric majorant.

Broad searches this pass used `renewal`, `residues`, and `rigidity`. The
[September 2026 permanent-pinch paper](https://arxiv.org/html/2609.02300v1)
constructs finite combinations in explicit Feynman examples by canceling
residues with fixed momentum labeling. Its general rule for extracting
leading divergences is explicitly conjectural (§1), and iterated residues
need a subtraction prescription. Therefore it supplies no established
arithmetic source-to-reader comparison. The
[July 2026 second-order polytope rigidity theorem](https://arxiv.org/html/2607.09252v1)
uses the actual derivative constraint matrix and tests its quadratic
forcing against cokernel stresses; existence of an analytic flex is used
through curve selection. Applying that method here would require a
source-derived nonlinear constraint and a nonzero blocking pairing. Calling
an existing linear comparison a deformation does not supply either. These
are method tests, not external Lean premises.

The second-variation deep/method search was also partial. Its leading
methods concern metric two-jets, finite positive-kernel calibration, and
bounded derivative estimates for other dynamics. No source-defined
route-L nonlinear constraint with the required blocking pairing was
retrieved. This search limitation is not a mathematical no-go; the prime
incidence proof proceeds through the actual arithmetic kernel instead.

C19's positive estimate has a sharp converse. For `a<=0`, choose `k` as a
product of arbitrarily many distinct primes. Every selected incidence
entry `(k/p)^(-a)` is at least one, so no uniform column constant exists.
Thus the exact column-control threshold is `a>0`, equivalent to the open
Gibbs chamber under `a=2*sigma-1`. The complete 18-theorem scratch file passed with no warnings, including
this converse and the literal operator repair theorem. The targeted final build passed, the umbrella import is wired, all 18
theorems have only standard Lean foundational dependencies, and formal lint
passed. [Dependency-closed proof, sharp threshold and audit](../3-formalized/route-l-prime-incidence-repair.md). No critical singular reader
has been constructed.

### C20 proved: source-defined shell flattening of the full Gamma tensor

C18--C19 left the full rectangular Gamma source/scalar model identification
unproved. The literal source has a canonical bounded leading-tensor reader;
its image of the principal operator is the sorted shell diagonal
`lambda_n=6^(-floor(log_6(n+216)))`, and its image of the complete remainder
has a summable diagonal. Test the source-defined multiplier
`d_n=1/((n+216)*lambda_n)`.

The existing shell bounds suggest `1/6<=d_n<=1`. Moreover degree-six Wold
transport sends `n` to `6*n+1080`, so `(n+216)*lambda_n` is invariant and
`d_(Wold n)=d_n`. Thus flattening should retain this exact dilation law and
send the literal principal diagonal to `1/(n+216)`. Multiplication by the
bounded profile preserves the summable full-source remainder. Reindexing
onto positive integers at least 216, with a finite omitted head, should
produce `Q` plus a summable correction from the actual full Gamma tensor.

This is a candidate actual-source comparison, not a chosen cyclic reader.
It preserves the leading coefficient and degree-six dilation on the tail;
it does not yet claim all-prime intertwining, Xi-jet fidelity, or agreement
with the fixed physical reader. The immediate proof target is the complete
source identity and summable correction, followed by its exact compatibility
or incompatibility with the C19 physical prime tests.

C20's full-source/coface deep search was partial and mostly returned other
Gamma-residue and physical-source families. The shell-normalization method
search did retrieve `DeningerGammaSixLogarithmicWoldJordanTransgression`;
its literal identity is `L(Wn)-L(n)/6=(log(6)/6)*lambda_n`. The current
candidate carries this through the same multiplier, predicting the nonzero
first-normal residue `(log(6)/6)/(n+216)`. This is not an asserted full
Xi-jet transport.

The broad paper searches used `transgression`, `renormalization`, and
`descent`; most hits were unrelated. The
[August 2026 stochastic RG exposition](https://arxiv.org/html/2608.11106v1)
defines its effective weight by conditional expectation and proves partition
preservation through that exact common-measure identity. It supplies no
such measure or conditional-expectation identity for this arithmetic tensor.
The [July 2026 mixed-state RG construction](https://arxiv.org/html/2607.08568v1)
starts with finite-dimensional Hopf-algebra tensor-network data, positive
trace-one density operators, and specified quantum channels. No matching
arithmetic channel or positivity law is obtained here. The source-defined
shell multiplier is being checked directly instead of importing these
additional assumptions.

C20's complete 24-theorem scratch file passed without warnings. The full
source-defined operator, summable reciprocal correction including the
finite head, admission in every open Gibbs domain, and failure of prime
cyclicity are checked. A bounded scalarization operator of the original
rectangular carrier is constructed, with exact degree-six Wold-pullback
and compression naturality and a trace-class complete remainder. The same
normalization retains the strictly positive first logarithmic coface.
The targeted final module build, complete 24-theorem axiom audit (standard
Lean foundations only), and formal lint passed; the umbrella import is
wired. [Dependency-closed full-source comparison and audit](../3-formalized/route-l-full-gamma-shell-flattening.md). The cyclic
producer candidate fails; the full-source comparison is its positive
survivor. Physical-reader agreement and full Xi-jet fidelity remain open.

The next compatibility check has a precise existing interface:
`BurnolSoninCompletedJetBridge.exists_soninExtendedCompletedMellinContinuationJetEvaluator`
constructs every finite completed continuation jet as a bounded functional
on `soninExtendedSpace a` throughout the open strip. Its literal Mellin-jet
identification is proved on `1/2<Re(w)<1`. The embedding in that theorem
preserves the underlying `L2` vector. Those conclusions require actual
membership in the same extended Sonin carrier; they do not identify C20's
leading-tensor coefficient with the required physical jet. A source map
into that carrier and the exact evaluation identity remain to be derived.
The current C20 logarithmic formula concerns the existing shell principal
jet, not all derivatives of the full tensor or all Xi jets.

### C21 proved: bounded physical probes of the complete source

Test a bounded linear map from the actual tensor carrier into Burnol's
co-Poisson quotient, before selecting any divisor. The quotient already has
bounded completed-Mellin evaluation vectors and a proved separation theorem
on the open right strip. These are literal physical probes, unlike an
arbitrarily chosen scalar coefficient.

For any bounded scalar probe `L`, the full source identity predicts
`d_n L(F_n)=L(v)/(n+216)+e_n`, with `sum |e_n|<infinity`.
Thus changing the bounded probe can change the reciprocal coefficient but
cannot absorb it into a summable repair. If this scalarized operator is
prime-pair cyclic in an open Gibbs domain, C19 applied after normalization
forces `L(v)=0`. Applying this to all actual Mellin probes of a bounded
quotient map `B` should force `B(v)=0` by Mellin separation. Conversely, a
nonzero `B(v)` should give a detecting strip point whose full-source scalar
operator fails prime cyclicity.

The positive target is the exact complete-source decomposition for every
bounded probe and the sharp criterion that its scalar diagonal is summable
exactly when the leading tensor coefficient vanishes. No source-to-Sonin
map, cyclicity premise, or nonzero target image is assumed as an RH input.
This tests bounded comparisons retaining a nonzero leading image; singular
comparisons and maps with source-dependent unbounded evaluation remain open.

The complete 18-theorem scratch file and targeted final module build passed.
All 18 theorem axiom audits use standard Lean foundations only; formal lint
passed and the umbrella import is wired.
The full-source decomposition, sharp summability criterion, fixed-domain
homogeneity and prime obstruction are checked for every bounded scalar
probe. Pullbacks of actual quotient evaluation vectors give literal Mellin
values, with `sigma=Re(w)`. Simultaneous prime cyclicity forces the leading
image to vanish by the existing Mellin separation theorem. A nonzero image
gives a detecting right-strip point with failed cyclicity. Every finite
literal completed-Mellin jet has the same proved coefficient criterion.
[Proof, scope and audit](../3-formalized/route-l-bounded-sonin-probes.md).

The two deep/method searches were partial; their finite-kernel and trace
continuation candidates supplied no missing comparison. Broad September
interpolation papers supply derivative or Sobolev approximation estimates
under explicit bounds, not an arithmetic evaluation identity. Exact search
coverage and primary-source checks are recorded in the proof card.

This does not identify the leading tensor image with a Xi divisor's top
jet. Killing that image can leave a nonzero complete remainder. The next
test is whether a source-derived comparison can retain the required Xi
jets there while respecting actual prime transport. The current corpus's
`XiThetaL2Cyclicity` proves density of the actual theta source's translation
orbit, and `XiThetaBoundaryCarrierNoGo` excludes continuous reporters
killing that whole orbit on a dense completion. Applying that result here
requires the actual tensor/Sonin transport law; it must not be assumed
from scalar coefficient vanishing. Source-forced singular comparisons
remain the other live possibility. RH and the physical-agreement gate
remain open.

### C22 proved: strict arithmetic tails retain conormal data

Test the inference that removing the leading source leaves no usable Xi
data. The current source corpus has exact successor transport for every
positive ordinary-integer label: removing its Möbius head and rescaling the
complete tail produces the full residual at the next nonzero Möbius label.
The scalar transport is proved on its actual convergence domain.

For the literal internally promoted strict tail, predict Fourier--Laplace
value `(M_p(m,w)-mu(p))*XiC^(k)(w)`. Successor transport and convergence of
the successor residual to its nonzero Möbius coefficient should prove that
the strict-tail multiplier is eventually nonzero, even though it tends to
zero. At every Xi divisor, the adjacent source-jet pair should therefore
retain its nonzero top coefficient at every sufficiently large depth.
This would give a positive surviving source after every finite head removal.

The first proof target is the complete strict-tail integral and exact
coefficient, then eventual nonvanishing and full multiplicity retention.
The physical Hilbert tail and its exact successor norm law are checked
separately. This is a test of the pre-tensor source used by Gamma-six;
identification with C21's actual Sonin quotient map, and transport through
the full tensor remainder, are not assumed.

All 22 scratch theorems passed without warnings. The targeted module build,
complete theorem axiom audit (standard Lean foundations only), and formal
lint passed; the umbrella import is wired. The literal strict-tail
source is synthesized before evaluation and its whole Fourier--Laplace
integral is absolutely admitted. For every positive label, the tail
multiplier tends to zero but is eventually nonzero by the source's exact
successor transport. It retains every Xi divisor's first nonzero internal
jet. The actual Hilbert tail tends strongly to zero while its normalized
norm has an exact positive limit. Its representative and integral are
identified with the evaluated source, including the full `2*pi` coordinate
normalization and every series term. The unpromoted source is exactly the
original physical tail; C20's Gamma-six countertransported tail is its
known half-density multiple. [Complete proof and audit](../3-formalized/route-l-strict-tail-xi-jets.md).

Thus finite head removal does not destroy the usable conormal source.
The successor normalization recovers the next nonzero coefficient, but is
depth-dependent and cannot be substituted for the fixed physical reader.
This is a positive survivor, not a new annihilation or RH theorem.
Deep/method searches were partial; the applicable successor nonvanishing
was retrieved and inspected. The broad September observability paper
requires a concrete Laplacian, boundary region and resolvent estimate;
none is an arithmetic comparison premise here. Details are in the card.

### C23 proved: full tensor remainder after leading-image removal

The next test must reach the actual tensor remainder left by C21. C22 now
provides a common-source integral and norm bridge for its one-factor
inputs. On the diagonal spectral parameter, the predicted tensor remainder
multiplier is `M_6(m,w)^2-1`, not merely `M_6(m,w)-1`. It factors as the
strict-tail coefficient times `M_6(m,w)+1`. C22 proves eventual nonvanishing
of the first factor, while the existing limit `M_6->mu(6)=1` gives eventual
nonvanishing of the second. Hence the candidate multiplier is eventually
nonzero despite tending to zero. At the first nonzero internally promoted
jet in both factors, its source value should retain the square of the Xi
top coefficient.

The scalar argument does not establish the tensor statement. Required next
work is the exact product-measure representative, full integral admission
and Fubini identity for the literal leading--tail, tail--leading and
tail--tail remainder, with the countertransported half-density restored.
Only then can the surviving tensor data be tested against the actual Sonin
quotient map and fixed reader. These identifications remain open.

All 22 scratch theorems pass without warnings. The targeted module build,
complete theorem axiom audit (standard Lean foundations only), and formal
lint passed; the umbrella import is wired. The internally promoted
source specializes at order zero to the existing Gamma-six source, and
the tensor at `(0,0)` is its existing complete remainder. The actual
product-measure integral is absolutely admitted, including each of the
three cross contributions, and equals
`a_m^2*(M_6(m,w)*M_6(m,z)-1)*XiC^(k)(w)*XiC^(l)(z)`.
Both Fourier-coordinate factors and the forced half-density are retained.
On the diagonal the multiplier tends to zero but is eventually nonzero.
At each divisor of multiplicity `q`, the source orders `(q-1,q)` and
`(q,q)` therefore form a vertical pair with nonzero top entry. Restoring
half-density and exact successor scale in this same integral gives limit
`2*mu(successor(6))*[XiC^(q)]^2`, proved nonzero. Thus leading-image
removal does not erase the actual tensor remainder's conormal data.
[Tensor proof and audit](../3-formalized/route-l-tensor-remainder-xi-jets.md).
The fixed physical-reader comparison remains unconstructed.

### C24 proved: literal integral columns and exact prime-test classification

C23's actual source integral does not escape the prime obstruction when
the bounded-Hilbert-reader assumption is removed. The complete source
itself forces the required summable correction class. This is an exact
positive classification of the integral columns, not a proof of global
unboundedness or agreement with the physical reader.

For every positive ordinary label `p`, the exact spectral coefficient norm
and complete majorant give, whenever `m*Re(s(w))>=3/2` in the admitted
multiplier domain,
`norm(M_p-mu(p)) <= K_p*(p/(p+1))^(m*Re(s(w))-3/2)`,
where `K_p=sum_j (p/(p+j+1))^(3/2)` is finite. Thus strict-tail norms are
summable in depth for every fixed `Re(s(w))>0`. The two-variable complete
tensor correction `M_6(w)*M_6(z)-1` also has summable depth norms.

For the complete every-depth integral source, retain `|Im(w)|,|Im(z)|<1`
and `Re(s(w)),Re(s(z))>1/3`. These admit every honest depth `m>=3`,
including at every strict-right divisor. The exact shell cardinality
`5*6^m` cancels the tensor half-density `6^(-m)`. With the fixed flattening
profile, the actual column is `c/(n+216)` plus an absolutely summable
integral remainder, where `c=XiC^(k)(w)*XiC^(l)(z)`. Reindexing includes
the omitted finite head in the scalar correction. No unadmitted early
integral is used as a physical correction.

The resulting operator is admitted by every open Gibbs domain with
independent parameter `tau>1/2`. Its diagonal is summable iff `c=0`, and
its prime-pair tests are cyclic iff `c=0`; in that case every literal
integral column is zero. At each admissible divisor, multiplicity-top
orders give `c!=0` and failed prime tests. This does not exclude those
divisors, since the needed source-to-fixed-reader agreement remains open.
All 23 scratch theorems, targeted module build, complete axiom audit
(standard Lean foundations only), and formal lint passed; umbrella wired.
[Full integral proof and audit](../3-formalized/route-l-integral-column-law.md).

### C25 proved: full-source critical Abel reader and physical first variation

The actual complete integral operator from C24 has a critical Abel reader
obtained through admitted open Gibbs domains `tau=(1+epsilon)/2`, with
`epsilon>0`. The literal partition satisfies `epsilon*Z_epsilon->1`,
diverges, and has vanishing inverse. A full summable diagonal correction
has normalized reader norm at most `Z_epsilon^(-1)*sum |r_k|`; this bound
comes from the actual source class and vanishes at the endpoint.

Consequently the complete reader tends to `c`, and its compression and
projection by every fixed ordinary dilation `n` both tend to `c/n`. The
exact exchange multiplier remains `n^epsilon`. Thus their literal defect
`D_epsilon` tends to zero but `D_epsilon/epsilon` tends to
`log(n)*c/n`. At each admissible divisor, multiplicity-top orders have
nonzero `c`; for every fixed `n>1` the slope is nonzero and the actual
positive-parameter defect is eventually nonzero. No zero slope can be
substituted for this retained response.

There is a positive, derived physical comparison:
`[D_epsilon-c*B_n((1+epsilon)/2)]/epsilon -> 0`,
where `B_n` is the existing physical BV boundary reader. This first-order
agreement holds before divisor specialization for the full integral
source, including its complete arithmetic correction, and uses no reader
agreement premise. It extends beyond the already known principal
six-shell continuation. The regulator is independent of the spectral
parameters: this does not identify its endpoint with `tau=Re(rho)` or
retain an arbitrary divisor's actual horizontal displacement by itself.
Even critical top-jet sources have nonzero regulator slope, so forcing
that slope to vanish would be an invalid replacement condition.
The result uses the ordinary-integer operator produced by the literal
column map; transport into the Sonin carrier and intertwining of all
source arithmetic actions remain unconstructed.

All 39 scratch theorems passed without warnings. The targeted module
build, all 39 axiom audits (standard Lean foundations only), and formal
lint passed; umbrella wired and all owned Lean processes completed.
[Full Abel proof and audit](../3-formalized/route-l-critical-abel-reader.md).
The source-forced fixed-reader comparison required for RH remains open.

### C26 proved: second-order physical comparison and complete correction recovery

For the same full integral source `T=c*Q+R`, the admitted correction
obeys `A_epsilon(R)/epsilon -> sum_k r_k`. The proof uses Tannery with
the source-derived summable bound `|k^(-epsilon)*r_k|<=|r_k|` and the
proved partition residue `epsilon*Z_epsilon->1`. Projection preserves
summability. Exact principal physical agreement and weighted exchange
then give

`[D_epsilon(n,T)-c*B_n((1+epsilon)/2)]/epsilon^2
  -> log(n)*sum_(n divides k) r_k`.

These coefficients at all ordinary `n>1` vanish exactly when the complete
correction is supported at the unit. Together with the scalar first
variation `(A_epsilon(T)-c)/epsilon`, they determine every diagonal
correction coefficient, including the unit. This is full diagonal
recovery, not an off-diagonal operator reconstruction or a prime-only
classification.

For the actual every-depth integral source, full second-order agreement
holds exactly when `c=0`; the omitted coordinate two detects `-c/2`.
The obstruction also survives every finite diagonal repair: at coordinate
`n+216`, the correction is the literal complete integral remainder.
C23's eventually nonzero full tensor multiplier and the exact depth law
at `n=6^m` give nonzero coefficients above every finite bound whenever
`w=z` and `c!=0`. Every finite diagonal counterterm vanishes at some
such coordinate. Reconstruction then gives a nonzero second discrepancy
at some ordinary dilation. At every admitted divisor `Re(rho)>1/3`,
multiplicity-top orders discharge `c!=0` unconditionally. This concerns
finite diagonal support, not finite operator rank.

The positive survivor is the complete measured correction and its sharp
kernel, together with source-derived finite-repair robustness. A vanishing
second discrepancy cannot be imposed as an RH condition: critical
multiplicity-top sources have the same obstruction. Regulator and
original spectral parameter remain distinct. Sonin transport, all-prime
source-action intertwining, and fixed-reader agreement at the original
horizontal anchor remain open.

All 27 scratch theorems passed without warnings. The targeted module
build and all 27 theorem axiom audits passed using standard Lean
foundations only. The subsequent C29 global lint audit passed, clearing the
previous unrelated reachability failures and completing the formal gate. The Route L umbrella is wired, whitespace
checks passed, and every owned Lean process completed.
[Complete proof and audit record](../3-formalized/route-l-abel-second-comparison.md).

### C27 proved: fixed-six measurement of the complete source tail

The original coordinate projection `E_M` onto `a>=6^M` is applied
to the full integral correction `R=T-c*Q` before reading its boundary. For the
admitted chamber `|Im(w)|<1`, `Re(s(w))>1/3`, its actual second
boundary coefficient at the fixed dilation six is

`J_M=lim_(epsilon->0+) D_epsilon(6,E_M*R)/epsilon^2`.

Restoring `a=n+216`, every retained shell has exact correction
`r_a=c*C_m/a`, where `C_m=M_6(m,w)^2-1` includes all three tensor
remainder terms. The finite divisible shell has mass
`h_(m-1)=(1/6)*sum_(j=6^(m-1)..6^m-1) 1/j`, and
`h_m->log(6)/6`. Absolute summability justifies the full regrouping
`J_M=log(6)*c*sum_(j>=0) C_(M+j)*h_(M+j-1)`.

C23's actual successor normalizer satisfies `N_m=N_1^m` and
`N_m*C_m->2*mu(successor(6))`. With `q=N_1^(-1)`, `|q|<1`.
A convergent normalized source sequence is bounded; multiplying by
`q^j` supplies a summable majorant for all moving tails. Tannery proves

`N_M*J_M -> 2*mu(successor(6))*c*(log(6))^2/[6*(1-q)]`.

The constant is nonzero whenever the retained Xi-jet product `c` is
nonzero. Every sufficiently late cutoff therefore has nonzero second
response at the same dilation six. Every finite diagonal repair
vanishes after a sufficiently late source cutoff and has exactly the
same normalized limit. At admitted multiplicity-top sources the
existing Xi multiplicity theorem proves `c!=0`.

This controls cancellation in the complete complex tail. It does not
prove that the uncut fixed-six coefficient is nonzero, identify finite
diagonal support with finite rank, or interchange the regulator and
source-depth limits. The Abel limit is taken separately at each fixed
cutoff. Critical top sources retain this response too, so vanishing is
not an RH condition. The original-anchor Sonin/Burnol comparison and
all-prime source-action intertwining remain open.

All 29 theorems passed scratch checking without warnings, the targeted
module build, and the complete axiom audit using standard Lean
foundations only. The module is wired into `RHTower`; all owned Lean
processes completed. The subsequent C29 global lint audit passed, clearing the
previous unrelated reachability failures and completing the formal gate. [Complete source proof and audit record](../3-formalized/route-l-fixed-six-tail-reader.md).

### C28 closed: complete integrand admission at every original divisor

The every-depth chamber `Re(s)>1/3` is no longer needed for the complete
cutoff source. For every positive original `Re(s)`, a cofinal set of
literal depth cutoffs admits all retained integrands. The mask is
applied before integration and is exactly the original coordinate
projection once every retained depth satisfies its convergence law.

The proof controls the source before arithmetic cancellation. Its
strict-tail coefficient mass is summable in depth, and the physical
coordinate factor cancels its Jacobian. The complete tensor remainder's
integrated norm is bounded by the half-density squared times
`I_k(w)*I_l(z)*[t_m(w)+t_m(z)+t_m(w)*t_m(z)]`.
Exact shell multiplicity then makes the sum over all original columns
of these integrated norms finite. This justifies integrability of the
complete source sum and its sum--integral exchange, also after every
ordinary divisibility filter. The leading Green component remains
separate.

At every sufficiently late cutoff, the actual operator's diagonal is
the integral of this admitted source. At label six its second boundary
coefficient is `log(6)` times the complete filtered source integral.
The original normalizer therefore retains C27's nonzero limit at every
Xi divisor, with no reflection or relocation. The adjacent lower/top
internal jets give an exact zero/nonzero pair. Every finite diagonal
repair retains the top response; no finite-rank claim is made.

All 45 theorems passed scratch without warnings, the targeted module
build, and the complete axiom audit using only standard foundations.
The new module is wired into `RHTower`. The subsequent C29 global lint audit passed,
clearing the previous unrelated reachability failures and completing the
formal gate. [Complete paper proof,
source identities and audit](../3-formalized/route-l-complete-integrand-admission.md).

Fixed Sonin/Burnol agreement and source arithmetic-action intertwining
at the original anchor remain open. Reflection alone does not supply
them: the existing reflected-normalizer norm ratio equals one precisely
at critical placement, while the adaptive reflection-averaged source's
global codiagonal retains lower modulus `3/4`. Neither supplies the
missing annihilation law. Critical top sources retain C28's response too.

### C29 closed: actual regulator--depth crossover and retained conormal pair

The actual admitted operator has an exact regulated-source identity.
Multiplying the original masked integrand by its Gibbs weight preserves
C28's integrated-norm majorant; the complete source sum is integrable,
and its integral equals the actual projected Gibbs trace. Original
coordinate regrouping retains `n+216`, fixed dilation six, the Gibbs
partition, and the gain `6^epsilon-1`.

For every eventually positive `epsilon_M -> 0`, the normalized actual
defect divided by the explicit attenuation `6^(-M*epsilon_M)` tends to
C28's original constant `K`. Thus finite product limit `tau` gives
`6^(-tau)*K`, while infinite product gives zero. This diagnostic division
is explicitly separate from the fixed reader. At every original Xi
divisor the actual top defect nevertheless remains nonzero at every
sufficiently late depth along every such path. The adjacent lower/top
internal jets retain an exact zero/nonzero pair, including in the
infinite-product regime. Finite diagonal repairs disappear pointwise
from all regulated defects after sufficiently late original cutoffs.

All 25 theorems passed scratch, targeted module build and complete axiom
audit with standard foundations only. The module is wired into
`RHTower`; global lint also passed. C26--C29 are now in stage 3.
[Complete original-source proof and audit](../3-formalized/route-l-regulator-depth-crossover.md).

Regulator suppression therefore cannot itself supply source conormal
annihilation or fixed physical agreement. Critical top sources retain
the same pair. The remaining mathematical attack must derive the
source-to-fixed-Burnol/Deninger comparison at the original anchor,
including arithmetic-action agreement, while retaining this data.
