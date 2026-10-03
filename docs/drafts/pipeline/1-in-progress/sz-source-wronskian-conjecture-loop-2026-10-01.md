# SZ source Wronskian conjecture loop

- **ID:** SZ-SOURCE-WRONSKIAN-2026-10-01
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md`, route SZ.
- **Objective:** fully formalize an unconditional proof or falsification of RH.
- **Current result:** no proof or falsification of RH.

## Constraints and plan

No subagents, numerical experiments, new axioms, proof debt, heartbeat increases, full builds,
or commits. One foreground Lean process at a time. Audit finished leaves directly with
`lake env lean`; use `lake --old` for needed targeted dependency builds. Wire finished leaves
into the existing umbrella. Preserve concurrent changes.

1. Audit exact source statements and existing obstructions through corpus search.
2. State one falsifiable source conjecture; give a dependency-closed paper argument or locate
   its exact failure. Distinguish an RH receiver from a producer.
3. Formalize genuine proved advances, audit dependencies/axioms and lint, then repeat.

## Initial evidence and adversarial audit

- Frontier map SZ: missing moving infinite-head signed residual and weighted shell-leakage
  bound in a topology retaining cusp cancellation.
- `SuzukiCompletedFormationEnergy.lean`: eventual local production bound is an RH equivalence,
  not an established bound. Monotonicity alone does not supply it.
- `CCMSuzukiCrossApertureCurvatureLeakage.lean`: retained curvature equals the next coercive
  shift increment times preceding-shell physical leakage. It does not vanish by algebra alone.
- `suzuki-terminal-frontier-ledger.md`: one-angle entire characteristic walls are refuted;
  pole-compatible two-angle meromorphic limits remain live. Avoid another scalar receiver.
- `suzuki-coupled-error-boundary-energy-attack.md`: causal source continuation and boundary
  inverse differ by a contour-jump defect; equating their derivatives discards the open content.
- Initial hybrid search completed, inventory complete, source-only candidate applicability
  unchecked. Compiler metadata mostly pending/stale; a search hit is not a fresh Lean audit.

## Working log

- 2026-10-01: session initialized; core and Suzuki fixed-log-jet memories read. No
  `docs/architecture.md` or `docs/testing.md` found. Existing unrelated working-tree edits left
  alone. Serena symbol API rejects the Lean path as ignored; use exact source reads. No
  `update_plan` tool exposed, so track steps here.
- Next: inspect literal cross-aperture response, metric transport and projective Wronskian
  definitions; search their exact open source estimates before proposing a bound.

## Frontier-only checkpoint after user steering

The user requires every turn to name route SZ, its hard open problems, and whether previous
activities actually advanced them. New coordinate identities, renamed criteria and already-known
obstructions do not count as frontier progress.

- The proposed auxiliary energy identity was abandoned before any Lean-tree edits. It would
  expose a metric-shift term but supplies no estimate on it. Scratch API inspection completed
  successfully; this is not a new theorem or RH progress.
- Ground-state/Markov shortcut: corpus already refutes modulus contraction on actual arithmetic
  profiles, including every continuous local scalar potential (`CCMThetaModulusObstruction`).
  No new no-go claim and no new module warranted.
- Convex prime-event induction: `SuzukiCheckpointStrictConvexEventNoGo` already proves that
  convexity, positive reservoir and endpoint positivity do not determine checkpoint sign.
  A literal prime-level payment is still required; this lookup is not a new result.
- Binet/inclusion–exclusion proposal: endpoint Binet error is already uniformly
  `O(N^(-3/4))` on the half-log moving window (`SuzukiEndpointPrimeRegularCofinalBinet`).
  Exact Mobius/divisor duality and its critical unit-aperture weld are also already formalized
  (`CCMFUSuzukiMobiusDivisorRieszTailDuality`, `CCMFUSuzukiMobiusDivisorUnitRieszWeld`).
  Neither supplies a sign or boundedness theorem for the remaining signed source. Repackaging
  these identities is rejected.
- Broad deep searches returned partial results after semantic runtime deadlines, with no
  proposed ingredient sets. Inspect returned sources and use narrower queries; do not treat
  partial misses as absence proofs.

### Audited source-cyclic attempt: not an unconditional producer

The source-realization ledger SR-109 isolates low-source spectral mass of the normalized
cross operator: a high-assisted target forces mass above `1/113` of order at least
`r/log^2(1/r)`. The unresolved estimate is a smaller bound for the **literal source**, not for
arbitrary vectors. Test whether the exact rank-two displacement/Green identity of the sinc Gram
controls this source after whitening. Must audit the original source, moving cutoff, ridge
inverse, and any RH premise in the spectral representation before using this branch. No
source-specific estimate or unconditional RH implication has yet been proved here.

The premise audit failed for use as an RH producer: Sections 14.22–14.23 of the
coalescing-anchor card explicitly assume RH to identify the restricted-Weil form with
unweighted sampling on real zero ordinates. The low-source band estimate remains meaningful
for testing a proposed limit under RH, but that representation cannot supply an unconditional
proof of RH. No new no-go theorem is claimed.

### Signed source and Wronskian attempts

- The actual-head signed producer already has an exact convergent limit
  `(groundEnergy - 2*gammaHardyPhaseRate 0) * physicalGroundNorm^2`
  (`CCMActualHeadSignedCompletedErrorGammaProducer`, final theorem). Its scalar-shifted sign,
  rather than convergence, is still missing. Another convergence argument adds nothing.
- Retained-block orthogonality is in the aperture-dependent Riesz metric. It does not make
  physical shell leakage vanish. The existing three-aperture law retains precisely this term.
- The exact projective identity is
  `theta_b(z)-theta_a(z)=(z^2+1)*W_ab(z)/(E_b(z)*E_a(z))`.
  Splitting `W_ab` into shell and metric-response norms discards the required cancellation.
  The existing upper-half-plane nonvanishing theorem for each `E_a` supplies no uniform lower
  bound for the moving denominator. Thus this estimate does not establish a Cauchy law.
- The research tool suggested “coercive shift summability via bounded perturbations,” but its
  retrieved steps only combine the known metric-gap identity with orbit-shift norm estimates.
  No identification of those orbit vectors with the literal shell, and no cofinal summability
  bound, was supplied. Applicability is unverified; the suggestion is not a proof.
- Cusp residual convergence on fixed right-closed rays is already proved in
  `ThetaSieveBidirectionalCuspVariation`. Its escaping signed moments prohibit replacing the
  moving-source question by fixed-window convergence or an unsigned boundary envelope.

These activities have **not advanced the open SZ estimate**. No new Lean theorem was written.
No formal build or lint success is claimed for a nonexistent new result.

### Next precise source conjecture

The corpus's Euler-defect germ connector isolates a smaller sufficient target than full
characteristic convergence. Construct an analytic upper-half-plane limit `D_src` from the
literal finite Suzuki deficiency measures and prove, on one high-half-plane neighborhood,

`D_src(z) = z * (z * deriv m_ext z - m_ext z)`.

Here `m_ext` must be the actual affine-sewn Carleman sheet-jump quotient, with the physical
`-i` normalization retained. The existing pole-rigidity theorem would then imply RH. Compactness
of the finite defect measures alone does not establish this germ identity; finite Donoghue
quotients and the exterior quotient have different divisors. The next mathematical attempt
must derive the germ from the complete source Green identity and control its moving remainder,
rather than declare these quotients equal or introduce the equality as a premise.

Status: conjecture only; no germ identity, residual bound, RH proof, or RH falsification obtained.

## Continuation: Euler/Green and mixed-resolvent tests

Previous goal turn classified **no frontier progress**. This continuation tested the proposed
mechanisms against current source statements; it has not proved a new SZ estimate.

1. **Automatic Euler removal of the Green remainder — insufficient.** Write the actual
   denominator-matched Green law as `z^2 R(z)=H(z)`, where `H` is Robin current plus completed
   Weil exterior. Direct differentiation away from zero gives
   `J[R](z)=H'(z)-3H(z)/z`. Thus the remainder disappears only if `z H'=3H`; the Euler operator
   does not remove it by denominator cancellation. This is a paper calculation, not a newly
   audited Lean result. A far-hinge normalized channel has `H(z)=-exp(i*ell*z)`, which does not
   satisfy that differential equation. This refutes automatic channelwise elimination, not
   cancellation of the full completed source.
2. **Larger Binet window — already present and does not control the missing signed action.**
   `SuzukiEndpointPrimeRegularCofinalBinet` already proves the three-quarter-log window with
   `O(N^(-1/8))` error. The earlier log's half-log description was incomplete. Merely enlarging
   this archimedean-error estimate does not establish the Euler germ or bound weighted shell
   leakage. No duplicate window theorem was added.
3. **Positive shifted resolvents imply a positive affine remainder — rejected by existing
   source law.** The literal one-mode dressed remainder has factor
   `alpha*beta/[s*(s-alpha)*(s-beta)]`. For `alpha<beta<s<0`, this is negative, and
   `SuzukiCriticalWallFieldResolventDressingLaw` proves the exact positive von-Mangoldt weight
   preserves its negative sign. A full mixed Robin/Weil estimate must pay this contribution;
   positivity of each shifted inverse is insufficient. No claim that a negative actual
   restricted-Weil eigenvalue exists is made.

The current `SuzukiVolterraSourceGermWeldRigidity` leaf proves the analytic Euler-source germ
exists **iff RH**, for each admissible package. It also gives the exact normal form
`m_ext = localCorrection - xiMultiplier`. Hence the germ proposal is an existing RH receiver;
constructing it remains the unsolved mathematical step.

Formalization boundary checked: `SuzukiCausalWeilRobinGreenIdentity` explicitly formalizes
reconstruction algebra and delayed-hinge recovery; its analytic integrations and distributional
identification are paper results. Neither that leaf nor the source-germ receiver supplies a
moving-remainder estimate. This distinction prevents treating their composition as a proof.

The next necessary conjecture is the **literal mixed-source estimate**: assemble marked Robin,
near-entry, far-prime and polar–Gamma terms on the same two-resolvent states, before taking
absolute values, and prove a uniform lower bound for their rectangular Ward defect on one
fixed-width logarithmic mesh. The existing semiboundedness connector would then give RH.
No such bound or new argument for it was obtained in this continuation. Keep goal active; do
not relabel any of these audits as a new theorem or a solution.

## Continuation: telescoping and source-resolvent amplification

Previous goal turn: **no frontier progress**. No unconditional source inequality was proved in
this continuation either.

- Adjacent-aperture averaging does not supply a new estimate. The exact endpoint Volterra law
  is already in `CCMFUSuzukiTriangularEventChamber`: consecutive readings differ by the signed
  inverse-moment history times the reciprocal-log mesh gap. Summing telescopes exactly, but the
  surviving signed history remains unbounded by the argument. No duplicate telescoping lemma.
- Tested an unconditional macroscopic-shift/free-collapse argument using prime-number-theorem
  cancellation on the actual boundary source. The ledger SR-81 already distinguishes strong
  fixed-profile cancellation from operator-norm cancellation: the latter fails. SR-82 requires
  a macroscopic coercivity margin; source identification under RH gives that margin, but it
  cannot be imported into an unconditional producer.
- The precise analytic gap is inverse amplification. Small source mass near the shifted
  spectral edge can have a large resolvent contribution; fixed-profile convergence alone does
  not bound that inverse-weighted mass. No such bound for the actual source was found.
- Ordinary positive-energy moment estimates cannot be promoted to the required control:
  SR-88–SR-92 retain a compatible condensed low-energy packet despite their paired first-moment
  and ultraviolet information. Their RH-conditional zero-sampling representation cannot serve
  as an unconditional argument. Its failure of first-moment uniform integrability must not be
  confused with the different, still unproved reciprocal-gap estimate considered here.

Both deep corpus searches completed with partial semantic coverage, no proof ideas and no
ingredient sets. Their current sources supplied the obstructions above, not a proof-producing
estimate. Search files cleaned; no Lean files or umbrellas changed, no builds pending.

Remaining concrete test: use the actual derivative/translation commutator and its boundary
terms to estimate source coupling to the nearly singular shifted spectral subspace. Any estimate
must be obtained from the prime–Gamma form before using a real-zero sampling representation.
If it only assumes a uniform coercivity margin or replaces the boundary term by a norm bound,
it repeats the failed argument. The RH-bearing signed residual and leakage bounds remain open.

## Continuation: vertical frequency propagation and terminal support projection

Status: paper conjectures under audit; no new theorem or RH estimate yet.

The literal paired equation has frequency form
`-2z f' + [-I + iz(rI-B) - khat J] f = iz g + h`, with
`r(z)=psi(1+iz)+psi(1-iz)+2 EulerGamma`, `khat(z)=pi*z/sinh(pi*z)`.
Along `z=x+iy` its homogeneous generator is
`-r/2 + B/2 - i(I+khat J)/(2z)`. Thus a uniform bound
`Re r(x+iy) >= 2 log|x|-C` would give forward vertical decay
`||U_x(y,t)|| <= C_B |x|^{-(y-t)}`. For a bounded physical profile supported
on the right, its transform on `Im z=-1/4` is uniformly bounded; propagation to
`Im z=3/4` would make this homogeneous contribution square integrable. The source
Duhamel term would also be square integrable if the actual primitive sources have
the asserted uniform weighted L2 bounds. This avoids estimating the nonnormal
group along the real-frequency axis. Gamma bounds, source bounds, zero-frequency
charges and identification with the physical transform remain to be proved.

An apparent obstruction to the source premise must be resolved first. The literal
source-assembly paper places `[Z,M]F` into its forcing, where `Z=I-KJ`. At an actual
root, the terminal cutoff keeps the inward orientation and kills the outward one;
it therefore does not commute with J even when no cutoff event remains. For
`P=diag(1,0)` and `F=(f,0)`, `[Z,P]F=(0,-Kf)`. Kernel decay in the translation lag
does not imply exponential decay of this persistent term in L for a bounded f.
This challenges the paper's estimate from boundedness and finite recurrence alone;
it is not yet a counterexample built from an actual completed eigenmode.

Possible repair: retain the terminal support projector P in the principal operator,
using `PBP` and `PJP` on `PX`. Root channels then have `PJP=0`, while paired interior
channels retain its +/-1 eigenvalues. The regular-singular exponents become
`-1/2` at roots, alongside `-1` and `0` in the paired interior. These root charges
must be controlled explicitly, not put into an exponentially decaying event error.
Only `M-P` and its genuine transitions may be eligible for recurrence estimates.
Need audit exact source equation and novelty before accepting this repair or
formalizing a result. Even a valid trace-zero admission theorem would leave the
RH-bearing nonzero-source residual/leakage problem; it is not an RH proof.

### Audit outcome and return to SZ's actual estimate

The root-cutoff issue is grounded in the exact proofs
`rootOutward_cutoff_eq_zero` and `rootInward_cutoff_eq_one` in
`SuzukiPairedCutoffEventGeometry.lean`. `SuzukiLogisticCoupling.lean` proves the
logistic kernel has mass one and a weighted operator bound; that bound transfers
weighted L2 membership of its input, not membership from mere boundedness. The
source-assembly paper's listed Lean certificates cover the uniform carrier bound,
event geometry, lattice summability, density, and algebra separately. Their list
does not supply a theorem estimating the persistent off-diagonal commutator.
No claim is made that the complete physical forcing cannot cancel it.

This investigation did **not** establish SZ's signed residual or leakage bound.
The paired-source admission branch belongs to a different intermediate domain
problem, so no new Lean leaf or generic projection algebra was added. The vertical
propagation proposal is parked, with its source premise unresolved.

A subsequent test of automatic leakage control from retained-block orthogonality
also gives no new argument. The proposed metric correction is not confined to the
retained block. Writing the exact split as `u_b=x+k+S`, orthogonality to the retained
vector x does not give orthogonality to x+k. The surviving pairing with k is exactly
the physical leakage multiplied by the shift gap. This is the same obstruction as
the earlier auxiliary-energy attempt, not an advance, and must not be repeated.

Deep searches for the terminal projection, actual signed bound, and shell-resolvent
cancellation returned no verified producer of the needed estimate. The terminal
query completed; the signed-bound query had partial coverage. Proposed search
ingredient sets are unverified and do not settle applicability.

Outcome: **no frontier advance** in this continuation; RH goal remains active.
No Lean sources, umbrellas, or other agents' files changed; no build was warranted.
Next attempt must work directly with the complete signed moving prime--polar--Gamma
source, before quadratic matched-head damping or norm splitting. A quantitative
estimate for that literal source is required; another reformulation, compactness
argument, metric identity, or domain detour is not progress.

## Continuation: literal Abel source and Selberg cancellation test

Previous turn: **no progress**. This turn pursued the signed source directly; no new
bound was obtained and no Lean theorem was added.

The current exact source is
`A(M)=sum_{1<=k<M} (sqrt(k+1)-sqrt(k))*(psi(k)-k)`.
`SuzukiTransitionCoreAbelSourceMultiGateWeld` retains its polar-lattice, polar,
and archimedean corrections. `SuzukiTransitionCoreCheckpointCurvatureWeld` and
`SuzukiCheckpointChebyshevMassErrorWeld` identify the same scalar in literal
prime--polar--Gamma and Chebyshev high-pass coordinates. These identities do not
estimate it. `CCMFUSuzukiSelbergOutgoingAbelWeld` proves `A(M)/M` uniformly bounded
iff RH. The Möbius-completed version differs by the exact Euler edge; even bounds
with every positive power loss are already an RH-equivalent target in
`CCMFUSuzukiMobiusDivisorAbelSubpower`.

**Conjecture tested:** retain the signed Selberg recurrence to improve the source
bound beyond PNT magnitude control. The available coarse inequalities cannot do
this: `PMSelbergPowerInputBoundary.pmPowerModel_selberg_input_counterexample`
exhibits a comparison remainder of exponent 3/4 satisfying both coarse Selberg
inequalities, with the actual von Mangoldt floor operator and unchanged constants,
while its canonical variance diverges. This is not a counterexample to the actual
Chebyshev remainder or RH.

The exact identity before that loss is `tatuzawa_iseki`. Applied to the completed
Chebyshev defect F, it equates
`F(N)*log N + sum Lambda(k)*F(floor(N/k))`
with `sum mu(n)*(log N-log n)*D(floor(N/n))`, where D is the literal logarithmic
factorial minus divisor sum plus Euler correction. `SelbergSymmetryCore` obtains
its O(N) error precisely by replacing this signed sum by absolute values and using
`|D(j)| <= 24 sqrt(j)`. Thus merely applying that inequality inside the Abel
readout repeats a certified insufficient input class. The exact identity is valid
for every input F, so its algebra alone adds no arithmetic estimate.

Also checked the genuinely unconditional completed Riesz graph results:
`CCMFUSuzukiCompletedRieszGraphEnergy` supplies square-summable graph increments,
summable harmonic charges with total zero, and an exact moving-boundary Abel law.
The law retains the harmonic prefix multiplied by the accelerating square-root
clock and its signed clock-acceleration history. Total charge zero does not bound
these terms. No rate against that clock was proved here. Neither generic graph
energy nor a new integration-by-parts identity should be formalized as a solution.

Three deep corpus searches completed with partial semantic coverage. Their
candidate lemmas and source arguments were inspected; no proof idea or ingredient
set supplied the missing bound. Exhaustive source-name references for the three
Abel boundedness predicates found only criteria and premise-consuming transfers,
including observer-jet linear action and the coupled-floor moving schedule. The
schedule's approximation error is proved, but boundedness along it remains open.

Next substantive conjecture must estimate the **joint signed Möbius--divisor
correlation** in the exact finite producer, retaining its terminal dilation band.
The divisor envelope alone, coarse Selberg inequalities, harmonic total charge,
and separate prime/Gamma estimates are excluded as sufficient inputs. No claim
that this narrowing advances the mathematical frontier: this continuation remains
**no frontier progress**, with the full unconditional SZ/RH goal active.

## Continuation: joint channel correlation and growing-core test

Previous turn: **no progress**. No new source inequality or formal theorem was
obtained in this continuation.

The literal joint pairing is now pinned to
`increment_rieszTail_eq_completedPrimePolarGamma_window`: the complete sum of
`(log n-tau(n)+2 gamma)` against the signed Möbius Riesz tail is exactly the
completed prime--polar--Gamma window. Its terminal band is inside that tail.
No separate bound on either factor is an estimate of the joint cancellation.

The existing diagonal-dominance branch supplies more source information than
the previous turn used. The full channel diagonal satisfies `Q(M)<=722 M^2`;
unsigned channels are nonnegative. However neither decreasing time weights,
separate gcd signs, adaptive stepwise contraction, nor a positive inclusive gcd
completion supplies the signed off-diagonal bound. The inclusive gcd completion
is already proved superquadratic. No duplicate theorem was proposed.

**Frontier correction:** the newer bounded-quotient card closes the global raw
unsigned envelope `K_d(M)<=a sqrt(M)`, with `a<9/50`, and the unit coefficient
has exact limit `c=log(2*pi)/2-gamma-1/4>9/100`. Thus eventual unit factor-two
comparison has no remaining middle-quotient gap. The older source-diagonal card
still describes that gap; do not use it as the current open target. Finite unit
cutoffs and arbitrary processed signed states remain separate. Improving a raw
unsigned envelope is not the missing growing-core estimate.

**Shape test:** a positive mixture of decaying powers would control a complete
Möbius product in a much simpler class, but the literal finite-cutoff channel
has a nonzero compactly supported dilation profile. It cannot equal such a
nontrivial positive mixture on the whole positive dilation axis: each positive
power kernel is strictly positive beyond the cutoff. This rejects that proposed
representation, not the literal off-diagonal conjecture. No generic shape lemma
was added to Lean, and no numerical evidence was used.

The exact finite-clock transport is in `MobiusDivisorCriticalClockProductTransport`.
Inserting p gives the causal shift with gain `1/sqrt(p)` and retains two different
finite endpoints. The squarefree-density factor absorbs the copied diagonal,
leaving the signed mixed correlation and a negative boundary surplus. It does
not bound the correlation through an exhaustive growing core.

The current-clock payment stack was checked for a possible composition:

- Actual shallow prime batches supply a positive quadratic payment, with the
  complete logarithmic cofactor weight and prefix control.
- Paid cutoff transport covers an original fourth-root interval.
- The growing-depth producer pays a prescribed q when
  `A*(1+log M)<=q` and `16*q<=M`, from its literal fixed seed.
- This does not process a fixed omitted prime at all later clocks: it eventually
  falls below the moving threshold. The seed and shallow helpers omit 2.
- The growing-core amplitude estimate has factor `2^(card P)`; it cannot be
  replaced by a uniform constant. Nested extensions and fresh future pools are
  not consequences of independent choices at each cutoff. Existing shallow
  payment does not cover inherited debts of order `M^2 log M`.

Hence iterating these producers as if their admission, freshness and constants
were preserved would be circular. No exhaustive schedule or subpower action bound
was constructed. Next test must retain the signed mixed term for a **fixed omitted
prime in an evolving core**, or prove a collective estimate for the complete
finite-clock correlations. Uniform fixed-core limits and positive diagonal
completion are insufficient. Searches completed with partial semantic coverage;
no returned proposal discharged this obligation. Full SZ/RH goal remains active.

## Continuation: prescribed-prime debt and finite-clock truncation

The proposed universally quadratic fixed-prime insertion cost is already excluded
by `exists_mobiusDivisorUniformMovingHelperDebt`: actual even cores admit a
prescribed prime whose positive debt remains of order `M^2*(1+log M)` under
every sufficiently late helper set with small reciprocal-prime mass. The exact
negative copied square does not remove this obstruction. No duplicate no-go
was added.

The local quantitative payment is already at
`min(delta,delta^2/K)/(128*r*p)`. Its ratio aperture, helper threshold and
finite-counting onset depend on the evolving core. Iteration alone supplies
no divergent reciprocal-helper sum. The uniform positive source-moment gap is
also already proved; proving it again would not advance the frontier.

New candidate: for the literal complete finite energy Q and offset clock W,

`(1+log M-card(P)*log 4)*Q_P(M) <= W_P(M)+4*M^2`.

Paper proof: write `v_r=r*F_P(M,r)^2`, so Q is the complete sum of v_r and
`(1+log M)*Q-W=sum log(M/r)*v_r`. Existing source amplitude gives
`0<=v_r<=4^card(P)*M`. Put B=4^card(P), X=M/B, N=floor(X).
For r>N, `log(M/r)<=log B`. For r<=N retain log B times the actual v_r
and bound only the excess by B*M*log(X/r). The elementary logarithm/square-root
bound and the proved reciprocal-square-root sum give
`sum_(r<=N) log(X/r)<=4*sqrt(X)*sqrt(N)<=4*X`.
Thus the excess is at most 4*M^2. M=0 is immediate. All cofactors remain in
the identity; no signs, asymptotic density, or prime-sampling premise is added.

Novelty audit so far: exact source references expose only the old
`4*((3/5)*2^(card(P)-1))^2*M^2` clock-defect bound. Deep search is partial;
candidate applicability must still be checked. This estimate removes one
exponential dependence in the finite clock conversion. It does not prove the
signed insertion bound or cumulative repayment. Lean verification pending.

### Verified result and remaining obligation

`MobiusDivisorClockCardinalityBound.lean` now proves the candidate as
`mobiusDivisorFiniteClockEnergy_cardinality_bound`, universally over
`Finset Nat.Primes` and every natural cutoff. There is no energy, sign,
density-limit or payment premise. The module is wired into `RHTower.lean`.

Final leaf audit passed without diagnostics:

`lake --old env lean GaloisForLFunctions/RHTower/MobiusDivisorClockCardinalityBound.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/MobiusDivisorClockCardinalityBound.olean`

A separate `/tmp` import audit printed exactly
`[propext, Classical.choice, Quot.sound]`. No custom axiom, computational
certificate, heartbeat override or full umbrella build was used. One premature
second Lean process was stopped immediately; all completed audits were sequential.

`scripts/formal_tools.py index` refreshed the three generated Lean maps and
reported one changed indexed source. Final `scripts/formal_tools.py lint` still
exits 1 for eleven unrelated unreachable leaves; the new module is reachable
and absent from those errors. Those other leaves were not edited or wired
without verification. Temporary research results and audit files were removed.

**Contribution:** finite-counting clock conversion now has the unconditional
error bound `card(P)*log(4)*Q_P(M)+4*M^2`, rather than only an exponential
core-amplitude constant times M^2. In the range
`card(P)*log(4)<=(1+log M)/2`, quadratic clock control implies
`Q_P(M)<=2*(W_P(M)+4*M^2)/(1+log M)`.

**Still open:** the actual moving signed residual, weighted physical shell
leakage, and a paid exhaustive history with the needed finite-cutoff controls.
The new comparison does not supply their cancellation. Next substantive
conjecture: a source-derived three-delay feedback estimate at the literal
finite counting cutoff, retaining its endpoint losses, strong enough for
changing-core prescribed-prime repayment. Do not replace this with another
fixed-core eventual limit or another absolute-value amplitude improvement.
The unconditional SZ/RH goal remains active and unachieved.

## Continuation: finite three-delay feedback test

Previous turn classification: **progress**. The new finite-clock cardinality
bound was Lean-audited and wired. It does not solve moving signed cancellation
or weighted physical shell leakage. This continuation has not obtained a new
source bound or formal theorem.

The frontier map still states the same SZ obligation. Corpus searches for
finite three-delay feedback returned the full-ray three-shift Gram theorem,
the exact finite critical-clock transport, the cutoff-growth estimates and
the existing fixed-core limiting payment theorem. Semantic coverage was
partial; exact source searches found no finite source feedback producer.
The projected shifted-Xi leakage norm bound is a different operator, and the
ground-leakage vanishing result consumes an odd-budget hypothesis. Neither
discharges the literal moving-source estimate.

The finite feedback calculation must keep three distinct endpoints. Write
`a=log p`, `alpha=1/sqrt p`, `rho'=rho/(1+alpha^2)`, and let
`f_j(t)=h_P(t-j*a)` on `t<=T`. Put `K_j=<f_j,f_j>` and
`z_ij=<f_i,f_j>`. Prime insertion is the proved causal law
`h_(P+p)=h_P-alpha*h_P(.-a)`. Consequently its finite density-energy debt
and its same-cutoff self-correlation feedback are

`delta = rho'*(-2*alpha*z_01-alpha^2*(K_0-K_1))`,

`D = rho'*(alpha*(K_1+z_02)+alpha^2*(z_01-z_12))`.

Unlike the full-ray proof, one cannot set all K_j equal or identify z_01
with z_12. The exact boundary-corrected square is

`D + rho'*alpha/2*(K_0+K_2-2*K_1)
   - rho'*alpha^2*(z_01-z_12)
 = rho'*alpha/2*||f_0+f_2||^2`.

Thus a positive square alone leaves a second difference of endpoint energies
and a signed last-slab correlation. This is the unresolved source boundary
estimate, not a bound supplied by the Gram matrix.

A symbolic generic test rules out the proposed Gram-only positive-debt
implication. Take a causal head equal to B on `(0,a)`, equal to
`-3*B/(2*alpha)` on `(a,2*a)`, and zero elsewhere, with `a,alpha,B>0`
and cutoff `T=2*a`. Direct integration gives
`delta=(3/4)*rho'*a*B^2>0` but
`D=-(1/2)*rho'*alpha*a*B^2<0`.
This is a paper-level countermodel for general causal heads, not a numerical
experiment, not an arithmetic-source counterexample, and not a Lean no-go
for SZ. The actual-source feedback conjecture remains open. No route is
retired and no new generic receiver is added.

Next substantive test must bound the displayed boundary combination using
the literal prime--divisor source and its finite cofactor counting measure.
Moving to the physical full-ray integral or dropping endpoint differences
would merely assume the missing step. The direct finite counting insertion
identity still retains its negative `p*log p` copied square; its signed mixed
term must be treated jointly with an admissible growing core. No new bound
for that joint term was obtained here. RH remains unresolved and the goal
remains active.

## Continuation: finite counting and preparation-cost audit

The preceding turn ruled out a Gram-only shortcut on paper but did not bound
the actual source. This continuation likewise obtained no new source estimate
or Lean theorem. The exact finite counting insertion law was retained, rather
than replaced by its full-ray density limit.

A stronger existing producer than the previously emphasized local pair theorem
was found and inspected: `exists_mobiusDivisorBudgetedInheritedPrimeInsertionProducer`.
For any inherited nonempty finite prime core and prescribed omitted prime,
actual helpers beyond any chosen bound can make that prescribed insertion
release energy. One budget controls all preparation subsets at all cutoffs.
But this budget is chosen after the core and prescribed prime: its proof uses
`K=(9/25)*exp(4*(sum_(p in P) 1/sqrt(p)+W+1/sqrt(r)))`.
This is not a uniform budget through an exhaustive growing core.

The same source file explicitly proves the distinction in
`exists_mobiusDivisorClockDelayedInsertionProducer`: the marginal insertion
can release energy after preparation while the prepared final state still
has a fixed positive net debt relative to the original core. Complete delayed
repayment requires positive reciprocal-prime mass. A distant bounded
inverse-square-root-mass preparation has reciprocal mass at most W/sqrt(B),
so sending the helpers farther out cannot turn this construction into net
payment. This is an existing arithmetic obstruction, not a newly proved no-go.

The natural logarithmic-diagonal bookkeeping was also checked. Summing its
individual prime-log copied squares is not a lower bound on actual payment:
each copied square contains signed off-diagonal source pairs. Their accumulated
covariance remains in the exact history balance. The source record
`rh-exhaustive-clock-continuation-facts.md`, particularly its finite-cutoff
diagonal-payment and finite-batch sections, already records this failure.
No duplicate carrier or generic averaging identity was added.

That record also closes off two tempting substitutions: whole-child fractional
payment has not been constructed, so Boolean rounding cannot be invoked as its
producer; the original-core all-order Boolean signs do not give the same signs
after arbitrary core changes. Its fixed-field source-cone results are not
uniform in growing field dimension. These are quantifier and source-covariance
gaps, not missing rearrangements of finite sums.

Both deep searches completed with partial coverage and no returned proof idea
or ingredient set supplying the missing bound. Exact source statements and
the preparation-budget proof were inspected. No Lean process or numerical
computation was started; owned search outputs were removed. The next meaningful
conjecture must control the full evolving inter-batch signed covariance and
old-wall completed action together. Repeating isolated favorable insertions,
diagonal bookkeeping, or bounded endpoint constructions would not address it.
The unconditional SZ/RH objective remains active and unachieved.

## Continuation: direct aperture energy and canonical-shift audit

Route SZ; no new hard source estimate or Lean theorem was obtained. The prior
preparation-cost audit had made no mathematical frontier progress, so this
continuation returned to the literal cross-aperture Wronskian rather than
repeating favorable finite prime insertions.

The attempted estimate was to control physical shell leakage through the
aperture-dependent coercive energy. Source inspection confirms why the direct
argument does not close: the shell is orthogonal to retained vectors in the
Riesz metric, whereas curvature pairs their physical embeddings. The metric
shift correction remains in that pairing. Coercivity of
`1 + J* B J + (norm B + 1) J*J` supplies no inverse bound of order
`1/(norm B + 1)` without additional information on the unshifted form.
No such information was proved here.

The actual remainder envelope in
`CCMRestrictedWeilGroundFrequencyLocalization` is
`abs(2*gammaHardyPhaseRate 0 - 1) + 4*a*exp(a) + 42*exp(a)`.
It does not give a summable cofinal leakage budget. The canonical completed
head error theorem bounds excess over the true ground-energy contribution;
it does not prove that contribution nonnegative. Local right-aperture energy
continuity and subsequential Schur compactness also do not identify the limit.

A narrower canonical-shift test exposed a prior-paper obstruction that must
not be mistaken for a new formal result. The moved paper card is now
`3-formalized/new_scientific_knowledge/suzuki/suzuki-coalescing-anchor-parity-locking-reduction.md`.
Its Section 14.22, Theorem AE, argues under RH that every shift
`lambda = -r` with `r >= r0 > 0` gives asymptotically equal normalized even
and odd source responses, hence defect angle tending to zero. A complete
Xi-identifying family would instead require the angle to tend to the exact
Xi value in `(77/85, 1)`. Thus the paper's necessary condition for such a
family is `max(0,-lambda) -> 0`. The actual canonical metric uses
`lambda = -(norm B + 1) <= -1`, so it cannot meet that necessary condition
if the paper's complete source identifications are established.

The certificate's wording is narrower than a literal-source Lean closure:
it certifies the mathematical cores. Inspection of
`SuzukiExpandingFrameAnnihilation.lean` finds the scalar spectral split,
two-block variational inequality, tail convergence and an abstract sequence
criterion. It does not prove the actual sampling-operator realization,
its two-block Gram estimate or the actual source-resolvent limit (301).
Therefore this continuation does NOT claim a Lean-certified canonical-shift
no-go, retire SZ, or infer RH from the RH-side zero representation. Even a
fully established canonical-shift obstruction would leave the singular
vanishing-shift/source-selection regime; the paper already records that
positive survivor. Another generic no-go wrapper would add no frontier value.

Three deep searches completed with partial semantic coverage. Their returned
source arguments were checked, and their proposed shift-selection ingredient
still assumes the free and ground endpoint limits. No result supplies the
missing actual-source estimate. No Lean build or numerical experiment ran.
Owned search outputs were removed after this audit.

Next mathematical target remains the jointly signed prime--polar--Gamma
remainder, with the physical leakage and metric response kept together.
Any proposal to infer convergence of inverses from fixed-profile PNT
cancellation must also control the literal source's near-zero spectral mass;
otherwise the inverse can amplify exactly the uncontrolled part. Neither
separate positive energy bounds nor the default canonical shift discharge
that requirement. RH remains unresolved; goal remains active.

## Continuation: source-domain, coherent-phase and signed-dilation tests

Previous turn and this turn: no mathematical frontier advance. Route SZ's
moving signed residual, weighted physical shell leakage and Xi identification
remain open. No Lean module was added and no build or computation ran.

1. Tested whether regularity of the literal exponential source could supply
   the missing inverse-response estimate. `CCMRestrictedWeilPolarOperatorDomain`
   does place every truncated real exponential in the actual operator domain.
   `CCMRestrictedWeilPolarSourceCancellation` gives its exact action with
   logarithmic boundary, Chebyshev error and reciprocal-Mangoldt error retained.
   These facts do not bound the source component amplified near the small
   spectral denominator. No source-specific spectral-tail estimate was derived.
2. Tested support-preserving coherent-field control on the same actual forms.
   `CCMActualHeadCoherentQuantileGammaNoGo` already proves
   `2*gammaHardyPhaseRate 0 + 4 < 0`. Support projection saves a nonnegative
   part of the coherent cost, but the remaining cost is still nonnegative.
   It cannot be paid from that negative scalar. The exact phase-square law
   subtracts both higher-Gamma energy and coherent energy; positivity of the
   square alone is insufficient. Its sign equivalence is already formalized,
   so adding another wrapper would not advance SZ. The open bound must keep
   the translation-increment/coherent-field cross phase.
3. Returned to the literal signed Mobius--divisor action and tested whether
   divisor oscillation plus its entire Mellin continuation controls all
   dilation responses jointly. The inspected entire-source identity is
   `D(s) = -zeta'(s) - zeta(s)^2 + 2*gamma*zeta(s)` away from the filled pole.
   It is a continuation of the original source, not an estimate of its full
   Mobius-weighted moving sum. `MobiusDivisorDilationMeanUniformRenewal` is
   uniform in the inserted prime and next dilation with the original core
   fixed; its constant depends on that core's contour boundary. It cannot
   be promoted to a growing-core bound. No oscillatory cancellation estimate
   for the complete finite signed sum was obtained.

All three direct deep searches completed with partial results; the signed-current
search explicitly reported pending coverage. None returned a verified ingredient set closing these
bounds. The source statements above were read directly. Search misses are
not absence proofs. Owned search JSON files were removed.

Next attempt must estimate the joint signed dilation sum at the physical
cutoff, including completion of the old cutoff and all inter-batch terms.
Replacing it by a fixed-core contour limit, an unsigned divisor envelope,
or a nonnegative coherent cost has now been explicitly checked and supplies
no such estimate. The unconditional RH objective remains active and unmet.

## Continuation: arity damping and finite counting correlations

Route SZ; no new mathematical frontier result in this continuation. The
moving signed residual, weighted physical leakage, and source-to-Xi
identification remain open. No Lean module or computation was added.

1. Proposed damping the literal coefficients by `u^omega(n)` and recovering
   the complete endpoint at `u=1`. The corpus already disproves the needed
   linear mean bound at `u=1/2`: see
   `MobiusHalfSelectionPoleObstruction` and
   `MobiusHalfSelectionGrowthObstruction`. The squared continued transform
   would have a simple zero at the filled zeta pole, whereas an analytic
   square has even vanishing order. The nonzero literal divisor-source
   value at one makes the obstruction effective. The stronger proposal
   for every `0<u<1` was not formalized: it would not repair this approach.
   `FullPrimeCofactorBoundary.fullPrimeDampedSeries_bounds` does retain
   the fractional boundary scale, but supplies no endpoint estimate.
2. Returned to the exact finite counting measure. With affine offset one,
   the existing source law is
   `W(P+p)-W(P)+2*sqrt(p)*C(P,p) = -p*log(p)*D(P,p)`, where `D>=0`
   and `C` is the actual weighted product of the two signed heads. The
   negative copied-square term does not imply `W(P+p)<=W(P)` without
   controlling `C`. At one cofactor, writing the two scaled values as
   `a,b` and the positive weights as `w,w+log(p)`, the elementary
   quadratic comparison has factor `1+w/(w+log(p))`, not contraction.
   This algebra is only a diagnostic, not a newly audited Lean theorem.
   It does not control accumulated mixed terms at the complete cutoff.
3. The deep search proposed making a clock pairing zero by symmetry.
   Rejected that suggestion: the literal diagonal pairing is strictly
   positive (`mobiusDivisorDilationMean_one_pos`), and the finite-clock
   identity retains the mixed correlation explicitly. A search-generated
   ingredient set is not a proof.
4. Tested whether a core-uniform estimate
   `|D_P(Y)| <= C*sqrt(Y)*D_P(1)` could provide the missing saving.
   Neither a proof nor a source counterexample for this relative bound
   was obtained. Do not label it refuted by the different absolute bound
   in `MobiusDivisorDilationMeanUniformCoreNoGo`. The source-specific
   `MobiusDivisorPrimeBlockEnergyEscape` shows that arbitrary terminal
   prime-window cores have total physical energy escaping every
   polynomial cutoff, even with density weighting. Consequently the
   available full-ray profile estimates cannot be used as uniform
   finite-cutoff majorants. The proposed clustered-prime mechanism also
   overlaps the existing inherited-prime producer; copying it would not
   supply the missing cumulative payment.

Five direct deep searches finished with partial results. The first reported
complete file inventory but mostly pending/stale compiler metadata; the
others timed out in query/reranking stages. Relevant source statements were
read directly. No absence claim or fresh Lean audit is inferred from these
searches. All five owned search outputs were removed after inspection.

The next estimate must stay at the literal finite cutoff: combine the
signed mixed correlations and copied-square payments before taking their
size, and account for the omitted old-cutoff portion when changing cores.
An estimate over arbitrary infinite-core profiles is stronger than needed
and currently unsupported. No unconditional RH proof or falsification has
been obtained; goal remains active.

## Current conjecture: exact simple Mellin jet of the finite prime source

The previous continuation made no frontier advance. Whole-block source
inspection still does not provide a cumulative signed-correlation bound.
The current narrower mathematical question is whether the already-known
nonzero finite-order Mellin jet actually has order one with an explicit
positive coefficient. This concerns the literal source term that any
finite-cutoff block cancellation must remove, not a substitute RH criterion.

Paper argument: let `B=divisorSourceEntire` and `Z=zetaPoleUnit`. On
`Re(s)>1`, the critical step Mellin transform is
`(s-1)*B(s)/(s*Z(s))`. Both B and Z are entire, `Z(1)=1`, and
`B(1)=divisorHarmonicBoundary>=1/30`. Thus division by `s-1` has limit
`B(1)>0`. The exact twice-Abel weld divides this coefficient by three.
The actual all-prime head Mellin factorization then gives leading term
`(B(1)/3)*delta*log(1/delta)`, with coefficient at least `1/90`.
The existing source files only assert existence of some nonzero finite
order. Searches were partial; exhaustive symbol references were inspected.
The leaf `MobiusDivisorCriticalSourceSimpleJet` passed direct Lean checking
and is wired into the umbrella. Axiom inspection remains pending. This
does not yet bound the remaining prime-block or Wronskian residual.

### Transfer conjecture: a forced negative physical prime head

Let `F(x)=criticalPrimeAbelHead(x)`, the exact finite sum of
`sqrt(p)*criticalContinuousAbel(x/p)`. The candidate full asymptotic is
`F(x) ~ -(B(1)/3)*x^(3/2)/log(x)^2`. A direct proof would require
logarithmic source moments and a two-range strong-PNT convolution estimate;
the Mellin jet alone does not justify that asymptotic.

A sharper argument for the needed sign obstruction is available without
claiming that asymptotic. Suppose globally `F(x)>=-C*x` for `x>1`.
The Mellin transform of `F+C*x` on that ray is nonincreasing as its real
decay exponent increases. At the boundary its limit is `2*C`, since the
actual source transform tends to zero. Consequently the source transform
at boundary distance `delta` is at most `4*C*delta`. But the audited jet
forces its quotient by `delta` to tend to positive infinity. Contradiction.
This derives a signed physical excursion from the literal source, not a
Tauberian converse. Next strengthen global escape to cofinal escape using
local boundedness, and identify which higher prime-interaction terms must
cancel this excursion in the complete SZ residual. No RH conclusion follows
from the prime head alone.

The transfer is now formalized in `MobiusDivisorCriticalPrimeNegativeEscape`:
`criticalPrimeAbelHead_cofinal_negative_linear_escape (C X : Real)` has no
arithmetic premises and yields an actual finite-source cutoff `x>X`, `x>1`,
with `re(F(x)) < -C*x`. Direct `lake --old env lean <leaf> -o <olean>` exited
zero. The proof also constructs local boundedness from exact square-root
interpolation, so the excursions cannot be confined to a bounded interval.
This is a new signed physical statement, stronger than the earlier
unspecified Mellin nonzero jet. It still concerns the all-prime head, not
the complete SZ residual. Axiom and lint audits follow.

### Next physical-cutoff weld, retaining the old portion

For the moving square-root core the omitted-prime source is the full prime
head minus `G(x)=sum_{p<=sqrt(x)} sqrt(p)*A(x/p)`, plus the complete source
`A(x)`. Thus the all-prime result cannot be silently used for this core.
Its missing old portion has Mellin transform
`sum_p p^(-1-delta) integral_{y>=p} A(y)y^(-5/2-delta)dy`.
Proposed exact transfer: prove this expression has a finite right derivative
at zero. Its derivative is dominated by
`2*integral_1^infty |A(y)|y^(-5/2)*log(y)*(1+log(y))dy`, using the finite
harmonic bound on primes below y. Strong PNT should make this finite.
This would retain the positive `delta*log(1/delta)` coefficient in the
moving square-root head after subtracting its finite boundary value. The
same monotonicity argument would then force signed excursions of that
literal head, including the old-cutoff correction.

The required moment construction is concrete: in log coordinates,
`exp(-3t/2)*A(exp t)` is the causal convolution of
`(1/2)*exp(-3t/2)` with `exp(-t)*psiDefect(floor(exp t))`.
The corpus's strong PNT and square-root-exponential moment integral give
all polynomial log moments of the latter source; exponential convolution
preserves them. This is not yet a Lean theorem, nor a claimed RH estimate.
It is the next missing analytic step of this same transfer, not a pivot to
a different route. Full moving-head Wronskian/correlation control remains
the RH-bearing problem even after this step.

Audit checkpoint: both new leaves are wired; the `/tmp` axiom audit exited
zero and reports only `propext`, `Classical.choice`, and `Quot.sound` for
all four jets and the cofinal escape theorem. Formal lint exited one solely
for ten unrelated modules unreachable from their umbrella, with no forbidden
declaration errors. No umbrella or full build was run.

Now constructing the log-moment input, starting with unconditional
`Summable (|psiDefect n|*(log n)^k/n^2)` for every natural k. Paper proof:
absorb the logarithmic power into half the existing strong-PNT exponential
saving and use the corpus's summable square-root-log weight. Treat the exact
Euler correction separately with the existing logarithm-weighted p-series.
This is needed to dominate the old-cutoff derivative above, not an attempt
to optimize a numerical constant. Direct deep search located
`HTGeometry.summable_log_pow_div_nat_rpow`; applicability and source signatures
were checked, with the Lean API audit next.
The API audit and direct leaf audit now passed. The theorem
`summable_psiDefect_log_moment (k : Nat)` is unconditional and wired into the
umbrella. No changed heartbeat limit or numerical computation was used.
The two initial Lean errors were redundant algebra tactics, not failures of
the mathematical conjecture. Its axiom audit also passed with only `propext`,
`Classical.choice`, and `Quot.sound`. The final lint run again reports only
the same ten unrelated unreachable modules and no forbidden declarations.

Next continuous weld: cover `[1,infinity)` by unit cells `[n+1,n+2)` and use
`MeasureTheory.integrableOn_iUnion_of_summable_integral_norm` (mathlib
`MeasureTheory/Integral/Bochner/Set.lean`, line 911). On each cell the floor
source is constant; for n>=1, `log(x)<=2*log(n+1)` and `x>=n+1`, so the
absolute weighted cell integral is bounded by `2^k` times the audited
discrete moment. The first cell is integrable separately. Then transfer
through the exact Abel integral by Tonelli/Fubini to obtain the degree-two
moment dominating the old-cutoff derivative. No continuous-moment theorem
or moving-core signed escape is being claimed yet.

End-of-continuation checkpoint: three new leaves are kernel-checked and
wired; frontier map updated with the exact proved boundary. Owned scratch
search/API/audit files are removed after inspection. No Lean process remains
running. The next conjecture is continuous absolute log-moment admission for
the literal Abel source, followed by differentiability of the old-cutoff
Mellin term. The previous all-prime sign obstruction is now a theorem, but
the full SZ signed-residual/Wronskian problem and RH are still unresolved.
Goal remains active.

## Continuous moment and retained-tail continuation

Classification of the previous goal turn: progress. Three source leaves
passed kernel and axiom audits, and changed the available signed-source
information. The hard SZ residual/correlation/Wronskian problem is still
open. Current source and frontier-map statements were re-read before use.

The unit-cell continuous log-moment proof is now being checked. For the
following Abel step, use an exact log-time positive convolution rather than
apply the strict-half-plane Mellin theorem at its boundary. Let
`q(t)=exp(-t)*psiDefect(floor(exp t))` and
`K(t)=(1/2)*exp(-3*t/2)`, on the positive ray. The existing real Abel bridge
gives `posConvolution(q,K)(T)=exp(-3*T/2)*A(exp T)` for T>0.
The continuous defect moments become integrability of `t^k*q(t)` by the
exponential change of variables. The kernel has all polynomial moments.
For the degree-two output use the exact identity
`T^2*C(q,K)=C(t^2*q,K)+2*C(t*q,t*K)+C(q,t^2*K)`.
Each right side is integrable by mathlib `integrable_posConvolution`; finite
interval integrability justifies the identity before passing to infinity.
This supplies the continuous absolute Abel moment needed for the old-cutoff
derivative. It is a dependency-closed paper argument, not yet a Lean result.

Boundary caution for the next derivative: use a right derivative, not an
open-neighborhood differentiation theorem. Strong PNT gives logarithmic
moments but no positive power saving. After exchanging the retained-prime
integral, write its kernel as
`y^(-5/2) * sum_{p<=y} (1/p)*exp(-delta*(log p+log y))`.
For delta>0 the difference quotient is bounded in absolute value by
`y^(-5/2)*sum_{p<=y}(log p+log y)/p`. Since p<=y and the finite harmonic
sum is at most `1+log y`, the complete majorant is at most
`3*|A(y)|*y^(-5/2)*(1+log(y)^2)`. This follows from
`1-exp(-delta*t)<=delta*t` for t>=0. Dominated convergence then gives the
right slope without assuming analyticity across the boundary. The new Abel
moment is exactly the required integrability assertion. The finite prime
cutoff and its indicator must be retained when identifying this kernel with
the actual omitted old portion.

The continuous unit-cell leaf passed its clean foreground Lean audit. The
Abel convolution leaf's first run found only two elaboration issues (an
`Integrable` versus `IntegrableOn` projection and a pointwise function-sum
reduction); both are repaired, with the second foreground audit running.

The retained-cutoff derivative search returned partial coverage and mostly
unrelated prime-gap declarations; it is not evidence of theorem absence.
Direct source inspection confirms the finite harmonic bound in this
mathlib and the filter dominated-convergence theorem. The actual adaptive
terminal-source identity still retains all unprocessed prime children and
the head square, so no identification of the all-prime head with the full
moving residual is made. Next construct the finite-cutoff boundary kernel
and its right derivative, followed by its exact transform identification.

The two moment leaves now pass leaf and axiom audits, with only `propext`,
`Classical.choice`, and `Quot.sound`. Both are wired. The retained-prime
boundary leaf is being audited: its theorem gives the right slope of the
literal finite-cutoff integral, with no analytic continuation premise.

Dependency-closed plan for the remaining exact weld: let
`G(x)=sum_p 1_{p^2<=x}*sqrt(p)*A(x/p)` and
`f_delta(p,y)=1_{p<=y}*p^(-1)*A(y)*y^(-5/2)*exp(-delta*(log p+log y))`.
Use counting measure on the natural prime indices and Lebesgue measure on
`y>1`. For fixed y, the counting integral is a genuinely finite sum; its
absolute value is bounded by the now-admitted source majorant. Thus
`integrable_prod_iff'` gives product integrability, including delta=0.
For each prime, x=p*y carries the f integral to
`1_{p^2<=x}*sqrt(p)*A(x/p)*x^(-5/2-delta)`, with the same identity for norms.
The alternate `integrable_prod_iff` then admits the transformed product;
Fubini identifies its x integral with the retained boundary transform.
This avoids assuming an unproved exchange of infinite primes and integrals.
The strict/non-strict boundary differs only at a singleton for each prime.
For the discrete adaptive head, select the explicitly covered core
`P={p: p^2<=M}`; do not silently replace the corpus's strict `<M` small core.

Once the weld is audited, the centered Mellin transform of `A+F-G` inherits
the positive `delta*log(1/delta)` jet: A and G have finite right slopes.
A hypothetical global lower linear bound would make its compensated
Mellin transform monotone, contradicting that positive infinite slope.
The baseline need not be zero; subtract its finite right limit explicitly.
This would be a moving-core sign obstruction, not RH. The complete residual
cross-correlation and source Wronskian remain the hard final gap.

The retained boundary leaf now passes clean `lake --old env lean` and all
three public theorem axiom queries (standard logical axioms only). The exact
right derivative is proved. The next product leaf is in its first foreground
audit: it proves absolute source product admission, exact prime-integral
exchange, and the pointwise dilation identity with the full Jacobian. The
API scratch found `ae_count_iff` under `Measure`, corrected before use; the
axiom outputs themselves succeeded. The actual old-head integral identity
still must be assembled; it is not inferred merely from these components.

## Audited retained-head closure and next conjecture

Five new leaves now pass clean foreground `lake --old env lean <leaf> -o
<olean>` checks and are wired into `RHTower.lean`:

- `MobiusDivisorCriticalContinuousLogMoments`: all natural log moments of
  the literal floor defect on the continuous ray.
- `MobiusDivisorCriticalAbelBoundaryMoments`: absolute quadratic boundary
  moment of the actual Abel source, by exact positive-time convolution.
- `MobiusDivisorCriticalRetainedPrimeBoundary`: measurability of A,
  absolute retained-kernel admission at zero, exact finite right slope.
- `MobiusDivisorCriticalRetainedPrimeProduct`: absolute source product
  admission, admitted prime-integral exchange, exact atom dilation.
- `MobiusDivisorCriticalRetainedPrimeMellin`: actual finite old-prime head
  `G(x)=sum_{p^2<=x}sqrt(p)*A(x/p)`, endpoint absolute Mellin admission,
  exact transform identity, finite right Mellin slope. The public final
  theorem is `criticalRetainedPrimeHead_right_slope`.

All twelve public theorem axiom queries for these five leaves report only
`propext`, `Classical.choice`, and `Quot.sound`. No new mathematical axiom,
RH premise, numerical experiment, heartbeat change, or umbrella build.
The final lint run fails only for the same ten unrelated unreachable
modules recorded in the previous checkpoint; no forbidden declaration.
All five new modules are reachable from their umbrella. No commits.

This closes the previously explicit old-cutoff domination/derivative weld.
It does not close the full moving-core sign problem or RH. The corpus
search for the next step was partial (generation 1180940, coverage pending),
but its source arguments recovered the actual prime-head negative-escape
and local-boundedness theorems. Their source proofs were inspected; no
absence claim is based on the incomplete index.

Next conjecture: for the complete moving head `R=A+Re(F)-G`, every real
C and X admit x>X, x>1 with `R(x)<-C*x`. First prove the centered logarithmic
jet. If `M_R(delta)` denotes its actual Mellin integral, the predicted
identity is
`(M_R(delta)+T_G(0))/(delta*(-log delta)) -> H/3 > 0`.
The corpus already gives `M_A(delta)/delta -> H/3` and
`M_F(delta)/(delta*(-log delta)) -> H/3`; the new exact retained-head
theorem gives `(T_G(delta)-T_G(0))/delta -> finite`. Use these actual
admitted transforms and retain the baseline `-T_G(0)`.

For eventual integrability of F, the existing negative-escape leaf obtains
it from its eventually nonzero real Mellin transform via
`Integrable.of_integral_ne_zero`. A and G are already admitted. Linearity
therefore applies on one common right-neighborhood filter. A hypothetical
global linear lower bound for R makes its compensated Mellin transform
monotone, contradicting the positive infinite centered slope. Extend to
cofinal escape using source-derived local boundedness of A, F, and G.
Do not infer a pointwise asymptotic from the Mellin jet. For a discrete
adaptive-head identification, retain the explicit core `p^2<=M`; the
corpus's `mobiusDivisorSmallSelectionPrimes` uses strict `<M`.

The next RH-bearing problem remains the complete signed residual/cross
correlation and source Wronskian. Goal remains active; no RH proof or
falsification has been obtained.

Checkpoint cleanup complete: owned scratch/API/search/audit files removed;
all owned Lean/search/lint sessions exited, and the owned-process check is
empty. Serena memory and route SZ frontier map record the audited boundary
and the centered moving-head conjecture for continuation.

## Centered moving-head continuation

Previous turn classification: progress. The actual retained term now has an
audited finite right Mellin slope. Current map and source contracts were
re-read. This turn targets the actual centered logarithmic jet of
`R(x)=A(x)+Re(F(x))-G(x)`, then its negative linear escape; the complete
signed residual/Wronskian problem remains open.

Use a real-ray Mellin receiver to combine the corpus's actual complex
simple/logarithmic jets with the actual retained integral. The source
receiver conversion includes the vanishing region x<=1. Both A and F are
eventually admitted because their source-certified Mellin quotients are
eventually positive, hence their integrals are nonzero. G is already
admitted. On that common filter, the integral of R is exactly A's integral
plus F's integral minus `T_G(delta)`. Divide A's simple jet and G's centered
finite slope by `-log(delta)->infinity`; both disappear. F retains H/3>0.
The resulting numerator is `M_R(delta)+T_G(0)`, not `M_R(delta)`.

The centered-jet draft's first audit found receiver simplification,
neighborhood orientation, function-addition elaboration, and a missing
explicit nonzero log denominator. Those are repaired; no mathematical
premise was added. A second leaf contains the actual compensated-transform
contradiction and local-source bounds for cofinal negative escape.

Subsequent discrete-transfer caution: R has jumps at prime squares, so do
not appeal to global continuity. Anchor a point x to its lower integer
n=floor(x). On [n,n+1), every prime square cutoff and every quotient floor
is fixed. The exact square-root interpolation therefore gives
`R(x)-R(n)=(sqrt(x)-sqrt(n))*(psiDefect(n)+sum_{sqrt(n)<p<=n}psiDefect(floor(n/p)))`.
A corpus-certified global linear defect bound and the finite harmonic
majorant would bound this unit-cell variation by O(sqrt(n)*log(n)), hence
by O(n); that coarse bound suffices to transfer arbitrary negative linear
escape to integer cutoffs without dropping prime-square jumps. This is a
next paper conjecture, not yet a checked theorem or an integer escape claim.

Source inspection confirms the needed unconditional linear defect bound:
`MobiusDivisorCriticalAbelMellin.lean` derives it from the current corpus's
`Mertens.sum_vonMangoldt_Icc_le`, with the Euler correction retained. The
lemma is private, so reconstruct that exact short source argument when
needed rather than assume an inaccessible constant.

Better discrete-transfer mechanism: retain the late-prime cancellation
before taking absolute values. Every surviving p has p^2>n, so the integer
quotient k=n/p satisfies k^2<=n. Thus |psiDefect(k)|<=C*sqrt(n). Also
`(sqrt(x)-sqrt(n))*sqrt(n)<=1` on [n,n+1), n>=1. Each late-prime cell
increment is bounded by C; there are at most n such primes. The Abel
increment is also bounded by C*n. This gives the required O(n) cell
variation directly from the actual late-prime source, without a new
harmonic estimate. Formalize the exact finite late-prime representation
first; the cancellation is essential to this proof. No integer escape is
claimed until that cell transfer is audited.

The centered Mellin leaf and complete moving-head negative-escape leaf now
pass targeted foreground audits. All eight exported theorem axiom queries
report only `propext`, `Classical.choice`, and `Quot.sound`. The API scratch
had one unrelated namespace error (`RHTower.Mertens`), repaired for its next
run. The finite-source leaf's first audit exposed an ambiguous natural-prime
binder cast in the filtered set; explicitly typing the binder fixes it.
The exact cell identity and integer transfer are still under audit.

The new broad deep residual search returned partial coverage and largely
unrelated source arguments; no absence conclusion follows. Direct corpus
inspection of `MobiusDivisorAdaptiveTerminalCriticalSource` gives the exact
adaptive head and energy receivers. At integer N the p=N child vanishes,
so the moving head identifies with the literal fibre for the core containing
exactly active primes p with p^2<=N. Integer negative escape will therefore
force this canonical square-root core's energy/N^2 to be unbounded. This
does not rule out adaptive terminal cores already constructed elsewhere in
the corpus: they process extra large primes. Positive survivor to extract:
any bounded-head extension must absorb unbounded negative signed child mass,
with the exact source balance retaining all added-prime signs. This focuses
the next cross-term attack on necessary cancellation, not an unsigned bound.

### Integer and literal-core closure, 2026-10-02

All five new leaves pass their direct `lake --old env lean <leaf> -o <olean>`
audits and are wired. FiniteSource needed explicit prime-index type and
`pow_two` cast normalization; IntegerEscape and CoreObstruction passed
their first targeted audits. The exact half-open cell identity gives
uniform linear variation, then cofinal integer negative escape. The
literal fibre weld retains p^2<=N and removes only the zero p=N endpoint.
Canonical energy/N^2 is unbounded. Every bounded-head adaptive extension
at those cutoffs must absorb large negative signed child mass, uniformly
over all its choices of added primes.

All eighteen public theorem axiom queries report only propext,
Classical.choice and Quot.sound. The combined API scratch now exits zero
after namespace and universe annotations. Global lint exits one solely for
eleven unrelated unreachable modules (the previous ten plus
ThetaTailEndpointCommutatorObstruction); no forbidden declaration finding.
No full or umbrella build, computation, new axiom or heartbeat change.
The no-go and strongest positive source survivors are recorded at
`5-failed/sz-canonical-square-root-core-bound.md`. The overall SZ route is
not retired; the signed correlation/Wronskian estimate is still open.

### Next conjecture: pointwise signed prime-convolution asymptotic

The previous work advanced the actual moving-source sign frontier. A
strictly stronger source classification may now be accessible:
`R(x)*log(x)^2/x^(3/2) -> -divisorHarmonicBoundary/3`.
This is a conjecture, not an audited theorem or a consequence of the
Mellin jet alone. The mechanism needs an independent pointwise proof.

In log time, put `a(v)=exp(-3v/2)*A(exp v)`. Its actual mass is zero and
its first moment should equal `-H/3`, by the simple Mellin jet plus the
proved absolute log moments. The normalized all-prime head is convolution
of a with the weighted prime measure having atoms 1/p at log p. Strong
PNT suggests kernel 1/(t-v). Its mass-zero expansion leaves
`t^(-2)*integral(v*a(v))`, hence the negative coefficient. Control the
finite-cutoff source and both tail ranges; an Abelian transform alone
does not justify this pointwise assertion. The corpus's strong PNT source
bound and exact Abel cell derivative may control the weighted prime error.
Search for the actual quantitative prime-harmonic / prime-counting input
is running. No new asymptotic code has been written yet.

The harmonic input exists in the corpus:
`Sieve.exists_mertensS_sub_logLog_sub_const_exp_rate` gives the actual
prime reciprocal sum with exponential square-root-log error. Its statement
and proof dependencies were inspected, alongside its uniform prime-window
corollary. The broad search was partial and returned mostly unrelated
source arguments; direct source inspection supplies the applicable input.
First formalize the exact signed zeroth and first boundary moments of A
by dominated right differentiation. The known absolute quadratic log
moment dominates the difference quotient. This identifies the coefficient
in the proposed pointwise convolution proof; it does not by itself prove
the conjectured asymptotic.

Improved paper mechanism: cancel G first, exactly as in the integer proof.
With t=log(x), the normalized moving head equals
`a(t)+integral_(t/2,t] a(t-u) dnu(u)`, where nu has atoms 1/p at log(p).
Thus there is no old-prime tail to estimate. Write
`H(u)=nu((0,u])=log(u)+B+E(u)`. The corpus's exponential Mertens rate
controls E uniformly for u>=t/2. Since a(0)=0 and
`a'(v)=q(v)/2-3*a(v)/2`, q(v)=exp(-v)*psiDefect(floor(exp v)), finite
prime-sum/Fubini gives the exact high-prime term
`integral_0^(t/2) a'(v)*(H(t-v)-H(t/2)) dv`.
The E contribution is bounded by twice the uniform error times integral|a'|.
Integration by parts of the main log ratio gives
`integral_0^(t/2) a(v)/(t-v) dv`, with both boundary terms zero.

Only the already-admitted quadratic moments of a and q are needed for
tails: they admit v^2*a' absolutely. Absolute continuity then gives
`t^2*a(t)->0` from the tail integral of a', once a(infinity)=0 is
established. Expand
`t^2/(t-v)=t+v+v^2/(t-v)` on 0<=v<=t/2. The zero mass removes the t term;
its omitted tail is O(1/t) by the quadratic moment. The last term is
bounded by `(2/t)*integral(v^2*|a(v)|)`. The surviving first moment is
`-H/3`. This is the planned source-faithful pointwise proof, with the
absolute-continuity/Fubini/real-clock Mertens transfers still to formalize.
It avoids assuming a Tauberian converse or a pointwise exponential bound
on the signed Abel source. The exact signed boundary-moment leaf is now
under its first foreground audit.

### Signed boundary moments audited

`MobiusDivisorCriticalAbelSignedBoundaryMoments.lean` now passes its direct
leaf audit and all four axiom queries (only propext, Classical.choice,
Quot.sound), and is wired. The two initial elaboration issues were beta
reduction before the Mellin integrand rewrite and pointwise negation /
multiplication order in the derivative limit. No mathematical change was
needed. The actual zeroth source moment is zero; the first logarithmic
moment is exactly `-divisorHarmonicBoundary/3`. Six leaves and 22 public
theorems are now checked in this continuation.

Final lint still has no forbidden declarations. It reports twelve
unrelated unreachable modules: previous eleven plus
XiMassTimelikeBilinearFlattening. Scoped `git diff --check` passed. The
pointwise prime-tail asymptotic is NOT formalized yet.

The last log-profile search was partial, generation1181414. Its applicable
hits recover the actual Mellin/source results, including the just-added
moment leaf; no new derivative producer was found in its returned source
arguments. This is not an absence claim. For the next source primitive,
mathlib provides `intervalIntegral.integral_hasDerivWithinAt_right`,
`intervalIntegral.integral_eq_sub_of_hasDeriv_right`, and
`intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`.
Their source signatures were read, but no new API scratch was run for
them. A right derivative is sufficient at every positive clock, avoiding
two-sided differentiability at integer source jumps. Natural floor is
constant in a small right neighborhood (prove with floor_eq_iff and
the strict next-integer bound). Continuity follows from the actual
source integral and `continuousOn_primitive_interval`.
The log-profile primitive, weighted derivative admission, finite-prime
Fubini, and real-clock Mertens error transfer remain next required work.

Checkpoint cleanup: all owned scratch, API, search, axiom and lint outputs
removed after inspection. All owned Lean/search/lint sessions exited; the
owned-process check is empty. The current no-go card, SZ map and Serena
memory record the six audited leaves and exact next pointwise-convolution
conjecture. No RH proof or falsification has been obtained; goal remains
active.

## Pointwise moving-head asymptotic continuation

Previous turn classification: progress. Current source and umbrella entries
confirm the six audited leaves. This continuation attacks the signed
prime-tail asymptotic, beginning with the actual log-profile primitive and
its weighted velocity admission. Right derivatives preserve integer source
jumps. The final RH problem remains cumulative signed correlation and the
source Wronskian; no local primitive identity alone closes that gap.

The current source search is partial, generation1181461; the applicable
hits recover actual signed moments and the Abel source weld. Their source
contracts are checked. Draft leaves now contain the log profile's admitted
moments, its actual right derivative / finite primitive, and the velocity
tail giving t^2*a(t)->0. These remain under sequential audits.

A simpler compensated-kernel proof handles the continuous prime-tail main
term: define on v>0
`F_t(v)=(1_(v<=t/2)*t^2/(t-v)-t)*a(v)`.
The exact zero mass makes its integral equal
`t^2*integral_0^(t/2) a(v)/(t-v) dv`. For t>=1, its absolute value is at
most `2*v*|a(v)|`: inside the cutoff the coefficient is t*v/(t-v),
outside it is -t with t<2v. For each fixed v the coefficient tends to v.
Dominated convergence with the actual first absolute moment therefore
gives limit -H/3 directly. This preserves mass cancellation inside the
integrand and avoids separate tail-error estimates for the main kernel.
It does not yet replace the discrete prime sum; the Mertens-error/Fubini
weld is still required.

Real-clock Mertens transfer to construct next: for u>=2 and
N=floor(exp u), the elementary floor/log inequalities give
`log N>=u/2` and `0<=log u-log(log N)<=2*exp(-u)`.
For the latter, apply log(z)<=z-1 first to exp(u)/N, then to
u/log N; use exp(u)-N<1 and log N>=1. The corpus's exponential
Mertens rate then transfers to H(u)=mertensS(floor(exp u)) with
another positive square-root-exponential rate. Taking the smaller rate
at most one absorbs the exp(-u) floor error. No optimization of constants
is needed. This will make the prime-tail error uniform on u>=t/2 and
negligible after multiplication by t^2.

The log-profile moment leaf and its literal primitive leaf now pass direct
foreground `lake --old env lean` audits and are wired. The primitive proof
retains the right derivative at every arithmetic jump. Its last repair
was syntactic: the norm majorant was simplified to absolute values, so the
nonnegativity fact supplied to nlinarith needed the same representation.
No mathematical premise was added. Public axiom queries remain pending.

The prime-tail search was partial, generation1181679. Its deep argument
hits were inapplicable; the narrower lexical Mertens search returned the
actual finite reciprocal-sum identity and MertensRiemannUniform. Reading
the latter confirms its O(1/log N) error is insufficient here. The source
exponential Mertens theorem remains the chosen input. A new draft now
contains the exact normalized moving-head/late-prime identity, finite
prime-sum/velocity interchange, and admission of its Mertens integrand.
These are not yet audited. The actual-source tail and compensated main
kernel also remain awaiting their first audits.

The discrete-error passage now has a direct dominated-convergence proof.
Put E(u)=mertensS(floor(exp u))-log u-B. The draft real-clock transfer
proves u^2*E(u)->0, retaining the floor correction explicitly; no optimized
constant or separate uniform exponential-rate theorem is needed. On
0<s<=t/2, both u=t-s and u=t/2 are at least t/2. Eventually
|u^2*E(u)|<=1, hence |t^2*(E(t-s)-E(t/2))|<=8 uniformly on this
moving interval. For fixed s this scaled difference tends to zero:
t^2*E(t-s)=(1+s/(t-s))^2*((t-s)^2*E(t-s)); the other term is
4*((t/2)^2*E(t/2)). Multiplication by the actual L1 velocity supplies
the fixed majorant 8*|v(s)|. DCT therefore removes the discrete error.
Combined with the exact finite-prime interchange, the boundary-free
logarithmic integration-by-parts identity, the compensated Cauchy limit,
and t^2*a(t)->0, this gives the target log-clock limit -H/3 on paper.
The final error module and final source composition have not yet been
written or audited. RH and the cumulative source Wronskian remain open.

The eight-leaf pointwise proof is now fully drafted:
MobiusDivisorCriticalLogProfile, LogProfilePrimitive, LogProfileTail,
CompensatedCauchy, PrimeTailSource, MertensLogError, PrimeTailError, and
MovingHeadAsymptotic (all with the MobiusDivisorCritical prefix).
The first two pass and are wired. The MertensLogError first audit passed;
two unnecessary tactic sequencing warnings were removed, so its final
source audit remains due. Tail, Cauchy and PrimeTailSource have received
targeted elaboration repairs; PrimeTailError and MovingHeadAsymptotic
await their dependencies' completed audits. No pointwise theorem is
claimed formalized yet. The final theorem is premise-free and concerns
the literal R(x): R(x)*log(x)^2/x^(3/2)->-H/3. A /tmp scratch lists all
23 public axiom queries, pending the completed dependency chain.

Next-hard-gap check while audits run: the corpus search (partial,
generation1181878) recovers the exact adaptive terminal source and the
already-proved exhaustive clock checkpoints/orders. Source inspection
confirms that nested adaptive cores with uniform current-checkpoint
weighted energy and fourth-root collars already exist. Constructing
another balanced terminal subset would be redundant. The missing estimate
concerns those same original cutoffs after further prime processing, plus
the intervals between collars. The density cancellation theorem in
MobiusDivisorCriticalClockProductTransport keeps the exact mixed product
and negative boundary surplus, but supplies no lower bound for the
cumulative signed mixed products. The new pointwise asymptotic calibrates
the actual source correction; it does not by itself pay that cumulative
debt. After its audit, attack that complete finite-clock mixed sum directly
rather than reprove scalar terminal selection or optimize collar constants.

Audit progress: LogProfileTail, PrimeTailSource and CompensatedCauchy now
pass clean direct leaf audits and are wired. The finite prime interchange
retains floor and endpoint conventions; its continuous logarithmic part
equals the Cauchy kernel exactly. The indicator repair needed expansion
of `Set.indicator_apply` with `mem_Iic`, avoiding an underspecified set
in a membership-lemma instantiation. MertensLogError's warning-cleaned
source is under final audit; PrimeTailError and MovingHeadAsymptotic are
the remaining proof audits before all 23 public axiom queries.

### Pointwise moving-head asymptotic fully audited

All eight leaves now pass clean direct foreground `lake --old env lean`
audits and are wired. The final API/axiom scratch exits zero: all 23
exported theorems and the exponential arithmetic Mertens input depend only
on propext, Classical.choice and Quot.sound. The final real-variable
theorem has no premises:
`tendsto_criticalMovingPrimeHead_pointwise_scaled` proves
`R(x)*log(x)^2/x^(3/2)->-divisorHarmonicBoundary/3`.

This resolves the actual pointwise source conjecture, using the literal
prime sum rather than a Tauberian converse. It strengthens the source
obstruction and identifies the signed correction scale. It does not solve
the cumulative mixed-correlation/original-cutoff Wronskian problem or RH.
The frontier map and the canonical-core positive-survivor card now record
the audited result. Global lint and checkpoint cleanup are pending.

Final lint exits 1 solely for eleven unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaCuspGaussianScaleOperator, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving. No forbidden declaration is reported; all
eight current leaves are reachable. Scoped git diff --check passes.
All owned Lean/search/lint processes have exited. The completed leaves
need no repeated build or axiom audit. RH remains unresolved; goal active.

Checkpoint cleanup completed: all nine owned /tmp search, API, axiom and
lint files were removed with apply_patch; the exact-path absence check is
empty. Current oleans retained. Serena memory now records the eight-leaf
proof, all audits, and the next original-cutoff mixed-correlation target.

## Original-cutoff correlation continuation

Previous turn classification: progress (the pointwise source conjecture
was formalized). Current source and frontier entries were revalidated;
no completed proof was rebuilt. The current deep correlation search is
nonpartial, generation1182057 (compiler metadata remains largely source
or stale snapshots). Applicable returned arguments include the actual
finite-clock density balance and the strictly positive inverse-cube
primitive in MobiusDivisorTruncatedMomentCancellation.

Conjecture test 1: use the positive primitive directly to control the
critical pairing by integration by parts. If f(t)=H_P(exp t)/exp t and
K(t)=integral_(-infinity)^t exp(-u)*f(u) du, the corpus gives K>0 after
source birth. But the critical pairing is integral f(t+a)*f(t) dt;
integration by parts differentiates exp(t)*f(t+a). Its derivative contains
the actual processed step defect H'_P(exp(t+a)), whose sign is not supplied
by primitive positivity. Thus no signed-correlation inequality follows
from that input alone. This is a failed proof attempt, not a counterexample
to the desired correlation bound.

Conjecture test 2: strengthen the primitive positivity to the inverse-square
primitive of the complete A. This is false on paper: if
B(X)=integral_1^X A(y)/y^2 dy were nonnegative everywhere, then the admitted
absolute boundary moment gives B(X)/sqrt(X)->0 and integration by parts
would yield 0=integral_1^infinity A(y)/y^(5/2) dy
=(1/2)*integral_1^infinity B(y)/y^(3/2) dy. Positivity near the first source
birth contradicts this. The exact zero boundary mass therefore forbids
discarding the critical primitive's signed part. This argument still needs
novelty/salvage and Lean audit before any route retirement; no new theorem
or no-go is claimed yet. The hard next task remains controlling the
translated derivative or its cumulative signed arithmetic sum, retaining
the original cutoff.

### Signed two-source moment and original-cutoff transfer

The generic uniform-core bound is not a viable replacement: the inspected
ShellAnchorDebt theorem proves divergent physical energy over fresh dense
shells above every fixed old core. ExhaustiveClockCheckpoints controls only
each current core at its current cutoff, explicitly not completed past
cutoffs. No new checkpoint or endpoint receiver was added.

Conjecture 3: exploit the actual boundary source's two moments to determine
its signed autocorrelation, rather than infer a sign from primitive
positivity. Paper proof succeeds: C(u)=integral a(t+u)*a(t) dt has absolutely
admitted second moment -2*(H/3)^2. Therefore C(u)<0 for some u>0. Finite
integration by parts strengthens this: some original complete critical
source pairing integral_0^T (A(exp(t+u))/exp(t+u))*(A(exp(t))/exp(t)) dt is
negative. Its endpoint term stays explicit, and the proof never assumes
infinite critical-energy admission.

Both leaves are drafted (MobiusDivisorCriticalSourceAutocorrelation and
MobiusDivisorCriticalFiniteCorrelationSign); audits are in progress.
The dependency-closed paper proof and local novelty audit are on
sz-critical-source-autocorrelation-balance.md. This refutes the proposed
pointwise-positive-pair shortcut and exposes an exact bilinear invariant;
the cumulative signed lower bound through exhaustive insertion remains
the hard unresolved target. No RH conclusion is claimed.

Both new leaves now pass direct foreground `lake --old env lean` audits,
with no heartbeat overrides, and both are wired. The nine public axiom
queries and final API verification are running; global lint is also running.

Next hard attack: retain the exact Tatuzawa--Iseki forcing before its
absolute-value bound. Deep search generation1182237 (partial) returned
SelbergSymmetryCore; its proof immediately replaces the actual signed
Mobius forcing by a 384*N envelope. Inspection of TatuzawaIsekiIdentity
and PsiDefectSqrtBound gives the literal forcing
S(N)=sum_(n<=N) mu(n)*log(N/n)*floorSummatory(psiDefect)(N/n),
equal to psiDefect(N)*log N+sum_(k<=N) Lambda(k)*psiDefect(N/k).
The inner floor summatory has an exact divisor/Stirling decomposition and
square-root bound. The missing estimate is the signed pairing of S with
the same Abel source; termwise absolute values lose the critical scale.

Paper calculation for the continuous counterpart, with D(x)=psiDefect(floor x)
and A'(x)=D(x)/(2*sqrt x):
integral_1^X A*D*log(x)/x^(5/2)
= A(X)^2*log(X)/X^2 + integral_1^X (2*log(x)-1)*A(x)^2/x^3.
The delayed Lambda terms contribute both mixed products and the actual
two-source Wronskian after integration by parts; neither sign is automatic.
Do not formalize this algebra alone as a frontier advance. Attack a
source-derived bound for its complete signed forcing/Wronskian combination,
retaining floor corrections, to control the original-cutoff energy.

Final checkpoint: both leaves pass clean direct audits; the combined API
and all nine public axiom queries exit zero, using only propext,
Classical.choice and Quot.sound. The no-go card, including the fully
formalized positive survivor, moved to
docs/drafts/pipeline/5-failed/sz-critical-source-autocorrelation-balance.md.
The SZ frontier map records the exact paired moment and original finite
cutoff result. Global lint exits 1 only for ten unrelated unreachable
modules (the prior list minus ThetaCuspGaussianScaleOperator); neither
current leaf is unreachable and no forbidden declaration is reported.
Scoped diff --check passes. No build, search or lint process remains live.
RH is unresolved; goal remains active.

Cleanup verified: all nine owned /tmp files removed; current oleans retained.
Serena memory rhtower/sz-critical-correlation-sign-2026-10-02 records the
completed source pair result and next hard forcing/Wronskian target.

## Continuation: literal divisor response and arithmetic phase

Route SZ. The preceding signed autocorrelation theorem ruled out universal
positive source pairs but did not bound cumulative leakage. The next
conjecture tested whole-half-plane passivity of the actual candidate
response K(s)=1/s-B'(s)/B(s), B=divisorSourceEntire. The corpus's exact
step-source quotient F=B/(s*zeta) gives the formal logarithmic forcing
-F'-(zeta'/zeta)*F=K*F. Its identification with a physical forcing integral
is not yet claimed.

Paper test succeeds as a falsification with a positive survivor: if
b(n)=log(n)-tau(n)+2*gamma, then c=b(1)>0 and b(2)<0. The latter follows
symbolically from the n=2 harmonic remainder and log(2)>2/3, without a
numerical approximation. The actual logarithmic derivative satisfies
2^s*B'(s)/B(s)->d=-b(2)*log(2)/c>0 as Re s->infinity, uniformly in height.
At the literal heights 2*pi*k/log(2), this forces Re(B'/B) above a positive
constant on each sufficiently right vertical line; Re(1/s) tends to zero.
Thus Re K<0 at unbounded heights on every such line.

The generic first-index Dirichlet limit was found by deep corpus search
(partial snapshot1182304) and reused. Earlier searches1182294,1182299,
1182300 found the exact source weld and Selberg absolute envelope, not a
matching source phase theorem. Follow-ups1182376,1182424 returned finite
depth Mellin identities and RH-equivalent source criteria, but no paired
forcing bound. Returned candidate statements and source arguments were
inspected; source/compiler freshness remains partial. A miss is not an
absence claim.

DivisorSourceLogPhase now passes a direct foreground leaf audit. The
response sign leaf is drafted and auditing. The complete paper proof and
no-go survivor are on sz-divisor-response-phase.md. Neither RH nor the
cumulative source estimate is proved.

Next actual hard test: write f(t)=exp(-t)*A(exp t), D(x)=psiDefect(floor x),
and S(x)=sum_(n<=x)mu(n)*log(x/n)*primeFreeDivisorDefect(floor(x/n)).
The continuous exact Tatuzawa identity should be
S(x)=D(x)*log(x)+sum_(k<=x)Lambda(k)*D(x/k); extending the integer
identity requires retaining the log(x)-log(floor x) correction and using
Mobius inversion, not replacing either floor. On each finite clock Y,
pairing it with A gives the diagonal production
Y*f(Y)^2+integral_0^Y (2t-1)*f(t)^2 dt, plus delayed terms
sum_k Lambda(k)/sqrt(k) times
[f(Y)*f(Y-log k)+integral_(log k)^Y W(t,log k)dt
 +2*integral_(log k)^Y f(t)*f(t-log k)dt],
where W=f(t)*f'(t-log k)-f'(t)*f(t-log k).
These are paper calculations with the physical/Mellin weld still open;
do not count their formalization alone as a frontier estimate.

The conjectural closure must control the **combined** forcing-minus-delayed
form at the original cutoff, yielding at most quadratic growth in Y for
the weighted energy. Neither the previous signed moments nor the new
uniform phase law supplies that bound. Taking absolute values repeats the
certified insufficient Selberg input; assigning a sign to individual
delayed pairs is now refuted. Attack the actual Mobius/divisor covariance
or a source-specific commutator inequality; a generic positive metric
changes the physical norm and leaves precisely the missing coercivity.

Further conjecture test: absorb the negative moving head using fresh
terminal primes with bounded insertion cost. Inspection of
MobiusDivisorAdaptiveTerminalCriticalSource confirms the exact energy is
the terminal head square plus the unprocessed prime-weighted child squares.
This can describe a favorable current cutoff, but exhaustion later removes
the remaining children at each old cutoff and restores A(old cutoff)^2.
Thus the construction still needs the complete old-cutoff signed debt bound;
it does not prove it. No duplicate checkpoint construction was formalized.

Search1182454 completed (compiler snapshots still mostly pending/stale)
and returned a genuine signed estimate: MobiusDivisorSectionSignLaw gives
a negative divisor-comparable Hilbert section; MobiusDivisorMonotoneSignLaw
extends it to nonnegative decreasing anti-diagonal weights. These theorems
do not cover the incomparable pairs of the actual Abel channel Gram.
MobiusDivisorAbelGcdCross retains every such pair and the shared-prime masks
under homothety. The proposed transfer therefore has two unresolved parts:
the actual cutoff-dependent kernel is not yet in the proved monotone class,
and the primitive coprime cross section remains. Uniform coprime harmonic
cancellation bounds reciprocal weights, not this physical kernel. No new
signed estimate was obtained in this test; merely renaming these components
would not advance the route.

Final checkpoint: DivisorSourceLogPhase and DivisorSourceResponseSign both
pass clean direct foreground `lake --old env lean` audits; both are wired
in RHTower. All five public theorem axiom queries pass with only propext,
Classical.choice, Quot.sound. The mathlib API scratch passes. Global lint
still reports exactly the ten unrelated unreachable modules recorded at
the previous checkpoint, and no forbidden declarations. Scoped diff check
passes. The card is now 5-failed/sz-divisor-response-phase.md, with its exact
uniform arithmetic phase survivor formalized; SZ frontier map updated.
No RH conclusion or new cumulative signed bound is claimed. The goal
remains active. Next research must attack the actual source-paired form or
complete old-cutoff covariance, not repeat generic sign or checkpoint tests.

Cleanup verified: all nine owned /tmp search/API/axiom files removed;
both audited leaf oleans retained. No owned process remains. Serena memory
rhtower/sz-divisor-response-phase-2026-10-02 records the result and hard
remaining target.

## 2026-10-02 — Signed pairing attempts and canonical bulk obstruction

Route SZ hard target remains the complete original-cutoff forcing-minus-delayed
Wronskian estimate. Searches1182527/1182541/1182572/1182593/1182618 examined
actual Tatuzawa forcing, complete gcd cross terms, iterated Selberg identities,
reflected physical pairing, and endpoint-to-bulk regularity. Metadata mostly
pending/stale; 1182527/1182541/1182618 partial, 1182572/1182593 complete retrieval.
Candidate statements/source arguments checked; retrieval misses are not proofs
of absence. No actual combined forcing bound found or proved.

Paper attempts: higher log weights have favorable absolute factorial bounds,
but control a transformed source. Fractional damping inserts the uncontrolled
inverse zeta(s+alpha), so it does not recover D at the critical line. Reflected
log derivatives retain residues and cutoff commutators. Complete coprime-column
inversion returns actual supported psi defects without estimating them. These
are failed proof attempts, not new formal theorems. Existing gcd sign and
inclusive-Gram obstructions prevent discarding incomparable signed pairs.

Selected new paper result, card sz-canonical-core-bulk-energy.md: U has literal
Abel density P(floor t)/(2sqrt(t)), bounded by12 using the corpus divisor bound.
Every finite Mobius core therefore has |H_P(x)-H_P(y)|<=24sqrt(N)|x-y| for
x,y<=N, uniformly in P. For B=-H_P(N)>0, N>=2, H_P(0)=0 gives B<=24N sqrt(N).
The interval [N-B/(48sqrt(N)),N] lies above1 and carries H_P<=-B/2, forcing
E(P)>=B^3/(192sqrt(N)N^3). Canonical moving-head asymptotics then force
E(P_N)>=cN/log(N)^6 eventually. This would rule out a polylogarithmic whole-ray
core-norm controller with a nontrivial positive survivor. It does not estimate
the compensated original source or resolve RH.

Formalization in progress: MobiusDivisorUniformLocalRegularity drafted, not
wired or audited yet. API scratch corrected after one nonexistent integral
lemma; current scratch build is foreground, no concurrent owned Lean process.
No no-go retirement until uniform regularity, bulk law, and canonical
consequence are all audited.

Regularity and endpoint bulk law now pass direct leaf audits; the latter's
style-only corrections pass a second clean audit. Canonical lower bound itself
also elaborated in the first canonical audit. Its final logarithmic-growth
corollary required resolving natural/real-power coercions; current canonical
leaf audit is running. No heartbeat changes or numerical experiments used.

Further hard-source attempts: the exact B=-zeta'-zeta^2+2gamma*zeta equation
and the functional equation yield a symmetric reflected combination with the
inverse zeta canceled. This still leaves the antisymmetric response and the
finite-cutoff boundary/residue terms; no signed energy bound follows from the
algebra alone. Search1182758 is partial/pending, returning the actual divisor
source continuation but no missing estimate. No identity-only leaf added.

Search1182778 (partial/pending) and exact lexical mobiusDivisorGcdCross retrieval
confirm the available complete decomposition and componentwise obstruction.
The actual diagonal is <=722M^2; the all-label cross is exactly full-head square
minus this diagonal. Individual gcd sections may be positive and unbounded;
the certified cutoff11 has negative total cross. These facts do not prove an
all-cutoff total sign. The divisor-comparable monotone sign law covers only a
proper pair subset and a restricted kernel. A complete original-cutoff signed
cross budget remains a live candidate. Do not substitute the canonical-core
whole-ray norm: its forced bulk mass lives near the square of its prime cutoff,
whereas the all-prime head already agrees with A on the causal initial interval.

Next hard attack: integrate the complete two-channel kernel on the original
physical interval before gcd grouping. Seek a source-specific decomposition
into the admitted comparable negative form and a remainder with cumulative
quadratic log-clock budget. Neither that decomposition nor its required signed
remainder estimate is proved. Do not formalize a receiver in place of the bound.

The exact physical pair to attack next, for 1<=d<=e<T, is
mu(d)mu(e)*sqrt(d)/e^(3/2) times
integral_1^(T/e) U((e/d)y)U(y)/y^3 dy.
It depends on the ratio e/d AND the retained endpoint T/e. Thus the proved
anti-diagonal comparable-pair monotonicity cannot simply be applied as a
weight w(d+e). Any proposed decomposition must keep the endpoint remainder
and all incomparable pairs; replacing this by the admitted infinite-ray mean
is exactly the forbidden norm shortcut exposed above. This is a paper change
of variables identifying the remaining estimate, not a new bound.

All three new leaves now pass clean foreground direct audits:
MobiusDivisorUniformLocalRegularity (2 public theorems),
MobiusDivisorEndpointBulkEnergy (1), MobiusDivisorCanonicalBulkEnergy (2).
All three wired into RHTower; no umbrella build. Final axioms query running.

Final checkpoint: all five public axiom queries pass with only propext,
Classical.choice, Quot.sound. Three clean direct leaf audits, exact single
umbrella imports and valid oleans verified. Global formal lint exits1 solely
with the same ten previously recorded unrelated unreachable modules; no new
leaf unreachable. Scoped diff check and new-source whitespace checks pass.
Card moved to 5-failed/sz-canonical-core-bulk-energy.md, positive survivor
formalized, SZ map updated, Serena memory rhtower/sz-canonical-core-bulk-energy-2026-10-02
written. All eleven owned /tmp search/API/axiom files removed and absence
verified. All owned build/search/lint processes have terminated. Valid audited
oleans retained. RH unresolved; goal remains active. Next work must attack
the original finite-cutoff complete signed pair kernel described above.

## Continuation — actual finite pair and counting corrections

Previous goal turn: verified progress (three new source/bulk leaves and exact
canonical norm obstruction). This continuation has not yet produced a new
signed bound. Hard target unchanged: cumulative full forcing/Wronskian at the
original cutoff, or complete original-source off-diagonal budget.

Search1182852 (partial; compiler mostly pending/stale) returned the actual
CriticalClockProductTransport and PaidCutoffInterval. Exact physical kernel
retains ratio e/d and endpoint T/e. Stationary divisor positivity instead
classifies kernels sum_(r|d,e)c(r); its Mellin factorization is not the actual
pair kernel. No substitution made. Source U positivity and its Lipschitz bound
do not estimate the signed Mobius inverse. Positive decaying-power mixtures
were already excluded in an earlier turn; do not rediscover that as progress.

Search1182860 (partial) returned exact Suzuki screw criteria, positive divisor
weights, and compensated logarithmic renewal. These do not supply the original
physical mixed estimate. No assumed-Hilbert source bound or generic positive
screw kernel was substituted for the actual arithmetic source.

Search1182874, restricted to MobiusDivisor, found exact finite counting
cancellation. Its c=0 terminal energy vanishes, whereas c=1 recovers the
complete head square. Subtracting the two exact identities cancels the copied
logarithmic diagonal payment and leaves the same unweighted mixed sum. Thus
combining affine offsets supplies no new sign for the missing total. Higher
weights vanishing at cofactor1 likewise miss that atom. This is a failed proof
attempt, not a new no-go theorem. The all-prime budget remains unproved.

New candidate under examination: use Binet/Lambert kernels to sum Mobius
coefficients before estimating the paired source. The ordinary Lambert
identity cancels a zeta factor exactly, whereas the logarithmic commutator
creates a von Mangoldt forcing. Must retain the finite tail and estimate that
forcing jointly; the unweighted identity alone cannot remove the log term.
Search and literal-source audit underway. No Lean wrapper or numerical
experiment added.

Lambert audit completed: Search1182919 is not partial, but compiler evidence
remains mostly pending/stale. ChronologicalZeroChargeTailBounds already proves
sum mu(k)/(exp(k*t)-1)=exp(-t), t>0; PrimeLambertMobiusInversion admits weighted
regrouping under explicit absolute summability. At the paper level, inserting
log k gives the divisor coefficient sum_(k|n)mu(k)log k=-Lambda(n), hence the
logarithmic Lambert image is -sum Lambda(n)exp(-nt). This is the compulsory
prime forcing, not a cancellation of it. The finite source additionally retains
the cutoff tail. No positive inversion back to the sharp physical cutoff has
been established; a positive decaying-kernel mixture cannot itself reproduce
that compact cutoff. No identity-only Lean leaf added.

Additional attempted synthesis: write the actual critical source as f=M*g,
where M is the finite causal Mobius delay sum with gains mu(n)/sqrt(n), and
g(t)=exp(-t)U(exp t). Multiplication by t satisfies the exact formal commutator
`t*f + LambdaDelay*f = M*(t*g)`. Pairing this with f leaves the same
M^*tM quadratic form; taking adjoints/symmetrizing does not supply its upper
bound. A source-independent norm bound for M is not proved or assumed.

Counting-offset, reflected-response, and Lambert cancellations thus do not
close the original finite signed estimate. This continuation is NO FRONTIER
PROGRESS: no new hard bound, unconditional RH theorem, or falsification. No
Lean source edited and no build run, because only premise-consuming or
algebra-only wrappers were available. These are failed proof attempts, not
newly proved no-go results and not grounds for retiring SZ.

Next conjecture to attack: the log-weighted Mobius/Binet forcing and its exact
finite tail, paired with the same Abel source, admit a cumulative quadratic
log-clock budget after the delayed Wronskian contribution is retained. Estimate
that joint remainder itself; do not replace it by the infinite Lambert image,
coarse Selberg absolute envelope, generic positive metric, or a fresh norm
controller. Goal remains active.

## Continuation — actual vanishing-shift source alignment

Route SZ. Last continuation made no frontier progress. Examine the literal
vanishing-shift source Wronskian, keeping its physical source and aperture
normalization. The coalescing-anchor paper sections 14.32--14.47 already reduce
the RH-side negative-shift candidate to a paired source ridge curve. Its latest
high-assisted obstruction is source-cyclic mass above squared correlation
1/113: a successful branch requires mass >r/(128 C_T), C_T=O(log(1/r)^2).
The actual Xi tail/capacity/spectral-measure specialization is paper-level;
Lean's RidgeMatchedCoherenceBarrier proves only the generic scalar steps.
Do not mistake the RH-side necessary conditions for an unconditional producer.

First conjecture: physical compatibility u_L=S_L h, u_H=S_H h might force
the complementary residual small. The exact candidate identity is
u_H-C^* (S_L S_L^*+rI)^(-1)u_L
=S_H [I-S_L^*(S_L S_L^*+rI)^(-1)S_L]h.
The original sampling map is physical-to-sequence, not its reverse. The
bracket is the physical low-approximation residual, already implicit in
the paper's exact ridge variational formula. Compatibility alone bounds
high improvement by remaining low approximation error, which can be order
one. It does not supply the required moving-scale decay. No algebra-only
Lean module will be added. Next test: exploit actual high-frequency source
decay together with the coefficient penalty, retaining the coupled low/high
cancellation and avoiding any growing-block zero-gap assumption.

Search1182992 is partial (reranking deadline); compiler evidence predominantly
pending/stale. Its low-band Fourier bounds concern the oriented primitive,
not the source-cyclic Schur mass. Source arguments and ingredient sets were
inspected; none supplies the missing moving-scale bound. The subsequent
parity/boundary and canonical/coercive searches are non-partial, with the same
compiler caveat. They expose the exact actual source form and covariance;
generic parity countermodels and finite Wronskian identities are not producers.

The physical-compatibility attempt fails already at the symbolic Hilbert-space
level. For h=(1,0), take sampling rows S_L=(1,b), S_H=(0,b), b>0. Then
u_L=1, u_H=0, low Gram=1+b^2, high Gram=b^2, cross=b^2. As r decreases to
zero, low leverage tends to 1/(1+b^2), full leverage tends to 1, and high
improvement tends to b^2/(1+b^2). Thus compatibility plus a vanishing direct
high source cannot force the coupled improvement to vanish. This is a
symbolic proof-attempt diagnostic, not an actual-Xi counterexample and not
a new Lean theorem. The exact residual identity survives but was already
implicit in the corpus ridge variational law. No route retirement claimed.

Next attempted ingredient: compare the two literal parity sources by
differentiation/integration. Although cosh'=sinh and sinh'=cosh, finite
aperture integration introduces a constant and an interval-length error;
differentiation multiplies zero coefficients by their ordinates and increases
the ridge penalty. On the actual form domain H^log, endpoint traces and
derivatives are not automatically available. The corpus already rejects
prime-seam Taylor arguments for precisely that domain reason. This attempt
does not supply a parity ratio or remove the source-weighted near-null modes.

Canonical coercive-shift candidate also examined. With G=A+r>=1 and an
operator-domain unit source h, the exact scalar-resolvent expansion would
give
r<h,G^(-1)h>-1=-<h,Ah>/r+<Ah,G^(-1)Ah>/r.
An actual estimate ||Ah||^2=o(r) would therefore prove source collapse.
Neither operator-domain admission with that estimate nor an applicable
unconditional bound was established. Strong PNT cancellation on fixed smooth
endpoint profiles is already in paper Theorem AB; it does not supply this
estimate for the full literal profile or for moving resolvent vectors.
The canonical shift is ||B||+1, whose unit coercivity margin does not imply a
uniform positive margin after exponential aperture rescaling. Thus Theorem AC's
macroscopic safe-shift hypothesis cannot be silently discharged by its name.
No conditional resolvent wrapper added and no claim of canonical collapse.

Assessment: NO FRONTIER PROGRESS this continuation. No new actual-source hard
estimate and no Lean source change. The remaining difficult quantity is the
source-visible coupled low/high cancellation at a moving aperture and shift;
on the arithmetic side it is the centered prime--archimedean form paired with
the same moving source resolvent. Fixed-profile strong convergence, direct
source-tail decay, and compatibility are all insufficient for that pairing.
Next conjecture must estimate this moving response itself, retaining its
coercivity deficit and boundary leakage, rather than introduce another global
norm or assume a source-cyclic mass bound. RH remains unresolved; goal active.

## Continuation — joint finite-clock forcing and critical source response

Previous continuation: no frontier progress. Return to the actual Tatuzawa
forcing and delayed Wronskian at their common finite clock. Direct source
inspection confirms the exact discrete identity and its square-root divisor
input. The continuous extension adds (log x-log floor x)*D(x) by the same
Mobius inversion; it does not permit replacing floor(x/n) by x/n. The
existing log-clock commutator M(tg)=t(Mg)+LambdaDelay(Mg) is the same
identity after source transport, so taking its inner product with Mg alone
cannot improve the bound.

New test: restrict the divisor response K(s)=1/s-B'(s)/B(s) to Re(s)=1/2,
which is not decided by the proved far-right negative phase law. Using the
corpus Hardy rotation, put theta=gammaHardyTheta, p=theta', Z=hardyZ,
q=p+2gamma. On the critical line the literal B is
exp(-i theta)*(X+iY), where
X=q Z-cos(theta) Z^2, Y=Z'+sin(theta) Z^2.
At a nonzero B the proposed response sign becomes exactly
X Y'-Y X' <= [Re(1/s)+p]*(X^2+Y^2).
The term X Z'' has no sign supplied by the Gamma phase-rate estimates;
the Hardy norm-coercivity theorem for a different normalized derivative does
not control this curvature. At a simple critical zero, the paper formula
reduces to Re K=Re(1/s)+2p+2gamma, eventually positive, but this local fact
does not control intervening heights or the full source pairing. No new
critical-line sign theorem established and no algebra-only Lean leaf added.

More fundamentally, even a critical-line sign would require a separate
finite-clock transfer. The source Mellin quotient is admitted in Re(s)>1;
using its critical boundary as the transform of f would assume precisely
the missing growth/integrability. Truncating first produces terminal and
delayed-tail corrections. Next attempt retains these finite corrections
and asks whether they cancel in the combined forcing/Wronskian pairing.
Searches for joint delay and critical response were partial; the latter
reported Qdrant timeout with coverage pending. Returned candidate/source
arguments were inspected, and exact source files were read independently.
No search absence claim or external blocker is inferred.

Finite-clock follow-up: let f_Y=1_[0,Y] f and F_Y(s)=integral_0^Y exp(-st)f(t)dt.
For a causal delay d in [0,Y], its truncated transform is exactly
exp(-sd)*[F_Y(s)-integral_(Y-d)^Y exp(-su)f(u)du].
The subtracted term is the transform of the piece of the delayed f_Y lying
after Y. Its ordinary L2 pairing with f_Y is therefore zero by disjoint
supports (endpoints have measure zero). This removes that particular tail
from a same-cutoff quadratic pairing. It does not remove a derivative's
terminal atom, justify replacing a finite symbol by B'/B, or bound the
remaining finite delayed quadratic form. In particular, for any finite
positive coefficients c_d the surviving expression is exactly
sum_d c_d integral_d^Y f(t)f(t-d)dt, with its original signs unchanged.
The earlier complete-source negative correlation theorem prevents assigning
a universal positive sign to these pairs. This cancellation is elementary
support bookkeeping, not a new source growth estimate; no Lean wrapper added.

Search1183103 (partial, reranking deadline, coverage pending) returned admitted
Laplace convolution laws with explicit integrability and the actual finite
Mobius/divisor atom weld. None discharges a critical-boundary passage or the
surviving mixed estimate. All search sessions terminated. No Lean source
modified, no build needed or run. This continuation again has no hard-frontier
closure: the source-weighted curvature and original finite delayed sum remain
unestimated. Next work should attack that finite signed form directly; do not
spend another turn replacing it by infinite-response passivity or derivative
algebra. RH unresolved; active goal unchanged.

## Continuation — common-divisor averaging of the finite signed form

Previous turn: no frontier progress. Exact current coprime-column and
common-divisor source modules inspected. The complete coprime inversion
returns signed psiDefect values on prime-supported quotients, including the
unchanged n=1 source. Shared-prime masks and terminal interpolation survive.
Thus a coprime-column rewrite does not discharge the unknown defect bound.
Search1183136 is partial (semantic retrieval deadline, coverage pending);
candidate lemmas and source arguments correctly identify these exact modules.

Common-divisor averaging attempt, at the paper level: for the continuous
unit source U and full Abel source A, write d=g*a, e=g*b with (a,b)=1.
The original finite energy has the exact candidate reindexing

E(T)=sum_(a,b<=T,(a,b)=1) mu(a)mu(b)sqrt(a*b)
  * integral_(max(a,b))^T U(y/a)U(y/b)y^(-3) S_(ab)(T/y) dy,
S_q(R)=sum_(g<=R,(g,q)=1) mu(g)^2/g.

This follows by x=g*y after expanding A(x)^2; zero U below1 keeps all
endpoints exact. It makes the obstacle explicit: unsigned common-divisor
mass leaves the signed coprime factors and couples its cutoff to y. A
pointwise upper bound for S_q cannot be inserted into a sum with both signs.
Replacing S_q by fixed-modulus density asymptotics requires a uniform
remainder through growing a,b and the boundary T/y near1; no such estimate
was obtained. A positive inclusive gcd completion is already known to grow
superquadratically, so it cannot pay for dropping that remainder. No
reindexing-only Lean module added and no new source bound claimed.

The corpus's genuine coprime logarithmic Mobius bound uses mu(d)/d and a
prime-recursion gain 1/p. It is not a critical 1/sqrt(p) estimate. Indeed
sqrt(d)U(T/d)=T^(3/2)/d * [U(T/d)/(T/d)^(3/2)]; applying the harmonic bound
leaves the excessive T^(3/2) prefactor. The square-root log-log schedule
module proves elementary schedule asymptotics only, not a Mobius estimate.
Neither result closes the missing half-power cancellation.

Next actual mechanism under examination: retain the oscillatory divisor
remainder inside the Mobius-weighted Tatuzawa forcing before pairing it
with A. This asks for cancellation of the joint signed kernel, not another
absolute source envelope. Corpus search for its exact representation is
underway; no representation, estimate, or critical-line passage assumed.

The centered modular primitive sign does not survive the source-paired
weight: summation by parts retains both its terminal value and the signed
source variation. Existing complete-column subpower errors explicitly leave
the finite numerator heads unestimated. The complete modular energy saving
is relative to N, not a polylogarithmic energy bound. None of these attempts
has improved the hard original-cutoff estimate.

New source-specific conjecture under audit: the actual autocorrelation is
not eventually nonnegative. A stronger mechanism emerged from the corpus:
its unilateral Laplace transform admits a local analytic continuation by
the imaginary-axis product L(s)L(-s) and straight-line holomorphic gluing.
The continued transform has a negative real residue at s=-1, equal to
-2*c*L(1), with c the proved positive unsigned channel mean. Landau transfer
would contradict any eventual lower envelope -k*exp(-u), k<2*c*L(1), and
would force the negative part's exp(u) moment to diverge. This is recorded
with all analytic/admission obligations on sz-critical-correlation-tail-sign.md.
The proof does not need an unproved noncancellation claim at complex zeta
zeros or an assumed critical-line Fourier representation. No Lean theorem
or RH advance is yet claimed.

Continuation checkpoint: the source-residue leaf and the generic
`LaplaceNegativeRealResidue` lemma now pass direct leaf audits. Actual
correlation continuity and L1 admission also passed; a linter-only edit is
queued for its final audit. Product, Mellin, gluing, and tail-sign leaves
are drafts under direct sequential checks. No cofinal-negativity theorem
is claimed until this chain and its axioms are checked. Deep corpus query
`sz-correlation-transform-search` used generation1183417, partial=true,
coverage pending; refresh was incomplete because the background indexer
was running. Its available declarations, candidate lemmas, and source
arguments were inspected. Missing hits were not treated as absence.

Negative-part search (deep, no-refresh, 60 seconds) returned partial
generation1183630; coverage snapshot1183632/current1183633 inventories
64277 files but has substantial pending/stale compiler metadata. The
candidate and source-argument lists include `WeilLagFunctionPositivePart`
and `TailMeasureLaplace`. The former concerns the different Weil lag
function and assumes the decisive admission; it does not bound this
literal autocorrelation. The latter is part of the already checked Landau
carrier mechanism. No theorem for this correlation's negative exponential
mass was supplied by those hits; the candidate proof remains the real-pole
positive-part argument recorded on the card.

Completed mathematical step: all seven new leaves pass clean direct
`lake --old env lean <leaf> -o <leaf.olean>` audits and are wired. The actual
correlation C is negative beyond every cutoff, falls below -k*exp(-u)
cofinally for every k<kappa, and max(-C,0) is not integrable with weight
exp(u). Here kappa=2*criticalCorrelationUnitMean*Re(L(1))>0. This follows
from the physical imaginary-axis product, local holomorphic gluing, the
negative real residue, and Landau with the compact head retained. No
nonreal-zero noncancellation premise is used. Seven intermediate axiom
queries are standard only; the four terminal queries are running.

Formal lint ran after all seven imports were wired. Exit1 is solely the
same ten unrelated unreachable modules previously recorded:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. No new leaf
is listed. No forbidden-declaration error was reported.

Hard frontier assessment: these results close eventual correlation
positivity and finite negative exp(u) mass, not the original-cutoff coupled
Tatuzawa forcing/Wronskian estimate. Next attacks must retain their signed
coupling; replacing it with an absolute correlation envelope repeats the
closed shortcut. Deep joint-forcing search generation1183816 completed
(partial=false), but its snapshot1183820 still has pending/stale compiler
metadata. Available candidates are generic Wronskian energy inequalities
and different theta/prolate sources; none supplies the literal SZ bound.
The next step requires a narrower source query, followed by an actual
paper attempt on the coupled form, not another imported conditional
energy inequality.

Final tail axiom audit completed: all four terminal theorems use only
propext/Classical.choice/Quot.sound, bringing the checked public chain to
eleven queries. Card moved to
`docs/drafts/pipeline/5-failed/sz-critical-correlation-tail-sign.md` with
the exact positive survivor; frontier map SZ updated. Completed owned
search/API scratch files removed, valid leaf oleans retained. Serena
memory `rhtower/sz-critical-correlation-tail-sign-2026-10-02` records the
result and unchanged hard coupled bound. A narrower actual Tatuzawa
source query is running for the next paper attack.

Narrow Tatuzawa query completed (partial=false, generation1183839,
coverage snapshot1183844 with pending/stale compiler enrichment). It
recovers the literal Möbius/divisor inversion and the exact coprime-column
transport, not a signed mixed estimate. Rechecked `tatuzawa_iseki` and
`abs_floorSummatory_psiDefect_le` in source. Their unconditional identity
and unsigned square-root forcing bound remain exactly the known inputs.

Paper attempt after the tail theorem: in log time set
P f(t)=sum_k Lambda(k)/sqrt(k)*f(t-log k), with the original causal cutoff.
The forcing operator is (t+P)(d/dt+1)f. Since the source vanishes at t=0,
commuting the derivative gives (d/dt+1)((t+P)f)-f, retaining the terminal
trace. Substituting the exact Möbius source moves (t+P) onto the unit-source
log clock, so the remaining pairing is between the same Möbius convolution
of U and of its log-weighted source. This does NOT establish coercivity:
symmetrization leaves signed mixed Möbius factors and the cutoff trace.
Treating this as an arbitrary-source positive quadratic form would repeat
the already refuted source-response passivity shortcut. No new bound or
Lean wrapper is claimed. The next conjecture must estimate this literal
coupled quadratic form, with its trace and signs, rather than asserting
an unsupported sign for its individual correlations. RH remains open;
the goal stays active.

## Continuation — source resonance and the original quadratic cutoff

Assessment: the preceding cofinal-correlation theorem is audited new
knowledge, but the present continuation has NOT improved the hard
original-cutoff Tatuzawa forcing/Wronskian bound. No Lean module was
added, no new audit is claimed, and no route is retired here.

Rechecked the actual source formula in `DivisorSourceEntire`:
`B(s)=-zeta'(s)-zeta(s)^2+2*gamma*zeta(s)` away from 1. There is no
additional rational term. Also rechecked the Abel subpower receiver:
RH already implies boundedness of the normalized Abel source, with no
zero-simplicity premise. A speculation that its quadratic clock-energy
target might force simplicity was therefore unsupported and is discarded.

Paper test of iterating the signed Tatuzawa identity: put
`F=B/(s*zeta)`, `g=B/s`, and `T=-d/ds-zeta'/zeta`. Direct differentiation
on the regular set gives `T^k F=(-1)^k*g^(k)/zeta`. At a zero rho of
multiplicity m (rho nonzero and different from 1), B has order m-1.
For `0<=k<m`, the leading pole coefficient is
`(-1)^(k+1)*m! / ((m-1-k)!*rho)` with pole order k+1; thereafter
the pole order is at most m. In particular, simple zeros do not produce
increasing pole order under this iteration. For m=1 the first response
ratio is `1/rho+2*gamma-zeta''(rho)/zeta'(rho)`. No sign estimate for
this ratio was proved. These are local paper calculations, not a new
Lean theorem or a no-go closure. They explain why repeated log-clock
identities alone supplied no coercivity.

Other attempted mechanisms, with their unresolved steps retained:

- Moving the log clock through the exact Mobius convolution leaves a
  mixed product of the same signed convolution applied to U and to its
  log-weighted source. Both the mixed signs and terminal trace remain.
- In the original finite energy, grouping d=g*a and e=g*b leaves the
  signed coprime quadratic form multiplied by
  `sum_(g<=T/y,(g,a*b)=1) mu(g)^2/g`. Positivity of this counting factor
  does not permit its pointwise upper bound inside the signed sum.
  A density approximation also needs the growing-modulus remainder
  uniformly through the boundary T/y near 1. No such estimate was proved.
- Replacing the prime error in a causal prime split by its own Abel
  source does not automatically improve the growth exponent: products
  at complementary multiplicative scales retain that same exponent.
  A signed amplitude estimate, rather than iteration of absolute
  envelopes, remains necessary.
- Reflection through `zeta(s)=chi(s)*zeta(1-s)` gives, at regular points,
  `B(s)+chi(s)*B(1-s)=zeta(s)*(4*gamma-chi'(s)/chi(s)
    -zeta(s)-zeta(1-s))`. At mirrored zeros this cancels the leading
  source values; no positive reflected Green pairing follows. The
  actual source-paired estimate has not been replaced by a pointwise
  modulus or phase assertion.

Corpus searches inspected candidates, source arguments and proposed
ingredients. Generations1183878 and1183978 completed; 1184027,1184047
and1184072 were partial. Coverage/compiler enrichment was pending or
substantially stale, so hits are source evidence and misses are not
absence proofs. The latest reflection query also recovered the exact
CCM short residual-pair identity. The frontier map already records its
uncontrolled signed off-diagonal; that identity is not a new producer.

Next hard target remains the actual complete quadratic form at the
original cutoff. In channel notation it requires control of the sum
of ALL signed common-divisor cross components against the already
proved quadratic diagonal, or an equally strong integrated bound.
Another identity, isolated sign, completed-support norm, or local-pole
classification does not discharge this estimate. No RH conclusion has
been obtained; the goal remains active.

## Continuation — causal residual pairing and zero-mass bootstrap

Previous turn: no progress on the hard bound. This continuation also
has no new original-cutoff estimate or Lean theorem. The tests below
are paper attempts, not completed no-go claims or route retirements.

Revalidated `CCMPrimeDeficitResidualPairing`, `ResidualReflection`,
`ShortQuadraticWork`, `DivisorSource` and `CoprimeBalance` in source.
The residual reflection is exact at every cutoff; short-tail causality
does not bound its retained action. The short quadratic work is already
an RH-equivalent producer target. Its uniformly bounded elementary
correction is not a bound for the work. Likewise the bounded complete
coprime balance retains the unknown signed cross term with opposite
sign to the critical energy. None of these existing identities closes
the SZ source estimate.

Tested a causal inversion bootstrap using the actual zero boundary mass.
Write a(t)=exp(-3t/2) A(exp t), b(t)=exp(-3t/2) U(exp t), with both zero
before source birth, and

K a(t)=sum_n a(t-log n)/n,
M_m v(t)=sum_(d<=m) mu(d)*v(t-log d)/d.

The literal source relation is b=K a. The corpus supplies integral a=0
and integral t*a(t)=-H/3, H=divisorHarmonicBoundary>0. At the paper
level the admitted positive-side Mellin identity and its limit at zero
give integral b=H/3. Thus the causal remainder a-M_m b has mass
`-(H/3)*sum_(d<=m)mu(d)/d`; zero mass is not automatically preserved
by the proposed iteration. For m=1 the mass is explicitly nonzero.
An absolute Fubini interchange with sum 1/n is NOT justified here:
the stated mass calculation instead uses positive damping and the
already admitted first moment before taking the limit.

Subtracting the divisor mean directly introduces the unknown future
tail into a finite-clock estimate. Consequently its norm is not paid
by earlier-clock values alone. The earlier positive-primitive result
uses a different weight and does not establish a sign for this tail.

Repair tested: let Delta_h=I-shift_h and take h>=log(m+1). Then
R_m=I-M_m*Delta_h*K and g_m=M_m*Delta_h*b give the exact formal
causal equation a=g_m+R_m*a. The remainder keeps a delay of at least
log(m+1), and Delta_h preserves zero total mass. This repairs the
mass/causality defect, but does not prove a critical norm contraction.
For integer q>m and h=log q, the residual kernel still has coefficient
-1/p at every prime p>q. Its absolute mass weighted by exp(t/2)
therefore includes sum_p 1/sqrt(p), which diverges. This rules out
the proposed absolute-kernel estimate, not a source-paired estimate.
Regularity-based cancellation also needs a norm preserved under the
iteration; differentiating the source introduces its arithmetic jumps,
and no closed critical regularity estimate was obtained. Finite delay
alone cannot supply it.

The remaining useful test of this repair would bound the COMPLETE
signed finite sum of iterates acting on g_m, at the original clock.
Bounding each kernel by absolute mass or each derivative independently
repeats the failure above. The sum is an unproved candidate, not a
replacement definition of success or an additional premise.

Search1184106 was partial; narrowed search1184117 completed;
search1184187 was partial. Candidates, source arguments and ingredient
sets were inspected. Compiler metadata remains predominantly pending
or stale, so no result is treated as newly audited. The retrieved
`CCMUnitRieszMobiusCausalVirial` explicitly contains finite algebra and
no estimate; it was inspected and not counted as progress. No Lean
source, umbrella or build artifact was changed. RH remains unresolved.

## Continuation — complete renewal depth and coupled metric response

Previous turn: no progress on the hard original-cutoff bound. Current
turn likewise proves no new estimate or Lean theorem. Finite renewal
termination was revalidated in `CCMPrimeDeficitEulerResolvent`; it is
explicitly independent of any critical norm estimate.

Paper test retaining every signed renewal depth: for the previous
notation and h=log q, put
`P_m(s)=sum_(d<=m)mu(d)/d^(1+s)` and `d_q(s)=1-q^(-s)`.
The remainder multiplier is `1-P_m(s)*d_q(s)*zeta(1+s)` and the forcing
transform is `P_m(s)*d_q(s)*B(1+s)/((1+s)*(3+2*s))` on the admitted
right half-plane. Assembling the complete quotient cancels P_m*d_q
and returns the original actual Abel transform. It leaves exactly
the same zeta denominator. At a nontrivial zero, the source identity
B=-zeta'-zeta^2+2*gamma*zeta retains the pole with multiplicity-dependent
residue; zeros of the added finite multiplier cancel on both sides.
Thus no pole exclusion or source annihilation was gained by this
regrouping. The finite-clock signed bound remains an additional
mathematical obligation, not a consequence of geometric termination.

The corpus's unit-Riesz all-grade collapse was also inspected directly:
the completed Mobius/log divisor sum is the negative positive
von-Mangoldt renewal. All the remaining cancellation is with its
polar continuum and endpoint, not with an unprocessed random Euler
factor. Separate positivity of prime atoms therefore supplied no bound
for their centered critical action.

Returned to the literal aperture source to test a different estimate.
Rechecked `CCMSuzukiCrossApertureCurvatureLeakage` and the source,
Fourier and Wronskian definitions in
`CCMSuzukiCrossApertureProjectiveWronskian`. The shell and metric response
occur in their exact signed combination. A tempting inverse-shift
bound is unsupported: `boundedPerturbedFormShift B=norm(B)+1`, so the
generic lower estimate for B+shift*I has margin 1, not margin comparable
to norm(B). One cannot infer that the physical response is O(1/shift)
and thereby pay the growing shift gap. Improving that margin for the
actual completed source, or bounding its coupled response directly,
still requires the missing source estimate. No altered coercive shift,
source norm, or assumed denominator lower bound was inserted.

Search1184232 returned partial results; search1184281 completed.
Candidates, source arguments and proposed ingredients were inspected;
coverage snapshots still report predominantly pending/stale compiler
metadata. The suggested Wronskian/anchor-jet ingredients are identities
and conditional leakage implications, not a cofinal source bound.
No new leaf or umbrella edit and no build was warranted. These failed
attempts do not retire SZ and are not an RH proof or falsification.

## Continuation — coupled Riesz energy and actual parity comparison

Route SZ. The hard obligation remains a cofinal bound on the complete
original-cutoff signed forcing and weighted physical shell leakage.
Neither the previous turn nor this turn supplied that bound. This turn
tested the joint metric/shell equation, then its actual even/odd source
components; it did not count another identity as frontier progress.

Paper calculation, not a new Lean theorem: write q_a for the actual
coercively shifted form, c_a for its prescribed shift, J for its physical
embedding, and u_a for a Riesz response to a retained-consistent source.
For a <= b, write i u_a for the existing form-domain extension and
d=u_b-i u_a. The already formalized retained-block and source equations
give

    q_b(i u_a,i u_a)=q_a(u_a,u_a)+(c_b-c_a)*||J u_a||^2,
    q_b(u_b,i u_a)=q_a(u_a,u_a).

Hermitian expansion therefore gives the real diagonal identity

    q_b(d,d)=E_b-E_a+(c_b-c_a)*||J u_a||^2.

No sign of c_b-c_a was assumed. The additional term is physical metric
work; form orthogonality of the metric-renormalized shell does not remove
it. It is also incorrect to replace the response bound by O(1/c_a):
the generic shifted coercivity margin is 1, as recorded above.

Apply the same calculation to the two actual Riesz responses to cosh(x)
and sinh(x). Let E_a,O_a denote their unscaled covariance energies,
N_e,N_o their physical squared norms at a, and D_e,D_o the q_b squared
norms of their complete increments. Then exactly on paper

    E_b*O_a-E_a*O_b
      = O_a*D_e-E_a*D_o-(c_b-c_a)*(O_a*N_e-E_a*N_o).

This retains both channels and their common aperture. It explains why a
bound on the normalized squared-resolvent difference alone is insufficient:
the signed increment-energy difference remains. D_e,D_o being nonnegative
does not order their weighted difference. These E,O are not the separately
scaled ActualEvenEnergy/ActualOddEnergy definitions: their common raw
deficiency factor must be restored when using that characteristic chart.
No denominator lower bound or normalization cancellation was asserted.

The source-specific comparison attempt used the actual boundary laws in
SuzukiTaV2ActualBoundarySourceLaw, the concrete cosh/sinh response vectors,
and the complete form diagonal in CCMRestrictedWeilFriedrichsOperator.
The boundary repairs have unequal coefficients a*tanh(a), a*coth(a).
Substitution retains a signed combination of two complete form values;
it does not make either prime, polar, or Gamma term separately positive.
Discarding this combination would discard the desired source estimate.

Relevant corpus obstructions were checked for scope. The positive-
resolvent/parity no-go controls generic position tilts, not this exact
cross-aperture source determinant. The archimedean parity Hankel kernel
has arbitrarily large negative subspaces; the prime-seam file proves a
finite packet mechanism with both signs. Neither result proves failure
of a comparison on the selected actual Riesz responses. They do preclude
assuming a general positive Hankel carrier in that proof. Consequently
the actual-source comparison is still open, not a falsified conjecture.

A further attempted way to pay metric work was source spectral localization:
small completed prime-polar action on an exponential source might force
its resolvent to behave like division by c_a. Even if a small relative
action were established, the inverse weights the spectral region near
the shifted floor. A second-moment estimate alone leaves that small
spectral mass multiplied by the inverse gap; it supplies no cofinal
relative response bound. Repeated action was not justified: the actual
arithmetic source has moving prime jumps and Gamma boundary terms.
No unproved spectral localization or operator-domain iteration was used.

Next proof obligation within the same route: estimate the JOINT signed
quantity O_a*D_e-E_a*D_o-(c_b-c_a)*(O_a*N_e-E_a*N_o) from the actual
prime-polar-Gamma source equations, with its physical source normalization
and common cutoff. Merely naming this expression, bounding its pieces
absolutely, or proving a generic parity identity would not discharge it.

Searches1184317 and1184383 completed;1184341 and1184419 were partial.
Candidate declarations, source arguments and ingredient sets were
inspected. Compiler metadata is predominantly pending/stale or source-
only; these reads are not new Lean audits. No Lean file, umbrella or
build artifact was changed, and no build/lint rerun was warranted.
No new unconditional estimate or RH proof/falsification was obtained.
The route and goal remain active; no route is retired by this attempt.

## Continuation — matched-pole source bound (in progress)

Previous turn classified no progress. Tested cancellation at movable anchor
c=1/2, where the two source vectors are the literal polar vectors. On each
parity sector, normalizing its source moment to one removes the polar
term by a constant: +2 in the even sector and -2 in the odd sector. This
alone does not control the remaining form or justify a positive inverse.
The complete quantile estimate is o(exp(a)) times physical mass plus
higher Binet energy. The latter is the form's Gamma translation energy,
not an extra squared-operator regularity norm. Its coefficient cannot be
absorbed with coefficient one by substituting epsilon=exp(-a): the
threshold depends on epsilon. These two attempts gave no hard bound.

New concrete paper proof to formalize: the prescribed norm shift is also
coercive after deleting the polar operator. For fixed aperture, modulate
ANY physical vector at a cofinal sequence on which all finitely many
prime-translation phases return to one. Its polar pairings tend to zero
by Riemann--Lebesgue, its mass is unchanged, and its prime quadratic tends
to the original prime quadratic. Thus the scalar-minus-prime quadratic
has absolute value at most norm(full bounded remainder)*mass. No assertion
about Gamma energy under modulation is needed: modulation is used only
to compare bounded operators on the physical Hilbert space.

Consequently the actual shifted form minus its polar quadratic is at
least form norm squared plus physical mass. For the actual Riesz response
to cosh(x/2), reflection makes the sinh(x/2) charge zero. Its polar
quadratic is exactly 2*E^2, while the complete shifted source energy is E.
The proposed unconditional conclusion is E <= 1/2, uniformly in aperture,
with accompanying actual response-norm control. This is an estimate on
one actual source channel, not a replacement definition of RH success.
The odd channel and the full cofinal signed Wronskian remain open.

Relevant source ingredients verified in CCMPrimePoleSchurModulation,
CCMCoherentGammaModulationRecurrence, CCMRestrictedWeilBoundedRemainder,
and SuzukiTaCoalescingCovarianceTangent. The similarly named
SuzukiKroneckerParityFloor concerns a different phase problem and is not
an ingredient. Searches1184500/1184529 partial;1184501/1184586 completed,
with source-only/pending/stale compiler metadata. New proof not yet
Lean-audited at this checkpoint.

The bounded-remainder recurrence leaf now passes its direct foreground
Lean audit. The matched-source leaf is being repaired at real/complex
self-inner-product coercions; no mathematical premise was added.

Next hard conjecture, based on the actual localization corpus: for the
selected odd shifted Riesz response v, use M(x)=tanh(x/2). Its product
with v is even, and its cosh charge is exactly the odd source energy O.
The shifted form q then has q(Mv,Mv)>=2*O^2. Its other source pairing is
Re q(v,M^2 v)=O-Re <sinh(x/2)/cosh(x/2)^2,v>. The latter source is uniformly
L2 on the whole line, so the last term is bounded by a constant times
sqrt(O), using the already available shifted physical coercivity.
Thus an aperture-uniform upper bound D<=K*O for the COMPLETE signed
localization defect D=q(Mv,Mv)-Re q(v,M^2 v) would bound O uniformly.
This is a new attack obligation, not a proved estimate or an RH criterion.
Form-domain multiplication/approximation must also be justified before
using the smooth-source identities at the completed response.

The pole contribution to D is itself 4*O^2-2*O*Re<g,v>, with
 g=sinh(x/2)/cosh(x/2)^2. The discrete prime term must cancel this term;
dropping it or using independent absolute bounds cannot close the proof.
No pointwise sign of v on a half interval has been proved. The literal
continuous Gamma/pole kernel has both signs, so no Markov contraction
for the full form was assumed. The conjecture remains open, not refuted.

Search1184772 (partial, pending coverage) supplied actual parity/source
identities but no matching bound. Search1184788 (partial, pending coverage)
supplied CCMThetaArithmeticLocalization, CCMThetaLocalizationCrossBounds,
CCMThetaPrimeLocalizationMoment and their sign witnesses. Both candidate
and source-argument sections were inspected; ingredient sets were empty.
All retrieved compiler metadata was source-only. Exact source reads show
that the known absolute localization estimate retains aperture-dependent
prime and continuous second moments; it is not the required D<=K*O.

Search1184816 (partial, source-only, pending coverage) did not supply
positivity of the actual odd response on a half interval. Its candidate
and source-argument sections were inspected; no ingredient set was given.
The modulus theorem in SuzukiLimitingLogIrreducibilityCore is for the
unit-interval finite-part logarithmic energy with kernel 1/|x-y|. It is
not a contraction theorem for the present full prime-polar-Gamma form.
No transfer from that different operator was made.

Even uniform energy, if audited, is not a weighted shell telescope:
D_i=E_(i+1)-E_i+(c_(i+1)-c_i)*N_i still retains the last term. Bounded
E_i alone does not bound its sum. The new estimate is on an actual source
channel; no normalized V2 energy, completed formation production, or
full cofinal Wronskian estimate has yet followed from it.

Both leaves now pass their direct foreground audits, including the final
SuzukiMatchedEvenSourceBound run (exit0, no warnings). The source energy
is unconditionally <=1/2 and the sum of squared form and physical norms
is <=1/8, for every positive aperture. The more general polar-free
shifted coercivity inequality is also proved. Both leaves are wired into
the umbrella; no umbrella/full build was run. Axiom queries for all six
public theorems and the formal lint gate are running.

Elaboration lesson: `norm_sq_eq_re_inner` applied to each explicit vector
and then used as a typed equality avoids competing complex field/norm
instance reductions in this import graph. All three required instances
were verified together in a scratch leaf. No heartbeat change was used.

Formal lint exited1 on14 unrelated unreachable modules, with no forbidden
new declarations or reachability error for either new leaf. Current names:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMFiniteEulerDenominator,
CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, ThetaCuspCurvatureDefectGrowthTransferEnvelope,
ThetaCuspCurvatureDefectGrowthTransferFlow, ThetaMovingShellFirstOrderPhase,
ThetaTailTwoPointPositivity, ZetaZeroDensityPowerSaving. These concurrent
out-of-scope files were not modified. Global lint is not green.

A further exact paper calculation sharpens the odd-source obligation.
For M(x)=tanh(x/2), set g(x)=v(x)/cosh(x/2)^2 (the square is essential).
Then
 (M(x+h)-M(x))^2*v(x+h)*conj(v(x))
   = sinh(h/2)^2*g(x+h)*conj(g(x)).
Thus, writing F(h)=sinh(h/2)^2*apertureAutocorrelation(g,h), the complete
prime-polar localization defect is exactly
 -Re(criticalMellinStieltjesPairing(a,F)).
The factor agrees with the corpus convention q_polar-prime=2*Re(pairing
of the ordinary autocorrelation). This leaves the same physical cutoff.
For a smooth admitted F with zero terminal value, the existing Stieltjes
integration-by-parts theorem identifies this defect with
 Re integral criticalMellinCompletedError(h)*F'(h) dh.
Differentiability of the actual completed response's F is NOT assumed.

The Gamma-only localization defect admits an aperture-independent physical
mass bound on paper: M is bounded and Lipschitz, and its squared increment
is at most min(h^2/4,4); the positive Gamma jump kernel is integrable
against this weight. The same estimate gives form-domain stability of M.
These analytic details are not yet formalized. The remaining hard bound
is on the signed critical-Mellin pairing for the selected g, not on Gamma.
Merely bounding |F| uniformly fails to control a signed carrier with
unbounded variation. Stronger decay of the actual response or cancellation
against its source equation is still required; neither has been proved.

Search1184859 was partial with pending coverage and source-only compiler
metadata. Candidate lemmas and source arguments were inspected, with no
ingredient set. CCMPolarPrimeStieltjesAutocorrelation supplies the precise
pairing normalization and the conditional differentiability/endpoint
requirements above. No new generic localization wrapper was formalized.

Final checkpoint: all six public theorem axiom queries passed in one
foreground `lake --old env lean /tmp/sz_matched_even_axioms.lean` run,
exit0. Each uses exactly propext, Classical.choice, Quot.sound. No new
axiom, sorry/admit, computation, heartbeat increase, full build, or
umbrella build. The complete paper proof and certificate are now in
3-formalized/sz-matched-even-source-bound.md; the route map records the
actual even-channel estimate and its limitations. This continuation made
real progress on one actual source channel. Odd signed localization,
weighted shell leakage and the RH implication remain unsolved. Goal active.

## Continuation — selected odd localization and weighted source equation

Previous turn: progress, with the two audited even-response leaves and six
standard-axiom queries. Current source re-read confirms those contracts.
No RH claim follows from them. This turn attacks the actual odd source,
not a new norm constant for the already bounded even source.

Tested a uniform multiplication estimate for M=tanh(x/2) in the actual
shifted form. Such an estimate would imply the required selected odd
localization bound and hence bound its source energy. The direct proof
fails: q(v)>=H(v)+N(v), while the upper bound for q(Mv) retains
2*norm(B_a)*N(v). Boundedness/Lipschitz continuity of M controls its Gamma
commutator but does not remove this aperture-dependent factor. This is
failure of that proof, not a counterexample to the selected bound.

Re-examined the complete quantile Gamma estimate and midpoint-odd normal
form. The known coefficient is epsilon*exp(a)*(N+H), not
epsilon*exp(a)*N+epsilon*H. Its negative H coefficient cannot be absorbed.
The midpoint-even energy cancels exactly, but both remaining positive
costs still have to be paid by the phase-sensitive square. No sign was
inferred from the square alone. Search1184906 partial/pending/source-only,
with candidate/source-argument sections inspected and no ingredient set.

Search1184891 returned source-only candidates and a proposed, unverified
ingredient set based on the Fu and rectangular autocorrelation examples.
Those examples do not identify the actual selected odd response. Its
proposed mapping is not a proof of the needed Stieltjes estimate.
Coverage snapshot1184896/97 has most compiler metadata pending or stale.

A source-side weighted estimate is being tested next. Put
w(x)=sech(x/2)^2 and g=w*v. The whole-line Gamma commutator with w has a
fixed bounded-multiplier estimate. In the bounded arithmetic term,
left multiplication by w reduces the support-compatible prime transport
weight: shifts h<=a cost at most their original weights, and shifts h>a
acquire the factor bounded by 4*exp(a-h). Thus a Chebyshev bound suggests
norm(w*T_a)=O(exp(a/2)); norm(w*P_a) has the same scale. The selected
source w*sinh(x/2) is uniformly L2. The weighted Riesz equation would
therefore yield
 (c_a-C)*norm(g) <= C*(1+exp(a/2)*sqrt(O_a)).
This estimate is not yet formalized; its use still requires a lower bound
for the actual shift c_a and a rigorous form-domain commutator argument.
It is a candidate for deriving response localization from the source,
not an assumed regularity bound. Interior localization alone would still
leave interactions between opposite boundary collars; that remaining
signed prime-polar contribution must be controlled, not discarded.

The entry-clock alternative was checked on the exact source contracts,
not inferred from their names. The odd chamber minimum principle requires
the two endpoint values; it does not prove integer-entry positivity.
The entry-age identities retain one common positive age loss in both
parities. Positive odd entry slopes alone do not pay this loss. The new
SHIFTED even covariance bound is not positivity of the UNSHIFTED even
pole compression, so it cannot discharge the even premise of the
integer-entry RH criterion. Search1184922 partial/pending/source-only;
candidate and source-argument sections read, no ingredient set.

Weighted-resolvent search1184930 also partial/pending/source-only. It
returns exact source bridges and localization counterexamples, not the
needed bound for the selected response; no ingredient set. The left-
weighted arithmetic operator estimate proposed above controls interior
mass only. The target F=sinh(h/2)^2*C_g(h) cancels the sech weights at
opposite boundary collars, so this interior estimate does not control
the large-lag Stieltjes pairing. It will not be formalized as a claimed
solution to that hard bound.

Further paper test: reflection splits the finite prime operator into
same-half transport and a cross-half Hankel operator. Same-half transport
sees only shifts up to a, while cross-half transport retains shifts up
to2a. Its nonnegative kernel does not make its quadratic form positive
semidefinite, nor does it give positivity of the odd inverse response.
An alternating-Neumann comparison would require an actual superharmonic
source inequality (operator applied to the positive source <= scalar
source); spectral-norm control alone is not that pointwise inequality.
No such inequality for the actual prime-Gamma source has been proved.

Classification of this turn: no new hard bound and no new Lean theorem.
The failed arguments identify the same unresolved source-dependent
cross-boundary pairing; none falsifies RH or the selected odd bound.
Next attempt must estimate that pairing directly, retaining the actual
Riesz normalization and Gamma term, rather than formalizing an interior
estimate or another equivalent criterion. No source-code changes, builds
or lint reruns were needed. Searches terminal; owned search files cleaned.
RH goal remains active.

## Continuation — bounded-variation iterates of the actual bounded remainder

Route SZ; no new hard estimate in the previous continuation. New paper
candidate: bound the odd matched-source energy by a finite approximate
inverse of A=c_a I+B_a, retaining Gamma through q>=A and q>=physical mass.
Here B_a=kI+P_a-T_a, c_a=norm(B_a)+1, H_a=B_a/c_a, and p=sinh(x/2)
on [-a,a]. All claims below are conjectural dependencies, not certificates.

Seek c_a>=m*exp(a), total variation of the full truncated convolution
measure for B_a <=C*exp(a), and a Fourier multiplier cancellation
sup_{|xi|<=exp(K*a)} |Bhat_a(xi)| <= C*exp(a-c*a^delta), delta>0.
The last bound needs a uniform twisted von Mangoldt prime number theorem
with its main term. Unweighted integer phase sums and log-ratio Vaughan
phases do not supply it. The corpus polynomial-frequency Moebius twist
rate gives a contour-proof blueprint, not the missing Mangoldt theorem.

If zero-extended BV iteration satisfies Var(H_a f)<=C0*Var(f), then
Var(H_a^j p)<=C0^j*O(exp(a/2)). Fourier tails beyond R=exp(K*a) are
bounded by Var/sqrt(R). Crucially R stays fixed while j grows; increasing
the frequency radius at every iteration would destroy the rate. For
n=O(a^(1-delta))=o(a), variation growth exp(O(n)) can be absorbed by R.
Low-frequency cancellation then gives an exponentially small residual
H_a^n p and a bounded geometric sum of the earlier norms. This seeks
many-moment control, not the previously insufficient second moment.

Set u_n=(1/c_a)*sum_{j<n}(-H_a)^j p and r_n=(-H_a)^n p. For the actual
Riesz response v, energy E=q(v)=Re<p,v>, square completion for A yields
 E <= <A u_n,u_n> +2*norm(r_n)*sqrt(E).
Since norm(A)<=2*c_a, norm(u_n)<=C*norm(p)/c_a and norm(p)^2=O(exp(a)),
the conjectured dependencies would give E=O(1). This does not iterate
Gamma or assume differentiability of the completed response. It still
does not settle canonical V2 normalization or weighted Wronskian leakage.
Next work: inspect exact full-main-term contour contracts and test the
uniform multiplier assertion for unavoidable low-frequency obstructions.

The multi-moment argument admits two substantial simplifications. First,
only qualitative uniform cancellation on each fixed polynomial frequency
range is required. Fix a sufficiently small contraction epsilon, take
n=ceil(a), and choose the fixed Fourier radius exp(K*a) large enough to
absorb C0^n. This produces exponentially small residuals without asking for
a particular subexponential rate. A fixed polynomial smoothing parameter
D=(log N)^2 in the corpus free-width Mangoldt estimate gives high-frequency
little-o between a sufficiently large power of log N and N^K. Below that
split, the existing ordinary PNT exponential remainder times the frequency
and its Abel integral is little-o. Weighted partial summation then gives
the required half-density multiplier cancellation; its smaller prefixes
must be discarded or bounded separately before applying uniform ranges.

Second, the iterates can be treated as finite sums of interval-truncated
exponentials with slopes +/-1/2. Translation and interval compression
preserve this class; the rank-two polar operator does too. The sum of
absolute coefficients times the maximum of each exponential on its
interval controls both sup norm and Fourier tail. Translation preserves
this budget and compression decreases it. The polar map costs O(exp a),
as does the finite prime coefficient mass. Thus normalization by c_a gives
a fixed per-iterate budget factor. This supplies a concrete alternative
to constructing a general BV convolution space.

The shift lower bound itself has a paper proof with no PNT input. For
f=h_++h_-, norm(f)^2=4*(sinh a+a) and <Pf,f>=8*(sinh a+a)^2. Both B's
quadratic and (B-P)'s quadratic are bounded by norm(B)*norm(f)^2, the
second by the audited phase-recurrence theorem. Subtraction forces
norm(B)>=sinh a+a, hence exp(a)<=2*c_a, including the actual interval
normalization. New leaf CCMRestrictedWeilPolarShiftLower is being audited;
this is a prerequisite of the iterative source argument, not odd control.

Exact candidate for the arithmetic dependency: use the already proved
MenonHarmonicFullFrequencySchedule majorant, with ambient X=exp(K*a).
Its logarithmic frequency floor is (log X)^311; it tends to zero uniformly
for integer prefixes between exp((log X)^(19/20)) and exp((log X)^2).
All prefixes between exp(a) and exp(2a) lie in this range eventually for
fixed K. Apply the free-width *von Mangoldt* prefix bound directly (not
the unweighted prime-polynomial receiver). Above the logarithmic floor,
partial summation by n^(-1/2) has no extra frequency factor, since the
prefix already includes n^(-i*tau). The discarded prefix n<=exp(a) costs
O(exp(a/2)), which is o(exp(a)). The continuous main term is also small
in that frequency range. Below the floor, direct partial summation against
the ordinary PNT remainder costs only a fixed power of a, absorbed by the
existing exp(-sqrt(log N)/960000) error. The second polar exponential and
the scalar remainder are O(1). Together these give the desired multiplier
little-o(exp(a)), if the two uniform prefix transfers are completed.

Research1185057 (BV),1185092 (shift),1185116 (symbol) were partial and
returned source-only candidates. The BV suggested ingredient set does not
give the required iterated-source tail bound; no ingredient set was
returned for the shift or symbol searches. The Mangoldt search also
returned the actual free-width theorem as a source argument. Relevant
contracts have been read; none of these searches is a compiler audit.

Scope check against earlier log: bounded shifted source energies alone
do not control the joint expression O_a D_e-E_a D_o-delta(c)(O_a N_e-E_a N_o).
This iteration mechanism must ultimately be tested against that signed
Wronskian and against shift removal. It is not a new RH criterion or a
proof that the canonical norm shift identifies Xi. The paper-only earlier
parity-locking obstruction remains relevant and has not been silently
discarded.

### Recovery and weighted-tail transfer, 2026-10-02

Interrupted foreground prefix audit and search had missing session handles,
no remaining owned process, no prefix olean, and an empty search output.
Restarted only after those checks. The first recovered audit exposed an
algebra-conversion tactic failure, not a mathematical counterexample.
A diagnostic leaf audit is running; no completed-prefix claim yet.

Search1185272 (polynomial Volterra) was partial with coverage pending;
its retrieved source arguments and candidate lemmas did not supply the
needed continuous rate transfer. Search1185273 (half-density prefix) was
also partial/source-only, with no proof ideas or ingredient sets. It
returned the newly written prefix statement as source only, so that hit
is explicitly not independent evidence that the statement compiles.
The useful existing contracts are Finset.sum_Ioc_by_parts and the audited
corpus sum_one_div_sqrt_le. They give a direct discrete Abel proof that
linear uniform prefix cancellation transfers to square-root-weighted
tails, without a frequency loss. The planned actual theorem retains the
whole Mangoldt sequence and every intermediate prefix in the window.

The complete Mangoldt uniform-prefix leaf now passes the required direct
`lake --old env lean ... -o ...` audit (foreground session97909, exit0,
no warnings/output), after explicitly discharging a definitional real-order
instance equality. It is wired into the root RHTower umbrella, without
building that umbrella. No RH assumption is present in its statement.
The weighted-tail scratch proof is now being checked against that olean.

The half-density transfer scratch passed (session21208). The final leaf
Sieve/VonMangoldtTwistHalfDensityWindow, including the complete retained
head, passes its direct audit (session34770, exit0, no warnings/output).
Its two public statements control the actual weighted tail and actual
complete weighted Mangoldt prefix uniformly over the growing window.
The only repair after the scratch pass was normalizing Nat.succ notation
for the exact prefix partition. Both arithmetic leaves are now wired.
The shift and prefix axiom audit (session35025) returned only propext,
Classical.choice and Quot.sound. Half-density axiom audit is in progress.

Lint session27472 exited1 on eleven unrelated unreachable leaves, listed
in P3:sz-bounded-remainder-arithmetic-inputs. No new owned leaf was
reported. This is not a globally green lint result. No full build,
numerical experiment, heartbeat increase, subagent, commit or push ran.

Search1185400 was partial/coverage pending, and returned the actual
SqrtExpDecay theorem as source-only (no ingredient set). A useful further
paper simplification: with J(h)=integral_0^h |E|, the completed-error
identity yields |D(h)|<=3+|E(h)|+J(h)/2 and
integral_0^h |D|<=3h+(1+h/2)J(h). Only J needs the half-cut PNT argument.
This attacks the missing low-frequency transfer while preserving its
Stieltjes endpoint. It does not supply the signed Wronskian sign.

Half-density public axiom audit session19093 also passed: both statements
use only propext, Classical.choice and Quot.sound. All six public statements
in the three new leaves are now audited. The formalized input card and
route SZ frontier entry record this exact scope. Next: formalize the
all-polynomial weighted absolute primitive J and the completed-error
Stieltjes transfer, then combine both frequency regions before iterating B.
The main RH goal remains active and unresolved.

### Low-frequency source transfer, 2026-10-02

Previous turn classified as progress: three leaf audits, six public axiom
checks, actual prefix/half-density source bounds, and umbrella imports.
Current attack is the missing low-frequency half of the multiplier theorem,
not a new RH criterion. Search1185473 was partial/coverage pending, returned
the actual normalized-Chebyshev PNT rate as a source argument, and supplied
no ingredient set. Source contracts and current-toolchain integral APIs
were checked in scratch; the exponential-power decay theorem is in the
root namespace, not Real. A scratch proof now attacks the actual absolute
primitive J by the moving half-cut and transfers every natural polynomial
weight. Its audit is running. Next weld is the exact completed-error
Volterra identity and its absolute primitive, preserving the Stieltjes
endpoint. Signed Wronskian and shift removal remain open.

Scratch session41850 passes all four actual all-polynomial source limits:
normalized Chebyshev error, its absolute primitive J, completed error D,
and D's absolute primitive. No analytic premise was added. Two routine
unnecessary-focus warnings were removed before creating the final leaf
CCMCriticalMellinPolynomialCancellation; its direct leaf audit is running.
The implementation uses the moving half-cut only once, then the exact
Volterra completion and monotonicity of J. A separate scratch proof now
retains the Stieltjes endpoint and targets uniform polynomial-frequency
cancellation of the actual polar-prime symbol. No actual-response smoothness
has been assumed and no signed Wronskian claim has been made.

CCMCriticalMellinPolynomialCancellation direct leaf audit session80033
passes exit0 and writes its olean. Output includes an advisory from an
internal ring attempt, but no error or linter warning; no heartbeat option
was added. The four public limits are wired in the root umbrella. The
Stieltjes endpoint/polynomial-frequency scratch is being audited against
that exact compiled leaf. The intended final multiplier statement is
uniform over all real frequencies abs(xi)<=(2a)^m, for every natural m.

Stieltjes scratch session10242 passes with no output. It proves the actual
endpoint estimate, uniform exponential-test pairing over abs(xi)<=(2a)^m,
and the corresponding actual polarPrimeStieltjesSymbol bound. The final
leaf CCMPolarPrimePolynomialFrequencyCancellation is now being audited.
The source schedule was checked directly: twoRangeT0 2 100 X=(log X)^311,
twoRangeLx 2 X=log 2+(log X)^2. Thus m=312 eventually covers its boundary
at X=exp(K*a), for each fixed positive K. The required next union must
retain floor(exp(a)) as the small head and floor(exp(2a)) as the original
cutoff, then bound the continuous polar main term in the high range.
No full exponential-frequency multiplier theorem has yet been certified.

Final symbol leaf audit session69404 passes exit0 with no output. Both
new leaves are wired. Seven public axiom queries are running. Lint
session45798 exits1 on eleven unrelated unreachable modules (current list
includes CCMEulerBoundaryQuotient, no longer SoninAnnularDilationNilpotent);
no new leaf was reported, and global lint is not green.

Full-frequency weld search1185668 was partial with stale coverage snapshot
and unavailable semantic coverage; most compiler records remain pending or
stale. It found the exact newly proved low-frequency theorem and the prior
half-density prefix theorem as source-only candidates. Its proposed
ingredient set is insufficient: the zero-frequency identity is 2*D(2a),
not a zero-at-origin assertion, and it cannot extend a polynomial band to
an exponential band. The high-frequency polar integral and exact cutoff
window specialization still have to be proved. No pivot follows from this
failed suggested ingredient set.

All seven new public axiom queries pass (session44288, exit0), with only
propext, Classical.choice and Quot.sound. Both source and symbol leaves
passed final direct audits and are wired. P3:sz-prime-polar-polynomial-frequency
and the route SZ frontier now record the exact advance. The hard next
step remains the literal-cutoff high-frequency polar/Mangoldt union;
truncated-exponential iterate control, actual odd energy, signed Wronskian
and RH remain unresolved. Scratch/search/lint files for this turn are
being removed after their terminal outputs were inspected. No own process
remains active.

### Exponential-frequency union, 2026-10-02

Previous turn classified as progress: both low-frequency leaves and all
seven public axiom queries passed. Current target is the actual multiplier
on every abs(xi)<=exp(K*a), with the original floor(exp(2a)) cutoff.
Search1185711 was partial/coverage pending and returned source-only hits,
no ingredient set. Direct source inspection gives the explicit polar
multiplier formula; for a>=0 and abs(xi)>=1 it yields
abs(polarMultiplier a xi)<=6*exp(a)/abs(xi). This replaces an unnecessary
new continuous-integral estimate. The cosine module must be identified
with twice the real part of the complete half-density vonMangoldtTwist
prefix at -xi, retaining the vanishing zero/one terms. Then specialize
ambient X=exp((K+1)*a), small head M=floor(exp(a)), and N=floor(exp(2a)).
The sublinear logarithmic cutoff exponent19/20 and polynomial split312
supply the two window overlaps. No full-frequency claim yet; names and
exact current source contracts are being checked.

Full exponential-window proof candidate is now in a foreground scratch audit.
The exact phase is vonMangoldtTwist(-xi), because its complex power uses
minus i*tau*log(n). The zero/one terms vanish, so no prime-power term is
lost in passing from Icc(2,N) to range(N+1). For L=K+1, the actual window
conditions follow from (L*a)^(19/20)/a -> 0 and (L*a)^311 <= (2*a)^312
for sufficiently large a. With M=floor(exp(a)) and N=floor(exp(2a)),
sqrt(M)<=exp(a/2) and sqrt(N+1)<=2*exp(a). Consequently the prime cosine
module is at most 42*exp(a/2)+16*eta*exp(a); choose eta=epsilon/32.
The explicit polar numerator gives the high-frequency bound
6*exp(a)/abs(xi). The polynomial-frequency theorem handles the remaining
band. This is the same literal multiplier, with no cancellation hypothesis
introduced. The theorem is still a candidate until its leaf audit passes.

Full-window scratch audit1813 and final leaf audit23736 passed exit0.
The leaf is CCMPolarPrimeExponentialFrequencyCancellation; five public
theorems include the exact cosine/twist identity and the final uniform
exponential-frequency symbol estimate. Root umbrella import is added;
no umbrella build. Five axiom queries are next. Global lint60973 exits1
on thirteen unrelated unreachable modules; the new leaf is not reported.
The unrelated current errors add CCMEulerBoundarySpectralChart,
CCMEulerBoundaryTransition, and ThetaTailOrderedRowMonotonicity relative
to the prior list, while removing CCMEulerBoundaryQuotient.

Next iterate-source searches1185843/1185853/1185899 are partial, with
pending/source-only compiler metadata. The broad first proposed ingredient
set concerns unrelated Mellin tails and is inapplicable. The focused
second search exposes HTGeometry/ExponentialPieceFourierDecay and
CCMRestrictedWeilPolarFourierRegularity. Their actual antiderivative/endpoint
proofs supply the next construction: for z*1_[l,r]*exp(s*x), use budget
norm(z)*exp(max(s*l,s*r)). The Fourier norm is at most budget/(pi*abs(xi)).
A new scratch proof generalizes the corpus piece lemma from integer
frequencies on [0,1] to real frequencies and arbitrary intervals, keeping
the exact endpoint budget needed by repeated shifted and clipped atoms.
It has not yet been audited. No new cancellation hypothesis is needed.

All five exponential-frequency axiom queries91656 passed, standard axioms
only. Frontier and P3 card updated. The next atom scratch23268 passed for
supremum, integrability, exact Fourier integral, and inverse-frequency tail.
Extended scratch30428 also passed exact translation, invariant translated
budget, monotone subinterval budget, and finite-sum Fourier decay. The
latter uses the sum of actual atom budgets without a separate count factor.
Final leaf CCMTruncatedExponentialFourierBudget is now under audit, adding
the exact aperture-intersection identity. No atom-to-Hilbert-operator
closure or odd-response theorem is claimed.

The operator closure should use literal functions with a finite list of
atoms, treating empty clipped intervals as zero. The actual remainder is
kappa*f plus the two crossed exponential rank-one outputs minus the finite
weighted symmetric translates, followed by aperture restriction. Source
inspection confirms this definition exactly in CCMRestrictedWeilBoundedRemainder.
Prove equality with its Hilbert cofunction; do not replace it by an abstract
operator satisfying the desired budget. The full-line Fourier multiplier
identification is likewise still needed for the one-step norm estimate;
search1185899 supplied no verified complete producer. Its hit named
suzukiPolarConvolution concerns suzukiWeilRemainderKernel, not this rank-two
polar operator, so it is not an applicable replacement.

Final atom leaf audit4101 passes exit0 without warnings/errors; all nine
axiom queries42237 pass with only propext, Classical.choice, Quot.sound.
It is wired into the root umbrella. P3:sz-truncated-exponential-fourier-budget
records the exact proved scope. This turn therefore closes the actual
exponential-frequency arithmetic input (five public theorems) and the
nine source-piece budget/Fourier estimates needed for the next iterate
construction. No RH conclusion and no actual odd-energy conclusion.

Final lint10308 exits1 on thirteen unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMEulerBoundaryKernelShell, CCMEulerBoundaryNonFredholm,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ThetaTwoNodePortTransversality,
ZetaZeroDensityPowerSaving. Neither owned new leaf is reported. Global
lint is not green; unrelated changes are preserved.

L2 tail search1186014 is partial with unmeasured semantic coverage and
pending/source-only compiler records. Its suggested ingredient set is not
a proof of this tail estimate: a special smooth cutoff bound plus a
compact Fourier L1 bound does not supply the literal atom-sum L2 tail.
The directly inspected usable equality is
norm_sq_sub_fourierCutoff_central_eq_tailIntegral in
SuzukiHlogCompactEmbedding:131. Combine it with the new pointwise bound
and integration of abs(xi)^(-2) outside [-R,R], yielding
2*V^2/(pi^2*R). SoninDecayTailMellin:84 shows the current
integral_Ioi_rpow_of_lt API; the negative half is reflection. The actual
full-line Fourier multiplier/compression identity and finite atom-list
operator closure still need proofs. These are the next hard-source tasks,
not reasons to abandon the current many-moment conjecture.

All own processes have completed. Scratch, search, and lint files from
this turn are being removed by exact path after results were recorded.

### Literal remainder orbit closure, 2026-10-02

Previous turn is progress: two audited/wired leaves prove exponential
frequency cancellation and exact finite-piece Fourier budgets. Current
source target is actual B/c iterate control, not a new RH criterion.
Search1186086 is partial, source-only, with pending/stale compiler metadata;
its proposed rank-one ingredient set is not an operator action proof.
Direct source search finds ccmApertureCompression_val and
ccmApertureSymmetricTranslation_coeFn (CCMRestrictedWeilPrimeOuterShell),
and the full generic ccmFinitePrimeOperator_coeFn_translation in
PrimeTransportPoleSchurNorm. These are exact existing producers. The
collective prime-band saving is only an operator norm saving, not the
low-frequency source cancellation needed here.

Implementation strategy: an inductively certified finite linear combination
of literal truncated-exponential L2 cofunctions, with additive endpoint
budget. Its constructors are actual zero/atom/add/scalar operations and
budget enlargement. Prove cutoff and translation preserve this class;
then use the actual crossed rank-one polar maps and complete prime sum to
prove closure under B. Construct membership for the actual odd pole source
and every normalized B iterate unconditionally. This avoids any assumed
regularity of the Riesz response. The global L2 multiplier/compression
estimate remains a separate necessary step, followed by Neumann and signed
Wronskian control; RH remains unresolved.

The literal-operator closure proof now covers translations, arbitrary interval
cutoffs (including empty intersections), the crossed polar map, every term
of the complete prime sum, and the actual prescribed-shift normalization.
The root source-orbit theorem has no extra premise: every natural iterate
of B/c applied to (p_+-p_-)/2 has budget C0^n*exp(a/2), where
C0=2*(norm(kappa)+46). Its L2 Fourier cofunction obeys the corresponding
V/(pi*abs(xi)) bound almost everywhere off zero. Current leaf audit is
pending; no claim of a passed final certificate yet. Compiler corrections
so far are coercions, integral syntax, and exact scalar norm normalization,
not counterexamples to the conjecture.

Search1186271 for the multiplier/compression connection is partial;
coverage is pending, all relevant hits source-only, no ingredient set or
proof idea. Its usable hit is
HTGeometry/L2ConvolutionFourierMultiplier.convolutionKernel_op_eq_fourierMulCLM.
Direct inspection also locates:
- CCMPolarPrimeSourceSign.polarFourierTransform_eq_polarMultiplier,
  including the full symmetric integral and exact rational symbol;
- CCMCoherentMidpointFourier's private fourier_logTranslation_ae, proved
  using public MellinL2.fourier_additiveTranslation and
  MellinL2.fourierPhaseMulAux_ae;
- HTGeometry/L2FourierMultiplier.norm_fourierMulCLM_le.
The similarly named CCMRestrictedWeilPolarMultiplier concerns the
*differential* pole-annihilator and is not the desired convolution bridge.

Next exact weld: compressed convolution by
1_[-2a,2a](h)*2*cosh(h/2) equals the actual crossed polar operator;
subtract the complete uncompressed prime translations, retain the scalar
atom, identify the symbol at -2*pi*xi, then split its action by a Fourier
cutoff. No cancellation estimate on arbitrary high frequencies is needed:
the proved finite-source envelope supplies that tail. The integrated-tail
scratch is written with reflection, the exact Ioi rpow integral, and the
existing physical Plancherel cutoff identity. This still does not prove
odd Riesz energy or the signed Wronskian.

Final orbit leaf audit35153 passed (exit0, no warnings), producing its
olean; the root RHTower umbrella now imports it. Eighteen public theorem
axiom queries are prepared. Earlier failed final audits13270/84083 were
an incorrectly focused `convert` proof at the initial odd source, repaired
by separating the definitional vector equality from its scalar budget
identity. No mathematical obstruction was found. Tail scratch96515 is
now the single running own Lean audit.

The remaining multiplier weld can use the existing exact complex Fourier
identity polarFourierTransform_eq_polarMultiplier, not merely a cosine
real-part bound. For profile g_a=1_[-2a,2a]*2*cosh(h/2), its classical
Fourier symbol is polarMultiplier(a,-2*pi*xi). At x,y in [-a,a],
g_a(x-y)=exp(x/2)*exp(-y/2)+exp(-x/2)*exp(y/2).
Using the aperture support of f and the existing L2 inner-product
integral identifies the compressed convolution exactly with the crossed
rank-one P_a. HTGeometry's Schur convolution operator supplies the full
L2 extension and its multiplier identity. Complete uncompressed prime
translations give the matching cosine sum. The arithmetic theorem then
applies on an enlarged fixed exponential band to absorb 2*pi.

Tail scratch96515 exposed only an explicit-argument requirement for the
reflection change of variables: integral_comp_neg_Ioi is a root theorem,
and its function must be supplied as (fun xi => norm(g xi)^2). The repair
is in audit11198. The positive-half inverse-square estimate already
elaborates without an additional integrability premise on g; application
to the actual L2 Fourier vector supplies integrability for joining both
halves and the Plancherel identity.

Tail scratch11198 passed without warnings. The new
CCMFiniteExponentialRemainderTail leaf has two public theorems: the
physical L2 truncation error squared is <=2*V^2/(pi^2*R), and this bound
holds for every literal normalized odd-source iterate with the certified
V_n. It is wired; final direct audit13836 is running.

Post-wiring formal lint66480 exits1 on twelve unrelated unreachable
modules: CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
SoninCutoffMonomialDilation, ThetaMovingShellFirstOrderPhase,
ThetaTwoNodeSignedSturmEnergy, ZetaZeroDensityPowerSaving.
Neither new leaf is reported. Global lint is not green; unrelated work
is preserved. Earlier lint31359 preceded the orbit's successful final
audit and import, and reported that then-unwired leaf as well.

Final tail leaf audit13836 passed (exit0, no warnings). All twenty public
theorem axiom queries52666 passed, each reporting only propext,
Classical.choice and Quot.sound. Both leaves are wired, and the frontier
map and P3 card now record their exact unconditional actual-source result.
The main odd-energy card remains in progress. This turn contributes by
closing actual operator representation and quantitative tail control at
every iteration, including linearly growing iteration counts; it does
not establish the required L2 contraction, odd Riesz bound or RH.

Next attack is the literal compressed multiplier identity above, followed
by the one-step estimate and growing finite recurrence. For the energy
weld, Neumann test vector u need only belong to physical L2: positivity of
A=cI+B and q(v)>=<A Jv,Jv> suffice for
E<=<Au,u>+2*norm(p-Au)*sqrt(E). Do not add a needless Gamma operator-domain
premise for u. The source Riesz equation and exact coordinate transport
must be retained. Signed Wronskian, normalization and shift removal stay
open after that selected source target.

All own audits and lint processes completed. Exact owned scratch/search/
lint paths are removed after this checkpoint; the two valid module oleans
are retained for dependent leaf audits. No subagents, numerical
experiments, heartbeat increases, full builds, umbrella builds, commits
or pushes were used.

### Actual polar convolution weld, 2026-10-02

Previous goal turn is progress: two final-audited leaves close actual odd
orbit representation and integrated Fourier tails, with all twenty axiom
queries standard-only. Current source files and open checklist revalidated.
The next conjecture is the literal operator equality
P_a=Pi_a C_{g_a} Pi_a, where g_a is the sum of the two exponentials on
[-2a,2a]. Its Fourier transform is the existing polarMultiplier at
-2*pi*xi. Prove this for arbitrary aperture L2 vectors using actual
support, rank-one cofunctions and Schur convolution; then subtract the
complete prime translations. This directly attacks the missing one-step
norm estimate. No regularity premise on the response is to be introduced.

Search1186552 is partial, semantic coverage unavailable; relevant records
source-only. Its proposed rank-one tensor/aperture Fourier ingredient set
does not prove this actual crossed-polar convolution identity. Lexical
follow-up finds the exact polarFourierTransform and convolutionKernel
sources already identified. The first scratch audit96606 proves the
literal compressed convolution equality for arbitrary aperture L2
vectors. Audit14447 adds its Fourier symbol and fails only on a real-to-
complex multiplication coercion at the integral identification, now fixed.
Audit80176 also checks exact polar L1 mass and the global convolution norm.
The next extension retains the complete prime translations and the scalar
atom to identify the full actual remainder symbol, not merely its polar
part. This is the operator connection needed for source contraction.

Polar leaf final audit71723 passed, no warnings. It is wired. Nine public
theorems include exact compression, exact Fourier symbol, mass 8*sinh(a)
and norm <=4*exp(a). Full-remainder scratch13698 found namespace errors,
then7210 proved all symbol identities but exposed an over-expanded norm
proof hitting the default heartbeat limit. The proof was rewritten with
explicitly typed scalar/polar/prime operator bounds and a short calc;
no limit increase. Audit33097 checks that optimized proof and the exact
compression identity with subtype coercion made explicit.

Band search1186728 is partial/pending, source-only, with no ingredient
set. Special packet/Kaiser cutoff estimates do not apply to this source.
It does retrieve the newly audited finite-exponential tail. The direct
applicable comparison is mathlib Lp.norm_le_norm_of_ae_le (LpSpace/Basic:340).
Use Fourier cofunctions to compare the actual full remainder applied to
the low-frequency cutoff with a scalar multiple of that cutoff; handle
the complementary source using the global remainder norm and the new
actual-orbit tail. This preserves the physical aperture compression.

Full-remainder final audit23929 passed, no warnings; its leaf is wired.
Seven public theorems prove actual prime/full compression, exact Fourier
cofunctions for full prime/polar/remainder operators, and the global
full-line bounds. No heartbeat increase was needed. The final norm fix
used add_le_add with an explicit reflexive inequality, avoiding a
same-name add_le_add_right shadow with the opposite addition orientation.

The source-contraction scratch now combines those exact identities with
the proven exponential-frequency arithmetic cancellation and the actual
finite-source L2 tail. Its final root theorem states the one-step norm
recurrence for every natural iterate of the actual odd pole source,
eventually in aperture, without an assumed source or response regularity
bound. This is the specific growing-iterate producer required by the
Neumann/Riesz argument. It is currently under Lean audit.

Source contraction scratch79461 and final leaf94938 passed without
warnings. All nineteen public theorem axiom queries82012 passed, each
using only propext, Classical.choice and Quot.sound. Three new leaves are
wired. This turn closes the previously missing actual multiplier and
one-step source norm estimate; no source regularity assumption remains
in the root actual-orbit recurrence. RH and actual odd Riesz energy are
still unresolved.

Final lint29335 exits1 on eleven unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
SoninTimeBandTaylorSourceDirection, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving. None of the three owned new leaves is reported.
Global lint is not green; unrelated changes are preserved.

Next-source search1186806 is partial with stale coverage snapshot and
unmeasured semantic coverage, relevant records source-only. Its proposed
Neumann ingredient set only gives norm-based convergence and positivity;
that does not give the needed aperture-uniform source bound. Direct
source inspection locates the noncommutative finite polynomial identities
geom_sum_mul, mul_geom_sum, geom_sum_mul_neg in
Mathlib/Algebra/Ring/GeomSum:232,237,240, and the scalar geom_sum_eq in
Mathlib/Algebra/Field/GeomSum:43. Their signatures still need a scratch
check before use. The lexical geom_sum search's first page was unhelpful;
no absence claim was made.

The actual source norms needed next are norm_sq_ccmPolarApertureVector_half
and norm_sq_ccmPolarApertureVector_neg_half in
CCMRestrictedWeilCanonicalHeadCompletedErrorControl:143,172, each equal
2*sinh(a). Together with inner_ccmPolarApertureVector_opposite=2a they
give squared norm(p_odd)=sinh(a)-a and hence norm(p_odd)<=exp(a/2).
The actual odd Riesz equation is suzukiTaRawCoalescingOdd_inner in
SuzukiTaCoalescingCovarianceTangent:177; energy is
suzukiTaCoalescingOddEnergy (definition128), with exact norm-square
identity suzukiTaCoalescingOddEnergy_eq_norm_sq at line211. Physical embedding is the
interval form embedding composed with suzukiTaToFormCLM
(SuzukiTaHilbertSpace:82). Retain the unitary transport of sinhVecC(1/2)
to (p_+-p_-)/2 in the energy weld.

Next hard proof: fix epsilon=exp(-4), K=2log(C0)+10, n=ceil(a), solve the
actual recurrence, bound finite alternating Neumann sum and residual, then
use E<=<Au,u>+2 norm(r)sqrt(E) with A=cI+B and the actual odd Riesz source.
Do not fall back to a merely conditional norm criterion or add Gamma-domain
assumptions for the physical test vector u. Signed Wronskian, canonical
normalization and shift removal remain open beyond that selected target.

All own processes are terminal. Exact owned scratch/search/lint files
are removed at this checkpoint; valid oleans for all three new leaves are
retained. No subagents, numerical experiments, full builds, umbrella
builds, heartbeat increases, commits or pushes were used.

## Growing Neumann source and actual odd energy, 2026-10-02

Route SZ continues from the proved actual odd-orbit contraction. That
result contributes directly: it controls every iterate without a response
regularity premise. The current hard target is to complete the finite
Neumann approximation and weld it to the actual odd Riesz equation.
Search1186930 is partial, source-only, with snapshot coverage; its proposed
Xi Gaussian remainder ingredient set does not apply to the actual Suzuki
operator. The existing scalar geometric identities and exact source norm
formulas are directly applicable and are being checked in Lean.

Proof simplification: keep epsilon=exp(-4), C0=2*(norm(kappa)+46),
K=2*log(C0)+10 and n=ceil(a). Inductively d_j is at most
epsilon^j*exp(a/2)+eta*C0^j, eta=L*exp(a/2)/sqrt(exp(K*a)).
Since eta*C0^n<=L*C0*exp(-9a/2), a uniform residual bound and a
geometric-sum bound suffice for uniform odd energy. No sharp constants
or rate optimization is needed. The actual root theorem must discharge
the recurrence and source assumptions, retaining the prescribed shift.

Scratch80753 checked the finite recurrence and found three elaboration
issues: unrestricted norm_num unfolded the aperture norm, dsimp had no
remaining target, and the recurrence constant needed an explicit binder.
These are proof-expression failures, not mathematical counterexamples.
The fixes retain the same argument. Scratch47982 additionally audits the
exact finite alternating-sum residual identity and the actual prescribed-
shift Neumann approximation. One foreground Lean process is active.

The actual energy proof is drafted separately while that audit runs.
It transports sinh(x/2) to the literal odd pole vector using the existing
unitary and the coalescing source identity. Positivity of cI+B on f-u
gives E<=2c*norm(u)^2+2norm(r)*norm(w), with E=norm(w)^2.
The finite approximation gives E<=4M^2+2R*norm(w), hence
E<=8M^2+4R^2. The source Cauchy--Schwarz bound E<=exp(a) covers
the remaining bounded aperture range. No Gamma-domain assumption is
needed on u for this energy comparison. The new conclusion remains
unverified until its direct Lean audit succeeds.

The first lexical energy query has no hits; a broadened any-term query
retrieves the exact suzukiTaRawCoalescingOdd_inner and inner_suzukiTa_eq
sources. Lexical output supplies no compiler certification. The actual
identities are read and used directly, not replaced by an abstract source.

Scratch47982 checked the complete growing-orbit estimate. Its remaining
three algebraic/elaboration errors were fixed: avoid dsimp unfolding the
iterate before its recurrence rewrite; qualify Finset.sum_range_succ;
preserve the aperture norm before norm_smul. Final leaf86995 is running
for CCMRestrictedWeilFiniteNeumannSource. No default-limit increase.

Next-source search1187063 is partial, source-only, semantic coverage
unmeasured. It retrieves the already proved finite-exponential Fourier
envelope, not a Gamma admission theorem. Direct source inspection finds
ccmArchimedeanFormWeight_le_logComparison in
CCMArchimedeanLogWeightEquivalence:58 and the exact weighted/domain
transports in CCMArchimedeanFormDomainEquivalence:128,184. Thus the next
physical-mass conjecture has a concrete corpus basis: split the actual
finite Neumann vector's logarithmic Fourier energy at exp(K*a). Its low
part is O(a*norm(u)^2), and its explicit 1/abs(xi) tail pays the complement.
After exact form-domain admission, test the actual residual in the form
equation to seek physical mass O(a*exp(-a)). This is not yet formalized
and is not needed for the current uniform odd-energy argument.

Final finite-Neumann audit86995 found only a redundant tactic after an
already closed goal. Replacing that sequencing with explicit all_goals
steps fixes it without mathematical changes. Final leaf34076 PASSED,
no warnings. CCMRestrictedWeilFiniteNeumannSource is wired. Its three
public theorems prove the literal odd-source norm bound, growing finite
orbit control, and the actual prescribed-shift Neumann approximation.
The actual odd Riesz energy leaf is now under a separate scratch audit.

Energy scratch57590 found scalar-field inference failures in polymorphic
inner-product lemmas, syntactic RCLike.re versus Complex.re differences
inside arithmetic tactics, and a redundant ring after field_simp had
closed its goal. The fixes make the complex field explicit, provide the
three exact norm-square identities in the actual energy decomposition,
and normalize the Cauchy--Schwarz real parts before nlinarith. No premise
or mathematical statement is weakened. Final energy leaf59494 is running
for SuzukiMatchedOddSourceBound; the final root has no hypothesis binders.

Energy audits59494,80278,44094 narrowed the remaining failures to generic
rewrites whose RCLike/subtype expressions did not syntactically match the
actual complex aperture expressions. Fully typed intermediate equalities
for the real self-inner-product and B symmetry resolve this. They are
derived from the same corpus lemmas; no axiom or bound change is involved.

FINAL ENERGY AUDIT87048 PASSED, no warnings. Both new leaves are wired.
All five public axiom queries29754 PASSED, using only propext,
Classical.choice and Quot.sound. The printed root is literally
  exists C>0, forall positive aperture a,
    suzukiTaCoalescingOddEnergy a (1/2)<=C,
with no hypothesis binders. The selected actual odd-source gap is CLOSED.
This is a frontier advance on route SZ, not an RH proof. The complete
signed Wronskian/cusp cancellation, canonical V2 normalization, shift
removal and Xi identification remain open.

Lint38433 exits1 on twelve unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
SoninPrimeSquareCorrectionNuclear, ThetaMovingShellFirstOrderPhase,
ThetaTailConfluentCenterGram, ZetaZeroDensityPowerSaving.
Neither owned leaf is flagged. Global lint is not green. Targeted tracked
whitespace check passed. Unrelated changes are preserved.

P3:sz-matched-odd-source-bound records the exact new theorem, paper proof,
and certificates. The SZ frontier map now records this closure and removes
stale open claims for the already closed iteration/odd-energy obligations.
The active iteration card continues with the concrete logarithmic-energy
and physical-response-decay conjecture; it includes the exact weighted
tail formula and actual form-residual proof mechanism.

Next exact source definitions verified: in CCMArchimedeanHilbertFormDomain,
the Gamma measure is volume.withDensity(formWeight) (line91), the weighted
Fourier norm is exactly its formWeight integral (line142), and the form
domain is the kernel of the aperture support defect (line230). Thus weighted
L2 admission of the actual Fourier representative, followed by the inverse
Fourier identity, constructs the required actual form lift. The comparison
theorem is CCMArchimedeanLogWeightEquivalence:58; the exact transports in
CCMArchimedeanFormDomainEquivalence remain available if logarithmic L2 is
used as the intermediate space. No new code for that next conjecture yet.

Checkpoint cleanup: all own processes terminal; all ten exact owned /tmp
search/scratch/lint files removed. Valid new leaf oleans retained. No
subagents, computations, full/umbrella builds, heartbeat changes, added
axioms, commits or pushes. RH goal remains active and unmet.

## Actual Gamma admission and physical-response decay, 2026-10-02

Previous turn is progress: actual matched odd energy is Lean-closed.
Current route SZ target is the next unproved physical-decay step, with
the complete signed Wronskian and RH identifications still open. Current
source inspection confirms the two audited leaves and the literal root.
New corpus search targets logarithmic weighted energy and form admission.
The corpus already has qualitative admission for a globally bounded
Fourier profile with an inverse-frequency envelope
(SuzukiH01FormDomain:246), but its pointwise hypotheses do not directly
match the current ae L2 representative, and it supplies no moving-band
quantitative energy bound. The actual quantitative low/tail split remains
the needed new theorem. The exact logarithmic tail primitive is
-(log(x)+2)/x; its derivative is (1+log(x))/x^2. Mathlib's nonnegative
derivative improper-integral theorem can prove both integrability and
the exact tail formula without a numerical computation.

The logarithmic-energy conjecture passed scratch and final leaf audit in
CCMFiniteExponentialLogEnergy. It proves integrability and the exact moving-band
bound for every certified source, then discharges the source budget for every
literal odd remainder iterate. Reflection required an explicit negative endpoint
to prevent Lean's inference timeout; no heartbeat limit was raised. The leaf is
wired. Actual Gamma admission, preserving the aperture vector and all band
bounds, also passed scratch; its final leaf audit is running.

Next source search: generation 1187500, partial=true, coverage pending,
candidate/source hits source_only, no ingredient sets. Broad query returned
unrelated boundaries. Exact lexical query recovered ccmMatchedOddPoleSource and
its norm theorem. The inspected finite-orbit proof already retains exp(-7a/2)
and exp(-9a/2) before discarding them. Strengthening that actual result, naming
the literal Neumann vector, and certifying its finite budget directly attacks
the Gamma residual comparison needed for physical-response decay.

CCMFiniteExponentialFormLift passed its final leaf audit and is wired.
CCMRestrictedWeilFiniteNeumannSource passed its final audit after strengthening:
literal N=ceil(a) residual is bounded by R exp(-7a/2), and the canonical finite
Neumann vector has certified budget C0^N exp(a/2)/c_a. Existing uniform APIs are
now corollaries, so no already-used result was weakened. The Gamma-decay scratch
uses band exp((2 log C0+10)a); its squared budget divided by this band is bounded
by 4 C0^2 exp(-a). Together with norm(u)<=2M exp(-a/2), this gives actual Gamma
energy O(a exp(-a)). Final physical comparison has been drafted: z=w-FromForm(g)
satisfies ||z||²=Re<r,Jz>-Re<g,ToForm(z)>, yielding ||Jw||²<=2||r||²+8||g||².
These last two claims are still under Lean verification, not yet closed.

Both claims are now Lean-closed. CCMFiniteNeumannFormDecay final audit13151
and strengthened SuzukiMatchedOddSourceBound final audit54388 pass without
warnings. The root eventually_suzukiTaMatchedOdd_physical_mass_decay has no
unproved premises and controls the actual physical matched odd response at
anchor1/2 by C*a*exp(-a). The three new leaves are wired. Full paper proof
and audit ledger: P3:sz-matched-odd-physical-decay.

Next conjecture is not another absolute constant refinement. The source
symbol is small on every exp(K*a) frequency band, while the exact Gamma
weight penalizes its complement by K*a/C_arch. Interpolating that with
actual A=cI+B>=I should prove norm(w)_Ta²>=L*a*norm(Jw)² for every fixed
L>0 eventually, uniformly for all actual form vectors. The complete paper
calculation, exact corpus ingredients, and intended rescaled residual
consequence are in P1:sz-growing-physical-coercivity. Deep search1187787 was
partial/source_only with no ingredient set; direct source inspection
verified the needed low-band and reverse logarithmic comparisons. No
absence or completed Lean claim is made for this new coercivity target.

The signed continuation search1187722 was also partial/source_only, with
no ingredient set. CCMSuzukiCrossApertureProjectiveWronskian:195 already
formalizes the exact completed Fourier shell-plus-metric decomposition;
:340 identifies its anchor value with the difference of projective first
jets. These identities retain the signed terms but do not supply their
cofinal bound. Neither the new matched mass bound nor the growing-floor
conjecture is being identified with shift removal or an RH proof.

Final axiom audit45262 passes all fourteen public theorem queries from the
five current leaves: only propext, Classical.choice and Quot.sound. Root
statement printed with no unproved hypothesis binders. Formal lint17821
exits1 on eleven unrelated unreachable modules (exact list on the P3 card);
none of our five leaves is reported. Global lint is not green. The final
root and all dependencies have passed their foreground leaf audits; no
umbrella build, new axiom, numerical experiment or heartbeat increase was used.

Checkpoint cleanup complete: all own processes terminated; all thirteen exact
owned /tmp search/scratch/lint paths removed, valid audited leaf oleans retained.
Every one of the five current leaves has exactly one umbrella import. Targeted
tracked-file whitespace check and all five source whitespace checks pass.
No commit/push or unrelated-source edit. The goal is active and unmet. Continue
directly with the mathematical growing-coercivity argument on its active card;
do not rebuild the five unchanged audited leaves or replay session initialization.

## Growing physical coercivity continuation, 2026-10-02

Route SZ; previous turn is verified progress. Current target is the uniform
growing physical floor and then exp(a)-rescaled response-minus-Neumann error.
The selected matched mass estimate is already closed, while signed joint
shell/metric control, normalization and shift removal remain hard open gaps.
The active paper argument is P1:sz-growing-physical-coercivity.

Search1187903 is partial with a complete source-inventory snapshot but many
compiler records pending/stale. Its proposed smooth-truncation ingredient
set does not supply the arbitrary-Gamma estimate. Source inspection found
the exact cutoff norm formula and pointwise tail weight in
SuzukiHlogCompactEmbedding. The actual operator contraction now retains its
unassumed Fourier tail for every aperture vector, and the certified-source
specialization reuses that estimate; final SourceContraction audit66319 passes.
CCMArchimedeanFourierTail final audit52297 passes and its new leaf is wired.
The growing-floor and rescaled approximation proofs are drafted in scratch;
needed exact form identities and the actual Ta residual norm estimate are
being exposed from the previously audited proof without new premises.

Further parity-source search1188058 is partial/source_only, snapshot coverage.
It recovers the actual even response/pole charges and the matched odd mass
bound. Its proposed Neumann-flux cancellation step concerns a boundary-condition
channel, not the finite inverse series used here; it is not an applicable
substitute for the signed two-source asymptotic calculation.

Current checkpoint: GrowingPhysicalCoercivity final33070 and
MatchedOddNeumannApproximation final74860 pass. Public axiom audit47142
passes fifteen queries, standard axioms only; root signatures checked. Three
new leaves are wired. The first axiom harness was stopped at its owned PID
after finding missing namespace qualification, before results; corrected
harness completed normally. Formal lint9165 exits1 on twelve unrelated
unreachable modules, none belonging to the changed/new leaves, with no
prohibited proof declaration reported. Full list is retained on P3.

The next hard target is actual odd/even metric balance. Search1188112 is
partial/source_only, coverage pending; no ingredient set. Search1188324 is
also partial/source_only, coverage pending, and returns finite telescoping
and exact remainder decomposition, not the needed limit. Source inspection
gives a shorter odd proof through O_a=Re<p_a,f_a>. The audited arbitrary
Gamma tail also proves complete remainder-quadratic vanishing by choosing
the exponential band width first, then applying low-band cancellation.
Both source mechanisms and exact obligations are recorded on
sz-matched-source-metric-balance.md. Metric norm-square transport and
complete remainder quadratic are drafted in /tmp, under sequential audits.
No complete metric balance or RH claim is made from these drafts.

## Actual odd metric-balance checkpoint, 2026-10-02

The complete bounded-remainder quadratic vanishes on the actual Neumann
vector by the new arbitrary-Gamma tail: choose an exponential band width K
first, then invoke signed symbol cancellation. MetricTransport58443 and
CCMFiniteNeumannRemainderQuadratic66228 passed final audits. Exact source
energy was exposed by a wrapper in OddSourceBound, final47712 passed.
OddMetricBalance final16313 passed: abs(c_a*norm(Jw_a)^2-O_a)->0, along
positive apertures, no unproved premise. Axiom58144 passes eight new public
queries, standard axioms only, complementing the earlier fifteen.

All eight current leaves are wired exactly once, with no trailing whitespace.
Global lint38139 reports twelve unrelated unreachable modules, no prohibited
proof declarations; exact list retained in P3:sz-matched-odd-metric-balance.
No full/umbrella builds or new axioms; no numerical experiments or heartbeat
increase. No subagents or commits.

Two source checks prevent overclaiming: the actual discrete metric term
uses covariance at b on the transported response from a, so same-aperture
balance does not yet control it; the V2 anchor-I identity uses parameter1,
whereas these estimates use matched parameter1/2. Both comparisons stay open.
The quadratic proof exposes the vector-profile conjecture
exp(-a)*norm(B_a u_a)^2->0, hence exp(a)*norm(f_a-p_a/c_a)^2->0. Its full
paper mechanism and actual mixed-aperture purpose are on the active metric
card. Next continuation should attack that vector statement and the actual
even channel, then the mixed-response signed determinant. RH remains unmet.

Final checkpoint cleanup: all owned Lean/search/lint sessions terminated.
All sixteen exact owned /tmp files removed; valid audited leaf oleans retained.
Targeted tracked-file whitespace gate passed; eight source whitespace checks
passed; every current leaf has exactly one umbrella import. Memory
rhtower/sz-growing-coercivity-odd-metric-balance-2026-10-02 records the new
results, audit ledger, next vector-profile conjecture and the two corrected
transfer gaps. Goal remains active and unmet. Continue the mathematical
vector-profile attack; do not repeat completed audits or session init.

## Explicit pole-profile continuation, 2026-10-02

Previous turn classified PROGRESS: actual odd metric-balance root and its
complete remainder/metric transport inputs passed final audits,23 public
axiom checks standard. Current source inspection confirms the final files.
Next hard target: the vector remainder vanishes after exp(-a) rescaling,
then actual f_a is asymptotic to literal p_a/c_a. This attacks the mixed
aperture comparison, while even balance, full shell cancellation, anchor
transfer, canonical normalization, shift removal and Xi identification remain
open. The source-based paper proof is on the active metric-balance card.
The stronger norm theorem will supply the existing quadratic as a corollary,
reusing the Gamma-tail argument instead of maintaining two parallel proofs.

### Uniform source-profile checkpoint, 2026-10-02

Route SZ; this continuation contributes PROGRESS to the hard source-control
problem. The source-uniform finite inverse, actual Gamma admission, full
prime-polar remainder norm, and exact actual covariance profile are all now
final-audited. Both literal matched parity responses have explicit physical
pole profiles. The actual parameter1/V2 source profile scratch50842 passes;
its final17439 is running. This is a proved source-control advance, not an
RH proof, a full shell estimate, or an assumed normalization transfer.

Detailed dependency-closed proof and audit ledger:
`docs/drafts/pipeline/3-formalized/sz-uniform-source-covariance-profile.md`.
Active mathematical continuation and search evidence:
`docs/drafts/pipeline/1-in-progress/sz-uniform-source-profile.md`.

Next hard conjecture is the actual prescribed-shift first defect limit0,
using the parameter1 profile and exact source pairings. The corpus's Xi
target defect is strictly positive, so this would force a concrete
shift-selection/shift-removal separation. The existing selected-negative-
shift collapse theorem is insufficient for that claim. Full mixed-aperture
signed cancellation, canonical normalization, shift removal, Xi identification
and RH remain unresolved. No numerical experiments or subagents were used.

Final checkpoint: all ten changed leaves pass final old-mode Lean audits;
all 38 public axiom queries pass in audit4858, using only propext,
Classical.choice and Quot.sound. Exact odd/even/V2 Tendsto signatures have
no hypothesis binders. Lint54349 still fails on thirteen unrelated
unreachable modules and reports no prohibited proof declarations. Every
changed leaf is wired once. RH remains unresolved; goal remains active.
Next: formalize P2:sz-prescribed-shift-first-defect-collapse, preserving its
actual defect0 law as the positive survivor before any no-go is closed.

Cleanup verified: all 19 exact owned /tmp search, Lean and audit files removed;
all owned sessions terminal; valid audited leaf oleans retained.

## Prescribed-shift parity continuation, 2026-10-02

Route SZ. Previous actual-source profile work contributes directly: it closes
the analytic error term in the literal V2 source pairings. Current stronger
paper survivor uses t_a=c_a exp(-2a): t_a(E+O)->1/2 and t_a(E-O)->0,
hence t_a E,t_a O->1/4 and actual first defect->0. This resolves a genuine
normalization/identification obstruction if audited; it is not RH or full
signed shell control. Current implementation is awaiting final leaf audits.
Scratch failures so far are explicit complex scalar coercions and implicit
inner-product arguments; no mathematical hypothesis was added. No heartbeat
increase, numerical experiment, or parallel own Lean build was used.

Next conjecture, based on search1189636 (partial, pending, source_only; no
proof ideas or ingredient sets): the entire actual prescribed-shift V2
Livsic family has zero as its sole upper-half-plane cofinal limit. The
search's finite-shift generator statements concern an independent small
shift and do not establish this growing-aperture claim. Existing actual
raw-carrier identity and physical Fourier/Riesz bridge supply exact targets.
Do not infer full collapse from the first derivative alone.

Potential paper mechanism, still pending dependency-closed audit: fix
1/2<s<1, p_s=exp(sx) cutoff[-a,a], f_1=actual physical raw deficiency1,
and r_s=c_a exp(-(1+s)a). Comparison with the audited half-pole norm gives
norm(p_s)<=exp(sa); reflection gives the opposite norm. Then
r_s |<p_±s,f_1-p_1/c_a>|<=C delta_a->0. Literal Gram integration predicts

    r_s <p_s,f_1> -> 1/(1+s),
    r_s <p_-s,f_1> -> 0.

The main terms are respectively
(1-exp(-2(1+s)a))/(1+s) and
(exp(-2sa)-exp(-2a))/(1-s). With exact Fourier evaluation at is and
actual raw reflection, these force Livsic_a(is)->0. Existing Schur
compactness then gives zero on an interior segment for any analytic cofinal
limit; identity-theorem continuation would classify that limit globally.
Every bridge must be proved against actual interval types; old free Ioo
aperture integrals cannot silently replace actual Icc interval spaces.

This conjecture would classify the failure of the prescribed norm shift,
exposing the need for a different actual shift/renormalization retaining
arithmetic data. It does not by itself supply such a shift, full shell
cancellation, or Xi identification. Finish current positive parity and anchor
survivors and strict Xi no-go before advancing the stronger conjecture.


### Prescribed-shift closure checkpoint, 2026-10-02

Classify current turn as PROGRESS: the actual V2 common-scale parity limits,
first-defect0 law, independent-aperture normalized anchor Wronskian0 law and
strict exclusion of all cofinal locally uniform Xi identifications are now
formalized. This closes the selected hard first-defect problem, not RH.
Final leaves66261/2082/13420 pass; all twelve public axiom queries60205 use
only propext, Classical.choice and Quot.sound. Four exact root signatures
have no hypothesis binders. All three leaves are wired once.

P2:sz-prescribed-shift-first-defect-collapse was promoted to P3. The failed
identification and strongest audited positive survivor are recorded on
P5:sz-prescribed-shift-direct-xi-identification. Current source/search-based
next conjecture is P1:sz-prescribed-shift-full-carrier-collapse, whose mixed
imaginary-source mechanism is written in detail. Attack that actual carrier
classification next; do not treat derivative0 alone as an identity theorem.

Lint64122 reports eleven unrelated unreachable modules (exact list on the
P3 card); no current leaf fails. Global lint is not green. Full signed
shell/metric Wronskian, shift removal, canonical normalization, Xi
identification and RH remain unresolved. Goal remains active and unmet.

Cleanup verified: all eight exact owned /tmp files removed; all owned
Lean/search/lint sessions terminal; valid audited leaf oleans retained.
Targeted tracked-file whitespace gate passed; all three new Lean leaves
have no trailing whitespace. No subagents, numerical experiments, full
builds, heartbeat increases or commits.


## Full prescribed-shift carrier classification, 2026-10-02

Previous turn classified PROGRESS: actual first-defect0 and strict Xi
separation passed audits. Current turn also PROGRESS: the stronger whole
carrier conjecture is now proved. Exact root
`RHTower.tendstoLocallyUniformlyOn_suzukiTaV2Livsic_prescribed_zero` has no
hypothesis binders and asserts locally uniform convergence of the literal
actual V2 family to0 on the entire upper half-plane along the full positive-
aperture comap filter. This is not merely a subsequence or a jet law.

Four final leaves pass: SuzukiTaV2MixedSourceGram88852,
SuzukiTaV2MixedSourceLimit74510, SuzukiTaV2ImaginaryCarrierCollapse5798,
SuzukiTaV2PrescribedCarrierCollapse20678. Thirteen public axiom checks22765
pass using only propext, Classical.choice and Quot.sound. Each leaf is wired
once. Exact mixed Gram integration and half-pole norm comparison remove the
aperture-length loss; complex source errors retain both channels; actual
Icc interval Fourier/reflection yields interior imaginary-segment collapse;
corpus Vitali and Mathlib's sequential compact-set criterion yield the full
filter. No full/umbrella build, numerical experiment, heartbeat increase,
new axiom or subagent.

P1 full-carrier card promoted to P3 with the dependency-closed paper proof.
P5 direct-Xi no-go now records this stronger positive survivor. Frontier
map updated. Lint68235 still fails on thirteen unrelated unreachable modules
(exact list in P3), with no prohibited proof declarations and no current leaf
among failures. RH remains unresolved, goal active.

### Next hard conjecture: unshifted signed source production

The next exact source target is nonnegativity, cofinally in head index, of
`ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer a
  (ccmRestrictedWeilCanonicalGroundHead a n)` for every positive aperture.
This is an EXISTING OPEN CORE, not a new equivalence or an already proved
consequence of carrier collapse. The known reverse-prime and canonical-ground
criteria are consumers only. It is the shared actual-head Suzuki/CCM source
interface for recovering the unshifted arithmetic information; the prime
wall-Gram bridge does not identify distinct common-clock and ground-head
operators.

Read current source in CCMActualHeadCompletedAutocorrelationProducer,
CCMRestrictedWeilCanonicalHeadCompletedErrorControl,
CCMRestrictedWeilCanonicalGroundHeadEnergy and
CCMRestrictedWeilCanonicalGroundRemainderNumericalRange. Search1190162 had
no useful deep hits (partial/pending); narrowed lexical ground-energy search
recovered the current ground, continuity, floor and sign-equivalence
interfaces. Search1190095 was partial/source_only with compiler enrichment
pending; its seam-shift norm ingredient is irrelevant to the metric shift.
The actual shiftEquation and the raw-exponential operator-domain theorem are
available, but source anchor changes do not remove the metric shift.

The full existing card
`docs/drafts/pipeline/1-in-progress/ccm-canonical-head-completed-error-producer.md`
was read in slices. It already closes Gamma and polar decomposition and
forbids generic lag-metric, positive-autocorrelation, modulus-ground,
separate chi-square budget and split-singular-Gamma shortcuts. The actual
full screw form fails Beurling--Deny; no positivity-preserving semigroup may
be assumed for its canonical head. The scalar phase-free chi-square budget
is strictly negative. The next conjecture/proof loop should test the
phase-preserving joint Gamma-increment/coherent-field inequality on the
literal canonical heads, retaining the outgoing endpoint and all prime
powers. Source definitions and prior attempts must be searched before new
Lean. Proving another receiver or assuming the unknown ground sign would
not count as progress.

Remaining SZ obligations: signed shell/metric/cusp control where needed,
lawful shift removal or an unshifted source producer, canonical Xi
identification and unconditional RH. The proved zero-carrier limit makes
direct identification in the original norm-shift coordinates unavailable;
it does not make any of those remaining signs automatic.

Full-carrier cleanup verified: all fourteen exact owned /tmp files removed;
all owned Lean/search/lint sessions terminal; valid audited leaf oleans
retained. Four exact umbrella imports and four source whitespace checks
passed; targeted tracked-file whitespace gate passed. No commits or pushes.

## Raised metric shifts and the remaining singular regime, 2026-10-02

Route SZ. The previous whole-carrier classification was actual progress.
This turn first tested whether the actual ground equation could close the
unshifted joint coherent phase gap. Pure stationarity is insensitive to
adding a scalar to the operator; it does not recover the needed central
scalar. The existing completed-square/chi-square no-go also blocks the
phase-free estimate. No new ground-sign proof or stationarity wrapper was
claimed or added.

New source-derived conjecture: increasing the actual prescribed metric
shift cannot rescue Xi identification. For C=(A+c)^(-1) and t>=0, the
constructed response x_t=C(I+tC)^(-1)p solves (A+c+t)x_t=p. Exact transfer
gives norm((c+t)x_t-p)<=norm(c C p-p). This is a change of the metric shift
of the same actual interval Friedrichs operator, not of the exponential
source parameter.

`SuzukiRaisedMetricShiftSource` scratch57265/final42847 and
`SuzukiRaisedMetricShiftLimit` scratch21196/final93705 pass without warnings;
both leaves are wired once. The latter proves both complex mixed pairings
have limits 1/(1+s),0 for every 1/2<s<1 in the joint aperture/increment
filter, uniformly over all nonnegative increment schedules. Actual
reflection, Fourier quotient identification and Xi exclusion are being
audited in the owned carrier scratch. Paper proof and audit details are on
P1:sz-raised-metric-shift-source-collapse.

Searches1190250/1190318/1190336-1190344/1190351/1190598 were partial, with
source-only or pending compiler enrichment. Relevant candidate statements
and source arguments were checked against actual files; retrieved consumers
were never treated as proved producers. No novelty claim follows from a
search miss.

Next conjecture is P1:sz-spectral-edge-shift-necessity: below c, a nonzero
target must force divergence of the exact transfer inverse and relative
approach to the actual interval spectral floor. A fixed positive resolvent
margin should still imply collapse. The existing simple-even-ground Cayley
universality warns that relative approach cannot justify a one-mode limit:
the actual moving-aperture source residues and parity leakage must survive.
This attacks shift selection; unshifted canonical-head positivity, signed
shell/metric control, Xi identification and RH remain unresolved.

### Raised-shift closure checkpoint

Classify this turn as PROGRESS on shift selection, not on unshifted ground
positivity. Source42847, limit93705 and carrier61584 final leaf audits pass
without warnings. All seventeen public axiom queries50108 pass using only
propext, Classical.choice and Quot.sound. All three leaves are wired once.
The no-go excludes even pointwise Xi identification on the interior
imaginary segment for every cofinal schedule of nonnegative increments.
Actual reflection and zero-increment identification are proved; no Schur
or whole-upper-half-plane collapse claim is made for the raised family.

The positive survivor card was promoted to P3; the existing direct-Xi
failed-route card and SZ frontier map record the stronger class exclusion.
Lint78784 reports eleven unrelated unreachable modules, listed on the P3
card; no current leaf or prohibited proof declaration is among failures.
Global lint is not green. Goal remains active and unmet. Next attack is
the exact actual spectral-edge necessity recorded on its P1 card, followed
by the surviving moving-aperture source-residue problem.

### 2026-10-02: all-admissible spectral-margin necessity, paper closure

Route SZ remains actual source/metric identification. The raised-shift
exclusion contributed a real class obstruction. Current conjecture strengthens
it to every shift above the actual attained spectral floor. Source search
1190824 returned partial/pending coverage, source-only candidates and no proof
ideas/ingredient sets; current source checks supply covariance positivity,
exact ground floor, actual shift equation and the audited prescribed profile.
No novelty claim rests on search absence.

For m>0 use d=c+(m-1)/norm(C), q=min(1,m), T=I+(m-1)C/norm(C).
Positivity and the operator-norm estimate give T>=qI, an actual inverse,
and q*norm(d*C*T^-1*p-p)<=norm(c*C*p-p). Weighted normalized mixed errors
therefore vanish uniformly over all admissible shifts. Nonzero carrier
convergence, literal quotient cancellation, and the nonzero free denominator
force q->0 and hence m->0. This is relative floor distance, not absolute gap.
No source-overlap, simple-ground, parity, shift-sign or shift-growth premise.
The exact positive statement is being formalized; RH is not proved.

Process correction: a second scratch Lean command was accidentally started
before session13394 exited. Owned replacement77328 was terminated (exit143);
original13394 then exited with its coercion diagnostic. Subsequent checks are
strictly serial. No unrelated process was touched.

### SZ-SHIFT-EDGE closure

Success: all-admissible relative-floor necessity now fully formalized.
Source17124, Limit44729, Necessity15580 and reused Xi witness2368 passed final
`lake --old env lean <leaf> -o <olean>` audits, warning-free. Axiom39186
checked all15 new public theorems plus the witness: only propext,
Classical.choice, Quot.sound. All3 new leaves wired once; no umbrella build.
Lint63539 remains red on10 unrelated unreachable modules (listed on P3 card),
none of these leaves. RH remains unresolved.

This contributes a new actual source constraint, not only an equivalent RH
receiver: every admissible fixed-source Xi schedule must satisfy
(E+d)/(E+c)->0. Exact source inverses and weighted complex limits are proved
without mathematical input premises. Xi convergence is the antecedent of
a necessity theorem, not asserted as a discharged input to an RH proof.

Next conjecture and paper mechanism are recorded in
P1:sz-actual-source-defect-quasimode. A nonzero carrier limit should force
actual normalized source defect to satisfy (I-C/norm(C))*y/norm(y)->0.
The implication remains relative-scale only. It provides no ground parity
or projection-overlap conclusion. The remaining hard arithmetic problem is
the actual signed residue/current; canonical-head Gamma--prime--polar
positivity and RH are still open. Corpus modulus search1191029 was partial
and returned decompositions, not an actual ground-sign theorem. The
limiting logarithmic operator's simplicity theorem cannot be transferred
to the actual Weil operator with its polar term.

Cleanup verified after closure: all10 owned /tmp files removed, no owned
process remains, audited oleans retained, new imports once each. Targeted
whitespace checks passed. Next source-defect conjecture remains active;
no RH completion or goal-status change.

### 2026-10-02 continuation: actual source-defect quasimode

Previous goal turn classified progress: it proved and audited all-admissible
relative-floor necessity. Current work attacks the actual vector created
by the singular inverse. Revalidated current source/necessity definitions;
search1191242 was partial with older snapshot1191238. Rejected its suggested
mix of limiting-log covariance and actual source covariance.

Current exact proof mechanism: y=d*x-p satisfies T*y=r_base. Literal carrier
cancellation and two mixed Gram limits force exp(-a)*norm(y) eventually
bounded below, hence norm(r_base)/norm(y)->0. With m->0, the exact residual
identity (I-C/norm(C))*y=r_base-m*(C/norm(C))*y yields the actual relative
quasimode. No source projection or overlap premise, no assertion of a
uniform ground gap. Source and asymptotic proof drafts are being audited.

### Actual-defect quasimode: verified closure

Success. Source scratch67821/final5344 and quasimode scratch13322/final76442
all exited0, warning-free. Both new modules wired once. Axiom52632 checks
all nine public theorems: only propext, Classical.choice, Quot.sound.
Final leaf commands used lake --old env lean with their explicit olean
outputs. Lint28194 fails on11 unrelated unreachable modules, listed in P3;
no current leaf is among them. No full/umbrella build or heartbeat change.

The theorem supplies an actual source vector and its asymptotic normalized
covariance equation; it does not prove its sign, projection overlap, or
closeness to one ground eigenspace. This is progress on route SZ's source
identification constraints, not discharge of RH. Next work changes focus
from unsigned localization to the exact signed phase gap on canonical
heads; P1:sz-canonical-head-joint-phase-credit records the precise target.
Do not create another equivalence receiver. Current corpus searches for
that target returned existing source/ground identities and finite-prime
recurrence, not the missing sign. The recurrence gives an upper return-time
bound, not the lower Gamma-cost bound a phase-credit argument would need.
The prime--polar terminal and all Gamma cross phases must remain intact.

Cleanup verified for this continuation: all eight owned /tmp files removed,
all owned processes terminal, audited oleans retained, imports once each,
whitespace checks passed. P3 source-defect card updated; direct phase card
records the retrieved complex two-shear candidate and its unresolved scalar
orientation transport. No proof of that sign or of RH is claimed.

### 2026-10-03: absolute source sign and quantile entropy debit

The intervening read-only turn changed the candidate mechanism but proved
no new hard sign theorem. Two-shear positivity loses the scalar orientation
already known to change sign; midpoint gauges preserve the source action;
normalized ground modulation retains scalar-shift ambiguity. These were
not promoted as new knowledge or formalized as additional RH receivers.

Current source attempt: retain Suzuki's exact arithmetic normalization and
separate its event-loading curvature cost from the signed first-order
history. The first dependency-closed statement concerns the actual outgoing
quantile cells. Their left-boundary centroid debit D_n is nonnegative,
bounded by 2*w_n^2/(2+M_n), and summable by the corpus's actual mass lower
bound and summable square-weight theorem. Exact cell displacement equals
w_n*(log(n)-b_n)-D_n. P1:sz-quantile-entropy-debit records the proof and
limits; /tmp draft is currently in a single foreground Lean audit. No
claim of full checkpoint-reservoir dual control or RH is made.
