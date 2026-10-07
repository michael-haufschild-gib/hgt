# WP02 result — exact source constructions and bounds

## Current frontier: exact sampled polar mass (cycle 13)

The eleventh owned leaf, `WeilWorkExposingRayLatticeMass.lean`, recovers complete coefficient mass from explicit rounded integer samples of the actual Fejer-profile lattice, for every real spacing X>=4. It retains all complex cross terms, every site count and the full polar defect. One actual vanishing half-pole suffices; full polar tests are included.

Writing n_d=ceil(exp(dX)), eta_d=log(n_d)-dX and R for the actual profile autocorrelation, every finite mixture of such half-polar packets satisfies

    sum_i alpha_i sum_j |c_ij|^2
      = -sum_(d=1)^M cosh(dX/2)*trace(n_d)/R(eta_d).

The source proof gives R(eta_d)>=1/4 and hence mass <=4*sum cosh(dX/2)*|trace(n_d)|. Every nonzero nonnegative mixture has a strictly negative sampled atom. The exact classification `sampled_nonnegative_iff_zero_active` says that nonnegative sampled traces occur exactly when every positive-weight coefficient row is zero.

All seven public theorems in `RHTower.ExposingRayLattice` pass full scratch/axiom audits with only propext/Classical.choice/Quot.sound. Final installed `lake --old env lean -o <target-cache> <leaf>` passes without warnings; cache current, umbrella wired. Formal lint has ten unrelated reachability findings and no WP02 finding; exact details in EVIDENCE.md. No computation, new axiom, heartbeat increase or full/umbrella build.

Assessment: exact source-class conservation and stability, extending beyond a bare no-go. The covariance/polar mechanism is classical; external scientific novelty unestablished. **Universal WP02 remains OPEN.** Neither arbitrary repairs nor the all-aperture signed Gamma/trace bound are covered. Next candidate, GEOMETRIC-POLAR-MASS-CONJECTURE.md, tests physical-mass recovery for overlapping Riemann profiles on integer-base grids; it must pass the explicit utility gate against existing geometric rigidity and its extra repeated-pole constraints before any further Lean work.

## Literal Riemann-source capacity (cycle 12)

The tenth owned leaf, `WeilWorkExposingRayLocalCapacity.lean`, proves a fixed positive total-energy floor for EVERY local-seed variance completion of the actual truncated unit-shift Riemann source, uniformly for L>=2. Seeds may differ; their number, weights, translations and profiles may all vary. No energy-positivity or RH premise enters the proof.

For short polar seeds g_j, nonnegative alpha_j, M=sum alpha_j>0, F=sum alpha_j*g_j(.-x_j), and R_j=M*g_j(.-x_j)-F, the exact signed identity is

    E(F)+sum (alpha_j/M)*E(R_j) = M*sum alpha_j*E(g_j).

It implies, at EVERY real frequency t,

    (pi/(5*log(2)))*|paperFT(F)(t)|^2 <= total completion energy.

The literal Riemann source retains positive zero-frequency mass independently of cutoff. This defines an explicit `riemannCapacity>0`. The full finite exposing mixture retains at least `riemannCapacity/(2*pi)`, with its actual k=0 normalization. Capstones: `variance_energy_capacity`, `riemann_local_completion_floor`, `exposing_mixture_local_completion_floor`, namespace `RHTower.ExposingRayLocalCapacity`.

Complete scratch and final installed leaf/cache audits pass without warnings. All ten owned leaves are umbrella-wired. Detailed axiom/lint/index evidence is in EVIDENCE.md; the global lint currently reports seven unrelated reachability errors and no WP02 error. No numerical computation, new axiom, heartbeat override, or full/umbrella build.

Assessment: an exact source-class obstruction with a positive quantitative survivor; generic variance/Cauchy–Schwarz ingredients are classical, external scientific novelty unestablished. **The original universal WP02 lower inequality remains OPEN.** Arbitrary discrete atom repairs need not admit this representation, and every residual in the exact truncated-ray realization remains load-bearing. Next candidate: the exact sampled polar mass law in LATTICE-REPAIR-CONJECTURE.md, with the existing geometric radical obstruction explicitly treated as prior work.

## Geometric completion gap (cycle 11)

The exact finite geometric completion has total energy at least `(3*pi/25)*(1-farPolarCoeff(N*s))^2` for every N>=1 and 0<=s<=1/200. Its zero-frequency invariant is `mass(N,s)*(1-farPolarCoeff(s))=1-farPolarCoeff(N*s)`. Hence every fixed positive separation gives a strictly positive uniform cost, even as the step tends to zero. This rules out the zero-cost endpoint of this entire geometric family; it does not bound arbitrary repairs.

The proof admits literal compact C2 tests into the exact CCM form domain, transfers the existing one-tenth ground gap with the correct 2*pi normalization, and uses the actual short-source plateau. The ninth leaf is WeilWorkExposingRayCoherentGap; the completion capstones extend WeilWorkExposingRayCoherentCompletion. Full scratch and final installed leaf audits pass without warnings, including the generalized positive-threshold corollary and original fixed-step conjecture. Both changed leaf caches are refreshed; all nine owned leaves are wired into RHTower. The imported-cache axiom audit passes for all eight new public theorems, with standard three axioms only. Global lint has 18 unrelated reachability findings and no WP02 finding; details in EVIDENCE.md.

Assessment: exact source obstruction and positive quantitative survivor, with classical ground-gap/finite-variance parents; external scientific novelty unestablished. **The original universal WP02 lower inequality remains OPEN.** No scope reduction or assumed cone nonemptiness. Next actual-source candidate is LOCAL-SEED-CAPACITY-CONJECTURE.md, with paper proof in LOCAL-SEED-CAPACITY-PROOF.md and Lean still outstanding.

## Uniform polar tail (cycle 10)

The eighth owned contribution proves fixed constants D,C>0 and Y such that, for every 0<c<=1 and y>=Y,

    D*c^4*exp(-C*exp(y)) <= polarExposingKernel(c,y).

Thus the entire small-shift family has one common strictly positive tail, including shifts tending to zero. The proof uses the complete theta differential source, explicitly pays every negative autocorrelation contribution, and transfers through a normalized positive Green average. It assumes neither RH nor a positivity certificate. Complete scratch and seven-capstone axiom audits passed; final installed-source verification is recorded in EVIDENCE.md.

Source: `WeilWorkExposingRayUniformPolarTail.lean`, namespace `RHTower.ExposingRaySmallShift`; capstones `polarExposingKernel_uniform_quartic_lower` and `polarExposingKernel_uniform_positive_tail`. Paper proof: POLAR-UNIFORM-TAIL-PROOF.md. All eight owned leaves are wired into RHTower.

**Main WP02 lower inequality remains OPEN.** Tail signs do not supply universal matched-family energy positivity. Verdict: unconditional source advance / BRIDGE; external scientific novelty unestablished. The next concrete source conjecture, COHERENT-GAP-CONJECTURE.md, asks whether the exact bounded geometric completion has a strictly positive total-energy floor. It does not assume a lower bound for arbitrary repairs.

## Literal exposing tail (cycle 5)

Verified source: `formal/GaloisForLFunctions/RHTower/WeilWorkExposingRayTailAsymptotic.lean`. Final `lake --old env lean` exits 0 without warnings; all eight audited capstones use only propext, Classical.choice and Quot.sound. RHTower umbrella import wired.

Write kappa=2*pi*exp(-2). The actual exposing weights are eventually strictly positive and satisfy

    log(exposingWeight n) / n -> -kappa.

For every 0<r<kappa there is C>0 such that `exposingTail N <= C*exp(-r*N)` for every N. Also `0 < exposingTail N` for every finite N. No sign assumption, zero-location assumption or added axiom enters these statements.

The proof retains the literal infinite mixture. Its outermost positive shift has distance two, while all negative shifts have distance at most one; sharp theta-autocorrelation envelopes force the positive outer shift to dominate. See TAIL-SIGN-PROOF.md.

This strengthens the existing repair estimate from a summable polynomial majorant to its exponential source scale. For cutoff N near exp(2A), this literal tail budget is doubly exponential in aperture A. This is not a necessary accuracy barrier for every RH argument: a compactness argument may first establish RH from more slowly vanishing slack. It does **not** prove the universal matched-family archimedean lower bound. Main WP02 objective remains OPEN. Scientific novelty beyond the source-specific synthesis is not certified.

**Verdict: CONDITIONAL ADVANCE. Main problem OPEN.**

Unconditional results now cover exact exposing-tail repair, coefficient-uniform packet coercivity, and a source inequality with an explicit primitive penalty for arbitrary smooth compact primitives. The cofinal positivity estimate needed for RH is unproved. Scientific novelty verdict: **BRIDGE / source-class boundary**; no claim of a new general uncertainty principle or an RH breakthrough.

## Smooth compact source result

For every existing smooth compact primitive G, its actual polar source F=G''-G/4, and every real b, the direct source theorem proves

    (b-C_a) * M(F) <= archEnergy(F) + exp(b)^4 * M(G)/4,

where M is Fourier squared mass and C_a is an explicit digamma constant. The theorem uses the existing `CCMComplexSmoothInteriorSource.polarMultiplier`; there is no positivity, arithmetic, packet-expansion or separation premise. A separate theorem covers arbitrary finite overlapping packets.

This explains the failed transfer from separated packets: approximating a fixed broad primitive by narrower overlapping bumps does not force M(G) to shrink like the fourth power of the bump width. `OVERLAP-PROOF.md` gives the energy-topology counterargument on paper. The no-go itself is not claimed as a Lean theorem; its strongest source-inequality survivor is formalized.

Capstone: `exposingCompact_archimedean_primitive_bound` in `WeilWorkExposingRayPacketCoercivity.lean`. Scratch axiom audit and final `lake --old env lean` source audit passed, with only propext, Classical.choice and Quot.sound. EVIDENCE.md records exact scope.

**Limit:** the explicit primitive penalty is unpaid on the full matched exposing ray. The proof also uses coarse source constants and discards positive remainders, so it does not identify the sharp exposed endpoint. No completion of the C² matched-cone inequality is asserted.

## Collective packet result

For every natural N and arbitrary complex coefficient function c, put w=1/(N+1) and F=resonator(N,c,w). The new theorem proves

    (log(N+1)-C) * integral |paperFT(F)|^2 <= archEnergy(F),

with one explicit finite constant C independent of N and c. There is no Weil-positivity premise. N=0 and the zero vector are included.

The proof keeps all Fourier cross terms. The exact compact primitive G satisfies Fhat=-(tau^2+1/4)Ghat and

    integral |Ghat|^2 <= R*w^4*integral |Fhat|^2.

Disjoint physical supports prove this inverse-mass bound; the proved digamma lower bound and a scalar logarithmic inequality then prove coercivity. The lower bound complements the existing packet upper-bound mechanism and rules out bounded-energy, mass-retaining near-null sequences within these shrinking packet spaces. General polar tests need not obey the inverse-mass bound, so no passage to the full matched cone is claimed.

Paper proof: `PACKET-PROOF.md`. Lean module: `WeilWorkExposingRayPacketCoercivity.lean`; capstones `exposingPacket_inverse_mass` and `exposingPacket_archimedean_coercivity`. Final targeted source audit exited 0 without warnings, using default heartbeats. Scratch axiom audit passed: multiplier, inverse-mass and coercivity capstones use only propext, Classical.choice and Quot.sound. EVIDENCE.md records details.

## Exact tail-repair statement

For every pair of natural cutoffs N,M, the explicit finite family indexed by
`max(2,N+1) <= n <= M` consists of smooth compactly supported polar tests with nonnegative mixture coefficients. At every integer m>=2, including all omitted coefficients, its dual atom trace is exactly

    exposingWeight(m) * 1_{N<m<=M}.

Its archimedean energy is at most the sum of the exposing majorant over that interval. When N<=M, this budget equals

    exposingTail(N) - exposingTail(M).

For all N,M, energy is at most exposingTail(N), hence has a uniformly vanishing upper bound in M as N tends to infinity. This is an upper bound on energy, not an assertion of absolute-value convergence or positivity.

If M<=floor(exp(2B)), every repair test has aperture at most B+1. The construction retains the polar constraints, nonnegative mixture coefficients and exact atom normalization `2*pi`.

## Consequence and unpaid estimate

Appending the repair, scaled by t>=0, carries a family matched to t*w_N to one matched to t*w_M. If a cofinal family of full dual bounds were proved at levels admitting those repair tests, with lower bound E-tau(M)-epsilon and epsilon tending to zero, the exact WP02 inequality would follow at every fixed cutoff and aperture. PROOF.md supplies the complete passage, including t=0.

**Unpaid:** source-derived archimedean lower bound on the whole matched-test cone at the cofinal levels. No positive producer, endpoint attainment or RH proof is supplied.

## Lean evidence

Module: `formal/GaloisForLFunctions/RHTower/WeilWorkExposingRayTailRepair.lean`.

Main declarations:

- `RHTower.exposingRepair_sum_atoms`
- `RHTower.exposingRepair_mass_eq_tail_sub`
- `RHTower.exposingRepair_energy_le_tail_sub`
- `RHTower.exposingRepair_uniform_vanishing`
- `RHTower.exposingRepair_level_le`

`lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayTailRepair.lean` exited 0. Scratch axiom audit exited 0; audited capstones use only `propext`, `Classical.choice`, `Quot.sound`. No added axioms, numerical computation, heartbeat increase or full build. The module is wired into RHTower under the user's explicit instruction.

Latest formal lint exited 1 on twelve unrelated umbrella-reachability errors; neither WP02 module is named. EVIDENCE.md records their scope. Existing work was preserved.

## hgtl7 assessment

- **New scientific knowledge beyond literature and corpus?** Not established. Tail repair quantifies an existing internal mechanism. The collective packet lower bound was not found in the inspected corpus sources, but its uncertainty parent is classical and retrieval coverage was incomplete.
- **Rediscovery?** Yes: the ground-state identity was already formalized; a proposed logarithmic-cost argument meets known logarithmic-Laplacian/uncertainty theory. These are not counted as breakthroughs.
- **Theatre?** Reporting this as RH progress through a new positivity estimate would be theatre. The actual deliverable is a verified extension budget required by the first milestone.
- **Frontier moved?** Cutoff transport is explicit in Lean; the collective packet family has a uniform source lower bound, and the whole smooth compact primitive interface has an explicit mass-penalty inequality. The hard positivity frontier for arbitrary matched mixtures remains unchanged.
- **Avoiding the hard problem?** The source sign was investigated but not proved. No effort estimate was used to exclude it. Further work must target the collective constrained source inequality.
- **Next cycle:** return to the exact gamma/arithmetic residual on the matched cone. Test whether the compact-primitive Green representation and all integer traces provide a sharp signed estimate; reject bounds that merely add a fixed loss. Existing ground-state variance countermodels must be included in that attack.

## Cycle 6: uniform actual-source truncation

The new source result has error `C exp(-exp(2(L-1)))`, uniformly for all polar shifts c in [0,1], both for the full weighted autocorrelation and for the actual normalized archimedean energy. Source module: `WeilWorkExposingRayUniformTruncation.lean`; complete scratch passed without warnings. Final installed leaf passed without warnings; all four capstones use only propext, Classical.choice, and Quot.sound.

`UNIFORM-TRUNCATION-PROOF.md` closes this estimate on paper. `REALIZATION-PROOF.md` supplies the next construction: for every epsilon>0, all sufficiently large N admit an exact finite matched family with aperture at most (log N)/2+C and energy at most E+(1+epsilon)*tau_N. That realization is PAPER ONLY until its finite-family assembly is formalized.

Assessment: a literal-source quantitative BRIDGE. Uniformity and the double-exponential error scale improve the construction budget. No new scientific novelty beyond the audited corpus is established. The universal source lower estimate, including multiplier zero, remains unpaid; the hard positivity frontier has not moved. Next work should finish the exact construction without promoting its upper bound into a positivity claim, then attack the universal signed residual itself.

## Cycle 7: exact finite realizations at natural aperture

`WeilWorkExposingRayFiniteRealization.lean` proves an unconditional existential source theorem: one fixed C works for every epsilon>0 and all sufficiently large N, with exact complete atom trace w_N, nonnegative mixture weights, actual polar C2 tests at aperture <=log(N)/2+C, and energy <=E+(1+epsilon)*tau_N. The public prescribed-cutoff theorem retains the explicit error C exp(-exp(2(L-1))); the repair theorem retains the complete box-weighted residual cost.

Complete scratch and three-capstone axiom audits passed without warnings, using only propext/Classical.choice/Quot.sound. Final installed leaf audit passed without warnings. The module is wired into RHTower. No computation, heartbeat override, or full build was used.

This completes the constructive upper side at a quantitative scale. It does not make the full lower inequality true: a different matched family may have lower energy, and the multiplier-zero cone remains included in the unpaid target. No literature-level novelty claim. The next audit asks whether an opposite-trace near-radical source exists, and whether cone rigidity or a source obstruction rules it out; no new receiver is being added.

## Far-polar leakage: sixth formal contribution

`WeilWorkExposingRayPolarLeakage` proves a sharp obstruction to independent-atom repair of the corpus's actual far-polar Fejer sources. For X>=4, the complete weighted absolute atom budget B_X satisfies

X exp(X)/32 <= B_X <= 6 exp(1)(3+boxConst) X exp(X).

At the same time, every source is an actual C2 polar test, its energy is eventually bounded above by a fixed negative constant, and its integer atom coefficients tend uniformly to zero. Thus even uniform smallness of the entire trace is too weak for cheap box-norm repair.

The exposing-target corollary is uniform in the chosen cutoff N: with K=sum exposingMajorant, the complete error budget for matching `exposingWeightTrunc N` is at least pi X exp(X)/16-K. The second correlation window, near exp(2X), controls the scale; ignoring it incorrectly suggests a smaller cost.

This bounds the specific weighted absolute-error certificate. It does NOT bound the minimum energy of arbitrary coherent repairs, prove a negative PBAP witness, or disprove opposite-ray production. Existing far-polar construction and negative-energy theorem are reused. The new formal contribution is the full quantitative repair-budget obstruction; scientific novelty beyond this corpus is not established.

Paper proof: POLAR-LEAKAGE-PROOF.md. Scratch, axiom and final installed-module audits passed; details in EVIDENCE.md. Next primary source mechanism: COHERENT-COMPLETION-CONJECTURE.md; common-profile lattice rigidity is a secondary diagnostic. Main universal lower inequality remains OPEN.


## Cycle 9: bounded coherent completion — seventh formal contribution

`RHTower.ExposingRayCompletion.bounded_coherent_completion` proves that every far-polar Fejer source at X>=4 has a finite nonnegative repair mixture of actual C2 polar tests at exactly the same aperture X+17/50. The combined trace is zero at EVERY integer n>=2, and repair energy has one upper bound independent of X. A positive finite geometric filter and weighted variance give the construction, including an exact total spectral-density and energy identity.

This resolves the finite-mixture version of COHERENT-COMPLETION-CONJECTURE.md. The earlier single-test statement remains unproved and is unnecessary for this dual-cone application. In conjunction with the completed X exp(X) box-budget theorem, the result proves that divergent independent-atom correction estimates can coexist with bounded coherent correction costs for the same actual sources and aperture.

The selected total energy is M^2 E(f_s), with 1/201<=s<=1/200; it is not shown to approach zero. No prime-blind positivity, nonempty global cone, or WP02 universal lower bound follows. Classical finite geometric factorization and variance identities are used; external scientific novelty is unestablished. The source-specific frontier moved from an obstruction to an explicit exact completion.

Final installed leaf audit passed without warnings using `lake --old env lean`; the capstone uses only propext, Classical.choice and Quot.sound. The 478-line leaf is wired into RHTower. Current global lint reports six unrelated reachability failures, no WP02 finding; details in EVIDENCE.md.

Anti-theatre: a bounded upper completion is not a lower positivity theorem. Anti-laziness: do not pursue single-factor infrastructure merely to compress an already valid finite family; return to the literal opposite exposing source and its vanishing tail budget. Before any proposed zero-cost far-Fejer completion, audit critical-zero spectral compatibility: the original Fejer spectrum differs essentially from the near-radical Xi spectrum. Existing small-aperture ground positivity does not supply that missing endpoint estimate.
