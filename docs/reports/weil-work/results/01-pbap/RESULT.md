# WP01 interim result

**WP01 status: OPEN. Latest completed sign result: the logarithmic width transition
for a nearest-node certificate, including its nonempty positive null-mixture
sector and negative actual seed. Scientific novelty remains unestablished.**

For the explicit unit bump, let `L=log(p)/2`,
`s=log(1/abs(log(floor(exp L))-L))`, `kappa=baseMass/norm(sourceIntegral)^2`,
and `W=kappa*(L/2+s-d*log L)*exp(-L/2)`. For every fixed `d<1`, sufficiently
large primes admit no single nearest-node cosine certificate. For every
fixed `d>1`, an explicit positive coefficient works at every real frequency;
all actual real integer-null corrections then have full energy at least
`(d-1)*log L/4` times physical mass. Such corrections exist at every M>1.
Six new leaves, 26 public theorem axiom checks and all targeted/final source
audits pass. The exact d=1 point remains open.
[Proof and precise scope](JOINT-ONE-NODE-BOUNDARY.md).

The many-node extension now has dependency-closed paper proofs for every
fixed width coefficient, a growing coefficient proportional to log log L,
and arbitrary fixed complex profiles. Its discrete Lean capstones remain
OPEN. The continuous component is verified in
`WeilWorkPBAPJointContinuousCertificate`: exact cosine-transform positivity
and dilation, plus a pole-cancelling energy certificate for nonnegative real
autocorrelation. Targeted build, final direct source audit and nine standard-
axiom checks pass. This component alone does not prove the discrete extension.
[Paper arguments and remaining obligations](JOINT-MANY-NODE-CERTIFICATE.md).
`JointShortPrefix` now pays the explicit derivative-order estimate and signed
Abel variation. `JointGammaFloor` and `JointSignedCertificate` close the
continuous estimate for arbitrary complex profiles, including zero source
integral and signed real autocorrelation. All four new leaves pass targeted
builds, final direct-source audits and 24 standard-only axiom checks.

The next stronger survivor has a [source-uniform two-window paper proof](JOINT-UNIFORM-PROFILE-CERTIFICATE.md).
One fixed coefficient system would certify every allowed pair of narrow
separated windows, independently of profile derivatives, and cancel in
aggregate-null mixtures even with different profiles and separations.
Its GLOBAL positive-completion extension is ruled out by the existing
semiprime-floor obstruction. The local survivor remains Lean OPEN; no
full-PBAP or arbitrary-many-window consequence is claimed.

The preceding balanced-width sector is:

For one explicit nonnegative smooth unit-supported bump, set `L=log(p)/2` and
`W=(baseMass/norm(sourceIntegral)^2)*L*exp(-L/2)`. For every sufficiently large
prime p, the literal two-cluster seed has negative FULL energy. The actual
integer `floor(exp L)` is real-active, and its constructed cosine certificate
holds at EVERY modulation height. Consequently EVERY nonnegative finite
correction satisfying the aggregate REAL integer-null equations has full
energy at least `(L/16)*(actual physical mass)`. Corrections exist for every
prescribed total correction mass `M>1`; the sector is nonempty.

`WeilWorkPBAPJointWidthSector` contains the unconditional concrete capstones
`eventually_jointUnitBump_negative_seed_certificate`,
`eventually_jointUnitBump_null_energy`, and `exists_jointUnitBump_prime_sector`.
Seven supporting leaves prove literal dilation, uniform Gamma remainder,
exact signed pole scaling, normalized seed limit, uniform high-frequency
energy and actual integer-phase control. All eight targeted `--old` builds,
all eight final direct-source audits and all 66 named axiom checks pass;
final source diagnostics are empty and only standard Lean axioms occur.
Imports are wired. [Dependency-closed proof and audit](JOINT-WIDTH-SECTOR.md).

This controls a concrete shrinking-width family at growing prime separation.
Arbitrary profiles, widths and mixtures remain outside the theorem. Full
`PrimeBlindPositive` and its positive-completion consequence remain OPEN.
The next core is simultaneous many-node cancellation at fixed correction
mass and broad profile as the prime grows, with the full-cone gap explicit.

The next boundary audit now has four verified bridges:
`WeilWorkPBAPJointUpper` preserves the exact paired Gamma mass coefficient
and controls its centered remainder by the first Fourier moment;
`WeilWorkPBAPJointPoleBounds` proves an explicit quadratic seed pole error;
`WeilWorkPBAPJointSeedExpansion` combines them into a uniform full seed estimate;
`WeilWorkPBAPJointPrimeLag` pays the actual arithmetic phase scale.
All four targeted builds, final source audits and twenty axiom checks pass.
[The logarithmic transition](JOINT-ONE-NODE-BOUNDARY.md) now has both a
dependency-closed paper argument and formalized failure/positive-survivor
capstones. These bridges are not claimed as new scientific knowledge.


The ten `WeilWorkPBAPCritical*` leaves prove the following unconditional statement: for every `0<=a<b` and every real `C`, an actual nonnegative finite smooth mixture, null at every symmetric integer-log sample, satisfies `a Gamma+b Pole+C Mass<0`. Its mass-one version has energy below any prescribed real threshold. In particular, no gamma coefficient below the pole weight can be rescued by a constant mass allowance. The fixed half-gamma capstone has no proposition input; the proof derives and discharges all intermediate coefficient-growth, convergence and residue obligations.

The positive structural survivor is the necessary coefficient boundary `b<=a` for every positive modified completion. This extends the previously discussed gamma-free obstruction to every strict coefficient deficit. It does not prove sufficiency at `a=b`, nor positivity at the literal PBAP normalization `a=b=1,C=0`. The leading residue comparison loses `C`; the equal-weight signed finite terms remain unpaid. [Complete paper proof](CRITICAL-SLOPE.md).

All ten targeted `--old` leaf builds and all ten final `lake env lean <leaf>` source audits pass, with no source diagnostics. Twenty-two axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`. All ten imports are wired; no full or umbrella build, numerical experiment, added axiom or heartbeat increase was used. The latest global lint outcome is recorded in `EVIDENCE.md`.

Lean module `RHTower/WeilWorkPBAPNullRepair.lean` constructs an explicit positive correction of every finite logarithmic defect. The repaired mixture satisfies all integer-null constraints exactly, and its full pole-plus-archimedean energy changes by at most a specified weighted total defect. The correction tests are smooth. Targeted build, direct Lean source audit, and capstone axiom audit pass. Only standard Lean axioms occur. Module is wired into `RHTower.lean`.

`RHTower/WeilWorkPBAPGramPackets.lean` now realizes every finite PSD matrix by smooth compact Weil tests, with exact autocorrelation samples at all rational logarithms of bounded denominator. Finitely many zero divisibility-diagonal sums give cancellation at **all** integer nodes. The capstone supplies an actual nonnegative finitely supported mixture in the full PBAP interface and retains its exact mass. Direct source compilation, targeted `--old` leaf build, and ten-theorem axiom audit pass. Only standard Lean axioms occur; umbrella import added.

`RHTower/WeilWorkPBAPMomentPackets.lean` now connects actual representing probability measures on the prime torus to these packets. Its integral moment matrix is proved positive semidefinite, with zero divisible entries and explicit trace. The capstone constructs a smooth, nonnegative finite mixture with mass exactly one, every integer-null constraint, and rational samples equal to the target measure's moment times the finite coefficient correlation. Direct compilation and targeted `--old` leaf build pass; final audits are recorded in `EVIDENCE.md`.

These realization and correction leaves supply no sign theorem. They are not claimed as significant scientific frontier advances.

`WeilWorkPBAPJointConvex`, `JointPhase`, and `JointEscape` classify exact simultaneous shifted-log cancellation: for every prime p>=5, every frequency threshold and total correction mass M, a finite nonnegative correction exists exactly when M>1. Strictly positive weights suffice with at most p−1 frequencies. Any two distinct positive nodes below p forbid a common negative endpoint phase; their exact constraints force logarithmic frequency cost to diverge as M approaches one. Targeted builds, final direct source audits and 17 axiom checks pass. These are classical-mechanism bridges with scientific novelty unestablished. Full PBAP remains open.

`JointProfiles`, `JointNull`, and `JointActive` complete the actual broad-profile interface. They construct smooth nonnegative finite mixtures with every integer null constraint and exact mass, then identify real nullness precisely with phase cancellation at the real-active shifted nodes. Two such distinct nodes force logarithmic-cost escape without extra equations at inactive nodes. All six Joint leaves now pass targeted builds and final direct-source audits; all 40 named axiom checks use only standard Lean axioms. The completed statement is a fixed-profile boundary obstruction, not the full-energy sign or a uniform bound as the prime varies.

`JointFourier` adds exact modulation and translation formulas at complex Fourier arguments, the paired density with its interference factor, and an inverse-quartic central-band density bound. Its targeted build, final direct-source audit and seven axiom checks pass.

`JointCoercivity`, `JointEnergy`, and `JointEnergyEscape` now prove the literal full-mass lower bound `e(T)>=2m log(2+|T|)-C`, with an explicit finite nonnegative cost retaining both signed poles. For fixed profile and prime, two real-active shifted nodes force actual real-null mixture energy, and energy divided by actual physical mass, to diverge as correction mass decreases to one. No energy lower-bound premise or extra nonzero-profile premise is introduced. Three targeted `--old` builds, three final direct `lake env lean <leaf>` source audits, and 24 named axiom checks pass, standard axioms only. All ten Joint leaves and 71 named checks are complete and wired. This closes the fixed-profile boundary energy diagnostic; positivity away from that boundary, uniform variation of prime/profile, and arbitrary-mixture extension remain open. Scientific novelty remains unestablished.




`RHTower/WeilWorkPBAPSpectralMeasure.lean` constructs the actual probability density from the Fourier squares of a normalized nonnegative mixture, then pushes it onto the prime torus. Every rational character moment equals the corresponding autocorrelation sample exactly. Its capstone realizes representing-measure moments with the earlier finite coefficient multiplier using smooth, normalized, complex-integer-null mixtures. Targeted build and nine-declaration axiom audit pass; the final direct-source audit is recorded in `EVIDENCE.md`. The complex-null subclass is stronger than WP01's real constraints; this leaf does not claim the converse without symmetrization.

`RHTower/WeilWorkPBAPPacketFourier.lean` and `RHTower/WeilWorkPBAPPacketEnergy.lean` now prove the full signed energy bound for the actual narrow integer packets, with arbitrary complex coefficients and no null premise. For `N>=1`, `L>=104`, energy is at least packet mass times `(1/4)*log N-11`. The sharper bound retains `(1/2)*log(1+N*L/4)-10-(2/L)*sqrt(1+log N)`. `gramPacket_uniform_energy_escape` proves uniform divergence per unit mass as `N` grows, including both pole terms. Targeted builds, final direct-source audits, and all twenty theorem axiom checks pass; both leaves are wired into the umbrella.

This closes the narrow-packet energy diagnostic in `PACKET-ENERGY.md`: arbitrary signs cannot make this realization preserve bounded full energy as its packet count grows. The mechanism is the corpus's Montgomery–Vaughan estimate plus a joint signed-pole bound. General overlapping tests and aggregate real integer cancellation remain outside the theorem. No full PBAP producer or scientifically novel general positivity mechanism is claimed.

Two proposed routes failed novelty audits: scalarization already appears in corpus L248 and classical convolution-root theory; the contemplated small two-window positivity sector is covered by the current full-support theorem. The unresolved problem is still arbitrary signed mixtures with aggregate integer cancellation and both pole terms retained.

`WeilWorkPBAPJointSourceBudget` adds source-uniform width/mass Fourier and
Gamma bounds, including the integrated logarithmic singularity. All eight
public theorem checks, targeted build and final direct-source audit pass;
import wired. These are supporting components for MC6. Its paper proof now
has the MC7 extension to a growing number of separated narrow windows;
both positivity capstones remain Lean OPEN. No new scientific novelty or
full PBAP solution is claimed from these technical bounds.

`WeilWorkPBAPJointLogQuadrature` now supplies complex integer-grid
quadrature, the exact logarithmic substitution and finite Abel variation
for the literal cutoff weights. Seven public audits pass, with targeted
build and empty final direct-source diagnostics; import wired. Together
those six support leaves have 39 standard-only theorem checks. The
paper's strongest sparse-window survivor is MC8, using geometric row sums
to allow spacing 4 log log log D. MC6 and MC8 remain Lean OPEN.

`WeilWorkPBAPJointFixedCutoff` instantiates the literal even plateau and
the normalized hyperbolic pole weight. Its uniform first/second derivative
bounds, exact leading integral with quadratic width error, and complex
inverse-square Fourier decay are fully audited. Targeted build and final
direct-source checks pass; 28 public axiom checks use only standard axioms.
Seven supporting leaves now have 67 checks. The paper's order-selection
proof also reuses the corpus window-landing theorem, reducing the remaining
middle-frequency work to three actual interval budgets. Neither change
closes MC6, MC8 or full PBAP, or establishes scientific novelty.

`WeilWorkPBAPJointGridGeometry` now discharges the interval geometry for
the concrete growing width at every positive b. It proves the actual
floor/ceiling endpoint bounds, dyadic containment, short length and full
logarithmic cutoff coverage eventually in L. Targeted and final-source
audits plus six standard-only axiom checks pass. Eight supporting leaves
now have 73 checks.

`WeilWorkPBAPJointGrowingOrder` pays the growing factorial cost and all
three order-window inequalities on that actual interval. Every frequency
from `exp(L)/sqrt(L)` to `exp((c log log L+1)L)` receives an admissible
order, and every prefix gains `exp(-(log L)^(1-c log2)/16)`.
Targeted/final audits and all nine standard-only axiom checks pass; import
wired. Nine supporting leaves now have 82 checks.

`WeilWorkPBAPJointMiddleCutoff` closes the actual complex middle-frequency
error bound for both frequency signs. Its exact pole factor leaves a
source-independent sublinear loss. Targeted/final audits and eleven
standard-only axiom checks pass; import wired. Ten supporting leaves now
have 93 public checks.

`WeilWorkPBAPJointGridFrequency` pays complex quadrature, the low-band
sublinear loss, and the high-band envelope with its exact leading plateau
mass. Above the growing ceiling it leaves 3L/4 against log|t|. All twelve
public source/axiom audits pass; import wired. `WeilWorkPBAPJointSymbolFloor`
now joins all frequencies and integrates the actual corrected symbol against
arbitrary narrow-source Fourier densities, leaving L/3 times physical mass.
Its two-source theorem also pays the literal choice b=1/(8 log2). Twelve
supporting leaves have 114 standard-only public axiom checks. Literal
source-energy identities and the MC6/MC8 positivity capstones remain open.

`PROOF.md` gives the exact repair proof and labels the unformalized scalarization argument. `EVIDENCE.md` records commands, sources, and lint outcomes. `TORUS-DENSITY.md` contains the closed finite-realization proof and the larger construction of exact integer-null mixtures approximating prime-torus representing measures, with an explicit obstruction to the stronger Jensen claim. The representing-measure connection, packet-mixture normalization, and actual spectral pushforward are formalized. Prime-exponent-box counting, weak convergence, and Jensen transfer remain unformalized. The Jensen route is not retired as a proved no-go. The working card `docs/drafts/pipeline/1-in-progress/weil-work-01-pbap.md` tracks continuation. No producer or solution is claimed.

`WeilWorkPBAPMollifierCausality` proves the exact one-sided second-order pole integral and its finite complex-frequency tail. It corrects the frozen-coefficient Lorentzian step of the L398 GY obstruction sketch: positive displacement annihilates the bare pole. It does not estimate the actual window with its zeta factor or settle either opposing GY conjecture. Targeted `--old` build, final direct source audit and seven standard-only axiom checks pass; import wired. This is a classical bridge, with no scientific novelty claim. See `GY-CAUSALITY-AUDIT.md`.

`WeilWorkPBAPJointJump` and `WeilWorkPBAPJointModulation` prove the exact full-energy increment
`e(T)-e(0)=integral K_L(y)*Re autocorr(beta)(y)*(1-cos(Ty))`, including both signed poles.
For support `[0,W]` and `L>2W`, the kernel is strictly positive on `(0,W]`.
Consequently profiles with nonnegative real autocorrelation minimize this paired energy at zero
modulation, where it equals the literal unmodulated cluster energy. That minimum can be negative;
the theorem does not settle arbitrary real-null mixtures or full PBAP. Both targeted builds and
final direct-source audits pass; all 11 named axiom checks use standard axioms only. Both imports
are wired. This is a verified bridge, without a significant scientific novelty claim. The general
cosine-certificate construction outside the explicit width sector and the proposed stronger
Levy-residual classification remain open.

`WeilWorkPBAPJointUniformHigh` and `WeilWorkPBAPJointBoundarySeed` now retain
the two exact coefficients needed by the logarithmic one-node boundary:
`2 log|T|` uniformly at high frequency, and `2(d-1)log L` after the actual
seed's phase-scale cancellation. Actual-prime specialization derives the lag
range and width geometry. Both targeted builds, final direct-source audits,
and fifteen public axiom checks pass. Four subsequent boundary leaves finish
the classification: d<1 forbids every nearest-node cosine certificate;
d>1 supplies one at all real frequencies, with a negative actual seed and
positive full energy for every real integer-null correction. The margin is
`(d-1)log L/4` times physical mass. This sector is nonempty at every M>1 for
all sufficiently large primes. All six new leaves pass targeted builds,
final direct-source audits and 26 standard-only public axiom checks. The
exact d=1 point and full PBAP remain open. See `JOINT-ONE-NODE-BOUNDARY.md`.
