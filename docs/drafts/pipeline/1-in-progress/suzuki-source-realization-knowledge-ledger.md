# Suzuki source-realization knowledge ledger

- **ID:** `suzuki-source-realization-knowledge-ledger`
- **Stage:** 1-in-progress
- **Type:** RESEARCH CONTROL / ANTI-REDISCOVERY LEDGER
- **Terminal objective:** prove RH, disprove RH, or prove a class-complete no-go for Suzuki's
  source-to-operator mechanism.
- **Current terminal verdict:** open.
- **Read first:** this file, `suzuki-terminal-frontier-ledger.md`, and every cited failed card.

## Admission rule

A result enters the **advance** column only if it changes a source-side statement before
specialization to a zeta-zero or co-Poisson annihilator character. The following never count as an
advance by themselves:

1. an RH-equivalent sign, norm, innerness, dense-range, or zero-free criterion;
2. an abstract Douglas, Schur, de Branges, Pick, Krein, colligation, or sum-of-squares wrapper;
3. a generic projection, trace, Bianchi, parity, or Ward identity;
4. a renamed theorem already present in the corpus;
5. Lean formalization of one of items 1--4.

Formal closure and no-go results remain valuable, but must be labelled as such. They prevent loops;
they are not novel scientific knowledge.

## Status vocabulary

- `PARENT`: standard mathematics or stated in cited literature.
- `CORPUS-KNOWN`: already present in project before current attack.
- `FORMAL-CLOSURE`: unconditional Lean bridge or anti-loop theorem, not new science.
- `FAILED-CLASS`: precise mechanism class killed; stronger classes remain possible.
- `LIVE-SOURCE`: unresolved statement about explicit source data before divisor specialization.
- `PRIOR-ADVANCE`: source theorem which genuinely moved frontier, but was already in corpus before
  current ledger attack.
- `ADVANCE`: new proved source theorem that strictly narrows or discharges a `LIVE-SOURCE` row.

## Knowledge register

| ID | Status | Exact knowledge | What it does **not** solve | Rediscovery fingerprint / controlling record |
|---|---|---|---|---|
| `SR-01` | `PARENT` / `CORPUS-KNOWN` | Normalized dilation has Mellin character `r^(w-1/2)` and transports only the projected cross-aperture evaluator; an orthogonal defect remains. | No fixed-aperture eigenvector, sign, or unitary quotient action. | “dilation eigenvalue,” “projected evaluator law”; `burnol-prime-dilation-copoisson-quotient-law.md` |
| `SR-02` | `CORPUS-KNOWN` | Difference of inverse/forward cross-aperture defect energies is exactly `(r^(2 Re w-1)-r^(1-2 Re w)) ||k_w^a||^2`. | Comparing those defects from source data. | “bilateral defect balance,” “hyperbolic sine orientation”; `burnol-bilateral-aperture-defect-energy-law.md` |
| `SR-03` | `CORPUS-KNOWN` | Burnol's closed co-Poisson source space has quotient `C_b^perp`; its projected kernels give a faithful Berezin diagonal. Quotient correction is in the real-analytic ideal `(Lambda_b, conjugate Lambda_b)`. | Sign of the Berezin diagonal on its annihilator variety. | “source-defined quotient,” “Berezin diagonal,” “ideal correction”; `burnol-copoisson-berezin-diagonal-reflection-law.md` |
| `SR-04` | `PARENT` / `CORPUS-KNOWN` | Full quotient order is equivalent by Douglas factorization to a contractive forward-through-inverse channel factorization. Fourier reflection makes either semidefinite order saturate to flatness. | Construction of contraction from co-Poisson seeds. | “Douglas contraction,” “parity block vanishes”; `burnol-copoisson-quotient-bilateral-order-rh-law.md` |
| `SR-05` | `CORPUS-KNOWN` | Compactly supported divided differences give explicit co-Poisson radical vectors. | Lifting their two-prime polarized operator to Sonin time-band ideal. | “finite log-support seed,” “co-Poisson/time-band lift”; `burnol-copoisson-prime-seam-calkin-lift.md` |
| `SR-06` | `CORPUS-KNOWN` | Suzuki's completed causal quotient is unconditionally contractive through safe exponential width `omega`; target width is `omega+1/2`. Missing width is exactly `1/2`. Off-line zeros form denominator model-space defect. | Crossing critical half-weight from Euler--Gamma source. | “weighted Schur seam,” “half-unit,” “full graph domain”; `ccm-completed-quotient-weighted-schur-seam-law.md` |
| `SR-07` | `FAILED-CLASS` | A generic source-framed conservative colligation merely repackages the four-unit/RH target unless metric, boundary defect, and strong limit are independently source-built. | Source-fixed causal metric or limit. | “construct a colligation,” “choose a metric”; `source-framed-conservative-colligation-four-unit-rh.md` |
| `SR-08` | `FAILED-CLASS` | Positive finite-valued cofinal extensions of nonsummable sharp-source mass fail, even on nonunital domains containing one completed positive profile. | Signed, fibre-pointed, non-conic source laws. | “positive finite part,” “semifinite trace fixes divergence”; terminal ledger items 12--13 |
| `SR-09` | `FORMAL-CLOSURE` | Fixed-aperture principal/relative splitting, cyclic logarithmic shell value, aperture lost-mass cocycle, and Schatten-1 curvature are exact. | RH orientation or co-Poisson fibre sign. | “principal shell trace,” “aperture anomaly”; `SoninPrincipalShellCyclicTrace.lean`, `SoninApertureCyclicMassConservation.lean` |
| `SR-10` | `FORMAL-CLOSURE` | Aperture curvature trace is a negative Hilbert--Schmidt square with canonical Ward cancellation. Bianchi makes scalar curvature an exact coboundary. | A nontrivial source orientation; exactness removes rather than supplies it. | “Ward energy,” “curvature cohomology”; `SoninApertureWardCurvature.lean`, `SoninApertureWardPotential.lean` |
| `SR-11` | `FAILED-CLASS` | Fourier-invariant complex-linear readers kill Fourier-odd bilateral holonomy; they equal positive Ward energy only in flat case. | Fibre-pointed, reflection-covariant readers. | “invariant relative trace reads holonomy”; `SoninApertureFourierParityNoGo.lean` |
| `SR-12` | `PARENT` / `CORPUS-KNOWN` | Complete-Pick, Schur-realization, Hermitian-square, and Positivstellensatz language can turn an already-proved kernel inequality into a factorization. | Source proof of inequality; Burnol space is not established here as a complete-Pick carrier with needed ideal saturation. | “negative square modulo ideal follows abstractly,” “Pick interpolation solves sign” |
| `SR-13` | `CORPUS-KNOWN` / `LIVE-SOURCE` | Determine whether explicit compactly supported co-Poisson summation supplies a one-sided causal polarization at critical half-weight. | This is not implied by reflection, quotient construction, or generic colligation theory. | Already named as `(ER12)` and the cofinal source-bornology/passivity core in `critical-multiplicative-compensated-cancellation-rh.md`. |
| `SR-14` | `CORPUS-KNOWN` / `LIVE-SOURCE` | Equivalently, produce before annihilator specialization a source identity `A_-A_-^*-A_+A_+^*=S^*S + R Lambda_b + Lambda_b^* R^*`, or a source-defined contractive factorization `A_+=A_-C`. | Writing either identity as a conjecture is not an advance; deriving its terms from seed map is. | `(ER12)` in existing co-Poisson/affine-residue audit. |
| `SR-15` | `CORPUS-KNOWN` / `FORMAL-CLOSURE` | Actual finite Müntz aperture operator, its positive Gram, exact finite Möbius reconstruction, visible radical, and local frame bounds already exist. | Cofinal closed range, source-selected norm, and boundary passivity. | `ConstrainedProlateTrueApertureMetric.lean`; `constrained-prolate-true-aperture-xi-moment-metric.md` |
| `SR-16` | `CORPUS-KNOWN` / `FAILED-CLASS` | `C_0` sampling is maximally blind; ambient `L2` has no point evaluation; finite-type analytic sampling can be injective while stable synthesis still fails. | Actual adjoint-range membership/closed range in source-selected topology. | `archimedean-sampling-total-variation-defect.md` |
| `SR-17` | `LIVE-SOURCE` | Construct cofinal source bornology in which exact difference-lag Stieltjes/co-Poisson boundary functional belongs to adjoint range with uniform passivity. | Algebraic Möbius inversion at each finite cutoff is insufficient; uniform graph norm is RH-bearing. | General open problem below; latest no-go chain in `critical-multiplicative-compensated-cancellation-rh.md`. |
| `SR-18` | `CORPUS-KNOWN` / `PRIOR-ADVANCE` | Polar--Gamma completion of the exact Suzuki tent is pointwise positive and the prime wall is its exact Mangoldt quadrature. | Domination of that quadrature by completed mass. | S66 in `docs/handover/sota-suzuki.md`; `suzuki-positive-arch-mangoldt-quadrature-deficit.md` |
| `SR-19` | `CORPUS-KNOWN` / `FAILED-CLASS` | Exact log-Haar cells discharge monotone bulk, but source-aligned prime powers are unique moving apices; every pointwise-dominating payment set is null. | Aggregate/source-operator compensation across the turning seam. | S67--S68; `SuzukiMangoldtLogHaarTransport.lean`; `SuzukiMangoldtApexLock.lean` |
| `SR-20` | `CORPUS-KNOWN` / `FAILED-CLASS` | Macroscopic width-five prime blocks have unbounded source surplus, but inclusion--exclusion and an atomless hostile measure prove that no scalar capacity-one transport theorem follows from this information class. | Operator-valued, source-specific prime--Gamma compensation. | S69--S72; `SuzukiBicausalNoFreeSplice.lean`; `SuzukiCriticalApexVacuumCapacityNoGo.lean` |
| `SR-21` | `CORPUS-KNOWN` / `FAILED-CLASS` | Coherent causal response loses a factor `1/(p+1)` relative to exact sharp source at its moving aperture. Bounded/frame-preserving recovery is impossible. | Closed unbounded relative observation or a different source channel. | S73; `SuzukiCoherentResponseGainNoGo.lean` |
| `SR-22` | `CORPUS-KNOWN` / `FORMAL-CLOSURE` | Faithful Sonin normal states carry a canonical cyclic logarithmic shell trace returning `m log p` on a prime-power Gram factor. | A cofinal signed completed lower floor. | S74; `SoninPrincipalShellCyclicTrace.lean` |
| `SR-23` | `CORPUS-KNOWN` / `FAILED-CLASS` | Exact all-prime sharp source has nonsummable squared norm, excluding ordinary `ell^2` recovery even through an unbounded graph and every fixed scalar renormalization. | Singular cutoff boundary spaces with non-Hilbert principal part. | S75; `SuzukiCoherentSharpSourceDomainNoGo.lean` |
| `SR-24` | `CORPUS-KNOWN` / `FAILED-CLASS` | No finite-valued positive cofinal finite part can preserve sharp cutoff masses; removing the unit still fails for every completed Mellin profile in the RH-bearing strip. | Signed non-conic anomaly fixed on a normalized source family. | S76--S77; `SuzukiCofinalPositiveFinitePartNoGo.lean`; `SuzukiCompletedMellinPositiveDomainNoGo.lean` |
| `SR-25` | `CORPUS-KNOWN` / `FORMAL-CLOSURE` | Fixed-aperture signed finite part is unique. Strict aperture loss exits the Schatten-1 ideal, but is an existing principal shell whose cyclic mass is exactly conserved; only trace-class curvature remains. | Fibre orientation after principal mass subtraction. | S78--S79; `SoninPrincipalRelativeTraceSplitting.lean`; `SoninApertureCyclicMassConservation.lean` |
| `SR-26` | `CORPUS-KNOWN` / `FAILED-CLASS` | Curvature is a faithful negative Hilbert--Schmidt square, globally exact by Bianchi, and every Fourier-invariant complex-linear reader kills the Fourier-odd bilateral holonomy. | Fibre-pointed readers exchanged rather than fixed by reflection. | S80--S81; rows `SR-09`--`SR-11` |
| `SR-27` | `CORPUS-KNOWN` / `FORMAL-CLOSURE` | A fixed dyadic BV prime window detects every right off-critical zero. Its Laurent residue transforms under square-index decimation by `r^(2w-1)`, exactly the Burnol horizontal character. | Source construction of a positive critical completion on which decimation is contractive and Laurent evaluation is bounded. | `bv-prime-window-laurent-orientation-polarization.md`; `bv-prime-window-polar-coefficient-decimation-law.md` |
| `SR-28` | `CORPUS-KNOWN` / `LIVE-SOURCE` | Finite coefficient cutoffs satisfy an exact positive Stein identity: total energy minus decimated energy is off-multiple energy. Ordinary Dirichlet--Hardy space excludes every uncensored source. | Canonical scale-zero boundary Gram retaining meromorphic principal parts. | `bv-prime-window-decimation-boundary-contraction-rh.md` |
| `SR-29` | `CORPUS-KNOWN` / `FAILED-CLASS` | Making coefficient inflation a contractive inverse/coisometry collapses the off-multiple layer, whose Laurent residue is the nonzero fraction `1-r^-2` of the source residue. | Genuinely one-sided completion in which inflation is unbounded or discontinuous. | Sections 3 and 5 of `bv-prime-window-decimation-boundary-contraction-rh.md` |
| `SR-30` | `FORMAL-CLOSURE` | Proposed insertion of `criticalMellinStieltjesPairing` into the adjoint of `trueApertureMuntzMap` is ill-typed at source level: the former is a functional on lag profiles/autocorrelations, while the latter is a Sonin `L2 -> L2` dilation sum. No canonical connector between them exists in corpus. | A separately constructed source map could connect them, but finite divisor Möbius algebra does not. | Exact definitions in `CCMPolarPrimeStieltjesAutocorrelation.lean` and `ConstrainedProlateTrueApertureMetric.lean`; collision caught 2026-07-22 |
| `SR-31` | `CORPUS-KNOWN` / `PRIOR-ADVANCE` | Actual all-depth von-Mangoldt--Gamma anomaly has strict common orientation; finite radial Cauchy Grams, two-boundary balance, arbitrary-order Hermite boundary packets, and cofinal square summability are already closed. | Transport from inverse prime-log Cauchy features to positive prime-log Mellin jets. | `prime-gamma-reflection-decimation-defect-resolvent-rh.md`, `(22c)`--`(22i)` |
| `SR-32` | `CORPUS-KNOWN` / `FAILED-CLASS` | Finite rational/log-order unbalancing, diagonal positive-log repair, fixed scalar Gamma conductor, and direct successor-Dirichlet Gram identification all fail. Diagonal repair already has divergent energy on prime slice. | Infinite-rank off-diagonal coupling with Gamma/polar modes before norm. | `PrimeMellinJetDiagonalEnergyNoGo.lean`; `prime-gamma-reflection-decimation-defect-resolvent-rh.md`, `(22j0)`--`(22j7)` |
| `SR-33` | `LIVE-SOURCE` | Construct singular or locally finite off-diagonal incidence converting balanced inverse-log Cauchy packets to positive-log Mellin jets, with growing Gamma/polar channel capacity or source-fixed principal-relative subtraction before norm; prove completed Green--Schur trace preserves Euler source law. | Abstract singular completion, positive carrier, bare moment identity, fixed scalar conductor, or uniformly Ward-bounded finite-packet family is insufficient. | Exact open arrows `(22j7)` and `(22j)` in `prime-gamma-reflection-decimation-defect-resolvent-rh.md`; narrowed by `SR-34`--`SR-35` |
| `SR-34` | `FAILED-CLASS` / `FORMAL-CLOSURE` | A linear incidence commuting with every resolved channel projection is exactly diagonal, without finite-dimensional or continuity assumptions. Its off-diagonal transfers vanish. Finite total projection-commutator energy is exactly twice off-diagonal Frobenius energy and vanishes exactly on diagonal maps. Combined with positive-log prime-energy divergence, no fully resolved channel-preserving incidence can realize a summable Mellin jet. | Connection-covariant completed trace preservation can mix channels because individual commutators need not vanish. | `resolved-euler-channel-ward-mixing-no-go.md`; `ResolvedChannelWardLaw.lean`; `PrimeMellinJetResolvedChannelNoGo.lean` |
| `SR-35` | `ADVANCE` | Universal Ward--Schur law converts weighted off-diagonal coherence lower bound `L` into `2L^2 <= E_comm W <= E_comm S^2`. For actual Gamma cyclic coupling and fixed scalar conductor capacity `B`, positivity forces `E_comm>=2(S/B-1)^2` once accumulated prime Schur cost `S>=B`. Since `S` is cofinally unbounded, every fixed `B` forces cofinally unbounded resolved commutator energy. | Does not construct source-canonical singular finite part, growing Gamma channel family, or completed Euler trace identity. | `resolved-euler-channel-ward-mixing-no-go.md`; `gammaConductorResolvedWardCapacity_lower`; `exists_primePacket_gammaConductor_resolvedWardEnergy_gt` |
| `SR-36` | `ADVANCE` | For an arbitrary self-adjoint parity, every correction family in its even sector leaves the exact odd packet Gram as a capacity-independent Pythagorean floor. For the actual Gamma measure this floor is `O(t,u)=(phi(t-u)-phi(t+u))/2`; at every prime log, `O(log p,log p)>=(1-sqrt(2)/2)/2`. Weighted by the actual nonsummable Gamma conductor Schur costs, the protected residual is nonsummable and cofinally exceeds every finite budget. Thus growing reflection-even Gamma/Jacobi boundary capacity is class-completely dead. | Odd/parity-mixing boundary modes and signed principal-relative finite parts are not even-sector Hilbert corrections and remain possible. | `gamma-even-boundary-parity-floor-no-go.md`; `ParityProtectedSchurFloor.lean`; `GammaEvenBoundaryParityNoGo.lean` |
| `SR-37` | `ADVANCE` | Actual odd Gamma-Jacobi coefficients satisfy the exact Mercer law `O(t,u)=sum_k a_k(t)a_k(u)`. Finite odd capacity leaves precisely the positive tail, and the least source rank at each prime making its actual Gamma-conductor-weighted diagonal at most `p^-2` yields a summable all-prime residual. | Pointwise ranks alone do not place this boundary inside Suzuki's completed Green--Schur incidence or prove Euler-source compatibility. | `gamma-odd-jacobi-capacity-saturation-law.md`; `GammaOddJacobiCapacity.lean` |
| `SR-38` | `ADVANCE` | Least primewise ranks can be zero-padded in the common absolute odd-Jacobi coordinate. The resulting cross-prime residual is positive semidefinite on every finite packet, its diagonal is exactly the `SR-37` tail, and its Gamma-conductor-weighted diagonal is summable. Thus odd capacity and cutoff/inclusion coherence are closed without a common rank. Generic Gram/capacity lemma is only `FORMAL-CLOSURE`; source connector is advance. | Coherent positive kernel is not yet the singular/local finite incidence or completed trace required by Suzuki. | `GammaOddJacobiCoherentCapacity.lean`; `AdaptiveMercerCapacity.lean` |
| `SR-39` | `ADVANCE` | Successor Dirichlet Gram has an exact all-order strictly negative Hankel-curvature density. Hence every additive ordinary Hankel boundary is class-completely incapable of repairing it. Placing the actual pointed Gamma--Bianchi raw feature in the same finite von Mangoldt coordinates instead gives the exact endpoint weld `difference + tail = head`; its forced mixed block has the exact opposite positive curvature, and the coupled Gram is a positive moment-Hankel matrix for every finite aperture and jet size. | Raw pointed boundary has no ordinary cofinal Hilbert limit. Finite Hankel welding does not incorporate odd Gamma-Jacobi capacity, completed Euler trace, or critical normalization. | `von-mangoldt-successor-bianchi-hankel-curvature-weld.md`; `ConservativeHankelRigidity.lean`; `VonMangoldtAdditiveLogJetHankelCurvature.lean`; `VonMangoldtSuccessorBianchiHankelWeld.lean` |
| `SR-40` | `ADVANCE` | Source-fixed principal subtraction of the exact finite weld is absolutely summable at every jet order. It retains exactly `Successor+Cross`, converges in every finite matrix topology to universal kernel `R(r,s)=rho_(r+s+2)`, and obeys all-order Hankel shift. Forced mixed curvature therefore survives and cancels successor defect at every aperture and order. | Signed jet current is not yet a positive/Krein source realization; coherent odd Gamma--Jacobi kernel lives on prime coordinates and cannot be added to jet matrix without a proved bivariate connector. Completed Euler trace and critical orientation remain open. | `von-mangoldt-successor-principal-relative-hankel-current.md`; `VonMangoldtSuccessorPrincipalRelativeHankel.lean` |
| `SR-41` | `LIVE-SOURCE` | Construct or class-completely refute an inclusion-compatible bivariate prime--jet completion whose jet compression is `SR-40` principal-relative Hankel current, whose prime/Jacobi compression is `SR-38` coherent odd Gamma residual, and whose cyclic source reader gives completed Euler multiplication/trace before Xi character or target moment is read. | By `SR-42`, positive and every fixed-index Pontryagin completion are impossible. By `SR-43`, ordinary coordinate partial trace is impossible at every index. Abstract finite matrix completion, separate direct sum, target-fitted cross block, generic Krein spectral decomposition, or trace-preserving marginalization does not count. | Exact post-`SR-40` operator-realization core below |
| `SR-42` | `ADVANCE` / `FAILED-CLASS` | Every full `SR-40` aperture section is a square Vandermonde congruence of explicit endpoint-divergence masses, so its positive, negative, and null indices are exact sign counts. Left endpoint is always negative. Primes `p>3`, `p=3 mod 4`, force distinct negative masses; negative index is unbounded. | No positive or fixed-index Pontryagin bivariate completion can realize all jet compressions. Surviving `SR-41` object must be genuinely infinite-index Krein, source-canonical, restriction-compatible, and still realize `SR-38` marginal plus completed Euler trace. | `von-mangoldt-successor-transport-inertia-law.md`; `SignedAtomicMomentInertia.lean`; `VonMangoldtSuccessorTransportInertia.lean` |
| `SR-43` | `ADVANCE` / `FAILED-CLASS` | Every finite bivariate coordinate-partial-trace realization has equal total traces on its jet and source marginals. Actual `SR-40` trace obeys exact opening law `tr R_(M,N+1)=tr R_(M,N)+rho_M(2N+2)` with strictly positive source flux at every nonempty aperture. Hence no fixed source marginal—specifically no finite `SR-38` coherent odd Gamma--Jacobi marginal—can coexist with two consecutive `SR-40` jet marginals, for arbitrary real kernels, arbitrary mixed block, and arbitrary Krein index. | Ordinary normal partial trace is class-completely dead. Surviving `SR-41` connector must vary source marginal with jet cutoff or use a singular, weighted/renormalized, non-trace-preserving cyclic reader carrying the explicit positive flux. | `von-mangoldt-bivariate-marginal-trace-lock-no-go.md`; `BivariateMarginalTraceLock.lean`; `VonMangoldtBivariateMarginalTraceLock.lean` |

## Level lift forced by `SR-35`--`SR-43`: bivariate prime--jet source completion

Current source problem belongs to more general problem of **source-renormalized covariant
Dirichlet forms relative to a resolved abelian channel algebra**.

For finite channel packet `F`, resolved projections `P_i`, and source incidence `T_F`, define

```text
delta_i(T_F)=T_F P_i-P_i T_F,
Gamma_F(T)=sum_(i in F)||delta_i(T_F)||_F^2.
```

`SR-34` proves flat connection `delta_i=0` is diagonal and cannot realize positive-log source.
`SR-35` proves fixed scalar Gamma capacity forces `Gamma_F(T)` to exceed every finite threshold
cofinally. `SR-36` kills every reflection-even growing boundary. `SR-37`--`SR-38` construct the
opposite-sector odd Gamma--Jacobi ladder and coherent summable residual. `SR-39` solves finite
placement: successor and pointed Bianchi boundary must share source coordinates, and forced mixed
block restores Hankel balance. `SR-40` solves signed cofinal jet current: source principal
subtraction retains that mixed block, converges, and is Hankel at every order. `SR-42` computes
its exact finite-section inertia and proves negative index unbounded, excluding Hilbert and every
fixed-index Pontryagin realization. `SR-43` then excludes coordinate partial trace at arbitrary
index: the two marginal traces must agree, but every new `SR-40` jet opens a strictly positive
source flux while the `SR-38` marginal is fixed. Capacity, packet coherence, finite cross-term
placement, matrix-entry cofinal renormalization, finite-index completion, and ordinary normal
partial trace are no longer open. Remaining issue is object-level coupling: `SR-40` is a jet
kernel after prime contraction,
whereas `SR-38` is a prime kernel after Jacobi contraction. Adding them is ill-typed. One bivariate
prime--jet source object must realize both marginals and Euler trace in infinite-index Krein
geometry through a singular or non-trace-preserving reader that exposes the exact jet-opening
flux.

Scientific-method question is now:

> Does there exist a source-fixed, inclusion-compatible bivariate prime--jet completion whose jet
> marginal is the proved principal-relative Hankel current and whose prime marginal is the proved
> coherent odd Gamma--Jacobi residual, with completed Euler multiplication encoded by one cyclic
> reader before completed moments or Xi characters are read?

Required data and conjectural identity are

```text
P_F                    resolved finite prime carrier,
V_N                    positive logarithmic jet carrier,
A_F                    common absolute odd-Jacobi carrier,
R_(F,N)                proved principal-relative jet form `Successor+Cross`,
J_F                    proved coherent odd Gamma-Jacobi prime form,
C_(F,N)                sought source bivariate coupling on `P_F x V_N x A_F`,
tau_(F,N)              sought cyclic reader fixed by Euler source algebra,

jetCompression(C_(F,N))=R_(F,N),
primeCompression(C_(F,N))=J_F,
tau_(F,N)(C_(F,N))=completed Euler trace packet,        (SR41)

with restriction-compatible `C_(F,N)` and cofinal reader.
```

This formulation makes predictions rather than renaming target sign:

1. `Gamma_F(T)` must diverge for every fixed scalar conductor realization by `SR-35`.
2. Merely growing a reflection-even boundary is impossible by `SR-36`; odd/parity-mixing residual
   and its source-coordinate inclusion law are fixed by `SR-37`--`SR-38`.
3. Dropping `X_F` is impossible by strict all-order curvature law in `SR-39`; `SR-40` proves exact
   source principal subtraction retains it and yields universal cofinal Hankel current.
4. Positive and every fixed-index Pontryagin completion are impossible by `SR-42`; negative index
   must grow without bound along full-jet apertures.
5. Inclusion `F subset G` must preserve common-coordinate weld, relative current, and odd Jacobi
   absolute mode labels before target moments are read.
6. Finite part must retain off-diagonal Euler covariance; projecting to diagonal channels recreates
   nonsummable positive-log energy.

Positive control is canonical full Gamma covariance already in corpus: it supplies finite positive
blocks with coherent cross-prime concentration and fixed scalar conductor only because its prime
block is non-diagonal. Negative controls are diagonal repair, fixed-rank Gamma conductor, and any
uniformly Ward-bounded resolved packet family.

`(SR41)` is falsified if no source-defined bivariate connector can have both fixed marginals, if
restriction destroys one marginal, if any connector must be fitted from Xi/zero data, if cyclic
reader fails Euler shift compatibility, or if finite part kills meromorphic principal component.
Corpus and `SR-40` supply both marginals separately; `SR-42` fixes required infinite-index
signature class, but no joint source object exists yet.

## Level lift: general problem containing current Suzuki frontier

Corpus already states the following functional-analytic version. It is not a discovery of this
session:

> **Cofinal stable synthesis/passivity for a source-selected multiplicative-summation bornology.**

Given actual Müntz/co-Poisson analysis operator and exact difference-lag boundary functional,
construct a coherent family of source spaces on which boundary functional belongs to adjoint
range with a cutoff-uniform closed-range/angle bound. Norm must be fixed before completed error,
zero divisor, or positive spectral part is evaluated.

The sharper coefficient-side formulation exposed by `SR-27`--`SR-29` is:

> **Critical positive boundary representation of multiplicative decimation with retained
> meromorphic principal parts.**

Let `P=span{p_j}` be the fixed BV prime-window dilation orbit and let `D p_j=p_(j+2)`. Finite
cutoffs already give a positive Stein defect

```text
G_X(a,a)-G_X(Da,Da)=offMultiple_X(a)>=0.
```

Continued Laurent functionals obey

```text
ell_w(Da)=r^(2w-1) ell_w(a).
```

Construct, from cutoff coefficients or compact co-Poisson seeds and before reading a zero, a
Hausdorff positive boundary completion `H` such that `D` is contractive and the uncensored
principal-part functional is bounded. Riesz then makes it an eigenvector of `D*`; contractivity
excludes `|r^(2w-1)|>1`. On the zeta annihilator this is RH.

This is not ordinary frame theory. It belongs to the more general problem space of **singular
boundary representations of semigroups**: rigged Hilbert/graph completions, Stein inequalities,
and meromorphic boundary functionals. The critical obstruction is simultaneous preservation of
three structures:

1. positive finite-cutoff Stein defect;
2. one-sided critical contraction;
3. nonzero meromorphic principal part.

Ordinary `ell^2`, positive finite parts, scalar transport, two-sided coisometry, and invariant
trace each preserve at most two. This three-way compatibility, not another zero criterion, is the
general problem to solve.

The cocycle language below is a specialization of this existing open core, not an alternative
frontier.

The frontier belongs to **source-canonical unitarization of a reflection-reversible cocycle on a
nested RKHS quotient**, with a critical-weight causal polarization.

Abstract data are:

```text
L_a                         nested point-evaluable Hilbert spaces,
C_a subset L_a              closed source-generated subspaces,
Y_a=C_a^perp                source quotients,
U_t : L_a -> L_(a exp(-t))  normalized dilation cocycle,
J U_t J=U_(-t)              reflection/time reversal.
```

On an annihilator character `w`, quotient transport has growth exponent

```text
delta(w)=Re(w)-1/2,
||U_t^* k_w|| / ||U_(-t)^* k_w|| = exp(2t delta(w)).
```

Reflection pairs exponents `delta` and `-delta`; it does not force either to vanish. The minimal
hostile model is the two-dimensional reversible cocycle

```text
U_t=diag(exp(delta t),exp(-delta t)),
J(x,y)=(y,x).
```

It satisfies `J U_t J=U_(-t)` for every real `delta`. Therefore reflection, positive Hilbert
metric, Bianchi identities, and abstract conservative realization cannot prove `delta=0`.

The missing datum must be source-specific and one-sided: a causal metric/polarization making the
forward quotient cocycle nonexpansive at the critical half-weight. Reflection then supplies the
opposite inequality, so cocycle becomes isometric and every exponent vanishes. For Burnol
characters this is RH.

This is same general obstruction as fixed `1/2` exponential-domain gap in
`ccm-completed-quotient-weighted-schur-seam-law.md`. Suzuki Hardy leakage and Burnol co-Poisson
orientation are two realizations of one problem:

```text
source summation at safe weight
  -> source-canonical transport across critical half-weight
  -> one-sided dissipativity / full causal domain
  -> zero horizontal Lyapunov exponent
  -> RH.
```

## Current specialization

`CRITICAL-HALF-WEIGHT-COPOISSON-UNITARIZATION` is a concrete specialization of `SR-17`, not new
scientific knowledge:

For `0<a<=1`, `r>1`, and `b=a/r`, the compactly supported Duffin--Weinberger--Burnol seed map,
with its source-fixed `L2` norm and no divisor-dependent renorming, induces a closed one-sided
graph between forward and inverse quotient channels whose transfer is contractive. Equivalently,
its Hermitian defect has a negative-square certificate modulo the completed co-Poisson multiplier
ideal before any annihilator character is imposed.

The conjecture is meaningful only with an explicit graph domain and a formula on seed functions.
An existence proof obtained from the desired quotient order, from a zeta-zero basis, or from the
inner factor of completed zeta is circular and rejected.

## Scientific-method decomposition

### Observation

All global/invariant readers erase orientation. Every surviving RH criterion asks for an
additional one-sided comparison across exactly one critical half-weight.

### Subclaims

1. Write co-Poisson summation on logarithmic seed space as a closed source operator with its
   source-fixed norm and reflection.
2. Decompose forward/inverse shifted finite seed windows into common interior and two boundary
   strips.
3. Prove or refute cancellation of common interior **before** quotient specialization.
4. Identify remaining boundary form exactly.
5. Prove that boundary form is `-S^*S` modulo multiplier ideal, or exhibit an unavoidable positive
   square on an annihilator.

### Positive control

At every safe weight `a<=omega`, completed causal quotient already has contractive exponential
transport. Proposed source graph must reproduce this theorem without using a divisor.

### Negative control

The reversible two-dimensional cocycle above and an arbitrary Fourier-invariant trace must fail.
Any argument proving their contractivity has silently assumed desired orientation.

### Falsifiers

Conjecture fails if any of the following is proved:

1. exact seed-window boundary form contains a positive square not divisible by `Lambda_b`;
2. required source graph is nonclosable in source-fixed norm;
3. transfer exists only after using inner/outer factor carrying off-line divisor;
4. construction reaches only safe width `omega`, leaving same invariant half-unit gap;
5. two reflected source boundary strips have equal status with no source-selected causal order.

### Current allowed experiment

The finite-Müntz/Stieltjes-adjoint experiment is rejected by `SR-30`; its domains do not match.
The first source object carrying both finite positivity and the correct horizontal character is
instead the fixed BV prime-window orbit of `SR-27`--`SR-28`.

The broad singular-completion problem and its finite prime--Gamma packets are already developed in
`prime-gamma-reflection-decimation-defect-resolvent-rh.md`; do not claim this formulation as new.
That card sharpens its live source core to `SR-33`.

Test the following direct co-Poisson specialization, with novelty still unverified:

> **BV--co-Poisson singular-graph connector.** Pole-filled BV continuation induces a closable
> source map from the algebraic coefficient orbit `P` into Burnol's co-Poisson quotient graph,
> intertwines square-index decimation with compressed normalized dilation, and sends the
> off-multiple Stein defect to the cross-aperture evaluator defect without killing the Laurent
> principal part.

Required predictions are exact:

1. `J(Da)=compressedDilation(Ja)` on finite source vectors;
2. quotient evaluation of `Ja` equals the continued Laurent functional of `a`;
3. the graph norm is fixed from source data and makes `D` contractive;
4. coefficient off-multiple defect remains a nonzero boundary channel, so inflation is not a
   bounded contractive inverse.

Falsifiers:

1. pole-filled graph is nonclosable in Burnol's source norm;
2. its kernel contains an uncensored Laurent source;
3. the intertwining error has a surviving principal part not represented by the co-Poisson
   aperture defect;
4. contractivity requires a divisor-selected weight or makes inflation contractive, contradicting
   `SR-29`;
5. construction only reproduces the safe weighted half-plane and leaves a positive exponent gap.

No Lean module is justified until one of these source identities is proved on paper. A generic
closed-graph, Douglas, or commutant-lifting theorem does not construct `J` and does not count.

## Advance checklist

Before claiming progress, record all answers:

1. Which `LIVE-SOURCE` row changed?
2. Which exact source formula was proved before annihilator specialization?
3. Which hostile control fails and why?
4. What observation would falsify result?
5. Does theorem reduce half-weight gap, or merely rename it?
6. Has corpus collision search been run with all synonyms?
7. Is scientific status `ADVANCE`, `FORMAL-CLOSURE`, or `FAILED-CLASS`?

## Log

- **2026-07-22 — ledger initialized.** Ward/Bianchi/parity results reclassified as
  `FORMAL-CLOSURE` and `FAILED-CLASS`, not new scientific knowledge. Generic Krein-colligation
  conjecture rejected because `SR-04`, `SR-06`, and `SR-07` already contain it. General problem
  lifted to critical-half-weight source-cocycle unitarization. First allowed experiment restricted
  to explicit co-Poisson seed-window boundary form.
- **2026-07-22 — immediate collision caught.** `critical-multiplicative-compensated-cancellation-rh.md`
  already states broader cofinal source-bornology/stable-synthesis/passivity problem and exact
  co-Poisson Douglas target `(ER12)`. `ConstrainedProlateTrueApertureMetric.lean` already supplies
  finite Müntz map and Möbius frame. Current specialization demoted from “new conjecture” to one
  explicit experiment inside existing open core. New admissible residue is cutoff-uniform adjoint
  synthesis for actual Stieltjes boundary vector, not another seed-window or Möbius identity.
- **2026-07-22 — full Suzuki-chain collision audit.** S66--S81 and the BV prime-window cards add
  the missing source results and failed classes to rows `SR-18`--`SR-29`. This prevents repeating
  scalar log-Haar transport, macroscopic block surplus, positive finite parts, aperture readers,
  or two-sided coefficient coisometries. The proposed finite-Müntz/Stieltjes adjoint insertion is
  rejected as an object-type mismatch (`SR-30`). Level-lifted open problem is a singular positive
  boundary representation of coefficient decimation retaining meromorphic principal parts. First
  admissible conjectural attack is a concrete BV-to-co-Poisson graph intertwiner; no theorem or
  novelty claim is made yet.
- **2026-07-22 — singular-completion collision caught.** The broader BV scale-zero boundary
  completion is already the subject of `prime-gamma-reflection-decimation-defect-resolvent-rh.md`.
  Rows `SR-31`--`SR-33` record its closed all-depth packets, killed diagonal/fixed-rank repairs,
  and exact surviving infinite-rank off-diagonal Green--Schur/Euler identity. Direct BV-to-Burnol
  graph is retained only as a co-Poisson specialization of that known open core, with no novelty or
  truth claim.
- **2026-07-22 — resolved Ward--Schur advance.** `SR-34` kills literal channelwise Euler
  preservation: full projection commutation is exactly diagonal and recreates positive-log energy
  divergence. `SR-35` composes new factor-two resolved Ward law with existing Gamma Schur-capacity
  theorem. Fixed scalar conductor capacity forces cofinally unbounded projection-commutator energy.
  `SR-33` is narrowed to singular/growing-capacity principal-relative connection; generic bounded
  off-diagonal mixing is no longer admissible.
- **2026-07-22 — parity-capacity closure.** `SR-36` proves every reflection-even correction leaves
  exact odd Gamma floor and cannot meet cofinal budget. `SR-37` proves actual odd Jacobi ladder
  exhausts floor and selects least primewise rank with summable residual. `SR-38` proves those
  cutoffs are restrictions of one zero-padded common-coordinate positive kernel. Generic Mercer,
  Gram, and adaptive-capacity lemmas remain `FORMAL-CLOSURE`; actual Gamma composition is source
  advance. Capacity and inclusion coherence are not to be reopened.
- **2026-07-22 — successor--Bianchi Hankel weld (`SR-39`).** Changed live row: finite
  Green-boundary placement. Exact pre-character formulas are
  `K(s+2,s)-K(s+1,s+1)=-sum_n C_s(n)<0` at every order and, on every finite aperture,
  `d_r+b_r=h_r` on common von Mangoldt coordinates. Consequently coupled Gram is exactly shifted
  head-moment Hankel Gram and forced mixed block has exact opposite positive curvature. Hostile
  direct-sum control fails because its cross block is zero and strict anti-Hankel curvature
  survives. Falsifiers were zero/nonnegative curvature, failure of actual raw-feature endpoint
  identity, non-Hankel coupled output, or nonpositive cross curvature; Lean rejects all four.
  Three-tree/pipeline and primary-source synonym searches found no collision, but external novelty
  remains provisional. Status: universal rigidity `FORMAL-CLOSURE`; additive-Hankel mechanism
  `FAILED-CLASS`; actual all-order source law and common-coordinate finite weld `ADVANCE`. This does
  not close critical half-weight: new `SR-40` is cofinal singular/principal-relative preservation
  of mixed block plus odd Gamma--Jacobi residual and completed Euler trace.
- **2026-07-22 — principal-relative Hankel current (`SR-40`).** Changed live row: cofinal signed
  matrix completion. Exact pre-character laws are `Head_M-Tail_M=Successor_M+Cross_M` and
  `R_M(i,j)=sum_n Lambda(n)/n*(log(n+1)^(i+j+2)-log(n)^(i+j+2))`. Every order is absolutely
  summable; fixed jet matrices converge; finite and limiting shift defects vanish; mixed curvature
  cancels successor curvature at every order. Falsifiers were nonsummability, loss of cross block,
  failure of matrix convergence, or non-Hankel limit; Lean rejects all four. Collision audit found
  generic summation/moment closure but no source composition. Status: generic layers
  `FORMAL-CLOSURE`, source connector `ADVANCE`, external novelty provisional. New `SR-41` is not
  “add odd residual”: that is ill-typed. It asks for one bivariate prime--jet object realizing
  proved jet and prime/Jacobi marginals plus completed Euler trace.
- **2026-07-23 — successor transport inertia (`SR-42`).** Exact endpoint atomization gives
  `R_M=V_M^T diag(d_M)V_M`; distinct logarithmic nodes make full finite-section inertia equal
  sign counts of `d_M`. Left endpoint is strictly negative. Every prime `p>3`, `p=3 mod 4`,
  contributes another negative mass because `p-1` is not a prime power, so negative index is
  unbounded. Generic signed-atomic inertia is parent theory; source composition is the advance.
  Positive and fixed-index Pontryagin `SR-41` realizations are now failed classes. Only
  source-canonical, inclusion-compatible infinite-index Krein coupling remains live.
- **2026-07-23 — bivariate marginal trace lock (`SR-43`).** Finite coordinate partial traces of
  any product kernel have equal total trace, without positivity, symmetry, or index assumptions.
  Actual `SR-40` sections instead satisfy
  `tr R_(M,N+1)=tr R_(M,N)+rho_M(2N+2)` with `rho_M(2N+2)>0` at every nonempty aperture.
  Therefore arbitrary mixed coupling and infinite negative index cannot make a fixed `SR-38`
  prime/Jacobi marginal coexist with consecutive jet marginals. Ordinary normal partial trace is
  now a failed class. The positive survivor is a singular, weighted/renormalized cyclic reader
  which carries this exact positive trace flux explicitly.
- **2026-07-23 — true Xi Wiener--Hopf complement (`SR-44`).** Recent Hardy transport's
  complementary factor was totalized quotient `P_Xi/P_right`, hence zero at every strict-right
  zero instead of removable nonzero value. Universal arbitrary-predicate genus-one product split
  and actual Xi complement are now entire and exact without enumeration. Old quotient and source
  are entire iff RH; under false RH identity continuation contradicts their wrong divisor values.
  Changed live row: infinite Hardy continuation is repaired, while totalized-quotient analyticity
  is classified as RH-equivalent and may not be reused as unconditional input. Exact source
  formula before character specialization is `XiC=P_right*G_comp`, with `G_comp` entire and
  nonzero on strict-right divisor; full Xi multiplicity stays in `P_right`. Hostile controls
  (subtype nonmultipliability, multiplicity loss, shared selected/complement divisor, vanishing
  Hadamard unit, accidental divisor equality) all fail in Lean. Status: universal split
  `FORMAL-CLOSURE`; Xi divisor repair and removability equivalence `ADVANCE`, external novelty
  provisional. This does not reduce critical half-weight or prove compound Bezoutian positivity.
  New live core remains `SUZUKI-COMPOUND-BEZOUTIAN-GRAM` using genuine factors only.
