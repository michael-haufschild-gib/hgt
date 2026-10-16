# CHMD stationary ground-state generators — 2026-10-16

RH goal remains ACTIVE and unbounded. No unconditional RH proof or compact operator core was claimed. This turn made verified structural progress: exact maximal-domain stationary ground-state cancellation; actual self-adjoint nonnegative generators; common operator domain and bounded-perturbation identity; trivial kernel of the stationary generator.

Formalised card: docs/drafts/pipeline/3-formalized/chmd-stationary-ground-generators-2026-10-16.md
Continuing core task: docs/drafts/pipeline/1-in-progress/chmd-archimedean-operator-core-2026-10-16.md
Prior arithmetic removal: mem:rh/chmd-prime-operator-domain-2026-10-16
Prior spectral nullspace: mem:rh/chmd-full-spectral-nullspace-2026-10-16

## User constraints
Read /Users/michael/.codex/attachments/2c5020c9-b71c-40b8-ba6c-e8fb1100e229/pasted-text-1.txt on each new turn. Corpus-first CHMD work; no web, novelty search, numerical experiments, or old research Markdown reads. Every new turn must produce a significant structural contribution, not merely an estimate, RH equivalence, or receiver. One owned Lean/build process at a time, no full/umbrella builds, no heartbeat hacks, final plain lake env lean on every new leaf, all-declaration axiom audit from /tmp only, wire completed leaves, cleanup owned scratch. No commits/push. No subagents authorised. Serena ignores Lean files: use established rg/apply_patch fallback. Plan tool unavailable; current task card tracks progress.

## Verified result
Namespace RHTower.CHMDDoobGraph, with MassSpace from CHMDPolar.
Theta=riemannKernelReal, c=cosh(x/2), massMeasure=Theta*c dx, kappa=archLevyDensity.
thetaProduct u = Theta*u.
stationaryEnergy f = integral_(t>0,x) kappa(t)(f(x)-f(x+t))^2.
thetaGroundPotential V(x) = c(x)^(-1) integral_(t>0) kappa(t)
  [(Theta(x+t)-Theta(x))+(Theta(x-t)-Theta(x))].
V is measurable and globally bounded, using global theta Lipschitz regularity and the already-proved first Levy displacement moment.

Pointwise exact cancellation:
Theta(x)Theta(y)(u(x)-u(y))^2 - (Theta(x)u(x)-Theta(y)u(y))^2
 = (Theta(y)-Theta(x))(Theta(x)u(x)^2-Theta(y)u(y)^2).
The defect is absolutely integrable for EVERY mass-L2 source, not just bounded/compact/smooth sources.
Consequently full arithmetic form admission iff finite stationaryEnergy(thetaProduct u).
thetaProduct u also belongs to ordinary Lebesgue L2.
The arch energy is stationaryEnergy(thetaProduct u)+integral V*u^2 dmass.
The full energy adds the existing bounded prime operator P.

stationaryGroundGraph is a literal complete graph on original massSpace x L2(stationaryMeasure),
where stationaryMeasure=archBase.withDensity(ofReal(kappa(t))), with edge coordinate
difference(thetaProduct source). It is closed by AE subsequences. Source projection injective.
archGroundEquiv and fullGroundEquiv preserve sources and identify the complete graph topologies.
The exact graph inner-product discrepancy is K=P+M_V, where
groundPerturbation = primeGenerator + groundPotentialOperator.

stationaryRieszLift = stationaryGroundSourceMap.adjoint.
stationaryResolvent Rg = stationaryGroundSourceMap.comp stationaryRieszLift.
Both source projections have dense range (all compact smooth mass-L2 classes occur as genuine compact lifts).
Both R and Rg are injective, positive and self-adjoint.
Exact identities:
  stationaryResolvent_full_shift: Rg(w-K Rw)=Rw
  fullResolvent_stationary_shift: R(w+K Rg w)=Rg w
  full_operator_domain_eq_stationary: Set.range R = Set.range Rg
  full_generator_relation_iff_stationary:
    R(u+v)=u iff Rg(u+v-Ku)=u.

Actual LinearPMaps now exist:
  arithmeticGenerator = generatorOfResolvent R resolvent_injective
  stationaryGenerator = generatorOfResolvent Rg stationaryResolvent_injective
  generatorOfResolvent R hR has domain R.range and value R^(-1)u-u,
  using LinearEquiv.ofInjective on R.toLinearMap.
Both actual generators are self-adjoint, closed and nonnegative.
Self-adjointness is proved, not assumed: for an adjoint-domain u, testing on every Rz gives
R(u+A*u)=u, hence u belongs to range R and the adjoint equals the original operator.
Both form identities pair generator output with any graph source and give literal edge inner products.
  arithmeticGenerator_domain_eq_stationary
  arithmeticGenerator_eq_stationary_add:
    L u = G u + groundPerturbation u on the exact common domain.

Kernel rigidity:
  stationaryGround_edge_zero_iff p: p.val.snd=0 iff p=0.
  stationaryGenerator_strictly_positive:
    u != 0 in Dom(G) implies 0 < inner(G u,u).
  stationaryGenerator_zero_iff: G u=0 iff underlying u=0.
Proof: zero edge forces Theta*u constant by constant_of_arch_zero; ordinary Lebesgue L2 admission
and infinite volume force that constant zero; Theta is strictly positive.
This is NOT a uniform gap and NOT the RH critical sign inequality.

## Seven audited leaves
All under formal/GaloisForLFunctions/RHTower:
CHMDStationaryGroundDomain.lean
CHMDStationaryGroundPotential.lean
CHMDStationaryGroundGraph.lean
CHMDStationaryGroundEquivalence.lean
CHMDStationaryOperatorDomain.lean
CHMDStationaryGenerators.lean
CHMDStationaryKernelRigidity.lean

Total: 999 lines, 106 declarations.
Main theorem locations: CHMDStationaryGenerators line159 domain equality, line165 operator identity;
CHMDStationaryKernelRigidity line65 strict positivity, line81 zero iff zero.

SHA256, revalidated after final audits:
CHMDStationaryGroundDomain db598eb747b39f45dd8bc94ed590a1c8b1b9b56c1fc8a5648e5e1d66ed294025
CHMDStationaryGroundPotential 5bb6ef1022ec8a686489454781b5668696ccbf49b9bb5e7474a80fab9eaa892f
CHMDStationaryGroundGraph 44933351897d0c87846138cc7d45a9b0e75bcd5b9766f6d3dc7da33f1eb25532
CHMDStationaryGroundEquivalence 1dd787bcb51d46e53424984992efef2542a509d64e3bf4e5d4d694cd5263a182
CHMDStationaryOperatorDomain bf09aa9589c7f7800334c2e82b35ec182090c906ab01153c31ff684a4a002801
CHMDStationaryGenerators 744040c033eeef86f12fc41a85b5c5c5960f363b53726519865e195439d12a06
CHMDStationaryKernelRigidity 5b842e9b2175c3e27951fb38eaca54157258981d628e680051616124a4222cb4

## Validation and cleanup
Each targeted lake --old build passed.
Final plain lake env lean <file> passed on ALL SEVEN leaves, with empty output.
A /tmp audit printed axioms of ALL 106 declarations and checked extra mathlib API probes.
Every declaration uses only propext, Classical.choice, Quot.sound; no errors/warnings/sorryAx.
Additional API probes also passed.
All seven root RHTower.lean imports occur exactly once.
106 declaration names checked unique among source files in namespace RHTower.CHMDDoobGraph.
Source hashes unchanged through final verification and cleanup.
No full/umbrella build. No commit/push by this agent.
All owned research/build/audit processes terminal; 24 exact owned scratch files removed.
No owned live process or scratch remains.

Authoritative scripts/formal_tools.py lint EXIT 1, seven unrelated UNWIRED modules:
RHTower.CHMDPrimeWindowTail
RHTower.DeningerMeyerStripCardinal
RHTower.DeningerMeyerStripJetLocalization
RHTower.DeningerMeyerStripSeries
RHTower.XiGaussianHeatFiniteFactor
HTGeometry.AnalyticEscapingFactorization
HTGeometry.AnalyticPolynomialDivisionGerm
No proof-debt lint error. Do not claim repository-wide lint clean or wire concurrent unfinished modules.
Concurrent CHMDThetaHarmonicIdentity, CHMDPointwiseGenerator, CHMDGeneratorWeilOperator,
CHMDThresholdWeylSequence are now root-wired (observed), but their latest work was not audited by us.
Some new files became tracked during concurrent workspace activity; we did not issue git commit.

## Remaining core obstacle and cautions
Compact smooth OPERATOR-core density for G is still open. Full compact FORM core was already proved,
and this turn's self-adjointness of the associated maximal-form generator does not close weak compact-test
domain admission. Do not confuse form density, self-adjointness, or trivial kernel with an operator core.
Do NOT identify G's operator domain with {u : Theta*u in ordinary Dom(A)} without proof;
weighted output admissibility can be weaker. The stationary pullback was constructed from its exact closed form.

Candidate next mechanism:
Uu=sqrt(Theta*c)u, a=sqrt(Theta/c). Under U, G should be a A a, where A is the correct stationary
symmetric Levy generator integral kappa(t)(2f-f_shift_plus-f_shift_minus).
Global positivity plus bounded theta second derivative gives sqrt(theta) Lipschitz via a Glaeser inequality;
bounded Lipschitz a should give bounded [A,a]. Need ACTUAL stationary A and compact core, actual half-density
identification, and a proved bounded-commutator essential-selfadjointness argument, then instantiate.
For J_e=(1+eA)^(-1), [aAa,J_e] has uniformly bounded terms tending strongly to zero:
a(e A J_e)[A,a]J_e + J_e[A,a](e J_e A)a. This remains candidate operator-core machinery, not formalised.
Alternative: direct translation-invariant closed graph plus commuting mollifiers and cutoff commutators.

Important corpus audit: SoninGammaClockSpectralDomain has an EXTRA 1/t in its Levy kernel.
Its symbol uses 2(cos(xi*t)-1)*ccmPublishedArchimedeanDensity(t)/t.
It is not the CHMD stationary generator. Reuse infrastructure only, not its operator domain.
Two deep corpus queries finished non-partial, inventory 72746/72746 and 72751 files; compiler metadata
contained pending/stale records. No applicable actual compact operator-core or essential-SA theorem found.
BoundedPerturbedFriedrichsFormCore only extends a compact operator from dense form tests; it is NOT an operator-core theorem.

## Lean details that avoided false starts
- C-infinity from Lp.dense_hasCompactSupport_contDiff has order (top:ENat) coerced to WithTop ENat.
  For C2 use hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2).
- After destructuring a LinearPMap domain-range witness, ordinary rw can fail because the target is not
  type-correct at instances transparency. erw works; a final rfl can clear remaining subtype coercions.
  No heartbeat change was used.
- For weighted-measure rewrites with measurable.comp, explicitly set w := fun e => kappa e.1.
- For shifted integrals, change archBase to the explicit restricted-volume product before simpa.
- Fubini sometimes needs a typed intermediate equality with the exact lambda, rather than rw with an
  implicitly inferred Pi.add function.
- Dense.eq_of_inner_left arguments can show different coercions; use exact chains of inner identities
  instead of rw. The full Riesz shift uses (inner_rieszLift w q).symm.
- LinearEquiv.ofInjective_symm_apply, LinearPMap.adjoint_isFormalAdjoint,
  LinearPMap.IsFormalAdjoint.le_adjoint, memLp_const_iff and Real.volume_univ were probed in THIS toolchain.
