# Growing-order Möbius Riesz smoothing: fixed-scale escape

Status: the fixed-scale unit-mass limit route is retired. Its strongest positive survivor is fully proved on paper and formalized in Lean: exact convolution structure and unit mass, an individual-shift exponential envelope, and quantitative escape beyond every fixed cutoff. All final compilation and axiom audits passed.

## Candidate and RH role

The fixed-order positivity route is already ruled out. A remaining candidate takes the positive threshold primitive for each finite prime set, normalizes its total mass, and passes to a nonzero positive limit at fixed logarithmic scale. Test whether that limit retains any information.

No numerical experiments. Read research only as Lean corpus results from scripts/formal_tools.py research. No web, Markdown, direct source, or memory reads.

## Definitions

For a nonempty list A of positive shifts, h(t)=max(1-exp(-t),0), packet A is its iterated backward difference, and g_A is its (length A - 1)-fold primitive from zero. Existing Lean proves g_A is nonnegative and causal. Let W_A be the product of all shifts and K_A=g_A/W_A.

For prime packets the shifts are log(sqrt p); every shift is at least c=log(sqrt 2)>0. The literal square-root cutoff and Möbius coefficients are preserved by the already-formalized arithmetic bridge.

## Dependency-closed paper argument: quantitative local bound

Assume every shift is at least c>0. Set lambda=2/c. For all real t and every nonempty A, claim

0 <= K_A(t) <= (2/c) * (1/2)^(length A) * exp((2/c)*t).

Base, one shift a: g_[a](t)=h(t)-h(t-a), between zero and one. At t<=0 it vanishes. At t>=0, exp(lambda*t)>=1 and 1/a<=1/c, giving the displayed bound.

Induction: the existing causal calculus gives g_(a::A)(t)=integral from t-a to t of g_A(u) du. Since W_(a::A)=a*W_A, K_(a::A)(t)=(1/a) integral K_A. Integrate the inductive exponential majorant. Its integral equals exp(lambda*t)*(1-exp(-lambda*a))/lambda, bounded above by exp(lambda*t)/lambda. Since lambda*a>=2, the bound acquires a factor at most 1/2. All integrands are continuous; a>0, so interval monotonicity applies directly.

Consequently, for any fixed upper scale T, sup over t<=T of K_A(t) is bounded by (2/c)*exp((2/c)*T)*(1/2)^length(A). For any sequence of lists whose lengths tend to infinity, this gives uniform convergence to zero on every bounded scale window. For finite prime sets the same conclusion holds whenever cardinalities tend to infinity.

The exact positive survivor to formalize is the normalized box-average recursion plus its quantitative geometric local bound and uniform fixed-scale extinction. This excludes a nonzero fixed-scale limit under this normalization. It does not exclude recentering or rescaling, and does not establish the RH cancellation estimate.

## Mass normalization audit

Paper identity: g_A is convolution of the causal exponential density exp(-t)1_(t>=0) with the unnormalized interval indicators 1_[0,a] for all a in A. For one shift this follows by integrating the exponential between t-a and t, clipped at zero; each further shift follows from the box-integral recursion. Tonelli gives integral g_A = product A = W_A. This identity and integrability are now proved in Lean. Endpoint choices for the interval indicators agree almost everywhere. The normalized profiles are nonnegative integrable functions of integral one.

## Stronger paper survivor: exact probability mass and tail escape

The convolution proof identifies the threshold primitive with successive box convolutions of the causal exponential density. Its integral is exactly W_A, so K_A has total mass one. The individual-shift envelope is

K_A(t) <= rate * product_(a in A)(1/(rate*a)) * exp(rate*t), for every rate>0.

For a>=c>0, take rate=2/c. Integrating the geometric exponential bound over (-infinity,T] gives

integral_(t<=T) K_A(t) <= 2^(-length A) * exp((2/c)*T).

Since the total integral is one, the upper-tail mass is at least one minus this quantity and at most one. Thus upper-tail mass tends to one for every fixed T as length grows. This proves genuine escape of unit mass, not a loss of total mass under normalization. The fixed-scale pointwise limit is necessarily zero, hence cannot retain unit integral.

The mass proof uses only integrable convolution, the interval indicator, the causal exponential, and the already-proved threshold box recursion. It preserves all shifts and the exact literal-prime bridge.

## Corpus audit

Deep corpus searches for normalized prime smoothing, box convolution, local extinction, and mass escape found no matching packet theorem. Searches returned the existing sharp positivity threshold and other, structurally different prime escape results. Semantic coverage was unavailable and some requests were partial; this is not an external novelty claim. All source reading remained restricted to Lean search output.

## Completed workflow

1. Audited corpus for existing escape/convolution results and applicable integral APIs.
2. Verified normalized recursion, exact mass, and quantitative bounds in scratch Lean.
3. Formalized uniform fixed-scale convergence, tail mass tending to one, and the obstruction to a unit-mass pointwise limit; specialized all endpoints to literal finite prime packets.
4. Compiled final leaves, audited axioms, wired imports, ran lint, refreshed index, and recorded exact scope.

## Final leaf verification (2026-10-09)

- MobiusRieszNormalizedEscape.lean: direct lake --old env lean compilation, exit 0, no warnings.
- MobiusRieszNormalizedMass.lean: direct lake --old env lean compilation, exit 0, no warnings.
- MobiusRieszPrimePacketEscape.lean: direct lake --old env lean compilation, exit 0, no warnings.
- A scratch #print axioms audit of all 35 new public theorems compiled successfully. Every result depends only on propext, Classical.choice, and Quot.sound. All scratch proof and audit files were removed after their processes terminated.
- All three modules imported by RHTower.lean. git diff --check reported no whitespace errors in the scoped diff. Corpus index refreshed; new finite-prime endpoints found by corpus search.
- Global formal lint exited 1. Its only reported errors were unrelated missing umbrella imports: RHTower.CCMFullGroundZeroSideEigen; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, and BoundaryCoronaCStarAlgebra. No errors concerned these three modules.

The retired premise is a nonzero unit-mass pointwise limit at fixed logarithmic scale obtained by increasing to the exact positivity threshold. Moving centres, rescaling, and the signed prime-minus-continuum cancellation bound are not ruled out. Further kernel corollaries alone do not supply that missing RH estimate.

Next RH-bearing source inspected through corpus search: CoupledFloorMobiusAffineRieszHandoff.lean. The theorem coupledFloorMobiusAffineRieszCofinalBounded_iff_mobiusDivisor assumes positive omega N and absolute readout-minus-mobiusDivisorSquareRootAbelMoment error below 1/(N+1) at M=N+1, then identifies readout boundedness with MobiusDivisorSquareRootAbelBounded. The theorem exists_coupledFloorMobiusAffineRieszHandoff_iff_rh already supplies an unconditional positive schedule tending to zero, with omega N < 1/(N+1), that satisfies the pointwise error bound and makes normalized readout boundedness equivalent to RH. Constructing another schedule does not prove the remaining bound. The next proof attempt should target the actual signed source: one B>=0 bounding the absolute normalized Möbius-divisor moment for every M>=2.

RH remains unresolved. No external novelty claim.
