# Uniform actual source profile for Suzuki covariance

- **ID:** sz-uniform-source-profile
- **Stage:** 1-in-progress
- **Route:** SZ
- **Date:** 2026-10-02
- **Status:** uniform actual covariance and odd/even/V2 physical profiles formalized; prescribed-shift first-defect separation remains open

## Hard objective

Control mixed-aperture covariance responses through a source-specific inverse
profile at the actual prescribed shift. The odd-only estimate needs an actual
even analogue and ultimately a uniform source theorem. Merely controlling a
same-aperture energy determinant does not control the discrete metric term.

For aperture b and a literal finite-exponential physical source p with
norm(p)<=V and certified budget V, target uniform estimates for the canonical
finite Neumann vector u_N(p), N=ceil(b), at the actual shift c_b:

    norm(u_N(p)) <= M*V/c_b,
    norm(p-(c_b I+B_b)u_N(p)) <= R*V*exp(-4b),
    Jg_N(p)=u_N(p),
    norm(g_N(p))_Gamma^2 <= D*b*V^2*exp(-2b).

M,R,D and the aperture threshold must be uniform in the actual p and V.
These universal helper theorems have explicit norm/budget binders; every
claimed actual source result must discharge them. No new axiom or source
regularity premise may be attached to an RH endpoint.

For literal odd/even matched poles, V=exp(b/2), recovering actual Gamma
energy O(b exp(-b)). For a pole source from aperture a extended into b>=a,
V can retain its original exp(a/2) scale. This is why the V-uniform theorem
advances the mixed-response problem rather than merely duplicating odd code.

## Current corpus evidence

Search1188865 is partial, pending coverage, source_only. It finds the actual
Neumann budget band, finite vector budget and even pole identities; no
proof_ideas or ingredient_sets. Its generated boundary-element query is a
different meaning of Neumann. Current source inspection gives:

- CCMFiniteExponentialRemainderOrbit.normalized_remainder for every certified
  source; one step multiplies its budget by C0=2*(norm(kappa)+46).
- CCMRestrictedWeilSourceContraction.eventually_ccmNormalizedWeilRemainder_budget_contraction,
  uniform over every actual source and every certified budget.
- CCMRestrictedWeilFiniteNeumannSource recurrence_bound and finite telescoping
  identity already have generic scalar/vector proofs. Its source restriction
  enters only initial norm/budget and the chosen amplitude exp(b/2).
- CCMFiniteExponentialFormLift.exists_ccmFormLift for every actual finite budget.
- CCMFiniteNeumannFormDecay's geometric budget band and shift bound depend
  on aperture and amplitude, not odd parity.

## Paper mechanism

Let q=exp(-4), C=C0, K=2log(C)+10, E=V and
eta=(4*(norm(kappa)+46)/pi)*V/sqrt(exp(K*b)). Budget induction gives C^n V.
The actual source contraction gives d_(n+1)<=q*d_n+eta*C^n and d_0<=V.
The existing scalar recurrence yields d_n<=q^n V+eta C^n.
For N=ceil(b),

    q^N V <= V exp(-4b),
    eta C^N <= L*C*V exp(-5b).

Retain V in the second term instead of replacing exp(b/2) by a number.
Both residual and finite norm sum follow uniformly, including V=0 because
budget admission implies V>=0. Exact finite telescoping gives the displayed
Neumann bounds. The finite-vector budget is C^N V/c_b. The already proved
Gamma lift and logarithmic band estimate then give D*b*V^2*exp(-2b).

The stronger full remainder norm argument from CCMFiniteNeumannRemainderQuadratic
also becomes uniform after replacing exp(b)*norm(u)^2 by
exp(2b)*norm(u)^2/V^2 when V>0, with V=0 handled directly. Combined with
arbitrary-L growing physical coercivity, the intended actual covariance
profile is

    exp(2b)*norm(response_b(p)-p/c_b)^2 <= epsilon*V^2,

uniformly for all admitted sources at all sufficiently large b. The exact
actual covariance/Riesz realization must be inspected and proved; it is not
assumed here. This would supply common control for literal even/odd sources
and transported old pole sources. Full signed shell cancellation, V2 source
identification, normalization and shift removal remain separate obligations.

## Implementation order

1. Generalize finite-budget iterate/orbit/vector estimates while preserving
   every existing odd theorem and literal odd-vector definition.
2. Generalize the Gamma lift estimate; instantiate the actual even pole source.
3. Prove the actual uniform covariance profile from exact Riesz identities.
4. Apply it to mixed-aperture pairings, retaining both parity signs and the
   original aperture cutoffs.

## Implementation checkpoint

The actual odd pole-profile scratch85107 and final31416 pass without warnings;
new leaf SuzukiMatchedOddPoleProfile is wired. Its source theorem builds on
CCMFiniteNeumannRemainderQuadratic final87163. Public axiom audit is pending
until the next dependency step is complete.

Generic source construction is drafted in /tmp/sz_uniform_neumann_source.lean
and under sequential scratch audit. It preserves every existing odd public
statement and the literal odd-vector definition, while the odd orbit and
Neumann estimates become specializations of the V-uniform argument. The
finite-vector budget is generalized as well. No source regularity condition
is assumed for a new actual endpoint: literal even admission must still be
constructed and passed through the generic producer.

Final CCMRestrictedWeilFiniteNeumannSource14820 passes without warnings.
The exact finite orbit and inverse residual now retain arbitrary source
amplitude V, including V=0. Existing odd statements and literal vector
definition remain intact, with their proofs specializing the producer.
Scratch41908 needed removal of a no-progress dsimp and direct trans_eq for
the definitionally equal old/new vector in the odd residual wrapper. These were
proof-engineering corrections, not changed mathematical inputs.

The source-uniform Gamma admission is drafted in /tmp/sz_uniform_form_decay.lean
and under scratch audit. Actual even source norm/budget, canonical inverse,
and its premise-free Gamma admission are drafted in /tmp/sz_even_neumann.lean;
they await the new Gamma producer.

Uniform Gamma admission: scratch70024 and final86441 both pass without
warnings. The actual even admission scratch89333 is running. A uniform
actual response estimate is drafted in /tmp/sz_uniform_covariance.lean:
response is FromForm(RieszInv(J.adjoint(e.symm p))), so its physical interval
embedding equals the existing suzukiWeilIntervalCovariance by definition.
The renormed inner-product definition gives the exact source pairing.
The residual argument and arbitrary-L coercivity then give
exp(2b)*norm(response_b(p)-u_N(p))^2 <= epsilon*V^2, including V=0
without division. Uniform full remainder cancellation remains to be checked.

Actual even admission: scratch89333 and final34774 pass without warnings;
CCMMatchedEvenNeumannSource is wired once. Uniform covariance scratch19045
is running. The uniform full remainder and explicit covariance profile are
drafted separately; neither is yet claimed Lean-closed. The resulting actual
even response specialization is drafted with its Riesz/cosh equality.

The stronger uniform profile does not itself control covariance_b applied
to an arbitrary extended response_a with the needed shift-weighted error.
Transported finite pole sources are admitted, but response errors need their
own transport analysis. Do not turn this into a false full-Wronskian claim.

Search1189189 (partial, complete file inventory, mostly pending/stale compiler
metadata) finds the literal metricRenormalizedShell physical identity and
metricShiftCorrection source, plus the newly generalized finite-source
producer. No proof_ideas or ingredient_sets are returned. Direct source
inspection of CCMSuzukiCrossApertureRieszTransport confirms the remaining
metric correction is (c_a-c_b)*C_b(extended actual response_a), not merely a
shift ratio times the smaller response. The endpoint profile theorem is a
real advance, but this term and the actual Fourier Wronskian still require
additional arguments retaining their signs and cutoffs.

## Next conjecture forced by the uniform profile

At the actual V2 source parameter 1, the pole norm and budget should both be
at most exp(a), by the literal truncated-exponential integral. Thus the
uniform response profile would give norm(f_a-p_{a,1}/c_a)->0 in physical L2,
with no exponential rescaling left. The actual covariance source identity
must be used to identify f_a; do not substitute parameter1/2.

For each fixed z with y=Im(z)>0, the Fourier test norm is O(exp(a*y)). The
explicit source p_{a,1}/c_a has Fourier coordinate at -z whose modulus,
after division by exp(a*y), is bounded below using exp(a)/c_a>=1/(norm(kappa)+47).
Its +z coordinate, divided by exp(a*y), tends to zero. The L2 response-profile
error contributes o(exp(a*y)) to BOTH Fourier coordinates. Consequently the
actual canonical-shift V2 Livsic quotient is conjectured to tend to zero
pointwise throughout the upper half-plane. This is a paper mechanism, not a
Lean claim; source/Fourier sign conventions and exact exponential integrals
must be checked. It may expose canonical-shift degeneration rather than a
nontrivial Xi limit. A no-go requires keeping the explicit covariance profile
and actual limit as positive survivors. It does not falsify RH or all SZ routes.

Related first-mode target: with common scale c_a*exp(-2a), actual even and
odd energies at parameter1 should both tend to 1/4, implying defect angle0
and normalized anchor Wronskian increments0 through the existing exact law.
Searches for actual V2 profile/defect and canonical-shift collapse are running;
no claim of corpus novelty is made until the returned sources are checked.

Uniform actual covariance approximation: scratch19045 failed only because
`field_simp` had closed a scalar goal before a trailing `ring`; removing that
tactic gives final43230 exit0. Lean emits a ring-normalization suggestion,
but no error. The exact source pairing and covariance identification both
check. CCMFiniteSourceRemainder final77471 is now running.

V2 corpus searches1189212 and1189222 are partial (first coverage pending,
second complete inventory but mostly pending/stale compiler metadata).
They retrieve exact projective scaling, actual parameter1 characteristic
identities and the free exponential denominator lower bound. The proposed
shifted-energy-core ingredient does not establish a moving-aperture limit.
SuzukiNegativeShiftEscape proves collapse after CHOOSING sufficiently negative
shifts along any cofinal aperture sequence. Its theorem does not by itself
show collapse at the prescribed norm shift. Thus the next conjecture is the
actual prescribed-shift strengthening, using the new physical profile.
The existing Fourier transfer bound contains a sqrt(window length) loss;
for this deduction one needs the exact exponential test norm at Im(z)>0,
which removes that aperture loss. This is needed to transfer o(1) L2 error,
not a numerical-constant refinement.

The actual parameter1 norm/profile specialization is drafted in
/tmp/sz_v2_source_profile.lean. Admission uses pointwise domination
exp(x)<=exp(a/2)*exp(x/2) on [-a,a], the audited half-pole norm, and the
existing exact finite-exponential polar budget. This avoids any unstated
transfer from the parameter1/2 response. A general sourceResponse_polar
identity identifies every real exponential with the actual raw deficiency.
The new Mathlib Lp domination API is included in its scratch verification.

Uniform full remainder final77471 exposed only a missing simplification of
the natural-number cast in exp(a)^2=exp(2*a). Rest of the proof elaborated.
The cast simplification is restored; final72877 is running.

Final72877 passes the full source-uniform remainder norm theorem. It retains
V^2 throughout the low-band/Gamma-tail estimate, including V=0, and assumes
no response regularity. Lean emits the same normalization suggestion but no
error. The actual covariance explicit-profile leaf final81615 is running.

Exact actual Fourier interface located: SuzukiTaCharacteristicRealization
provides suzukiTaSpectralExponentialL2 at every complex spectral point;
SuzukiTaCharacteristicEntire identifies its pairing at star(z) with the
literal physical Fourier coordinate. This avoids introducing a replacement
carrier or silently equating interval-Icc and free-model interval-Ioo L2.
CCMSuzukiV2ProjectiveRawCarrier.suzukiTaV2Livsic_eq_rawDeficiency removes
the actual common normalization exactly. Use these interfaces for a future
prescribed-shift collapse proof; the old apertureFourier free model needs an
explicit bridge before reuse.

## Sharper next frontier test: actual first-mode separation

Directly inspected SuzukiXiFirstDefectJetSource: Xi identification forces the
finite parity defect to tend to the strictly positive Xi scalar; the existing
exact target has even share in (81/85,1), odd share in (0,4/85). A proved
actual prescribed-shift defect limit0 would therefore rule out direct Xi
identification for that shift, while preserving the source profile and the
explicit free limit as positive results. This is not an RH falsification.

Prioritize the actual first-mode test before the full complex Fourier limit:
SuzukiTaV2ActualDefectJet already supplies
coalescingEnergy_add_eq_norm_sq and coalescingEnergy_sub_eq_inner_re,
as well as physicalFourier at +/-I and exact defect/derivative identities.
With f_a approximately p_{a,1}/c_a and norm error o(1), Cauchy--Schwarz gives
both physical source-pairing errors o(exp(a)). Exact exponential integrals
then give diagonal main term sinh(2a)/c_a and cross main term 2a/c_a.
The diagonal is bounded below at scale exp(a) by the proved shift upper
bound; the cross is o(exp(a)). Hence the defect should tend to zero, with
no need yet for a general complex spectral test bound. These integral and
actual source identifications remain to be formalized, not assumed.

Uniform explicit actual covariance profile: final81615 exposed only the
coercion equality after unitary norm transport; `rfl` closes it. Final27643
passes without warnings. All three profile statements (finite Neumann,
actual Ta response, existing interval covariance) are kernel checked. The
actual even response profile is now in final audit61093; actual V2 source profile is next in the sequential queue.

Actual even profile final61093 exposed the same explicit-map/CLM-coercion
identity in the unitary physical transport. Added `rfl` after apply_symm_apply;
final68617 is running. The identical coercion step in the V2 scratch is
corrected before its audit. No mathematical estimate or input changed.

Actual even profile final68617 passes without warnings, closing the actual
matched even pole-profile endpoint. SourceResponse_matchedEven proves exact
identity with the existing raw cosh response; its Tendsto root has no source
admission or response premises. Actual V2 scratch now runs next.

Actual V2 physical-profile final17439 passes without warnings. Its full
parameter1 admission and actual raw-deficiency identity are proved. All ten
changed leaves now have passing final audits. The 38-public-theorem axiom
audit is running, with three exact premise-free endpoint signatures checked.

Next first-defect target now has a dependency-closed paper proof on
`docs/drafts/pipeline/2-fully-proven/sz-prescribed-shift-first-defect-collapse.md`.
It uses the actual parameter1 profile, exact source pairing and shift bounds;
it is explicitly NOT yet a Lean theorem or completed no-go. Formalize that
exact actual limit and its positive first-mode survivor next.

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
