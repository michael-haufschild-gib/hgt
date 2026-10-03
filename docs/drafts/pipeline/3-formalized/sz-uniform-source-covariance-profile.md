# Uniform actual Suzuki covariance source profile

- **ID:** sz-uniform-source-covariance-profile
- **Stage:** 3-formalized
- **Route:** SZ
- **Type:** POSITIVE
- **Date:** 2026-10-02

## Exact result

`eventually_suzukiWeilIntervalCovariance_source_profile` proves, for every
epsilon>0 and all sufficiently large positive a, uniformly for every actual
aperture source p and real amplitude V with norm(p)<=V and a certified
finite-exponential budget V,

    exp(2a)*norm(C_a p-p/c_a)^2 <= epsilon*V^2.

Here C_a is the existing completed interval covariance, transported by the
existing aperture/interval unitary, and c_a is the prescribed shift
norm(B_interval,a)+1. No substitute covariance, response regularity bound,
Fourier-tail assumption or RH premise is introduced. Source admission is an
explicit binder of this universal helper; every actual endpoint must prove
it. The estimate includes V=0 without division by V.

The actual matched odd source already discharges admission and yields the
premise-free root `tendsto_suzukiTaMatchedOdd_pole_profile`:

    exp(a)*norm(f_odd,a-p_odd,a/c_a)^2 -> 0.

Actual even norm, budget, finite inverse and Gamma admission are also proved
in CCMMatchedEvenNeumannSource. Actual even and V2 response specializations
are recorded below only after their final audits.

## Dependency-closed paper argument

Write H_a=B_a/c_a, N=ceil(a), C0=2*(norm(kappa)+46). Every admitted source
iterate has budget C0^n*V. The existing low-band multiplier cancellation and
finite-exponential Fourier tail give a uniform scalar recurrence. With
q=exp(-4) and K=2log(C0)+10, its geometric solution retains V:

    norm(H_a^N p) <= R*V*exp(-4a),
    sum_(j<N) norm(H_a^j p) <= M*V.

Exact finite telescoping for
u_N=c_a^(-1)*sum_(j<N)(-H_a)^j p gives

    norm(u_N)<=M*V/c_a,
    norm(p-(c_a I+B_a)u_N)<=R*V*exp(-4a).

The literal vector budget is C0^N*V/c_a. Its actual Gamma lift g satisfies
Jg=u_N and norm(g)^2<=D*a*V^2*exp(-2a). The constants and aperture threshold
are independent of p,V. These results follow by retaining the amplitude in
the earlier odd proof, instead of substituting V=exp(a/2).

The new source response is FromForm(RieszInv(J_interval.adjoint(e.symm p))).
Its physical interval embedding is definitionally the existing covariance.
The exact renormed inner product gives <response,z>=<p,Jz>. For the actual
Gamma test lift, z=response-FromForm(g), the weak source equation proves

    norm(z)_Ta <= norm(p-(c_a I+B_a)Jg)+norm(g).

Thus norm(z)^2<=F*a*V^2*exp(-2a). The already proved physical coercivity
L*a*norm(Jz)^2<=norm(z)^2 holds eventually for every L, independently of z.
Choosing L=F/epsilon gives the uniform scaled response-minus-Neumann error.

For the full remainder B_a u_N, the shift lower bound gives
exp(2a)*norm(u_N)^2<=U*V^2. The actual Gamma Fourier tail T beyond exp(K*a)
satisfies K*exp(2a)*T^2<=C_arch*D*V^2. The complete multiplier split gives

    norm(B_a u_N) <= eta*exp(a)*norm(u_N)+P*exp(a)*T.

Choose K large, then eta small, to prove norm(B_a u_N)^2<=epsilon*V^2.
This uses the complete prime-polar cancellation; no separate positive
estimate for those competing terms is substituted.

Finally c_a*(u_N-p/c_a)=-(B_a u_N+r_N). Since exp(a)<=2c_a,

    exp(2a)*norm(u_N-p/c_a)^2 <= 8*(norm(B_a u_N)^2+norm(r_N)^2).

The residual decays uniformly at its original amplitude V. Combining with
the actual response-minus-Neumann error gives the stated covariance profile.

## Final leaf audits

All use `lake --old env lean <leaf> -o <leaf.olean>` in foreground, one owned
Lean process at a time. No full or umbrella build, heartbeat increase,
numerical experiment, commit or push.

- CCMFiniteNeumannRemainderQuadratic87163: stronger actual odd remainder norm,
  previous quadratic statements preserved.
- SuzukiMatchedOddPoleProfile31416: four actual odd profile roots.
- CCMRestrictedWeilFiniteNeumannSource14820: source-uniform orbit, budget,
  finite vector and residual; previous odd definitions/statements preserved.
- CCMFiniteNeumannFormDecay86441: source-uniform actual Gamma admission;
  previous odd statement preserved.
- CCMMatchedEvenNeumannSource34774: actual even admission and finite inverse.
- SuzukiFiniteSourceCovariance43230: exact existing covariance realization,
  exact source equation, residual norm and uniform physical approximation.
- CCMFiniteSourceRemainder72877: uniform full remainder cancellation.
- SuzukiFiniteSourceProfile27643: finite, Ta and existing-covariance profiles.

The covariance and uniform-remainder audits emitted a ring-normalization
suggestion but exit0; the other listed final audits are silent. All new
leaves are wired. Public axiom audit4858 passes all 38 theorem queries with
only propext, Classical.choice and Quot.sound. The three actual odd/even/V2
Tendsto signatures have no hypothesis binders. Formal lint54349 reports only
the thirteen unrelated unreachable modules listed below; global lint is not green.

## Remaining mathematical frontier

The source-uniform statement preserves the amplitude of a transported old
finite-exponential source. It does not automatically admit an arbitrary
extended old actual response, whose contribution is explicitly required by
the discrete metric correction (c_a-c_b)*C_b(extended response_a). Full signed
shell/metric Wronskian control remains open.

The new profile suggests a stronger next test at actual V2 parameter1:
physical response approaches the literal exp(x)/c_a source in L2, potentially
forcing prescribed-shift defect0 and a free/zero carrier limit. The corpus
already proves selected-negative-shift escape; it does not by that theorem
alone prove the prescribed-shift claim. Xi's first defect is strictly
positive, so actual defect0 would require a different shift-selection or
shift-removal argument. These are conjectural consequences until audited.
Canonical normalization, shift removal, Xi identification and RH are not
closed by this profile theorem.

## Actual even specialization

SuzukiMatchedEvenPoleProfile final68617 passes without warnings. Its exact
sourceResponse_matchedEven identity identifies the existing raw cosh response.
The new premise-free root tendsto_suzukiTaMatchedEven_pole_profile proves
exp(a)*norm(f_even,a-p_even,a/c_a)^2->0. The unitary-coercion equality required
an explicit rfl after apply_symm_apply; no mathematical premise changed.

## Lint checkpoint

Formal lint54349 exits1 on thirteen unrelated unreachable modules, with no
prohibited proof declarations reported. All ten current changed leaves have
exactly one umbrella import and no trailing whitespace. Global lint is not
green. The current unrelated errors are:

- CCMApertureChainProfile
- CCMApertureTranslationChains
- CCMExponentialRampPrimeMoment
- CCMExponentialRampSourceDissipation
- CCMExponentialRampTerminalEntropy
- CCMRetainedChainKernelLower
- MoebiusMollifiedCriticalMoment
- MoebiusMollifiedErrorThreeLines
- SoninPrimePolarGroundTransfer
- ThetaCoordinateCanonicalFlux
- ThetaCuspCurvatureDefectGrowthPureNextMoments
- ThetaMovingShellFirstOrderPhase
- ZetaZeroDensityPowerSaving

## Actual V2 parameter1 specialization

SuzukiTaV2RawSourceProfile: scratch50842 and final17439 pass without warnings.
The exact sourceResponse_polar identity identifies every real exponential
source with the existing raw deficiency. At parameter1 its norm admission
follows from exp(x)<=exp(a/2)*exp(x/2) on the actual interval and the proved
half-pole norm. The literal polar budget supplies exp(a).

The premise-free root `tendsto_suzukiTaV2_rawSource_profile` therefore proves

    norm(J(rawDeficiency_a(1))-p_{a,1}/c_a)^2 -> 0.

This closes the physical-profile transfer to actual V2 parameter1. It does
not claim convergence of normalized characteristics or an Xi identification.
The next proposed actual first-defect separation remains unproved.

The next actual first-defect separation now has a dependency-closed paper
proof in P2:sz-prescribed-shift-first-defect-collapse. Its Lean status remains
open; no canonical-shift no-go is claimed complete here.

Cleanup verified: all 19 exact owned /tmp search, Lean and audit files removed;
all owned sessions terminal; valid audited leaf oleans retained.
