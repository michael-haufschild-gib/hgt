# Growing actual physical coercivity and rescaled odd approximation

- **ID:** sz-growing-coercivity-relative-error
- **Stage:** 3-formalized
- **Route:** SZ
- **Type:** POSITIVE
- **Date:** 2026-10-02

## Exact new results

`eventually_suzukiTa_physical_coercivity` proves, for every real L,

```lean
∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ w : SuzukiTaHilbert ⟨a, ha⟩,
  L * a * ‖suzukiTaPhysicalEmbedding ⟨a, ha⟩ w‖ ^ 2 ≤ ‖w‖ ^ 2
```

The floor is uniform over all actual Ta vectors. It is derived from the
actual prime--polar multiplier, exact Gamma weight and prescribed interval
shift. No source regularity, tail estimate, or new spectral hypothesis is
assumed.

`tendsto_suzukiTaMatchedOdd_neumann_relative_error` states that

    exp(a)*norm(Jw_a-u_a)^2 -> 0

along positive apertures tending to infinity, where w_a is the literal raw
coalescing odd response at anchor1/2 and u_a is the existing canonical finite
Neumann vector with n=ceil(a). The formal domain filter is the pullback of
real atTop under the positive-aperture inclusion. The preceding epsilon
theorem also gives the estimate directly for all sufficiently large real a
and every proof of positive aperture.

## Dependency-closed paper proof

For a form vector g, set f=Jg, F=norm(f), G=norm(g)_Gamma^2,
T=norm(f-Q_R f), c=c_a, and A=Re<(cI+B_a)f,f>.
The known prescribed-shift inequality gives A>=F^2>=0.

Low-band cancellation, full-line norm at most D*exp(a), exact compression,
and exp(a)<=2c give, eventually for R=exp(K*a),

    norm(B_a f) <= (c/4)*F + 2D*c*T.

The symbolic square (F/2-2D*T)^2>=0 then yields

    A >= (c/2)*F^2-M*c*T^2,    M=4D^2.

For every actual Gamma vector, without a finite-source hypothesis, the exact
Fourier cutoff norm and reverse logarithmic comparison give

    K*a*T^2 <= C_arch*G.

For L>0 choose K=2*C_arch*M*L. Since exp(a)/a tends to infinity and
c>=exp(a)/2, eventually c>=2L*a. Multiply the lower bound for A by 2L*a,
use A>=0 to replace 2L*a*A by at most c*A, and add c*G. The tail term is
paid by the Gamma inequality. Divide by positive c to obtain

    L*a*F^2 <= A+G = norm(w)_Ta^2.

Nonpositive L is immediate. This proves the uniform actual floor.

For the previously constructed odd-source lift g_a, put
z_a=w_a-FromForm(g_a). The exact residual equation gives

    norm(z_a)_Ta <= norm(r_a)+norm(g_a)_Gamma.

The proved source estimates therefore imply
norm(z_a)_Ta^2<=F0*a*exp(-a) with fixed F0>0. Apply the new physical
floor with L=2F0/epsilon. Multiplication by exp(a) and cancellation of
positive aperture give exp(a)*norm(Jz_a)^2<epsilon, eventually.
Because Jg_a=u_a exactly, Jz_a=Jw_a-u_a. The epsilon estimate proves the
stated unconditional limit.

## Lean audit ledger

Final foreground leaf audits passed for:

- CCMRestrictedWeilSourceContraction, audit66319: arbitrary-vector split;
  the existing certified-source contraction reuses it.
- CCMArchimedeanFourierTail, audit52297: exact arbitrary-Gamma Fourier tail.
- SuzukiMatchedOddSourceBound, audit81700: exact form identities exposed;
  actual Ta response-minus-test norm bound extracted from its existing proof.
- SuzukiGrowingPhysicalCoercivity, audit33070: uniform growing physical floor.

SuzukiMatchedOddNeumannApproximation passed scratch90661 and final audit74860
without warnings. All three new leaves are wired. Public axiom audit47142
passes all fifteen queries: only propext, Classical.choice and Quot.sound.
Both root signatures were checked. Current formal lint9165 reports twelve unrelated unreachable modules;
it reports no prohibited proof declarations. The root result is not a global
lint pass. The first axiom harness was cancelled after detecting missing
namespace qualification, before any theorem result; the corrected harness
uses fully qualified names.
Every final leaf command uses `lake --old env lean <leaf> -o <leaf.olean>`.
No umbrella or full build, numerical experiment or heartbeat increase is used.

Unrelated unreachable modules reported by lint9165:

- GaloisForLFunctions.RHTower.CCMApertureChainProfile
- GaloisForLFunctions.RHTower.CCMApertureTranslationChains
- GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment
- GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation
- GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy
- GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower
- GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
- GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
- GaloisForLFunctions.RHTower.RoutePLcmAbsoluteObstruction
- GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase
- GaloisForLFunctions.RHTower.ThetaTailConfluentCoordinatePort
- GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving

## Remaining hard frontier

This closes the growing-floor and rescaled approximation questions. It does
not determine the complete signed shell/metric Wronskian, remove the shift,
or identify a canonical Xi limit. RH remains unresolved.

The next concrete source calculation is c_a*N_o,a-O_a -> 0, followed by
its actual even analogue and the signed determinant cancellation. The full
paper mechanism, exact source dependencies, and remaining obligations are in
`../1-in-progress/sz-matched-source-metric-balance.md`.
