# Actual matched odd metric balance

- **ID:** sz-matched-odd-metric-balance
- **Stage:** 3-formalized
- **Route:** SZ
- **Type:** POSITIVE
- **Date:** 2026-10-02

## Exact result

`tendsto_suzukiTaMatchedOdd_metric_balance` proves

    abs(c_a*norm(Jw_a)^2-O_a) -> 0

along positive apertures tending to infinity. Here c_a is the actual prescribed
interval shift, w_a is the literal raw coalescing odd response at parameter1/2,
J is the actual physical embedding, and O_a is its completed covariance energy.
The root has no unproved premise. The filter is the pullback of real atTop
under the positive-aperture inclusion; an epsilon theorem also states the
estimate for all sufficiently large real a and every proof of positive aperture.

Two new analytic components are independently exposed:

- The actual complete bounded-remainder quadratic of the canonical finite
  Neumann vector u_a tends to zero: abs(Re<B_a u_a,u_a>)->0.
- Replacing actual physical squared norm by norm(u_a)^2 costs o(1), even
  after multiplication by the prescribed shift c_a.

## Dependency-closed paper proof

The existing literal finite source and its actual Gamma lift g_a satisfy
exp(a)*norm(u_a)^2<=M and norm(g_a)^2<=D*a*exp(-a), with fixed positive
constants. For R=exp(K*a), the new arbitrary-Gamma Fourier tail gives

    exp(a)*norm(u_a-Q_R u_a)^2 <= C_arch*D/K.

The complete remainder splits into low-band multiplier and Fourier tail.
For every fixed K>0 and eta>0, the actual low-band symbol is eventually
bounded by eta*exp(a). Its full-line norm is bounded by P*exp(a), with
P=norm(kappa)+46. Hence the complete quadratic is bounded by

    eta*M + P*sqrt(M*C_arch*D/K).

Choose K first, then eta. This proves quadratic vanishing without splitting
prime and polar terms into independent positive estimates or sharpening the
finite-exponential budget. The actual Gamma lift supplies the required tail.

Exact unitary transport and physical compression give
c_a<=1+P*exp(a)<=(P+1)*exp(a). The audited rescaled approximation says
exp(a)*norm(f_a-u_a)^2->0, where f_a=Jw_a. Since
exp(a/2)*norm(u_a) is bounded, the norm-square difference inequality

    abs(norm(f_a)^2-norm(u_a)^2)
      <= norm(f_a-u_a)*(2*norm(u_a)+norm(f_a-u_a))

proves c_a*abs(norm(f_a)^2-norm(u_a)^2)->0.

The exact source equation gives O_a=Re<p_a,f_a>. Write
r_a=p_a-(c_a I+B_a)u_a. Then

    O_a-c_a*norm(u_a)^2
      = Re<p_a,f_a-u_a> + Re<r_a,u_a> + Re<B_a u_a,u_a>.

The first term vanishes by norm(p_a)<=exp(a/2) and the rescaled response
error. The second vanishes by the actual finite-source residual estimate
and the half-exponent norm bound for u_a. The third is the new complete
quadratic limit. Combining with norm-square transport proves the root.

## Lean audit ledger

All final audits use `lake --old env lean <leaf> -o <leaf.olean>`, in foreground,
one owned Lean process at a time. No full or umbrella build is used.

- SuzukiMatchedOddMetricTransport: scratch41623, final58443 passed.
- CCMFiniteNeumannRemainderQuadratic: scratch55478, final66228 passed.
- SuzukiMatchedOddSourceBound: final47712 passed after exposing the exact
  source-energy identity as a public wrapper, preserving its existing proof.
- SuzukiMatchedOddMetricBalance: scratch97390 exposed a namespace-sensitive
  addition monotonicity alias; explicit add_le_add fixed it. Final16313 passed.

Final leaves pass without warnings and all three new modules are wired.
Axiom audit58144 passes all eight new public queries with only propext,
Classical.choice and Quot.sound. The premise-free actual balance root
signature was checked. Current formal lint38139 exits1
on twelve unrelated unreachable modules and reports no prohibited proof
declarations. None of the changed or new leaves is reported; global lint is
not green. Previous fifteen public queries for
coercivity/relative error passed with only standard Lean axioms.

Unrelated unreachable modules reported by lint38139:

- GaloisForLFunctions.RHTower.CCMApertureChainProfile
- GaloisForLFunctions.RHTower.CCMApertureTranslationChains
- GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment
- GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation
- GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy
- GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower
- GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
- GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
- GaloisForLFunctions.RHTower.SoninCorrectionResponseRecovery
- GaloisForLFunctions.RHTower.ThetaCuspMixedPairOddFourFloor
- GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase
- GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving

## Remaining hard frontier

Actual even-channel balance and the signed two-source determinant remain open.
The discrete cross-aperture metric correction uses covariance at the larger
aperture applied to the extended smaller response. Same-aperture balance
alone does not pay that mixed-response term, even for bounded aperture gaps.
The complete signed shell Wronskian remains open.

The current estimates use matched parameter1/2. The V2 anchor-I first-mode
identity uses parameter1. Their transfer must be proved explicitly; these
results do not close full V2 source control, canonical normalization, shift
removal, Xi identification, or RH.

The proof exposes a stronger next vector-profile conjecture:
exp(-a)*norm(B_a u_a)^2->0, hence exp(a)*norm(f_a-p_a/c_a)^2->0.
Its paper mechanism and mixed-aperture purpose are recorded on the active
card `../1-in-progress/sz-matched-source-metric-balance.md`; it is not yet
claimed Lean-closed.
