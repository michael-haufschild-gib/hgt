# SZ uniform exponential-frequency prime-polar cancellation

- ID: sz-prime-polar-exponential-frequency
- Stage: 3-formalized
- Type: THEOREM (Lean)
- Route: SZ
- RH status: unresolved

## Actual-source theorem

For every fixed K>0 and epsilon>0, eventually in aperture a,
  abs(polarPrimeStieltjesSymbol a xi)<=epsilon*exp(a)
for every real xi with abs(xi)<=exp(K*a).

This is the literal multiplier with cutoff floor(exp(2*a)), all prime
powers, and both endpoints. There is no RH or cancellation premise.

## Dependency-closed paper proof

The corpus polynomial-frequency theorem covers abs(xi)<=(2*a)^312.
For the complementary band, use ambient X=exp((K+1)*a), M=floor(exp(a)),
and N=floor(exp(2*a)). Put L=K+1. The limit (L*a)^(19/20)/a -> 0 gives
  twoRangeXmin(19/20,X)<=M
for sufficiently large a, including the floor loss. Also
  log(N)<=2*a<=log(2)+(L*a)^2,
  twoRangeT0(2,100,X)=(L*a)^311<=(2*a)^312,
  abs(xi)<=exp(K*a)<=2*pi*X.
Thus the audited complete half-density Mangoldt prefix estimate applies
at tau=-xi. Its real part is exactly half the prime cosine module:
the zero and one terms vanish and every other prime power is retained.
Since sqrt(M)<=exp(a/2) and sqrt(N+1)<=2*exp(a), that estimate gives
  abs(primeCosineModule)<=42*exp(a/2)+16*eta*exp(a).
Taking eta=epsilon/32 proves uniform high-frequency prime cancellation.
The explicit polar multiplier formula independently gives
  abs(polarMultiplier)<=6*exp(a)/abs(xi)
for a>=0 and abs(xi)>=1. This is negligible above the polynomial split.
The two frequency regions therefore cover the full exponential window.

## Lean audit

Module: CCMPolarPrimeExponentialFrequencyCancellation.

Five public theorems include the exact cosine/twist identity, the polar
frequency bound, the high-frequency prime estimate, and the full symbol
estimate. Scratch audit1813 and final direct leaf audit23736 exited0.
Final command from formal/:
  lake --old env lean GaloisForLFunctions/RHTower/CCM/CCMPolarPrimeExponentialFrequencyCancellation.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCM/CCMPolarPrimeExponentialFrequencyCancellation.olean
No warnings or errors. All five axiom queries (session91656) exited0 and
reported only propext, Classical.choice, Quot.sound. Root RHTower umbrella
import added; no umbrella or full build.

Global lint60973 exited1 on thirteen unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMEulerBoundarySpectralChart, CCMEulerBoundaryTransition,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ThetaTailOrderedRowMonotonicity,
ZetaZeroDensityPowerSaving. The new leaf was not reported; global lint is
not green.

## Remaining hard obligations

The exponential window is the arithmetic input for a growing number of
actual normalized bounded-remainder iterates. Prove closure and Fourier
tail bounds for their finite truncated-exponential representations, then
control the Neumann residual and actual odd Riesz response. Uniform
shifted source energies alone neither determine the signed aperture
Wronskian nor remove the shift or identify a Xi limit. RH remains open.
