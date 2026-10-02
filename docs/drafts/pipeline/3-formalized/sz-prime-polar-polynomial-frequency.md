# SZ uniform polynomial-frequency prime-polar cancellation

- ID: sz-prime-polar-polynomial-frequency
- Stage: 3-formalized
- Route: SZ
- RH status: unresolved

## Actual-source theorem

For every natural m and every epsilon>0, eventually in aperture a,
  abs(polarPrimeStieltjesSymbol a xi)<=epsilon*exp(a)
uniformly for all real xi with abs(xi)<=(2a)^m.

The statement uses the literal finite-aperture polar-prime symbol,
including every prime power and the original terminal cutoff. There is
no RH premise, response regularity assumption, or added axiom.

## Paper proof and positive content

Let E be the actual normalized Chebyshev error, J(h)=integral_0^h |E|,
and D the literal completed critical-Mellin error. The corpus PNT rate
and global driver bound give, by splitting the integral at h/2,
  J(h)<=(h/2)*(h+1)*exp(h/4)+2B*exp(h/2-c*sqrt(h/2))
eventually, with c>0. Thus h^m*exp(-h/2)J(h) tends to zero for every m;
the same holds with |E(h)| in place of J(h).

The exact Volterra completion gives
  |D(h)|<=3+|E(h)|+J(h)/2,
  integral_0^h|D(t)|dt<=3h+(1+h/2)J(h).
Consequently both D and its absolute primitive retain every fixed
polynomial saving. Absolute integration has not discarded the moving head.

Apply the existing zero-terminal Stieltjes identity to
exp(i*xi*h)-exp(i*xi*2a), then restore the constant test through its exact
completed-error identity. This retains the endpoint and proves
  norm(pairing)<=|D(2a)|+|xi|*integral_0^(2a)|D(h)|dh.
The four source limits give uniform smallness on the full polynomial
frequency band. Twice the real part is the actual polar-prime symbol.

## Lean audit

- CCMCriticalMellinPolynomialCancellation: four public source-limit theorems.
- CCMPolarPrimePolynomialFrequencyCancellation: endpoint estimate, uniform complex pairing, uniform actual symbol.

Both final leaf commands used `lake --old env lean <leaf> -o <leaf.olean>`
in formal/, one foreground process at a time. Both exited0. The first
printed an internal ring advisory but no error or linter warning; the
second printed no output. All seven public axiom queries exited0 and
reported only propext, Classical.choice, Quot.sound. Both leaves are wired
into the root RHTower umbrella. No full or umbrella build was run.

Global lint exited1 on eleven unrelated unreachable leaves:
CCMApertureChainProfile, CCMApertureTranslationChains, CCMEulerBoundaryQuotient,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
Neither new leaf was reported. Global lint is not green.

## Next hard obligations

Join this region to the audited uniform half-density Mangoldt estimate at
the literal cutoffs floor(exp(a)) and floor(exp(2a)), retaining the head
and the high-frequency continuous polar main term. Prove uniform smallness
on every band abs(xi)<=exp(K*a). Then certify the truncated-exponential
iterate class, growing number of moments, Neumann residual, and actual odd
Riesz response. Signed aperture Wronskian control and shift removal remain
open even after the proposed uniform odd-energy bound.
