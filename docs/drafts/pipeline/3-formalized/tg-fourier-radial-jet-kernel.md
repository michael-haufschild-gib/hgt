# TG-C9.1: the literal radial jet excludes maximal-domain Fourier collisions

- **ID:** TG-C9.1-20261001-01a0
- **Stage:** 3-formalized
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetKernel.lean`
- **Parent:** `../1-in-progress/tg-fourier-radial-jet-completion.md`

## Exact new theorem

Let H be actual physical complex L2, F the actual Fourier unitary, and M multiplication by
x² on its actual maximal domain. The concrete linear map

`E : D(M) × D(M) → H × H`, `E(f,g)=(f+F g, M f+F M g)`

is injective, with no external analytic premise. The theorem holds on full physical L2,
so also on the even source carrier. Every literal Burnol prime-depth column belongs to
D(M), and its M image is exactly the even radial jet of order two from the existing corpus.

## Proof

The maximal domain is preserved by physical dilation U_r and `M U_r=r^-2 U_r M`.
If g=F f and M g=F M f, symmetry gives
`<M f,U_r f>=r^-2<f,U_r M f>`.
Fourier unitarity and `F U_r=U_(1/r) F` give the same left side with factor r².
For every r>1, `<f,U_r M f>=0`. Strong dilation continuity at r=1 gives `<f,M f>=0`.
Its real part is exactly the nonnegative integral of x²|f(x)|². Since the zero set of
x² is a null singleton, f=0. Applying this kernel exclusion to E's two zero-output
equations proves injectivity. No derivative regularity, decay, or boundary premise is used.

## Audit

- Scratch `lake --old env lean /tmp/tg-c9-kernel-01a0.lean`: exit 0.
- Production `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetKernel.olean GaloisForLFunctions/RHTower/PrimeBurnolFourierJetKernel.lean`: exit 0, no warnings.
- Separate import/axiom audit of all four public theorems: exit 0; each uses only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Wired into `RHTower.lean`; declaration index refreshed. No umbrella or full build.
- Formal lint exits 1 on eleven unrelated unwired RHTower leaves:
  CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
  CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
  CCMRetainedChainKernelLower, MobiusDivisorCriticalRetainedPrimeMellin,
  MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
  No error names the new TG leaf.
- No added axiom, hole, heartbeat increase, numerical experiment, subagent, commit, or push.

## Frontier effect and remaining hard problem

C8's positive Fourier synthesis loses the neutral coordinate through its completed kernel.
Retaining this literal jet excludes every such collision on the maximal domain. It does
not yet establish injectivity after graph closure, bounded neutral transport, prime-depth
graph-core density, Gamma–Xi identification, Hardy-index transfer, or the sub-unit action.

The next candidate `../1-in-progress/tg-fourier-jet-weak-kernel.md` attacks graph-closure
injectivity directly. Actual Schwartz Fourier identities reduce a closed-graph collision
to a weak inverted-oscillator equation; the corpus Hermite ladder yields a recurrence
whose nonzero normalized solutions violate Bessel summability. That stronger proof remains
to be formalized. RH remains unproved and unfalsified.
