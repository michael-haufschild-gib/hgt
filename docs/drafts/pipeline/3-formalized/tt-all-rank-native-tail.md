# TT: positive native tail at every finite rank

- **ID:** tt-all-rank-native-tail
- **Stage:** 3-formalized
- **Type:** C50; THEOREM (Lean), unconditional source statement
- **Route:** TT, all-rank center-flux construction C45

## Target and scope

For every finite rank N and every nonnegative integer shift s, the actual
matrix `((-1)^(i+j+s) nativeJet(2(i+j+s),x))_(i,j<N)` is positive definite
for all sufficiently large x. Radius may depend on N and s. This closes the
outer source region for each rank; it does not establish the compact-region
correction, its zero integrated payment, or RH.

Corpus basis: `ThetaCuspNativeOddFourCofinal` proves only odd rank four;
`ThetaCuspNativeJetFirstAtomApproximation` proves all-order relative source
error smaller than any fixed inverse Gaussian-scale power;
`ThetaCuspOddFourGaussianFlow.firstAtomPair_eq_affine` is an exact source
identity; `PoleUnitGammaBase` proves strict positivity of all positive-shape
Gamma moment matrices. No numerical experiments or finite atom replacement.

## Paper mechanism

Put q=pi exp(2x), u=q^(-1/2), S(z)=sinh(z)/z extended by S(0)=1,
Z(u,t)=t S(ut). The actual first-atom reflected profile, with its mass
removed, is exactly

    K(u,t)/D(u),
    K(u,t)=exp(-4 Z(u,t)^2) [D(u)-24 u^4 Z(u,t)^2],
    D(u)=(2-3u^2)^2,

after replacing reflection t by u*t. K is jointly smooth at u=0 and
K(0,t)=4 exp(-4t^2), D(0)=4. Consequently every fixed reflection derivative
converges to the corresponding Gaussian derivative. The signed even limit
is M_k=16^k (1/2)_k: the Gaussian ODE g'=-8tg gives
M_0=1 and M_(k+1)=8(2k+1)M_k.

The complete-source error theorem transfers this limit to every native jet.
For each s, M_(s+i+j)=M_s 16^(i+j) (s+1/2)_(i+j), a positive diagonal
congruence of a Gamma moment matrix. Entrywise convergence and openness of
positive definiteness give eventual positivity. Undo the first-atom mass
and q-power diagonal congruence to recover the literal source matrix.

The quantifiers are `forall N,s, eventually x`; no radius uniform in rank
is claimed. C49's negative center jets remain compatible with this theorem.

## Remaining research

Use this positive outer region in a source-specific construction of diagonal
and mixed zero-integral flux corrections on the remaining compact interval.
Neither the moving-minimizer variance nor a positive tilted Gram norm signs
that correction. The aperture derivative of a differentiated packet retains
a signed mixed term; dropping it would change the complete current.

## Log

- 2026-10-02: formulated from current corpus. Prior turn's C49 established
  necessary diagonal repair at unbounded orders; current Schur/Gram attempts
  have not supplied that repair. All-rank tail proof and Lean audit in progress.

## Lean certificate

The paper mechanism above is fully formalized in two new leaves:

- `ThetaCuspAllOrderGaussianLimit`: `firstAtom_scaled_jet_tendsto` and
  `native_scaled_jet_tendsto`, in namespace `RHTower.ThetaCuspGaussianLimit`.
- `ThetaCuspAllRankNativeTail`: `profile_signed_even_jet` and
  `nativeShiftedMatrix_posDef_eventually`, in the same namespace.

The final theorem has only the natural-number parameters N and s. It has
no unproved source premise or RH assumption. Every public theorem was
checked with `#print axioms` in a separate /tmp file; each uses exactly
`propext`, `Classical.choice`, and `Quot.sound`. Mathlib API probes in that
scratch audit also passed.

Targeted builds used `lake build --old +<module>`: 88 seconds for the
all-order limit leaf, 62 seconds for the matrix leaf. Final direct
`lake env lean GaloisForLFunctions/RHTower/ThetaCuspAllOrderGaussianLimit.lean`
and `lake env lean GaloisForLFunctions/RHTower/ThetaCuspAllRankNativeTail.lean`
both exited 0, without leaf diagnostics. Both leaves are explicitly wired
into RHTower. No heartbeat changes, holes, added axioms, numerical
experiments, subagents, full builds, or umbrella builds.

`formal_tools.py index` refreshed the three generated formal indexes.
Global `formal_tools.py lint --check-generated` exited 1 only for ten
unrelated unreachable modules: CCMApertureChainProfile,
CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase,
and ZetaZeroDensityPowerSaving. No new-leaf or stale-generated-index error.
Scoped whitespace checks passed.

## Corpus search and research assessment

Five current-corpus deep searches covered the actual successor diagonal,
aperture Gram representation, polynomial-weighted aperture curvature,
all-order integrated diagonal signs, and all-rank Gaussian tails. Their
reported `partial` flags were false; background refresh was incomplete and
semantic coverage was unmeasured. Candidates, source arguments and proposed
ingredient sets were inspected. Direct source reads identified the exact
first-atom identity, complete-source error law, and Gamma moment theorem.
No exhaustive novelty or external-literature claim is made.

The attempted direct Schur and differentiated-Gram arguments did not sign
the compact contribution. C50 instead closes the positive outer source
region at every finite rank, extending the previous explicit odd-four
result to all ranks and shifts. This is a proved part of the matrix-flux
construction, not its missing integrated payment. C45 and C48-S remain
open. Next work must construct and sign the actual compact correction,
retaining its diagonal entries, cross terms and zero boundary integral.
