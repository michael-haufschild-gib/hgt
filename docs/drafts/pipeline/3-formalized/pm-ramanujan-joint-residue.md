# Joint-residue drift cancellation at natural Ramanujan cutoffs

- **ID:** pm-ramanujan-joint-residue
- **Stage:** 3-formalized
- **Route:** PM
- **Source:** `../1-in-progress/pm-ramanujan-band-critical-profile.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PMRamanujanJointResidue.lean`

For the literal actual coefficients a and cofactor residue R_d, set
`K(d,r)=a(d)*r^(-1-epsilon)*R_d(r)`.
Finite convolution and actual cofactor inversion prove

`sum_(d*r=l)K(d,r)=a(1)*mu(l)*l^(-1-epsilon)`.

This identifies the spatial linear mode exactly. Remove it before taking
norms, defining

`V_l(N)=-sum_(d*r=l)K(d,r)*d*fract(N/d)`.

Each V_l has norm at most `sum_(d*r=l)|K(d,r)|*d`, uniformly in N,
and finite anchored energy `sum_N |V_l(N)|^2/[N(N+1)]`.
With `W_Q(l)=sum_(k<=Q/l)k^(-1-epsilon)`, the actual centered natural
prefix is exactly `sum_(l<=Q)W_Q(l)*V_l`. The complete band X<q<=Y
is exactly the difference of these finite sums at Y and X.
All cofactor masks and product cutoffs are retained.

This supplies a valid bounded-atom representation. It does not prove a
uniform bound on their signed sum, small-damping admission, or RH.
The unscaled cube-free local classification on the source card remains
paper-only; the formal drift proof does not assume it.

## Validation

Ten public declarations; 216 lines. Targeted
`lake --old build GaloisForLFunctions.RHTower.PMRamanujanJointResidue`
passed, with the new leaf built in 105s. All ten /tmp axiom reports use
only propext, Classical.choice, and Quot.sound. Final actual-file
`lake env lean GaloisForLFunctions/RHTower/PMRamanujanJointResidue.lean`
exited0 with an empty log. Umbrella import present exactly once.
No full/umbrella build, numerical experiment, new axiom, or heartbeat
increase. Explicit reindexing arguments resolved an inference timeout.

Global lint exited1 with unrelated missing umbrella imports:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ThetaTailOrderedRowMonotonicity,
ZetaZeroDensityPowerSaving. No new-leaf proof-debt finding.
