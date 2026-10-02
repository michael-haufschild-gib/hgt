# PM: nearby-prime covariance survives reciprocal-mean removal

- **ID:** pm-ramanujan-nearby-prime-resonance
- **Stage:** 5-failed: uniform covariance conjecture; positive survivor formalized
- **Route:** PM, actual anchored Ramanujan Gram
- **Parent:** pm-ramanujan-band-critical-profile
- **Goal relevance:** test the proposed uniform growing-cofactor remainder
  after removing the fixed-cofactor totient/reciprocal-mean term.
- **RH status:** no admission bound or RH proof.

## Candidate tested

The existing fixed-cofactor law has a rank-one limit
`p <D_p P_q,P_r> -> -phi(r)/2 * (-Lambda(q))`.
It was tempting to remove reciprocal means and then treat the remaining
mixed covariance as uniformly bounded for growing p-free cofactors.
The following exact positive survivor contradicts that proposed uniform
bound. It does not contradict the fixed-cofactor theorem.

## Positive survivor: a continuous local covariance profile

Fix r>1. Put `F_r(x)=P_r(floor(x))/x` for x>0 and zero otherwise.
Since P_r(0)=0 and P_r is bounded, F_r belongs to L2(R). The audited step
Gram formula identifies `<F_r,F_s>=G(r,s)`.

Use the normalized dilation `D_a f(x)=sqrt(a)*f(a*x)`. Its group law,
isometry, and strong continuity are already proved in
`SoninDilationContinuity.lean`. Define

`K_r(c)=Re <F_r,D_c F_r>` for c>0.

Then K_r is continuous, `K_r(1)=G(r,r)>0`, and
`|K_r(c)|<=G(r,r)` by Cauchy--Schwarz. This retains a full spatial
covariance profile, not merely a negative statement about one proposal.

For p prime not dividing r, the actual primitive identity gives

`F_(p*r)/sqrt(p)=D_(1/p) F_r-F_r/sqrt(p)`.

Thus, for distinct primes p,q not dividing r, expansion of the inner
product and dilation isometry give

`|G(p*r,q*r)/sqrt(p*q)-K_r(p/q)|
 <= G(r,r)*(1/sqrt(p)+1/sqrt(q)+1/sqrt(p*q))`.

No prime-distribution theorem is used in this error estimate. In
particular, whenever p,q tend to infinity with q/p tending to one,

`G(p*r,q*r)/sqrt(p*q) -> G(r,r)`,
`G(p*r,q*r)/p -> G(r,r)>0`.

The error bound follows term by term from isometry and Cauchy--Schwarz:
the two mixed base-vector terms have absolute values at most G(r,r),
as does the final base-vector square. All functions here are actual
primitive step vectors, and all their norms are finite before the
inner-product expansion.

## Unconditional prime realization and mean removal

`STCPrimeWindowPackets.exists_prime_pair_ratio_lt` supplies arbitrarily
large distinct primes with ratio in (1,1+delta), for every delta>0.
Take the threshold above r, and let delta tend to zero. This realizes
the preceding positive asymptotic unconditionally with p not dividing
q*r. If r is a non-prime-power, Lambda(r)=Lambda(p*r)=Lambda(q*r)=0.
The audited reciprocal-mean formula therefore leaves the Gram unchanged
by reciprocal-energy centering.

The mixed dilation itself also remains large:

`p <D_p P_r,P_(q*r)> = G(p*r,q*r)+G(r,q*r)`.

Here D_p on sequences means floor dilation, not the normalized Hilbert
dilation above. Cauchy--Schwarz and the prime recursion give
`|G(r,q*r)|<=G(r,r)*(sqrt(q)+1)`, so this last term divided by p tends
to zero. The normalized mixed dilation consequently tends to G(r,r),
despite the zero reciprocal mean of its slow input P_r.

For squarefree composite r, the actual coefficients a(p*r) and a(q*r)
have the same sign. The surviving nearby-prime Gram contribution is
therefore positive after inserting the actual coefficients. Cancellation
must involve other cofactor branches in the complete natural cutoff;
neither reciprocal-mean removal nor this branch alone pays the budget.

## Corpus and Lean audit

Search108 complete (inventory generation1186189), Search109 complete
(1186247), Search110 complete (1186267), Search111 partial (1186289).
All inventories complete; compiler metadata largely pending/stale.
All candidate/source statements and ingredient proposals inspected.
No nearby-prime primitive Gram profile was returned. Read actual
`PMPairedRamanujanGram`, `StepFunctionCarrier`,
`SoninDilationContinuity`, and `STCPrimeWindowPackets` signatures.

Lean leaf: `PMRamanujanNearbyPrimeResonance.lean`, 14 public declarations
(three definitions and eleven theorems). The actual step-vector/Gram
identification, exact prime insertion, continuous profile, quantitative
finite covariance estimate, and unconditional unbounded centered Gram
are implemented. The full scratch check and targeted old-mode leaf build
passed; the new leaf compiled in 14 seconds. All 14 public declarations passed the `/tmp` axiom audit: only
`propext`, `Classical.choice`, and `Quot.sound`. The final actual-file audit
`lake env lean GaloisForLFunctions/RHTower/PMRamanujanNearbyPrimeResonance.lean`
exited 0 with no diagnostics. The leaf is wired once into RHTower;
no umbrella build was run. No added axiom or RH premise.

The two displayed sequential limits, mixed floor-dilation limit, and
actual coefficient-sign consequence above are paper corollaries; no
separate Lean exports for those corollaries are claimed. The positive
survivor formalized here is the stronger finite profile/error law and
its unconditional prime realization.

Continuation searches112 and113 were complete, with complete inventories
(generations1186542 and1186552 respectively; compiler metadata largely
pending/stale). Candidates, source arguments, and the proposed ingredient
set were inspected. The antidiagonal proposal leaves “Ensure cancellation”
unproved. Exact Ramaré dilation retains its unequal-prime covariance;
complete old-cofactor block factorization retains both complement-boundary
terms. None of these supplies the missing moving-cutoff energy estimate.


Global `scripts/formal_tools.py lint` exits 1 on eleven unrelated modules
unreachable from the RHTower umbrella: CCMApertureChainProfile,
CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase,
ThetaTwoNodeSignedSturmEnergy, and ZetaZeroDensityPowerSaving.
No lint error names the new leaf. Existing large-file warnings remain.

Route PM is not retired. Its hard signed small-damping anchored-energy
upper bound is still unproved; the RH goal remains active and unmet.
