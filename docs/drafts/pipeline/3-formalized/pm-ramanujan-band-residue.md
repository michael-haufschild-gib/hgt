# Actual Ramanujan band cofactor residue

- **ID:** pm-ramanujan-band-residue
- **Stage:** 3-formalized
- **Route:** PM
- **Source:** `../1-in-progress/pm-ramanujan-band-critical-profile.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PMRamanujanBandResidue.lean`

For epsilon>0 define C_d(p)=0 when p divides d and
C_d(p)=p^(1+epsilon)/(p^(1+epsilon)-1) otherwise. The positive squarefree
weight h_d has local values h_d(p)=C_d(p), h_d(p^k)=0 for k>=2.
The literal actual Ramanujan coefficient satisfies

`mu(m)*a(d*m)=a(d)*m^(-1-epsilon)*h_d(m)`.

This gives the exact finite actual cofactor. Its signed residue
`R_d=mu*h_d` satisfies

`R_d(p)=C_d(p)-1`, `R_d(p^2)=-C_d(p)`, `R_d(p^k)=0` for k>=3.

For every fixed d!=0, `sum_n |R_d(n)|/n` is finite. Outside the finitely
many deleted primes, the local absolute tail is at most 4/p^2. At a deleted
prime it is 1/p. The existing positive multiplicative Euler summability
theorem applies. Exact divisor inversion, finite hyperbola interchange,
and dominated convergence give

`sum_(n<=x) h_d(n)/x -> H_d=sum_r R_d(r)/r`.

Weighted hyperbola interchange also gives the literal cofactor as

`d*a(d)*sum_(r<=Q/d) r^(-1-epsilon)*R_d(r)
               *sum_(k<=Q/d/r) k^(-1-epsilon)`.

The product cutoff and multiplier-one boundary are retained. Finally,
the candidate profile factor is exactly B_p/(1+B_p/p), with B_p=C_1(p).

These are actual source identities and a fixed-mask mean theorem. They
do not prove the weighted dyadic band limit, its complete density-product
normalization, or the moving signed anchored-energy bound. RH remains open.

## Validation

All 18 public declarations report only propext, Classical.choice, and
Quot.sound in a /tmp scratch audit, which exited0. The first audit was
interrupted by the host; no live process or handle remained, and its
replacement completed. Targeted
`lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandResidue`
passed; only the new leaf built (255s). Umbrella wired.
Final `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandResidue.lean`
passed with no diagnostics. No full/umbrella build, new axioms, numeric
experiments, or heartbeat increases.

Global lint exited1 solely for twelve unrelated missing umbrella imports:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
Sieve.VonMangoldtTwistPolynomialWindow, ThetaCuspLogJetOscillation,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
