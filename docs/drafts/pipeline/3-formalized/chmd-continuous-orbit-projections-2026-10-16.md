# CHMD: continuous divisor readouts and exact orbit projections

Status: FORMALIZED. All seven leaf builds and final plain Lean audits passed. Overall goal remains unconditional RH and is not achieved.

## Frontier and conjecture

The actual full arithmetic graph now contains primitive cardinal frames, but their spectral identities were proved only for the constructed sources. An abstract strip multiplier radical theorem does not identify readouts on arbitrary completed graph vectors. Conjecture: every actual Xi orbit defines an explicit continuous signed projection on the full graph, with coefficients equal to literal cosine Fourier samples of its source. This must retain the original graph topology, all prime atoms, multiplicities, and polar cancellation.

Verdict: SURVIVES PRELIMINARY ATTACK within the current corpus. The existing abstract multiplier readouts and finite-dimensional signed-form algebra do not prove this assertion: the missing step is the continuous literal-source identification on the maximal graph. External novelty audit omitted under the user's explicit no-web/no-novelty instruction. No claim of novelty beyond the checked corpus.

## Dependency-closed paper proof

Let mu(dx)=Phi(x) cosh(x/2) dx and p have source coordinate v in L2(mu). Define C_p(z)=integral Phi(x) v(x) cos(z x) dx. The kernel k_z(x)=cos(z x)/cosh(x/2) has real and imaginary parts in L2(mu): its weighted square is bounded by Phi(x) exp(2 |Im z| |x|), integrable by the existing full exponential moments of theta. Consequently C_p is a continuous real-linear functional of p for every complex z, given by the two L2 inner products with k_z. The weighted integral identity proves that this functional is exactly the literal source integral, not an arbitrarily chosen extension. It is even in z and Schwarz symmetric because v is real.

For a Xi zero a with Re(a)>0, choose the already admitted cardinal frame (u_a,v_a), with source Re(U_a), Im(U_a). Put A(z)=1_{z=+/-a}, B(z)=A(conjugate z), and M_a=sum_rho m_rho (A(gamma_rho)+B(gamma_rho))/2. This is a finite, strictly positive sum. Its relation to the prior positive energy mass K_a is M_a=K_a for real a and M_a=2 K_a for nonreal a.

First take a real compact C2 source f. Its full zero sum is absolutely summable. The cardinal source g_c=Re(c U_a) has transform (c A+conjugate(c) B)/2 on every zero and zero at both poles. Both mixed sums have finite orbit support. Expand the signed energy of f+g_c and polarize. For real f, conjugate(FT_f(conjugate z))=FT_f(-z); hence the mixed summand is m_rho Re(C_f(z) V_c(z)). Evenness and Schwarz symmetry of C_f reduce each nonzero incidence to Re(c C_f(a)), with coefficient (A+B)/2. Thus

  B(p,u_a)=M_a Re C_p(a),
  B(p,v_a)=M_a Im C_p(a).

The left sides and the literal-source readouts are continuous in the full graph. Density of genuine compact C2 tests extends both identities to EVERY graph vector p. This is the central domain/continuity step.

At a nonreal orbit define P_a p=2 Re C_p(a) u_a - 2 Im C_p(a) v_a. At a real orbit define P_a p=Re C_p(a) u_a. The cardinal identities give C_{P_a p}(a)=C_p(a), so P_a is a continuous idempotent. Its range is primitive and its residual is signed-orthogonal to the selected frame. Therefore the original signed energy splits exactly into the projected and residual energies. At a nonreal orbit the projected form is 4 K_a ((Re C_p(a))^2-(Im C_p(a))^2), with K_a>0 and genuine rank two; at a real orbit it is K_a (Re C_p(a))^2 and has rank one. Distinct four-point orbits have mutually annihilating projections. Every vector in the actual signed radical has C_p(a)=0 at every Xi zero; the real-orbit imaginary frame vector belongs to that radical.

The existence of an actual positive real Xi zero supplies a premise-free nonzero projection instance. No nonreal zero is asserted to exist, and no positivity hypothesis is used.

## Work plan

1. Literal all-plane cosine readouts as continuous graph functionals.
2. Compact mixed cardinal pairings with honest summability and polar accounting.
3. Extension to all graph vectors, exact orbit projections and radical consequence.
4. Leaf builds, plain final Lean audits, API/axiom checks, umbrella wiring, index/lint, cleanup.

## Boundary

No primitive positivity, complete spectral expansion, full radical classification, or RH claim. Cosine packets detect the even part; odd-sector detection and global completeness remain separate obligations. The goal remains premise-free unconditional RH via CHMD.

## Verification

All seven `lake --old build <leaf>` checks passed without warnings in the new declarations. Each final `lake env lean <leaf>` passed with an empty log. The compact mixed proof explicitly proves summability before distributing the full zero sum. The universal theorem uses the already proved dense compact core and has no source regularity premise on its arbitrary graph vector. All 94 explicit new declarations passed the axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`; 88 explicit mathlib API probes passed. Each new leaf is wired exactly once into the theorem-area umbrella. Index generation passed and includes the new projection declarations. No full or umbrella build was run.

Global `scripts/formal_tools.py lint` was rerun after concurrent umbrella changes. It still exits 1 solely because the unrelated, concurrently developed `GaloisForLFunctions.RHTower.PaperThetaSpatialSolvability` is not yet wired into the theorem-area umbrella. The earlier `EvenSectorPolarCompletion` reachability error was resolved by its owner. These concurrent files were not changed by this task. Existing large-file warnings remain. The seven new CHMD leaves have no lint errors.

All owned processes terminated. Removed all 25 owned scratch/search/probe/build/audit artifacts from `/tmp`; retained the verified Lean build artifacts. No commits or pushes.

The final leaf defines a canonical operator directly on `PositiveXiZero`, choosing the already proved actual cardinal frame. Its statements do not require a user-supplied frame, admission assumption, or positivity assumption. A separate premise-free theorem supplies a nonzero member of this actual family.

Seven new leaves, 955 lines:

- `CHMDGraphCosineReadout`: continuous all-plane literal cosine integrals and absolute integrability.
- `CHMDCompactSourceClass`: compact source admission to the required decay, Lipschitz, theta and exponential-moment classes.
- `CHMDCosineSourceFourier`: exact cosine/Fourier convention bridge.
- `CHMDCardinalIncidencePairing`: multiplicity-preserving orbit incidence and positive orbit mass.
- `CHMDCompactCardinalPairing`: fully summable mixed zero sums and compact graph pairings.
- `CHMDUniversalCardinalPairing`: arbitrary graph pairings, exact frame samples, and signed-radical annihilation.
- `CHMDContinuousOrbitProjection`: canonical continuous projections, idempotence, exact ranges, signed symmetry, energy splitting, mutually annihilating distinct orbits, and a premise-free nonzero instance.

Source SHA256:

```text
CHMDGraphCosineReadout e3c9b4d5bdee75e0e24638c8a1f4bd4e85da47acf0975f1678034e9e98b689eb
CHMDCompactSourceClass 09116ae973c038d982872d4e32b70379e4867950b98f8de3d0825d125bb7c5aa
CHMDCosineSourceFourier 237c47899770cafd3a6ac1664738c8cb63982d5c86b99b43009c553587744974
CHMDCardinalIncidencePairing 0687549a0600e89fa2b23de47739d5219b796ebdc836c1cc965c2bed76f76c50
CHMDCompactCardinalPairing 0f896b9cf681d1eba2027dfb99a483d4317aeca3da6dd459ab241279ecfd3be8
CHMDUniversalCardinalPairing 2e8b7bab6ca2280576c00fcd5cc63ffac06f1b7779156acb7fb7ab443127db44
CHMDContinuousOrbitProjection 9fd6300725a46e1dd3d038a380b81db00784f87aa867a6d5f6d759c12e2d38bb
```

## Research audit and next obstacle

The contribution closes an actual corpus gap: literal spectral samples now represent signed pairings on the entire maximal graph, and individual orbit planes split off continuously. The previously known finite-dimensional signature calculation alone did not imply this. The work did not prove RH, primitive positivity, or a complete spectral expansion. No external novelty claim is made because the user explicitly prohibited that audit. The auxiliary integration and summability lemmas were required to close the completed-graph statement; stopping with those helpers would not have met the target.

The next falsifiable structural conjecture is the converse on the even sector: an even graph source with zero cosine samples at all Xi zeros and zero polar cosine moment lies in the full signed radical. Proving it requires a justified mixed zero-sum limit for arbitrary graph sources, or an independently proved completeness theorem. Neither is assumed here. Odd-sector detection remains a separate obligation. No hard step was discarded on effort grounds.
