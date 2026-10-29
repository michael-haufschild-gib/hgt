# Finite Ramanujan packet forms at strict spacing

- **ID:** ramanujan-spacing-archimedean-rank-one-limit
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** complete-Weil norm quasimodes, normalized Ramanujan Gram limit, exact atomic mass and pole identities
- **Statement:** Actual mass, Markov, and complete-Weil forms have explicit limits on every fixed finite Ramanujan packet for every fixed `0<c<1`.
- **Count:** uncounted; supporting corollaries of the complete-Weil spectral package

## Scope

Finite-packet corollaries of the
[complete-Weil spectral law](complete-weil-spacing-ramanujan-spectral-law.md).

Fix real `C²` profile `phi` supported in `[0,1]`, with `M2=integral(phi²)>0`,
`I=integral(phi)`, `sigma=log(1/(2*pi*c))+bumpRobin(phi,1)/M2`, and `0<c<1`.
For finite positive conductor set `S` and real coefficients `b`, put

`x_b(n)=sum_(m in S) b_m*normalizedRamanujanMode(m,n)/sqrt(n)`,
`f_(b,N)(u)=sum_(n=1..N) x_b(n)*phi((u-log(n))/(c/N))`.

Write `b_1=0` when `1` is absent from `S`. The proved limits are:

`integral(f_(b,N)²)/((c/N)*log(N)) -> M2*sum_(m in S)b_m²`,

`Markov(f_(b,N))/((c/N)*log(N))
 -> M2*sum_(m in S)b_m²*(sigma+log(m)+tameDifferent(m))-c*I²*b_1²`,

`Weil(f_(b,N))/((c/N)*log(N))
 -> M2*sum_(m in S)b_m²*(sigma+log(m)+tameDifferent(m))+c*I²*b_1²`.

The range is the full strict-spacing range; signed profiles and conductor one
are included. The prime, Gamma and both pole terms are retained.

## Proof assembly

Let `v_(m,N)` be the normalized Ramanujan vector and `W_N` the actual complete
Weil matrix. The proved norm residual is
`||W_N v_(m,N)-lambda_m v_(m,N)|| -> 0`; normalized mode norms tend to one.
Cauchy--Schwarz and the proved Gram limit give
`<W_N v_(m,N),v_(l,N)> -> delta_(m,l)*lambda_m`.
Finite summation gives both mixed packet limits, without a new spectral input.
Here `lambda_m=sigma+log(m)+tameDifferent(m)+alpha*[m=1]`,
`alpha=c*I²/M2`.

The literal coefficient vector is `sqrt(log N)*v_(b,N)`. Since `c<1`, atom
separation holds eventually. Exact atomic mass is then
`(c/N)*M2*log(N)*||v_(b,N)||²`. The exact complete-matrix identity gives
`Weil(f_(b,N))=(c/N)*M2*log(N)*<W_N v_(b,N),v_(b,N)>`.
These identities transfer the Gram and mixed energy limits to actual tests.

Put `H_(b,N)=sum x_b(n)/sqrt(n)` and `O_(b,N)=sum x_b(n)*sqrt(n)`.
The harmonic Gram against conductor one gives `H_(b,N)/log(N) -> b_1`.
Every nonconstant Ramanujan mode has zero period mean and bounded partial
sums, so `O_(b,N)/N -> b_1`. For the two exponential moments `A_N,B_N` of
one atom and its squared mass `G_N=(c/N)*M2`, the proved quadratic error gives
`|N*A_N*B_N/G_N-alpha| <= C_phi*c²/N`. Thus the exact two-pole contribution,
divided by `(c/N)*log(N)`, equals
`2*M2*(N*A_N*B_N/G_N)*(H_(b,N)/log(N))*(O_(b,N)/N)` and tends to
`2*c*I²*b_1²`. Subtracting it from the complete Weil limit gives the stated
Markov limit. No positivity or spectral premise is introduced.

## Lean declarations

All declarations are in `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory`.

- [TheCompleteWeilFormIsDiagonalOnFiniteRamanujanPackets.lean](../../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheCompleteWeilFormIsDiagonalOnFiniteRamanujanPackets.lean):
  `tendsto_normalizedRamanujanPacketVector_inner`,
  `tendsto_completeWeilMatrix_packet_inner`, and exact profile normalization.
- [TheRamanujanPacketPoleCoordinatesSelectConductorOne.lean](../../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanPacketPoleCoordinatesSelectConductorOne.lean):
  `tendsto_ramanujanPacket_harmonic_pole`,
  `tendsto_ramanujanPacket_ordinary_pole`,
  `tendsto_horizon_mul_normalized_atom_pole_product`,
  `tendsto_ramanujanPacketTest_two_poles`.
- [TheMarkovAndWeilPacketFormsHaveOppositePoleShifts.lean](../../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheMarkovAndWeilPacketFormsHaveOppositePoleShifts.lean):
  `tendsto_ramanujanPacketTest_mass`,
  `tendsto_ramanujanPacketTest_weil`,
  `tendsto_ramanujanPacketTest_markov`.

## Gates

- [x] Exact scope identified; complete-Weil spectral law already proved
- [x] Dependency-closed packet argument and exact carrier identities
- [x] Actual packet endpoints formalized in Lean
- [x] Individual installed-source and transitive axiom checks
- [x] Umbrella integration, card transition, owned scratch cleanup

## Verification

Three individual installed-source checks passed with empty diagnostics. Nine
transitive axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. Three unique imports are integrated into the owner umbrella;
only the two required dependency oleans were generated. No umbrella build,
existing olean rebuild, placeholder, or limit override was used.

Evidence: [source checks and hashes](../../../../logs/ramanujan-packet-forms-source-audit-2026-10-29.log),
[axiom reports](../../../../logs/ramanujan-packet-forms-axioms-2026-10-29.log).
Owned scratch files are removed. Foundational README is unchanged. No novelty
audit or web search was performed; supporting uncounted status is retained.
