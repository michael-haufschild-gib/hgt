# CHMD: signed divisor pairing on the actual completed graph

Status: fully formalized and directly audited. Overall goal remains unconditional RH.

## Structural target

Identify the literal signed graph energy, and its real polarization, on all finite theta-divisor sources with the full multiplicity-weighted Xi zero pairing minus the original polar term. No graph-domain, convergence, or decay premise may remain on the finite-divisor family.

## Corpus ingredients

- `CHMDFiniteDivisorGraph`: every admissible finite divisor quotient with allowed polynomial numerator has actual real/imaginary graph representatives.
- `WeilPrimeBlindZeroSideIdentity.tendsto_W_truncTest`: unconditional convergence of the entire zero sum under the smooth bulk cutoffs for every `ExpDecayTest`.
- `WeilConeXiDivisibleBlindTest.tendsto_paperFT_truncTest`: convergence at both polar points.
- `WeilMarkovOneBoundState.markovEnergy_eq_W_sub` and `weilPoleTerm_weilTest_eq`: exact compact-test identity, including both polar products.
- `CHMDSignedGraphPolarization`: signed graph energy and pairing are continuous; compact lifted energy is the original Markov energy.
- `ThetaZeroDivisionRealization`: smoothness and exact Fourier factorization of admissible list divisions and polynomial combinations.

Two corpus deep searches completed. Requests reported nonpartial results; snapshot/semantic-coverage warnings require checking candidates against Lean. Direct corpus inspection located the actual cutoff zero-sum theorem.

## Paper proof

1. The bulk cutoffs are bounded between zero and one, converge pointwise to one, and have a common Lipschitz constant. For a bounded inverse-Doob profile v in the literal graph,
   |D(v chi_n)-Dv| <= 2|Dv| + M Lip(chi) |t|.
   The full displacement is in edge L2. Dominated convergence gives strong graph convergence of the actual compact cutoffs, retaining all prime atoms and the singular archimedean measure.
2. Apply continuous signed graph energy to that limit. Apply the existing unconditional zero-sum and polar-transform cutoff limits to the exact compact-test identity. Uniqueness of limits identifies the full signed energy on the noncompact source. Polarization gives the mixed identity.
3. Every admissible theta-list division has a first derivative decaying exponentially. On x>=0, apply the weighted-tail bound with a=|Im alpha|+1. A trigonometric factor grows only at |Im alpha|, leaving an exp(-x) factor. Reflection and evenness transfer the derivative estimate to x<=0. Smoothness follows from admissibility and seam cancellation. The source itself already has every exponential decay rate.
4. The real and imaginary parts of every finite polynomial partial-fraction combination therefore satisfy `ExpDecayTest`. Instantiate the graph identity on every such source; no extra analytic hypothesis remains. Include an unconditional nonzero instance from an existing positive real Xi zero.

## Formal results

- `CHMDBulkCutoffGraph.bulkTestLift_tendsto`: the explicit-formula cutoffs converge strongly in the full literal graph.
- `ThetaDivisorDecayClass.exponentialFirstJet_listComb`: every admissible finite divisor combination has C2 regularity and exponential source/derivative decay. This needs no numerator degree restriction; the Fourier realization uses the existing degree restriction.
- `CHMDGraphDivisorPairing.sourceEnergy_eq_signedZeroEnergy`: graph energy equals the full zero sum minus both polar products, on the literal source representative.
- `CHMDGraphDivisorPairing.sourcePair_eq_signedZeroPair`: the real polarization agrees as well. `signedZeroPair` is defined by polarizing the full zero-sum expression, not by dropping any terms.
- `CHMDFiniteDivisorPairing.finite_divisor_signed_graph`: every admissible quotient with allowed numerator has actual graph vectors, exact real and imaginary energies, their mixed pairing, and the original all-plane Fourier factorization. No graph-domain, decay, or cutoff-limit premise remains.
- `CHMDFiniteDivisorPairing.exists_exact_zero_division_signed_graph`: no-input existence theorem with a positive real Xi zero, nonzero preserved Fourier mass, the exact divided transform, and all three signed pairings.

All four leaves build; 503 lines, 27 declarations. Each leaf passes its final plain `lake env lean` audit with an empty log. All 27 declarations pass `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`. The initial 21 API probes and final 96 explicit `have := @Name` probes pass. Each new leaf has exactly one umbrella import.

Audited source SHA256:

- `CHMDBulkCutoffGraph`: `037a4209875ca62812509c11f689cfd01d98fb21957752aad769bdaba510f6e5`
- `ThetaDivisorDecayClass`: `34b8ffdf19ef706bace0aa5ed5811ab6d811b376ce9d944e99024824fc0f747d`
- `CHMDGraphDivisorPairing`: `aae631d28450e00dc7e1c49aa5a8ad6eeca1be4786b3107ae07a7b5cff9821ac`
- `CHMDFiniteDivisorPairing`: `832f7c47e8c82f337c58149ea4cdcc9d49f6a23e6dc9bf3f979d9ba4046f7fd9`

## Global checks

`scripts/formal_tools.py index` passed (6 changed modules, none removed; API, gaps, and overview refreshed). `scripts/formal_tools.py lint` exited 1 with exactly two errors: concurrent modules `CHMDKleinGordonBoundarySingularity` and `DeningerMeyerHasseFlowCoefficients` are unreachable from the RHTower umbrella. Neither belongs to this change. The four new leaves are all wired and introduce no active proof holes or forbidden declarations.

Owned build, direct-audit, API, axiom, index, and lint processes reached terminal status. Temporary search, probe, and log files are removed at closeout. No full build, heartbeat override, web search, numerical experiment, commit, or push was used.

## Boundary

This closes an equality-of-forms obstacle. It does not prove nonnegativity of the nondegenerate critical-band complement or exclude off-line zeros. Concurrent BV/quantile and Klein–Gordon leaves remain outside this write scope.
