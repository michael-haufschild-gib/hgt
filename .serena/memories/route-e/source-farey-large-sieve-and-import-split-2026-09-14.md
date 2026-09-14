# Route E source Farey large sieve and import optimization (2026-09-14)

Proof chain remains: source cancellation → bounded unit-frequency Gamma–Hankel covariance → finite Möbius energy → Mellin continuation → RH.

Implemented lightweight `KloostermanSourceFourier.lean`, `KloostermanSourceFareyLargeSieve.lean`, `KloostermanRamanujanDivisorSum.lean`, and `FiniteReciprocalBound.lean`. Removed heavy Theta/Hawking import from `KloostermanCompleteColumnRamanujan.lean` and Route T paper-scale import from `KloostermanProductUnitChordSum.lean`. `KloostermanTerminalSourceFourier.lean` now imports the standalone source transform.

Key closed theorems: `sum_normSq_kloostermanSourceFourier_le_largeSieve`, `kloostermanWeightedUnitFrequencyEnergy_le_largeSieve`, and capstone `kloostermanGlobalFrequencyCollisionEnergy_le_two_sq_largeSieve`. They convert pairwise-coprime receiver multiplicity ≤2 and Farey spacing into a collision bound at classical source scale `N + M^2 * (1 + log (M^2 / 2 + 1))`, with uniform weight cap `W`.

Hard obstacle: no concrete Route E caller yet identifies physical moving-cusp data with generic `Q,w,B,b`. Generic spacing does not beat the `M^2` barrier. Next work must formalize exact source identification, then exploit actual weight decay or correlated Möbius cancellation. A uniform max-weight bound only closes if physical `W` decays strongly enough and is likely too crude.

Verification: direct `lake env lean <file>` passed for all changed theorem files, including collision capstone; small targeted `lake build` passed for SourceFourier, SourceFareyLargeSieve, and FiniteReciprocalBound. Large legacy target builds expanded into thousands of unrelated jobs and were interrupted; no full or umbrella build. Formal lint was blocked only by concurrently added, unwired `SuzukiTaV2ActualSecondDefectJet*` modules. No `#print axioms`, no heartbeat overrides, no `sorry/admit/axiom/opaque/unsafe` in changed files.