# CCM fixed-diagonal graph-admissible no-go

- **Claim:** `[CCM-FU-FIXED-DIAGONAL-GRAPH-NOGO]`
- **Target:** kill every cutoff-independent diagonal multiplier on actual causal-depth Γ source with ℓ² graph admission, uniformly bounded response, and rank `≤ (qN)²`.
- **Chain:** graph admission → fixed Hilbert–Schmidt feature → finite-rank density gives response pairing `o(N)` → transition-core Ward semiboundedness requires `Ω(N)` → contradiction.
- **Outside class:** non-ℓ² source, cutoff-moving multiplier, superquadratic rank, unbounded response, non-diagonal transport, distributional relative trace.
- **Status:** proved in Lean; target build and axiom audit pass. `no_suzukiCausalDepthGammaFixedDiagonalGraphWardProducer`.
