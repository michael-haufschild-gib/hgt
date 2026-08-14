# The exact closed cutoff-graph relation, formalized

- **ID:** `suzuki-wiener-cutoff-closed-graph-relation`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-wiener-cutoff-closed-graph-relation.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/MultiplierClosedGraph.lean`
  - `formal/GaloisForLFunctions/HTGeometry/CarlemanOperatorBound.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ResolventSubordination.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiCutoffCommutator.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiCarlemanCommutatorKernel.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiBandlimitedPort.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiExteriorRiggedRealization.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiSupportPrunedSeamCarrierBounds.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiSupportPrunedSelfAdjointSeamCarrier.lean`

## Formal content

| Card | Lean |
|---|---|
| `(2)`–`(3)` finite-aperture symbol and its two parts | `suzukiExteriorSymbol`, `suzukiSymbolRemainder`, `exists_bound_suzukiSymbolRemainder`, `suzukiWienerMass` |
| `(4)`, `(15)` high-pass threshold and margin | `exists_suzukiExteriorThreshold`, `tsum_enorm_suzukiExteriorInverse_le` |
| `(13)`–`(14)` valuation-Wiener element and Neumann inverse | `suzukiHighPassElement`, `suzukiExteriorInverse`, `discreteConv_suzukiHighPass_inverse` |
| `(6)`–`(7)` coefficient state and the carrier equation | `suzukiWienerEval_carrier`, `summable_norm_suzukiExteriorInverse` |
| `(8)`, `(17)`–`(18)` evaluation is a convolution character | `suzukiWienerEval_discreteConv`, `suzukiWienerEval_inverse_mul` |
| `(19)` closed multiplier graph domain | `multiplierGraph`, `isClosed_multiplierGraph`, `supportedIn`, `isClosed_supportedIn`, `isClosed_multiplierGraph_supported`, `isClosed_fourierMultiplierGraph` |
| `(20)`–`(21)`, `(24)` low-frequency Paley–Wiener port | `BandLimited`, `integrable_pow_smul_of_bandLimited`, `norm_iteratedDeriv_fourier_le_of_bandLimited`, `highPass_add_lowPass` |
| `(22)`–`(23)` exact cutoff graph identity | `cutoff_graph_identity` |
| `(10)`, `(27)` interior form of the defect | `cutoff_defect_eq` |
| `(25)` bounded part of the commutator | `norm_commutator_le` (`≤ 2‖q_a‖∞`) |
| `(26)` subordination of the logarithmic symbol | `integral_Ioi_resolvent_diff`, `logSymbol_eq_integral`, `integral_Ioi_exp_neg_mul_right`, `integral_Ioi_resolventKernel` |
| `(26)` resolvent kernel ↔ resolvent symbol | `integral_Ioi_cexp_neg`, `fourierIntegral_exp_neg_mul_abs`, `integrable_resolventKernel`, `fourierIntegral_resolventKernel`, `fourier_resolventConvolution` |
| `(26)` the cutoff commutator kernel | `kernel_cutoff_commutator`, `logSymbolKernel`, `logSymbolKernel_cross_le` |
| `(26)` Carleman boundedness | `integrableOn_carlemanSchurWeight`, `lintegral_carlemanSchurWeight`, `lintegral_carleman_sq_le`, `lintegral_carlemanBlock_sq_le`, `lintegral_sq_logSymbolCross_le` |
| `(11)` prime translations are homogeneous self-adjoint | `norm_suzukiFinitePrimeAdjacency_le`, `suzukiGammaPositivePrimeAdjacency_isSelfAdjoint` |
| `(12)` the isolated weighted target | `WeightedCarlemanTarget`, `weightedCarlemanTarget_mono` |

## What the card actually closes

The graph relation is closed with no bound whatever on the symbol: `L²` convergence forces
convergence in measure, an almost everywhere convergent subsequence carries the defining identity
to the limit, and the support condition is a closed subspace — so the graph domain of the growing
logarithmic symbol is complete, and transporting it through the `L²` Fourier isometry keeps it
closed.  The coefficient state is the Neumann parametrix of the valuation-Wiener element above the
explicit margin `log⟨ξ⟩ - C_a - M_a`, whose `ℓ¹` norm bound and character evaluation are already
Lean objects; multiplying by the element recovers the carrier equation and the evaluation identity.

The cutoff identity is exact algebra for any bounded operator and any idempotent cutoff, and the
interior projection of the defect is the exterior transport `-P a_a(D)(1-P)`.  Its bounded part
costs at most `2‖q_a‖∞`.  Its logarithmic part is now identified rather than asserted.  The
logarithmic symbol is the resolvent superposition
`log(1+z) = ∫₀^∞ [(1+λ)⁻¹ - (1+λ+z)⁻¹] dλ`, each resolvent symbol `(μ²+4π²ξ²)⁻¹` is the Fourier
transform of the two-sided exponential kernel `e^{-μ|x|}/(2μ)` — proved from the complex ray
integral `∫₀^∞ e^{-cx}dx = 1/c` for `Re c > 0` — and convolution by that kernel therefore has
exactly that symbol.  Superposing the kernels in the same parameter, by the substitution
`λ = μ²-1`, gives `∫₀^∞ e^{-√(1+λ)r}/(2√(1+λ)) dλ = e^{-r}/r`: the logarithmic kernel is
`e^{-|x-y|}/(2|x-y|)`.  Cutting any kernel operator to an interval leaves precisely the kernel
weighted by `1_I(y) - 1_I(x)`, so the defect lives on the two crossing regions; writing the
crossing at an endpoint as `x = a-s`, `y = a+t` gives `|x-y| = s+t` and the cross kernel
`e^{-(s+t)}/(2(s+t)) ≤ 1/(2(s+t))`.  Schur's test with the weight `t^{-1/2}` then bounds the cross
block on `L²`, so the cutoff defect is a bounded Carleman cross block, exactly as `(26)` claims.

Nothing else is left unclassified: the low-frequency port is bandlimited, so every derivative of
its profile is bounded by `(2πR)ⁿ` times the band mass, and the two ports reconstruct the mode; the
polar remainder is the `O(e^{-L})` Gamma-subcritical port of the polar-remainder card; the prime
translations are the bounded self-adjoint finite adjacency.  What is left is the weighted target
`(12)`, isolated as a predicate and shown to be a strip condition: it descends to every smaller
weight on the ray.

## Hypotheses

Object data only: measurability, integrability of the specific integrands, `0 < μ` for the
resolvent parameter, `Re c > 0` for the ray integral, the aperture margin `C_a + M_a < L₀` for the
Neumann inverse, and idempotence plus a contraction bound for the cutoff.  No RH, no spectral
premise, no `sorry`, `axiom`, `opaque`, or `unsafe`.  Every theorem named above audits to
`[propext, Classical.choice, Quot.sound]`.

## Open boundary

The card's open gates stay open: `(12)` itself, trace-zero entry into `H¹₀`, raw Evans injectivity,
and RH.  One link inside the closed part is formalized at the level the card argues it rather than
as a single operator equation: the passage from the resolvent family to `log⟨D⟩` is certified as
the scalar symbol superposition together with the matching kernel superposition and the
resolvent-by-resolvent operator identification, not as an operator-valued Bochner integral —
that last exchange needs an `L²` Fourier-multiplier calculus for unbounded symbols, which the tree
does not yet carry.  Every statement listed above is unconditional as stated.
