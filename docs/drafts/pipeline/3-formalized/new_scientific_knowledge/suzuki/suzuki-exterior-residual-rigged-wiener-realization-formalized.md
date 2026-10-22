# The completed exterior residual has an exact rigged Wiener carrier, formalized

- **ID:** `suzuki-exterior-residual-rigged-wiener-realization`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-exterior-residual-rigged-wiener-realization.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/LogKernelExteriorL2.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiExteriorSymbolBounds.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiExteriorWienerAlphabet.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiExteriorHardyAmplitudes.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiValuationEvaluationAlgebra.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiExteriorRiggedRealization.lean`
  - Wiener stack (pre-existing): `HTGeometry/DiscreteL1Convolution.lean`,
    `RHTower/Suzuki/SuzukiWienerNeumannMajorant.lean`, `RHTower/Suzuki/SuzukiWienerMixedNormCarrier.lean`,
    `RHTower/Suzuki/SuzukiWienerNuclearBoundaryCarrier.lean`
  - alphabet (pre-existing): `RHTower/Suzuki/SuzukiRootPortObservationGram.lean`,
    `RHTower/Suzuki/SuzukiPrimeValuationSeam.lean`
  - archimedean input (pre-existing): `HTGeometry/DigammaVerticalUniformLog.lean`,
    `HTGeometry/GammaShiftExpIntegral.lean`, `HTGeometry/ReflectedDigammaAnomaly.lean`

## Formal content

| Card | Lean |
|---|---|
| `(6)`–`(8)` exterior residual in `L²` | `integral_inv_sub_kernel`, `abs_integral_kernel_le`, `integrableOn_log_collar_sq`, `integrableOn_log_tail_sq` |
| `(9)` two-port splitting | `suzukiExteriorLeft`, `suzukiExteriorRight`, `suzukiExterior_add_eq` |
| `(11)` `L²` Hardy amplitudes | `memLp_suzukiLeftPortAtOrigin`, `memLp_suzukiRightPortAtOrigin`, `norm_fourier_suzukiLeftPortAtOrigin`, `norm_fourier_suzukiRightPortAtOrigin` (Plancherel) |
| `(10)` opposite boundary phases | `fourierIntegral_suzukiLeftPortAtOrigin`, `fourierIntegral_suzukiRightPortAtOrigin` |
| `(13)` the atom family `t_a` | `suzukiWienerAtoms`, `suzukiOrientedStep`, `suzukiOrientedStep_injOn` |
| `(18)` exact Wiener mass | `discreteMass_enorm_suzukiWienerAtoms` = `ofReal (2 ∑ (log p) p^{-j/2})` |
| `(14)`, `(17)` bounded remainder | `suzukiArchRemainder`, `exists_bound_suzukiArchRemainder`, `suzukiTruncatedPolarKernel`, `exists_bound_suzukiSymbolRemainder` |
| `(12)`, `(15)`, `(16)` `κ = 1` | `suzukiWienerEval_atoms` (evaluation = Suzuki's cosine sum), `suzukiWienerEval_highPassElement` |
| `(19)` threshold | `exists_suzukiExteriorThreshold` |
| `(20)`–`(21)` Neumann inverse | `suzukiHighPassElement`, `suzukiExteriorInverse`, `discreteConv_suzukiHighPass_inverse` |
| `(22)` margin bound | `tsum_enorm_suzukiExteriorInverse_le` (`≤ (L₀ − C_a − M_a)⁻¹`) |
| `(2)`, `(23)`, `(24)` rigged carrier | Wiener stack: `tsum_eLpNorm_wienerTwoRoot_le`, `suzukiWienerTwoRootCarrier`, `summable_tsum_norm_clm_comp` |
| `(25)` absolute evaluation | `suzukiWienerEval_discreteConv`, `suzukiWienerEval_inverse_mul`, `suzukiWienerEval_carrier` |

## What the card actually closes

The archimedean normalization is now a theorem, not a source check: `Re ψ(1/4 + iξ/2) − log⟨ξ⟩` is
bounded on the whole frequency line — the vertical digamma asymptotic handles `|ξ| ≥ 2`, the
abscissa `1/4` keeps `ψ` regular near the origin so continuity and compactness handle the rest, and
conjugation symmetry transports both halves to negative frequency.  Adding the Fourier transform of
the compactly truncated polar kernel, which is bounded by its `L¹` norm, gives `‖q_a‖_∞ ≤ C_a`.
The prime block is one finitely supported element of the valuation Wiener algebra whose `ℓ¹` mass
is *exactly* `2 ∑_{p^j ≤ e^{2a}} (log p) p^{-j/2}`: the two oriented atoms of a visible step are
distinct because the seam coordinate of a visible step is strictly positive, and distinct steps
have distinct valuation labels.

That makes the threshold `(19)` explicit and unconditional, and above it the Neumann series is an
actual two-sided convolution inverse with `ℓ¹` norm at most `(L₀ − C_a − M_a)⁻¹`.  The evaluation
step is where the earlier version was wrong, and it is now proved rather than assumed: unit-phase
evaluation is multiplicative whenever one factor is `ℓ¹` and the other finitely supported — exactly
Suzuki's configuration — so `Ev(h⁻¹) · p_a = Ev(δ₀) = 1`, and the carrier `c = h⁻¹ ⋆ s` satisfies
`Ev(c) · p_a = Ev(s)`.  No `ℓ²`-to-scalar map occurs anywhere in the chain.

## Hypotheses

Object data only: the aperture `a`, the threshold data `0 ≤ C_a`, `C_a + M_a < L₀ ≤ L(ξ)`
(itself produced unconditionally by `exists_suzukiExteriorThreshold`), `MemLp b 2` and the aperture
support condition for the source, and finite support of the two-root source family.  No RH, no
spectral premise, no `sorry`, `axiom`, `opaque`, or `unsafe`.  Every theorem named above audits to
`[propext, Classical.choice, Quot.sound]`.

## Open boundary

The card's remaining gates are research and stay open: the global-to-support-pruned logarithmic
carrier intertwiner, realizing the exact cutoff equation in the middle `ℓ²` space, applying the
Gamma wall and weighted-tail coercivity, raw Evans injectivity, and RH.  The low-frequency zeros of
`p_a` are deliberately not divided out; they remain the two-port matching problem.
