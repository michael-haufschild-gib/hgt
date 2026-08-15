# Flat Suzuki primitive flux is exponentially small without a prime-group bound, formalized

- **ID:** `suzuki-flat-primitive-flux-volterra-liouville`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PAPER-PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-flat-primitive-flux-volterra-liouville.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/SuzukiCoordinateCutoffPrimitiveFlux.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiPrimitiveFluxNonnormalGraphReduction.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiFlatFluxChargeAutomatic.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiFlatPrimitiveFluxAssembly.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaWallCutoffCommutator.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaCommutatorConvolution.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaCommutatorBlock.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiFlatFluxBlockValue.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiFlatFluxBlockTail.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiFlatFluxCoercive.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiFlatFluxEnvelopeBridge.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiFlatFluxWeightedL2.lean`
  - `formal/GaloisForLFunctions/HTGeometry/FlatVolterraDecay.lean`
  - `formal/GaloisForLFunctions/HTGeometry/CoerciveResolutionBound.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExpEnvelopeAlgebra.lean`
  - `formal/GaloisForLFunctions/HTGeometry/YoungConvolutionL2.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)`, `(2)` the augmented flux system, `A = 2L I + R − B` | `twoLPlus`, `primitiveFluxSystem_pointwise`, `primitiveFluxSystem_exponential_pointwise` |
| `(3)` all-orders flatness in unit-block `L²` | `SuperpolynomiallyFlat` |
| `(6)` the Gamma cutoff commutator | `gammaWallCommutator`, `gammaWallCommutator_integrand` |
| `(7)` the localized block estimate | `enorm_gammaWallCommutator_le_lintegral`, `lintegral_gammaCommKernel`, `enorm_gammaWallCommutator_le_blockSum`, `enorm_gammaWallCommutator_le_envelope` |
| `(7)` unlocalized: `‖[R,χ]F‖₂ ≤ 8Λ‖F‖₂` | `lintegral_enorm_sq_gammaWallCommutator_le` |
| `(8)` the block norms and their exponential envelope | `blockNorm`, `blockNormSq`, `expEnvelopeZ`, `expEnvelope_le_of_exp_decay` |
| `(9)` cutting leaves only the Gamma commutator | `primitiveFlux_eq_cut_flux`, `primitiveFlux_cut_of_commuting` |
| `(10)` the coercive lower bound of the terminal block | `lintegral_position_ge`, `lintegral_position_block_ge`, `reInner_sub_ge`, `norm_le_of_reInner_ge` |
| `(11)` the localized value estimate | `blockValue_absorb`, `blockValue_of_coercive`, `expEnvelopeZ_absorb`, `expEnvelopeZ_weighted_le` |
| `(11a)` the terminal charge is automatically zero | `tendsto_natCast_mul_of_superpolynomiallyFlat`, `flat_flux_terminal_charge_automatic` |
| `(12)` the backward flux integral | `terminal_flux_eq_neg_integral`, `enorm_terminal_flux_le` |
| `(13)` the backward flux tail | `lintegral_Ioi_le_blockTail`, `blockNorm_le_of_bound`, `blockNorm_flux_le_blockTail`, `blockTail_le` |
| `(14)` the Volterra inequality for the flux | `volterraTail`, `volterraTail_step`, `flat_flux_exponential_decay` |
| `(15)`–`(20)` the flat Volterra lemma | `flat_volterra_decay`, `flat_volterra_decay_of_tail` |
| `(14) ⟹ (21)` the coupled decay | `envelopeSeq`, `envelopeSeq_value_le`, `envelopeSeq_flux_le`, `envelopeSeq_exponential_decay` |
| `(21)` exponentially weighted value and flux | `lintegral_weighted_sq_le_blockSum`, `weighted_blockTerm_le`, `tsum_int_eq_tsum_nat_of_support`, `tsum_geometric_ofReal_ne_top`, `lintegral_weighted_sq_ne_top`, `flatFlux_weighted_mass_ne_top` |
| `(22)`, `(4)` the weighted flux derivative | `ennreal_add_sq_le`, `lintegral_weighted_sq_sub_ne_top` |
| `(23)`, `(25)` the exact cutoff source | `primitiveCutoffFlux_pointwise`, `primitiveCutoffFlux_with_zeroOrder_pointwise`, `linearCommutator_sub` |

## What the card actually closes

The theorem is that an all-orders-flat solution of the augmented primitive-flux system enters every
exponential weight below the source rate, for an **arbitrary bounded nonnormal** prime adjacency —
no polynomial bound on `exp(−ixB)`, no adjoint, no normality.  The only operator property used is
the coercive lower bound of the terminal Gamma block.

**The commutator is a convolution.**  Each cutoff difference across a gap `s` cancels the
singularity of the Gamma jump kernel at the origin — the Lipschitz factor beats `1/s` — and past
the origin inherits its exponential decay.  So the commutator integrand is dominated by `4Λe^{−s}`
uniformly in the base point, and reflecting the negative half-line turns the pointwise bound into a
genuine two-sided convolution against a kernel of total mass `8Λ`.  Young's inequality then gives
`‖[R,χ]F‖₂ ≤ 8Λ‖F‖₂`, and cutting the convolution into unit blocks gives the localized form `(7)`:
on a pair of blocks the kernel is almost constant because `|L−t| ≥ |n−m|−1`, which costs exactly one
factor `e`, and on a block of length one Cauchy–Schwarz turns the `L¹` mass into the `L²` mass with
no constant at all.

**The envelope absorbs itself only at mixed rates.**  This is the one place where the obvious
argument fails.  Composing two envelopes of the *same* rate degrades it,
`E_μ ∘ E_μ ≤ S·E_{μ/2}`, because the diagonal is summed over — and a degraded rate cannot be
absorbed, since `E_{μ/2} ≥ E_μ`.  Composing *different* rates does not degrade: from

```text
ν|n−m| + μ|m−j| = ν(|n−m|+|m−j|) + (μ−ν)|m−j| ≥ ν|n−j| + (μ−ν)|m−j|
```

one gets `E_ν ∘ E_μ ≤ expRowMass(μ−ν)·E_ν` with the outer rate intact, and `expRowMass ρ` is finite
for `ρ > 0`.  Hence: if `f_m ≤ α_m + b(E_μ f)_m` with `b·expRowMass(μ−ν) ≤ 1/2`, then
`(E_ν f)_n ≤ 2(E_ν α)_n`.  The smallness of `b` is exactly what the growing terminal coefficient
`2(n−1) − ‖B‖` supplies, and the reciprocal of that coefficient is pulled out of the envelope up to
a linear weight — which likewise costs only a rate drop, since `(1+t)e^{−εt} ≤ 1/ε`.

**The flux is a backward tail.**  Superpolynomial flatness makes the terminal charge vanish
automatically, so the flux is the backward integral of its source; cutting the terminal ray into
unit blocks and using Cauchy–Schwarz on each turns that into a tail of block norms, and the
exponential off-block kernel of `D` turns it into `(13)`.

**The two estimates close.**  Substituting the value estimate into the flux estimate produces a
single backward Volterra inequality whose flat solutions decay at every rate below the source rate.
The extended-norm block sequences are transferred to real sequences by `toReal` — finiteness of the
envelopes is not an extra assumption, since an infinite envelope makes the `ℝ≥0∞` estimate vacuous
— and finally an exponential weight is almost constant on a unit block, so

```text
∫ e^{2δL}‖F(L)‖² dL ≤ Σ_{n∈ℤ} e^{2δ(n+1)}‖F‖²_{L²([n,n+1))},
```

a convergent geometric series once the blocks decay faster than `e^{−2δ''n}`.  That is `(21)`, and
`Y' = DF − H` with the same block decay gives `(22)`, hence `(4)`.

## Hypotheses

Object data only: a normed space `X` for the profiles (a complex Hilbert space where the quadratic
form is used), the operators `R`, `B`, `D`, `Z`, `M` as linear endomorphisms, the profiles
`F, Y, G, H`, the rates, and — where an integral is taken — measurability of the pointwise norm,
which is part of what "`F ∈ L²`" means and not a mathematical premise.  The card's own hypotheses
are the exponential source bounds, the all-orders flatness `(3)`, the terminal-ray support, the
exponential off-block kernel of `D`, and the commutation of `B` with the scalar cutoff.  No RH, no
normality of `B`, no group bound, no `sorry`, `axiom`, `opaque` or `unsafe`.  Every theorem named
above audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

What stays open is what the card itself declares open, and both are research rather than missing
Lean: the passage from this weighted value/flux statement to `H¹₀` for completed trace-zero modes,
and raw Evans injectivity.  Section 7 of the card also isolates the narrower
`SUZUKI-ROOT-PRIMITIVE-DERIVATIVE-PROPAGATION` for the finite-range prime term `[B,M]F`.  The
value/flux level of the Hatano–Nelson obstruction is bypassed.
