# Forced Gamma transport: trace zero is exact upper-strip gluing, formalized

- **ID:** `suzuki-forced-gamma-upper-strip-gluing`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-forced-gamma-upper-strip-gluing.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiForcedStripParticular.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiForcedStripHolomorphy.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiForcedStripGluing.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiForcedStripLineBridge.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiForcedStripDatum.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiStripTransportUniform.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaForcedStripHardy.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripCarrierTwoSided.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaVerticalRatioUniform.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaRatioStripUniform.lean`
  - `formal/GaloisForLFunctions/RHTower/StripFourierTranslation.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripGluing.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiHalfLogScatteringKernel.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripSquareIntegrable.lean`
  - `formal/GaloisForLFunctions/HTGeometry/WeightedHardyInequality.lean`
  - `formal/GaloisForLFunctions/HTGeometry/SegmentParameterHolomorphy.lean`
  - `formal/GaloisForLFunctions/HTGeometry/SegmentParameterPrimitive.lean`
  - `formal/GaloisForLFunctions/HTGeometry/CompactTestTransformOrder.lean`
  - `formal/GaloisForLFunctions/HTGeometry/CompactTestTransform.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PowerTailIntegral.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExpSelfAdjointNormBound.lean`

## Formal content

| Card | Lean |
|---|---|
| `(3)` the transport `Q` and the propagator `H = z^{-1/2}Q` | `stripTransport`, `stripPropagator`, `stripPropagatorInv`, `stripPropagatorInv_stripPropagator` |
| `(7)` the particular solution along the segment | `forcedParticular`, `forcedSegmentIntegral`, `forcedParticular_eq_propagator_apply` |
| Theorem 1: `p` is single-valued — every half power cancels | `forcedParticular_eq`, `forcedParticular_eq_total`, `integral_stripPropagatorInv_segment` |
| Theorem 1, `(8)`: `p(z) = O(z)` | `norm_forcedParticular_le` |
| Theorem 1: `p` is holomorphic through the frequency origin | `differentiableOn_forcedParticular`, `differentiableOn_forcedParticular_imStrip` |
| Theorem 1, `(9)`: the channel vectors are unique | `forcedChannel_pos_unique`, `forcedChannel_neg_unique` |
| Theorem 1, `(10)`: the half-log scattering coefficient | `halfLogScatter`, `halfLogScatter_eq_zero_iff` |
| Theorem 2, `(11)`: `β = 0 ⟺ c₋ = -ic₊ ⟺ forced gluing` | `forcedGlue_iff_halfLogScatter_eq_zero`, `forcedGlue_of_channel` |
| Theorem 2, `(12)`: the propagator and its inverse on a shifted line | `exists_stripPropagator_line_bounds`, `norm_stripPropagator_shift_le`, `norm_stripPropagatorInv_shift_le` |
| Theorem 2: polynomial growth on every closed substrip | `exists_bound_stripTransport_substrip`, `exists_bound_stripTransportInv_substrip`, `exists_bound_forcedParticular_substrip`, `exists_bound_norm_stripSolution` |
| Theorem 3, `(14) ⟹ (15)`: `f(·+iσ) ∈ L²(ℝ;X)` | `forcedStripLine`, `lintegral_enorm_sq_forcedStripLine_lt_top` |
| the segment and line representations agree | `hasDerivAt_forcedSegmentIntegral`, `forcedSegmentIntegral_line`, `stripSolution_add_forcedParticular_eq_forcedStripLine` |
| Theorem 3, `(16)`: `e^{2πσL}F(L) ∈ L²(ℝ;X)` for every `0 < σ < 1` | `stripDatum_forcedStripSolution`, `exists_memLp_exp_smul_forcedStripFourier` |

## What the card actually closes

Three theorems, all unconditional.

**Theorem 1** is the statement that the forcing contributes no regular-singular term.  The
particular solution is the contour integral of `H^{-1}b` along the segment from the frequency
origin, and both `H(z) = z^{-1/2}Q(z)` and `H(w)^{-1} = w^{1/2}Q(w)^{-1}` carry the principal half
power.  Parameterising the segment by `w = zs`, `s ∈ [0,1]`, the inner half power splits as
`(zs)^{1/2} = z^{1/2}s^{1/2}` — the second factor is a nonnegative real, so the principal branch is
multiplicative there — and one factor `z^{1/2}` comes out of the integral.  It cancels the outer
`z^{-1/2}` exactly:

```text
p(z) = z · Q(z) ∫₀¹ s^{1/2} Q(zs)^{-1} b(zs) ds.
```

The right side has no half power at all.  Hence `p` is single-valued across the frequency origin,
vanishes to first order there, and — since the branch-free kernel is holomorphic by differentiation
under the integral sign on a star-shaped domain — extends holomorphically through the origin.  The
channel vectors of the two boundary representations are then unique, because the transport is
injective wherever the branch does not vanish, and the half-log coefficient of the forced solution
is the homogeneous one.

**Theorem 2** is the forced gluing law.  Because the same particular solution appears in both
channels, the forced criterion collapses onto the homogeneous one: zero endpoint trace, `c₋ = -ic₊`,
and gluing into a single holomorphic strip solution are equivalent.  The growth statement is
quantitative: the exact Gamma quotient bounds the transport on every closed substrip and its inverse
by a linear factor, so the particular solution grows at most polynomially there.

**Theorem 3** is the weighted source criterion.  Variation of constants rebased at the origin of the
shifted line, together with `‖H(x+iσ)‖ ≤ K(1+|x|)^{-1/2-σ}` and `‖H(x+iσ)^{-1}‖ ≤ A(1+|x|)^{1/2+σ}`,
makes the bracket uniformly bounded under `(14)`; the remaining propagator power has square exponent
`1+2σ > 1`, which gives `(15)`.  For `(16)` the segment representation is identified with the
horizontal one by the primitive property

```text
d/dz ∫_{[0,z]} H(w)^{-1}b(w) dw = H(z)^{-1}b(z),
```

itself the parameter fundamental theorem `(3/2)Φ(z) + zΦ'(z) = G(z)` for the half-power weight.  The
glued forced solution is then a strip datum — holomorphic, polynomially bounded on closed substrips,
square integrable on interior lines — and the vector-valued Paley–Wiener translation returns one
frequency profile `F` with `e^{2πσL}F ∈ L²(ℝ;X)` for every `0 < σ < 1`.

## The analytic input that had to be built

The Beta-integral method bounds a vertical Gamma ratio only from above, because it needs a positive
real part in the second Beta argument.  The inverse Gamma transport needs the opposite bound.  It is
obtained by keeping the error of the fundamental-theorem identity explicit:

```text
| log‖Γ(a+iτ)‖ − log‖Γ((a+δ)+iτ)‖ + δ log τ |  ≤  δ (1/τ² + π/(2τ) + (a+δ)²/(2τ²)),
```

whose dependence on the parameters is only through `a+δ`.  Exponentiating gives a two-sided bound
`c τ^{-δ} ≤ ‖Γ(a+iτ)‖/‖Γ((a+δ)+iτ)‖ ≤ C τ^{-δ}` for `τ ≥ 1`, uniform on every parameter box, and
hence the substrip-uniform Gamma quotient bound `c(1+|x|)^{-2σ₁} ≤ ‖Γ(1-τ+ix)‖/‖Γ(1+τ+ix)‖ ≤ C`.

The Paley–Wiener package also had to absorb polynomial growth rather than boundedness, which needs
the entire test transform to decay faster than every power; iterated integration by parts supplies
`‖Ψ(z)‖ ≤ C_k(1+‖z‖)^{-k}` on every horizontal strip.

## Hypotheses

Object data only: `X` a complex Hilbert space, `T` bounded and self-adjoint, `E` a holomorphic
nonvanishing branch of the square root of the Gamma quotient on the strip, `b` holomorphic on the
strip with polynomial growth on every closed substrip, and — for Theorem 3 — the literal weighted
source bound `(14)`.  These are the card's own hypotheses.  No RH, no spectral premise, no `sorry`,
`axiom`, `opaque`, or `unsafe`.  Every theorem named above audits to
`[propext, Classical.choice, Quot.sound]`.

## Open boundary

What stays open is what the card itself declares open: construction of the carrier-valued cutoff
forcing and the exact intertwiner on the completed source domain, corona no-return, raw Evans
injectivity, and RH.  The forced Gamma-strip analytic-continuation gate is closed.
