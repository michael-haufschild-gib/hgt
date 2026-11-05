# Real-weight camera and local count transfer

- **ID:** real-weight-camera-and-local-count-transfer
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); final Lean verification pending.
- **Source:** review-0511, A40.

## Statements

The local moment camera accepts arbitrary complex coefficients `c(z)` with
summable absolute Lorentzian mass `Σ |c(z)|/(1+|γ_z|²)`. One pair of
windows, chosen from the carrier geometry, reads every such weighting.
Its local Taylor error uses absolute cluster mass. On the actual ζ carrier,
`zeta_weighted_discMoment_readout_explicit` retains aperture `λL_T`, `λ>1/2`,
error `Σ_cluster |c(z)| r^(j+1) T^(M+κ_λ) + exp(−K log³(T/2π))`, and the
explicit height `zetaWeightedMomentCameraHeight`. The cluster is isolated
at distance `T^(−M)` and has radius at most `T^(−(M+κ_λ+1))`.

For every fixed aperture `a>0` and `θ>1`, there are `A≥0` and `T₀≥40`,
independent of the mimic, with the following property. Let `w(z)≥0` be
supported on `Re z=1/2`, have summable absolute Lorentzian mass, and give
exactly the ζ diagonal image for every aperture-`a` window. For `T≥T₀`,
`x≤y`, and any finite set `s` with `|Im z−T|≤T/2` and `x≤Im z≤y`,

`Σ_(z∈s) w(z) ≤ θ/(2π) log(T/2π)(y−x) + A log(T/2π)`.

This transfers weighted mass. It does not bound support cardinality:
for every aperture and every `N`, a positive on-line weighting with finite
absolute Lorentzian mass has `N` distinct atoms in `(0,1]`, all weights
below one, yet every window image is the same flat form `∫f·conj(g)`.
This example concerns a flat image, not a ζ-specific mimic.

## Proof

The isolating pair depends only on the geometric carrier count. Its Taylor
estimate is linear in each coefficient; summing absolute values replaces
integer multiplicity by absolute cluster mass. The far-tail estimate already
holds for arbitrary coefficients with summable absolute Lorentzian mass.
The explicit carrier and tail budgets therefore give the same moment height.

For count transfer choose a smooth bump `b` supported in `[-ε,ε]`, and put
`F=b̂`, `K(t)=|F(t)|²`. Vertical integration, Cauchy–Schwarz and Young's
inequality give a common envelope

`E(t)=(1+ε)|F(t)|²+(1+1/ε)∫_(-1/2)^(1/2)|F′(t+iv)|²dv`.

It bounds both `|F(t+iv)|²` and the actual off-line point-image
`|F(t+iv)·conj(F(t−iv))|`. Plancherel gives

`∫E ≤ [1+ε+(ε+ε²)e^ε]∫K`.

The bracket tends to one as `ε→0`. For any `q>1`, choose `ε≤a` and
`R≥1` so that `Q=∫_(-R)^R K>0` and `∫E≤qQ`.
The function `Q⁻¹∫_(x−R)^(y+R)K(t−X)dX` majorizes `[x,y]`.
Integrating modulated admissible windows transfers this bound directly
through equality of images. An interval source-mass bound `D·length+C`
gives integrated envelope at most `[D(y−x+2R)+C]∫E`, by reflection
of the intervals and Fubini.

Use ζ zeros in `|Im z−T|≤3T/4` as the finite central source. Their
multiplicity mass satisfies the sharp local bound proved from the explicit
rectangle count. For `T≥8R` and `[x,y]⊆[T/2,3T/2]`, exterior source
zeros lie farther than `T/8` from every modulation point. Sixth-order
transform decay and ζ's Lorentzian mass below one bound their image by
`B=320 C_b²e^ε`, uniformly in the modulation point. The integrated error
is `B(y−x+2R)/Q`.

Set `θ_m=(1+θ)/2`, `θ_s=(1+θ_m)/2`, `q=θ_m/θ_s`, and
`δ=θ−θ_m`. Choose the kernel for this `q`. Requiring
`log(T/2π)≥max(1,2πB/(Qδ))` absorbs the tail into the density slack.
The result has density `θ/(2π)` and additive constant
`A=2Rθ/(2π)+q·zetaCameraCountConstant(θ_s)`. Clip arbitrary interval
endpoints to the target height band. All constants are independent of `w`.

Finally, the simple lattice `{1/2+πik/L}` with weight `1/(2L)` has
normalized form `∫f·conj(g)` whenever `L≥a`.
Taking `L=max(a,π(N+1))` puts its first `N` positive atoms in `(0,1]`.
The existing tempered lattice bound supplies absolute Lorentzian summability.

## Lean endpoints

Owner: `GaloisForLFunctions/ZeroConfigurationGeometry/RealWeights/`.

- `Readout`, `EffectiveReadout`, `ZetaReadout`: uniform arbitrary-coefficient moment cameras.
- `ZetaTransfer`: `zeta_positive_mimic_weighted_count`.
- `FlatLattice`: `exists_real_weighted_flat_image_with_many_atoms`.
- `StripEnvelope`, `StripFourier`, `KernelChoice`: near-unit-mass strip envelope.
- `PositiveImages`, `IntervalMajorant`, `IntervalCount`, `CountMajorant`,
  `CountTransfer`, `ImageEnvelope`, `ZetaMass`: convergence, majorization,
  convolution, localization, and the actual ζ multiplicity count.

Final source checks, transitive axiom audits, and umbrella wiring pending.
