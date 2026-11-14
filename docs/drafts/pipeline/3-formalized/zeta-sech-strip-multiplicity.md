# A positive strip test bounds zeta multiplicity

- **ID:** zeta-sech-strip-multiplicity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Every sufficiently high critical zeta or xi zero has multiplicity at most `(3/(8π)+ε)log|γ|`, for every `ε>0`.

## Stronger uniform statements

Write `m(ρ)=(analyticOrderAt riemannZeta ρ).toNat`.
For `3/8<a<1/2` and `ε>0`, there is `T₀≥2` such that every finite set `F`
of nontrivial zeros at common height `T`, with `|T|≥T₀`, satisfies

`Σ_{ρ∈F} m(ρ) sec(π(Reρ−1/2)/(2a)) ≤ (a/π+ε)log|T|`.

For every `ε>0`, all sufficiently high nontrivial zeros satisfy the uniform envelope

`m(β+iγ) ≤ [(3/(8π))cos((4π/3)(β−1/2))+ε]log|γ|`.

Consequently, multiplicity is `o(log|γ|)` on either outer line `β=1/8` or `β=7/8`.
The critical-line bound retains a positive coefficient; it does not settle B47.

## Proof

The corpus quasi-RH theorem puts every nontrivial zero in `1/8≤Reρ≤7/8`.
For fixed `7/8<σ<1`, three-circles interpolation for `ζ′/ζ` between a bounded
Dirichlet-series disk and an `O(log|t|)` disk in the zero-free half-plane gives
`O((log|t|)^θ)` with `θ<1`. Thus `ζ′/ζ(σ+it)=o(log|t|)` at both signs of height.
For `G(s)=(s−1)ζ(s)`, reflection and Stirling give `G′/G=-log|t|+o(log|t|)`
on fixed lines `0<σ<1/8`; the right boundary has zero logarithmic coefficient.

Choose `3/8<b<a`. The kernel

`K(s)=1/cos((π/(2a))(s−(1/2+iT)))`

has positive real part throughout the zero strip, secant weight at height `T`,
exponential vertical decay, and real vertical mass `2a` on both contour lines
`Re s=1/2±b`. Apply the finite-rectangle residue theorem to `K G′/G`, retaining
only the positive contributions from `F`. Actual zero-free horizontal edges
with polylogarithmic bounds make their integrals vanish. Absolute integrability
passes the vertical edges to full integrals. Logarithmic convolution then gives
boundary coefficient `a/π`, uniformly as `|T|→∞`.

The singleton case gives the cosine bound. A uniform Lipschitz estimate in `a`
passes to width `3/8`, yielding the stated envelope, including its outer endpoints.

## Lean declarations

Namespace `GaloisForLFunctions.ConjugateDiagonalGeometry`:

- `TheLogarithmicDerivativeIsSmallOutsideTheZeroStrip.lean`:
  `exists_logDeriv_zeta_log_power_bound`, `exists_logDeriv_zeta_le_epsilon_log`.
- `TheResidueUnitLogDerivativeHasItsBoundaryAsymptotics.lean`:
  `exists_logDeriv_residueUnit_right_le_epsilon_log`,
  `exists_logDeriv_residueUnit_left_add_log_le_epsilon_log`.
- `ResidueUnitBoundaryConvolution.lean`:
  `tendsto_sechResidueUnitBoundary_log_normalized`.

Namespace `GaloisForLFunctions.SquareRootThreshold`:

- `SechBoundaryMultiplicity.lean`: `sum_fibre_multiplicity_mul_sech_le_boundary`,
  `exists_fibre_sech_multiplicity_bound`, `exists_critical_zeta_multiplicity_bound`,
  `exists_critical_xi_multiplicity_bound`.
- `SechMultiplicityEnvelope.lean`: `exists_zero_multiplicity_cosine_envelope`,
  `exists_outer_boundary_multiplicity_le_epsilon_log`.

Supporting modules: `SechStripKernel`, `SechRectangleMultiplicity`,
`SechHorizontalExhaustion`, `LogarithmicConvolution`,
`LogarithmicBoundaryNormalization`.

All named main results pass Lean. Transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
