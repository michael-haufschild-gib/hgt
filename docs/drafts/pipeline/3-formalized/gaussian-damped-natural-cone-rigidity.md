# Gaussian damping makes the natural two-prime cone rigid

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** SC2; a replacement probe for the unattained-width obstruction.

For actual zeta zeros, write `z_ρ=ρ−1/2` and let `w_ρ` be the
multiplicity-weighted eighth-power spline coefficient. Fix `τ>0` and set

`K_τ(t)=Σ_ρ w_ρ exp(τ z_ρ²) exp(t z_ρ)`.

For distinct primes, `a=log p`, `b=log q`, define

`C_τ(m,n)=K_τ(ma+nb)−K_τ(ma)−K_τ(nb)+K_τ(0)`.

For every `σ≥0`,

`zetaZeroWidth≤σ  ↔  ∃M, ∀m,n∈ℕ, |C_τ(m,n)|≤M exp(σ(ma+nb))`.

In particular, bounded coupling on this natural cone is equivalent to RH.
No simplicity, uniform zero spacing, or attained maximal width is assumed.

This changes the probe by Gaussian damping. It does not establish transfer
of bounded coupling from the original spline kernel, and does not deform
zeros through the de Bruijn–Newman flow. Original SC2 remains open.

## Proof

Four forward differences of the coupling give the moments of

`d_ρ=w_ρ exp(τ z_ρ²)(exp(a z_ρ)−1)(exp(b z_ρ)−1)`.

Removing the allowed growth rate uses shifted clocks
`u_ρ=exp(a(z_ρ−σ))`, `v_ρ=exp(b(z_ρ−σ))`. The coupling hypothesis bounds
all their nonnegative mixed moments by one constant.

Fix a zero with `δ₀=Re z_ρ₀>σ`. Its residue `d_ρ₀` is nonzero. Local
finiteness gives a fixed positive distance from every other zero. Baker
separation then gives

`|u_ρ−u_ρ₀|+|v_ρ−v_ρ₀| ≥ c/(2+|Im ρ−Im ρ₀|)^J`.

The actual zero-count estimate bounds the number of distinct zeros below
height `N⁴` by `CN⁵`. For each such zero other than `ρ₀`, choose the larger
clock gap and use `(U−u_ρ)/(u_ρ₀−u_ρ)` or its `V` analogue. Each affine
factor vanishes at its selected zero and equals one at `ρ₀`. Its coefficient
norm, and its values throughout the zero strip, are at most a fixed
polynomial in `N`, hence at most `exp(AN)`.

Their product `P_N` kills the entire finite head except `ρ₀`. Both its
coefficient norm and its global value bound are at most `exp(KN⁶)`.
Induction on factors bounds its moments using only the two forward clock
shifts. No inverse clock powers occur.

Multiply by `u^(N⁷)`. The selected atom has modulus
`|d_ρ₀| exp(gN⁷)`, where `g=a(δ₀−σ)>0`. The full sum is bounded by
`M exp(KN⁶)`. The remaining zeros have ordinate magnitude greater than
`N⁴`; their Gaussian factor is at most `exp(τ/4−τN⁸)`.
Absolute summability of the undamped mixed residues bounds the tail.
Dividing by the selected atom's growth gives

`|d_ρ₀| ≤ M exp(KN⁶−gN⁷) + L exp(KN⁶+(a/2−g)N⁷−τN⁸)`.

Both terms tend to zero, contradicting `d_ρ₀≠0`. Reflection gives the
width bound. Conversely, a width bound controls both clock differences
by their allowed exponential rates; absolute summation gives the coupling
bound directly.

## Lean

Main declarations in `ArithmeticCouplingTheory/ConeBoundary/GaussianConeKernel.lean`:

- `zetaZeroWidth_le_iff_gaussian_coneCoupling_rate`.
- `riemannHypothesis_iff_bounded_gaussian_coneCoupling`.
- `gaussianConeCoupling_eq_kernel_difference` identifies the spectral series
  with the exact four-term scalar-kernel difference.

`GaussianConeRigidity` proves the moment criterion; `GaussianFiniteFilters`
constructs the isolating products. `FiniteClockProducts`,
`StripClockSeparation`, `GaussianZeroGeometry`, `GaussianResidues`, and
`GaussianFilterCosts` supply the finite interpolation and analytic bounds.

Every new module passes direct `lake --old env lean` checks. The main
transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`; the arithmetic-coupling umbrella imports every module.
External priority has not been checked.
