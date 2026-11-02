# Gaussian damping and natural-cone rigidity

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** SC2; an actual-zeta criterion without attained maximal width.

For actual zeros, put `z_ρ=ρ−1/2`,
`w_ρ=mult(ρ)(sinh(z_ρ)/z_ρ)^8`, and, for fixed `τ>0`,

`K_τ(t)=Σ_ρ w_ρ exp(τ z_ρ²) exp(t z_ρ)`.

**Target:** For distinct primes `p,q`, bounded mixed coupling of `K_τ` on
`{m log p+n log q : m,n∈ℕ}` is equivalent to RH.
More generally, coupling growth at most `C exp(σ(m log p+n log q))`,
`σ≥0`, should be equivalent to `zetaZeroWidth≤σ`.

This changes the probe by Gaussian damping; it does not assume or prove that
bounded coupling of the original spline kernel transfers to this probe.
It is distinct from deforming the zeros through de Bruijn–Newman heat flow.

## Candidate proof

Mixed differences bound all moments of
`d_ρ=w_ρ exp(τ z_ρ²)(exp(a z_ρ)−1)(exp(b z_ρ)−1)`,
where `a=log p`, `b=log q`. Fix a zero `ρ₀` with `Re z_ρ₀>σ`.
Its coefficient is nonzero.

Write `u_ρ=exp(a z_ρ)`, `v_ρ=exp(b z_ρ)`. The proved averaged-clock
separation `ConeBoundary.exists_two_prime_clockDefect_lower`, applied to
either `z_ρ−z_ρ₀` or its negative, gives a polynomial lower bound for
`|u_ρ−u_ρ₀|+|v_ρ−v_ρ₀|`. The fixed-target isolating radius follows from
`finite_window`.

For each other zero with `|Im ρ|≤T`, choose the larger clock gap and
normalize its affine factor: `(U−u_ρ)/(u_ρ₀−u_ρ)` or its `V` analogue.
Each factor kills that zero and equals one at the target. Its coefficient
norm is at most `2(R+1)/δ` when the joint gap is at least `δ` and clock
moduli are at most `R`. Multiply these factors. The actual zero count is
`O(T log T)`, so both coefficient norm and uniform tail value cost at most
`exp(C T log²(2+T))`.

All clock values are uniformly bounded on the zero strip. Thus these
polynomials remain bounded by the same exponential cost on the entire tail;
they do not grow polynomially with the tail height. Moment bounds for their
products follow inductively from the two positive clock shifts.

Multiply `P_T` by `u^m`, with `m` of order `T^(7/4)`. The selected zero
contributes growth `exp(a(Re z_ρ₀−σ)m)`, which beats the interpolation cost.
The remaining tail is bounded by

`C exp(−τT²+O(m)+O(T log²(2+T)))`,

which tends to zero. This contradicts the moment bound. Reflection then
excludes both sides outside width `σ`. The converse follows directly from
absolute summability and `|exp(t z_ρ)|≤exp(σt)` for `t≥0`.
Take `T=N⁴`, `m=N⁷`. The elementary inequality `log N≤N` gives
`T log²(2+T)≤C N⁶`. After dividing by the selected atom's growth,
the two errors are bounded by

`M exp(C N⁶−a(Re z_ρ₀−σ)N⁷)` and
`L exp(C N⁶+(a/2−a(Re z_ρ₀−σ))N⁷−τN⁸)`.

Both tend to zero, contradicting its fixed nonzero coefficient.
This uses only polynomial comparisons `6<7<8`.

A direct bound avoids logarithmic asymptotics: `zeroCount_upper` and
`ncard_lowZeros_le` in `RHTower/ZetaZeroCountUpperBound.lean` give at most
`C N⁵` distinct zeros below `N⁴`, using `log(N⁴)=4 log N≤4N`.
Each normalized linear factor costs at most `C₀N^J≤exp(C₁N)`.
Multiplying at most `C N⁵` factors gives the required `exp(C₂N⁶)` bound.

## Unfinished audits

`clock_product_moment_bound` and `exists_affine_clock_separator` in
`ConeBoundary/FiniteClockProducts.lean` are formalized and pass direct
standard-axiom audits. They prove the positive-shift product bound and the
normalized affine interpolation cost above.
`exists_strip_joint_clock_lower` in `ConeBoundary/StripClockSeparation.lean`
proves polynomial joint-clock separation throughout a vertical strip, with
a direct standard-axiom audit.
`exists_zeta_fixed_target_radius` and `exists_zeta_fourth_cutoff_count` in
`ConeBoundary/GaussianZeroGeometry.lean` prove fixed-target isolation and
the `CN⁵` cutoff count, also with direct standard-axiom audits.
`GaussianResidues.lean` proves absolute convergence, preservation of every
nonzero right-of-line mixed residue, and the quadratic Gaussian tail bound,
with a direct standard-axiom audit. `GaussianFilterCosts.lean` proves the
sixth-power interpolation cost and the seventh/eighth-power decay comparison,
with the same audit result. `exists_actual_clock_filters` in
`GaussianFiniteFilters.lean` now constructs the finite isolating products,
with uniform value and moment costs `exp(KN⁶)` and a direct standard-axiom
audit. `GaussianConeRigidity.lean` proves the full shifted-moment width
criterion, with direct standard-axiom audits of the target/tail estimate and
`zetaZeroWidth_le_iff_bounded_gaussian_moments`. The scalar-kernel coupling
bridge remains unformalized.
Local search found `XiGaussianAnnihilator` and
`GaussianCentralGapFilterLightCone`: the former uses polynomials in squared
spectral points; the latter varies a Gaussian filter and its center.
Neither inspected statement proves this fixed-Gaussian natural-cone criterion.
External priority has not been checked. The bounded-local-density exact-spline
model is formalized; the Gaussian criterion remains unproved.
