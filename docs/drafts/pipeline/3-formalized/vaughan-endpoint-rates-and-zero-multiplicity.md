# Vaughan endpoint rates, simple zeros, and unavoidable oscillation

- **ID:** vaughan-endpoint-rates-and-zero-multiplicity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Verification:** All thirteen endpoint-oscillation and boundary-multiplicity targets passed final direct Lean checks and standard-axiom audits. Both modules are wired; owned scratch files are removed.
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** Attained positive Vaughan tail rates force simple zeros on their boundary line; the maximal possible tail and empty-leg energy scales cannot have little-o decay.

## Definitions

Let `F_ε(N)=Σ_(d>N) μ(d)d^(-1-ε)`, `ε>0`, and let `S_ε` be its nonnegative
power-rate set: `η∈S_ε` means `|F_ε(N)|≤C N^(-ε-η)` for some constant `C`,
all `N≥1`. Let `E_ε(N)` denote the centered square empty-leg energy divided by
`(N²)^(1-2ε)`. The proved quartic comparison is

`(Z²/2)[N^ε F_ε(N)]⁴≤E_ε(N)≤Z²[N^ε F_ε(N)]⁴`,

where `Z=ζ(1+ε)>0`.

## Attained rates constrain multiplicity [LEAN-VERIFIED]

For every positive `η∈S_ε`, every zero on `Re(s)=1-η` is simple.
In particular, attainment of tail exponent `1/2`, cutoff-energy exponent `2`,
or horizon-energy exponent `1` implies RH and simplicity of every nontrivial zero.
No endpoint attainment is asserted.

The inverse Abel estimate gives `|M(N)|≤C N^β`, with `β=1-η`.
The already proved exponent bound gives `Θ≤β`; thus `1/2≤β<1`.
For real `x≥1`, the identity `M(x)=M(floor x)` and monotonicity of `x^β`
give the same bound `|M(x)|≤C x^β`. The integer bound also gives
`M(N)=O((N+1)^(β+δ))` for every `δ>0`, including `N=0`.

Apply the read source theorem `natCast_order_le_of_mertens_oneSided` in
`RHTower/MertensFrontierOneSidedOmega.lean` with sign `1`, logarithmic degree
`a=0`, and additive constant zero. It bounds the analytic order on the whole
line `Re(s)=β` by one. At a zero in the open strip, the analytic order is finite
and positive, so it is exactly one. At `η=1/2`, `Θ≤1/2` gives RH; the quartic
comparison transfers the same conclusion from either energy endpoint.

The same source supplies a lower bound for the local nonzero factor:
if `ζ(s)=(s-ρ)g(s)` at a boundary zero, then
`1≤4C polylogConst(0) |ρ| |g(ρ)|`.
Thus endpoint attainment controls residues as well as multiplicity.

## The square-root endpoint cannot be little-o [LEAN-VERIFIED]

For each fixed `ε>0`, there is a constant `c_ε>0` such that, for arbitrarily
large integers `N`,

`|F_ε(N)|>c_ε N^(-ε-1/2)`.

Suppose instead `F_ε(N)=o(N^(-ε-1/2))`. Put
`A_ε=(1+ε)2^ε`. The exact inverse Abel identity is

`M(N)=F_ε(0)-(N+1)^(1+ε)F_ε(N)
       +Σ_(1≤n≤N)[(n+1)^(1+ε)-n^(1+ε)]F_ε(n)`.

The read compact-interval power estimate gives
`0≤(n+1)^(1+ε)-n^(1+ε)≤A_ε n^ε`.
For any `δ>0`, choose `N₀` such that the assumed little-o bound is at most
`δ n^(-ε-1/2)` for `n≥N₀`. The finitely many earlier summands contribute a
constant `C₀`. The boundary and remaining sum then give, for `N≥N₀`,

`|M(N)|≤C₀+[2^(1+ε)+3A_ε]δ sqrt(N)`.

Here `Σ_(n≤N)n^(-1/2)≤2sqrt(N)+1≤3sqrt(N)` for `N≥1`.
Since `δ` is arbitrary, `M(N)=o(sqrt(N))`. Passing to real arguments by
`M(x)=M(floor x)` contradicts the read unconditional theorem
`mertens_omega_pm_sqrt` in `RHTower/MertensSquareRootOmega.lean`.
Negating the little-o assertion gives the stated positive constant and infinitely
many large integer witnesses.

At those same witnesses, the quartic lower comparison gives

`E_ε(N)>(Z² c_ε⁴/2)N^(-2)`.

Consequently the normalized empty-leg energy is not `o(N^(-2))`, equivalently
not `o(T^(-1))` along square horizons `T=N²`. These are unconditional lower
oscillation statements, stronger than merely excluding a larger power exponent.
They do not decide whether the corresponding big-O endpoint bound holds.

## Status

All six boundary declarations in `VaughanEndpointRatesForceSimpleBoundaryZeros.lean`
passed the corrected final direct check, with standard axioms only and no warnings.
The module is wired and its scratch removed:

- `boundary_zeta_order_and_factor_bound_of_moebius_power`
- `analyticOrderAt_eq_one_of_vaughan_tail_rate`
- `riemannHypothesis_and_simple_zeros_of_vaughan_half_tail_rate`
- `riemannHypothesis_and_simple_zeros_of_vaughan_square_energy_endpoint`
- `riemannHypothesis_and_simple_zeros_of_vaughan_horizon_energy_endpoint`
- `exists_boundary_factor_bound_of_vaughan_tail_rate`

These certify the boundary order/factor estimate, simplicity from an attained
tail rate, all three endpoint consequences, and the common local-factor bound.
Their all-positive Abel and exact rate-set dependencies also passed final
direct checks and standard-axiom audits.
All seven oscillation declarations in `VaughanEndpointScalesHaveUnavoidableOscillation.lean`
passed the corrected final direct check, with standard axioms only and no warnings.
The module is wired and its scratch removed:

- `exists_eventual_mertens_sqrt_bound_of_vaughan_tail_bound`
- `frequent_vaughan_scaled_reciprocalTail_sqrt_lower`
- `not_tendsto_vaughan_scaled_reciprocalTail_sqrt_zero`
- `frequent_vaughan_reciprocalTail_sqrt_lower`
- `frequent_vaughan_square_energy_endpoint_lower`
- `not_tendsto_vaughan_square_energy_endpoint_zero`
- `frequent_vaughan_square_energy_reciprocal_lower`

These retain the finite head in inverse Abel summation and transfer the actual
positive Mertens square-root oscillation through the quartic comparison. Both
normalized nonconvergence statements and unscaled positive cofinal lower bounds
are certified. No external novelty claim or fixed positive strip is made.
