# Uniform second-scale vanishing over product horizons

- **ID:** uniform-product-horizon-vaughan-second-scale
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/vaughan-tail-scale-contraction.md
- **Statement:** For `0<ε<1/2`, every centered Vaughan Gram entry divided by `(UV)^(1-2ε)` tends uniformly to zero as `UV→∞`, without requiring either individual cutoff schedule to diverge.
- **Novelty status:** A uniform specialization of the proved mean-zero prefix estimate and the exact covering identity. No external novelty claim.

## Uniformly truncated Möbius patterns

Let `r_U(d)=μ(d)1_(d≤U)`. Its partial sum is `M(min(U,x))`. For any `η>0`,
the proved mean-zero Möbius theorem gives a finite constant `C_η` such that
`|M(y)|≤(η/2)y+C_η` for all `y`. Thus

`|Σ_(d≤x)r_U(d)|≤(η/2)x+C_η≤ηx`

for all sufficiently large `x`, uniformly over every cutoff `U`. Also `|r_U(d)|≤1`.

The checked proof of `eventually_abs_patternPrefix_le_of_meanZero` uses only this
eventual linear partial-sum bound, the common coefficient bound, and the fixed damping.
Its threshold therefore works uniformly for this family. Explicitly, the estimate
`abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos` is

`|A_(r_U,ε)(n)|≤3D^(1-ε)+(13/ε)η n D^(-ε)`.

For a target `θ>0`, choose a small fixed `δ>0` with `3δ^(1-ε)≤θ/2`, then choose
`η>0` with `(13/ε)η(δ/2)^(-ε)≤θ/2`. Taking `D=floor(δn)` beyond the uniform
partial-sum threshold gives

`|A_(r_U,ε)(n)|≤θ n^(1-ε)` for all sufficiently large `n`, uniformly in `U`.

Absolute convergence gives the uniform initial bound
`|A_(r_U,ε)(n)|≤2Z_ε n`, where `Z_ε=Σ_(d≥1)d^(-1-ε)`.
Writing `β=1-2ε>0`, split the energy before the common threshold `N_θ` to obtain

`E_(r_U,ε)(T)≤4Z_ε² N_θ+θ²(1+T^β/β)`.

First let `T→∞`, then `θ→0`. This proves `E_(r_U,ε)(T)/T^β→0` uniformly in
`U`. The centered first and second Vaughan legs are exactly these pattern prefixes
at cutoffs `U` and `V`, respectively. This strengthens their absolute atom estimates
without supplying a fixed power rate.

## The covering horizon

At `T=UV`, the literal both-large piece vanishes throughout the horizon, and its
centered norm divided by `T^(β/2)` is at most

`Z_ε |U^ε(ρ-A_U)| |V^ε(ρ-A_V)|`.

The signed-tail theorem gives `f(N)=N^ε(ρ-A_N)→0`. It is uniformly bounded:
for `N≥1`, apply `abs_tsum_tail_rpow_le_of_linear` with slope `L=1` to get
`|f(N)|≤2+1/ε`; the zero index contributes zero.
If `UV≥K²`, at least one cutoff is at least `K`. Its factor is uniformly small,
and the other factor is uniformly bounded. Hence the centered large-leg norm is
`o(T^(β/2))` uniformly over every factorization of `T`.

The centered pole correction has norm at most `1/2`. The actual interior norm is
`o(T^(β/2))` by the checked source theorem. The exact sum of all five centered pieces
is the interior prefix, so the same uniform conclusion follows for the remaining
small-small piece. Cauchy–Schwarz proves the whole centered Gram law. The same result
holds for the centered diagonal and any fixed real coefficient packet.

## Audit and status

The general mean-zero prefix proof and its energy proof in
`TheMeanValueIsTheLeadingCoefficientOfTheReceiver.lean` have been read. Their thresholds
depend only on the uniform partial-sum modulus and the common coefficient bound; the
finite initial-energy term is uniformly bounded by the displayed absolute estimate.
The product-horizon vanishing, mean factorization, scaled signed tail, and source
little-o dependencies are tracked on the earlier product-horizon card. No additional
analytic estimate is assumed.

This strengthens `vaughan-product-horizon-centred-gram-has-zero-trivial-density.md`.
The exact finite Abel tail-rate equivalence shows why a fixed power improvement is
still the full strip problem. Uniform little-o alone does not supply scale contraction.

The uniform-family prefix and energy estimates, uniform truncated Möbius mean, arbitrary
moving-truncation energy limit, and exact small-leg identification passed all ten scratch
axiom audits with standard axioms. The checked source is now
`UniformTruncatedMobiusReceiversHaveZeroTrivialDensity.lean`; its producing check passed.
Its final direct `lake --old env lean` audit passed.

The product-horizon specialization passed all fifteen scratch axiom audits: its
audit targets include all five component norms, trace and matrix limits, a common threshold
for every cutoff pair, bounded moving coefficient packets, and the two-divergent-cutoff
corollary. The checked module is `ProductHorizonVaughanGramsHaveZeroTrivialDensity.lean`.
Its producing and final direct `lake --old env lean` checks passed. All proofs used
default Lean limits and only standard axioms.
