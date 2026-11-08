# Conductor-weighted convergence of the full spacing kernel

- **ID:** hhac-weighted-mixed-spacing-convergence
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL RATE THEOREM

## Theorem

Use the original product spacing radius `rε(m,n)=exp(−ε(1/m+1/n))` and define

`Bε(m,n)=twistedEnergy(rε(m,n),m,n)+weilPrimeKernel(m,n)`
`+[m=n](log(2ε)−tameDifferent(n))`.

For every `0<α≤1` and `δ>2α`, there is `Cδ,α>0` such that, for every `ε>0`,
finite positive-conductor support `S` and real coefficients `x`,

`Σ_{m,n∈S}|x_m x_n Bε(m,n)|≤Cδ,α ε^α Σ_{n∈S} n^δ x_n²`.

The same right side bounds

`|spacingForm(ε,S,x)+log(2ε)Σx_n²−spacingLimit(S,x)|`.

Every positive conductor exponent is admitted: `α=min(δ/8,1)` works.
For an infinite probe on positive integers with `Σ n^δ x_n²<∞`, the entire
absolute error series is summable and satisfies the same bound. Its sum tends
to zero as `ε→0+`. The Lean sequence on `ℕ` is extended by `x_0=0`.

The [prime-row obstruction](../5-failed/hhac-mixed-spacing-prime-row.md) rules
out unweighted row control even at a fixed positive regulator. No endpoint
rate `α=δ/2` or optimality claim is made here.

## Proof

Full root groups split by exact order. Double Möbius inversion gives

`T_exp(−t)(m,n)+[m=n]φ(n)log t+I(m,n)`
`=R(t,m,n)=Σ_{d|m,e|n} μ(m/d)μ(n/e)gcd(d,e)F(t lcm(d,e))`,

where `F(u)=log u−log(1−exp(−u))`. The logarithmic coefficient is the common
primitive-root multiplicity. Torsion adjunction on the diagonal and the known
off-diagonal intersection law give the exact normalization

`Bε(m,n)=[g/φ(g)]R(ε(1/m+1/n),m,n)/√(mn)`, `g=gcd(m,n)`.

Exponential convexity gives `0≤F(u)≤log(1+u)`. For `0<α≤1`,
`F(u)≤(1+1/α)u^α`. Taking absolute values in the divisor transform therefore gives

`|R(t,m,n)|≤(1+1/α)τ(m)τ(n)g(t lcm(m,n))^α`.

At the actual spacing scale, `t lcm(m,n)≤2εmn`. Also
`g/φ(g)=Σ_{d|g} μ(d)²/φ(d)≤τ(g)`. For every `κ>0`, subpolynomial divisor growth
absorbs the three divisor counts and yields

`|Bε(m,n)|≤Cα,κ ε^α g(mn)^(α+2κ)/√(mn)`.

The normalized gcd form has the positive-square identity

`Σ_{m,n} gcd(m,n)z_m z_n/√(mn)=Σ_d φ(d)(Σ_{d|n} z_n/√n)²`.

Cauchy–Schwarz on multiples bounds it, for `η>0`, by

`ζ(1+η)Σ_n z_n² n^η Σ_{d|n} φ(d)/d^(1+η)`.

The inner divisor sum is at most `τ(n)`. Another divisor bound consequently
controls the gcd form by `Cβ Σ n^β z_n²` for every `β>0`, on arbitrary finite
positive supports.

Choose `κ=(δ−2α)/8`, `β=(δ−2α)/2` and apply this bound to
`z_n=|x_n|n^(α+2κ)`. Since `β+2α+4κ=δ`, it gives the claimed absolute estimate.
Every finite set of positive pairs lies in a square conductor window.
Nonnegative finite-sum exhaustion transfers the bound to the infinite series;
the positive power of `ε` then gives its limit.

## Lean and audit

All modules lie in `formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/`.

| Module | Exact result |
|---|---|
| [PrimitiveTorsionDivisorFormula.lean](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/PrimitiveTorsionDivisorFormula.lean) | `torsionEnergy_exponential_decomposition` |
| [PrimitiveSpacingRemainder.lean](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/PrimitiveSpacingRemainder.lean) | `torsionExponentialDefect_abs_le` |
| [WeightedGcdForm.lean](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/WeightedGcdForm.lean) | `normalized_gcd_form_finite_bound` |
| [SpacingErrorIdentity.lean](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/SpacingErrorIdentity.lean) | `spacingKernelError_eq`, `spacingForm_error_eq` |
| [SpacingKernelMajorant.lean](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/SpacingKernelMajorant.lean) | `spacingKernelError_conductor_bound` |
| [WeightedSpacingConvergence.lean](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/WeightedSpacingConvergence.lean) | `spacingKernelError_weighted_absolute_rate`, `spacingForm_weighted_error_rate` |
| [InfiniteSpacingConvergence.lean](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/InfiniteSpacingConvergence.lean) | `spacingKernelError_infinite_absolute_rate`, `tendsto_spacingKernelError_infinite_absolute` |

Each passes a direct `lake --old env lean` audit. Printed capstones depend only
on `[propext, Classical.choice, Quot.sound]`. Finished modules are wired into
the programme umbrella.

## Contribution and boundary

The actual mixed error has uniform power control on every positively weighted
arithmetic probe space, including infinite probes. This strengthens fixed-support
limits and the sharp prime-row survivor while preserving the original regulator.

Normalized gcd sums are classical; see [Bondarenko–Seip](https://arxiv.org/abs/1402.0249).
[Washburn](https://arxiv.org/abs/1309.2716) studies Abel summation of
Ramanujan–Fourier expansions. The contribution here is the comparison for the
actual spacing kernel; no literature priority claim is made.

The limiting form remains indefinite, and no self-energy payment follows.
Absolute error summability alone does not construct the full infinite forms:
[weighted torsion-form completion](hhac-weighted-torsion-form-completion.md)
proves the separate limiting-kernel bound and constructs the actual infinite
forms, scalar counterterm and operator-norm convergence.
