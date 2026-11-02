# Continuing the actual Epstein-to-Mayer transform

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [PM tasks](route-pm-mayer-scattering-and-escape.md), Mayer 2–4.
- **Source:** [quadratic averaging](../3-formalized/gauss-mayer-quadratic-averaging.md).

## Target

Continue the actual Cauchy integral identity
`Φ_w(a) = K_w *_M E_w(a)` from `Re w>2` to `Re w>0`, `w≠2`,
where `E_w` is half the uncompleted rectangular Epstein field defined
independently by its Gaussian count. Prove absolute convergence and
holomorphy of this continued integral, including at `w=1`.

## Height bounds and proposed domination

The certified weak functional-equation pair splits the completed field as

```text
Λ_y(s) = ∫₁∞ t^(s−1)(θ_y(t)−1) dt
       + y^(-1) ∫₁∞ t^(−s)(θ_(1/y)(t)−1) dt
       − 1/s − y^(-1)/(1−s).
```

For `y≥1`, the first integral is uniformly bounded on compact parameter
sets. In the second, split the theta product into
`(θ(t)−1)θ(t/y²) + (θ(t/y²)−1)`. Monotonicity, Poisson duality, and scalar theta Mellin integrability give

```text
|E_w(y)| ≤ C y^(1−η),  y≥1,
```

uniformly on a small parameter ball, for `0<η<min(1, inf Re w)`.
The certified height reciprocity `E_w(y)=y^(−w)E_w(1/y)` bounds
small heights. Keeping the same `Re w` in the reciprocal field and
Cauchy weight cancels their parameter-dependent powers exactly. For fixed
positive `a`, the remaining coefficient `a^(−Re w−1+η)` is locally bounded.
For every positive `t`, the Cauchy norm is bounded both by `1` and by
`t^(−Re w−2)`. Splitting at `t=a` therefore gives the proposed bounds
`C a^(1−η)t^(−1+η)` and `C a^(−Re w−1+η)t^(−1−η)`, with no intermediate
interval. These integrable bounds would support holomorphic parameter
integration.

A sharper route to the dual-tail bound uses only one scalar integral.
For `y≥1` and `Re w≥η`, its second summand is bounded by

```text
y^(-1) ∫₁∞ t^(−η/2)(θ(t/y²)−1) dt
 ≤ y^(1−η) ∫₀∞ u^(−η/2)(θ(u)−1) du.
```

The last integral is in the ordinary theta–zeta convergence chamber
because `0<η<1`. The first dual summand is bounded independently of
`y` by `θ(1) ∫₁∞(θ(t)−1) dt`: indeed
`θ(t/y²)≤θ(1/y²)=yθ(y²)≤yθ(1)` for `t,y≥1`.
This avoids requiring a Bessel expansion
or a sharp asymptotic expansion of the field.

Holomorphy and absolute convergence of the averaging integral remain
to be formalized.
No continuation of a totalized divergent lattice series is being asserted.

## Certified input

`RenormalizedIntersectionTheory/GaussMayerEpsteinReciprocity.lean` proves
`differentiableAt_epsteinField` and `reciprocity` on `Re w>0`, `w≠2`.
The proof clears both poles of the independent weak FE-pair, uses the
entire reciprocal Gamma function, and extends the lattice reciprocity
by the identity theorem. Five axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.

`RenormalizedIntersectionTheory/GaussMayerEpsteinHeatBounds.lean`
certifies absolute integrability and bounds for both real Gaussian tail
weights. With `0<η<1`, `η≤σ≤β`, `β>1`, and `y≥1`, their integrals obey

```text
original ≤ (θ(1)+1) M(2−β),
dual ≤ θ(1) M(0)+y^(1−η) M(η),
M(η) = ∫₀∞ t^(−η/2)(θ(t)−1) dt.
```

The twelve axiom audits contain only the same standard axioms.
`RenormalizedIntersectionTheory/GaussMayerEpsteinHeatRepresentation.lean`
identifies both actual complex Gaussian tails and proves their absolute
convergence for every spectral parameter. It proves the displayed heat
expansion away from `w=0,2` and the resulting explicit norm bound, retaining
both pole terms `2/|w|` and `2/(y|w−2|)`. Ten axiom audits contain only the
same standard axioms.


`RenormalizedIntersectionTheory/GaussMayerEpsteinHeightGrowth.lean`
proves `locally_uniform_height_growth`: every `w₀` with `Re w₀>0`, `w₀≠2`
has a spectral ball and constants `0<η<1`, `C>0` such that
`|E_w(y)|≤C y^(1−η)` for every `y≥1` and every `w` in that ball.
The explicit spectral coefficient is continuous away from the source
poles. Three axiom audits contain only the same standard axioms.

`RenormalizedIntersectionTheory/GaussMayerEpsteinHeightMeasurability.lean`
proves height measurability of the actual original and dual Gaussian tails,
and hence of `E_w` away from `w=0,2`. The lattice count is a measurable
sum; measurability of parameter integrals supplies the continuation.
Three axiom audits contain only the same standard axioms.

## Boundary

This would identify the canonical Mayer scattering state with an actual
continued Epstein integral. It would not classify every Mayer eigenspace,
construct a Hermitian form, or prove a fixed zero-free strip. For nonreal
`w`, the kernel retains a variable complex phase.
