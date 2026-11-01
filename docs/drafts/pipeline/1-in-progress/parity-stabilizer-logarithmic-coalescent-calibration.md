# Literal odd-pair model under the signed coalescent kernel

- **Stage:** 1-in-progress
- **Type:** CANDIDATE / SIGNED MODEL CALIBRATION
- **Route:** Argon §4.1.
- **Parents:** [Raw normalization](../3-formalized/stabilizer-incomplete-periods-and-prime-comparison.md), [phase obstruction](../3-formalized/frullani-sieve-phase-resonance.md).

## Target

Evaluate the literal `stabilizerModelOddCoalSum` with smooth time weight,
logarithmic phase, taper and coalescent aperture. Determine its leading negative
term for a general raw scalar β; scalar two has unit raw mean, while the existing
scalar one quarter has one eighth of that mean.

## Mechanism and unresolved steps

The existing `abs_sum_dynamic_poissonHorizon_singularSeries_add_le` controls the
linear phase `2r/m` at conductor horizon `Q=floor(m/b)`, for time support `[a,b]`.
Its signed main term is minus `cosTransform Ω 0` times the odd-conductor sum
`Σ μ²(q)/φ(q)`. This cancellation must precede absolute values.

The literal model fixes Q across every pair; the Poisson theorem chooses a
row-dependent `Q(m)=floor(m/b)`. These are different sources. For a fixed Q,
rows with `m<Qb` retain additional nonzero dual modes. Either evaluate those
modes or define and calibrate a row-dependent model with its own exact
prime-minus-model discrepancy. The dynamic theorem alone cannot evaluate the
fixed-Q model.

Transport from `2r/m` to `log(m+2r)−log m`, retain the factors
`1/sqrt(m(m+2r))` and `g(log m)`, and control the actual aperture and upper
endpoint. Then evaluate the odd-conductor sum and sum over odd m. The raw
rectangle audit alone proves none of these weighted estimates. Even a complete
model evaluation leaves the actual prime-minus-model signed discrepancy open.

## Cotangent error

At `Q=floor(m/b)`, the existing conductor error is proportional to
`Q⁻¹ Σ_{q≤Q, odd} μ²(q)σ₂(q)/φ(q)²`. A uniform linear bound for this
sum would leave `O(1)` against the negative main term of order `log Q`.
For squarefree q its Euler factor is `(1+p²)/(p−1)²=1+2p/(p−1)²`;
the divisor expansion's mean has convergent local increments
`2/(p−1)²`. This offers an unconditional way to pay the conductor error
without taking absolute values of the leading signed kernel.

The corpus already gives `Σ_{d≤N} μ²(d)/(d φ(d))≤4`
(`RHTower.Sieve.sum_sqfreeTotientInv_div_le`). For odd primes,
`2/(p−1)²≤3/[p(p−1)]`. A threefold Dirichlet-convolution majorant
therefore suggests the explicit bound `Σ_{q≤Q, odd} μ²(q)σ₂(q)/φ(q)²≤64Q`.
The required finite divisor expansion and convolution domination have not yet
been formalized.

An equivalent comparison uses arithmetic functions directly: let `g=μ²/φ`
and let `a(q)=1_{q odd} μ²(q)σ₂(q)/φ(q)²`. At an odd prime p,
`a(p)≤1+3g(p)=(zeta*g³)(p)`; higher prime powers have `a=0`.
Multiplicativity and nonnegative convolution coefficients reduce the desired
mean bound to `Σ_{d≤Q}(g³)(d)/d≤(Σ_{d≤Q}g(d)/d)³≤64`.

## Odd-conductor main term

The corpus proves the full sum `F(Q)=Σ_{q≤Q} μ²(q)/φ(q)∼log Q`.
Its parity identity is `F(Q)=O(Q)+O(floor(Q/2))`, where O is the odd sum.
Monotonicity gives `F(Q)≤2O(Q)≤F(2Q)`, hence `O(Q)∼(1/2)log Q`.
Together with the [uniform conductor bound](odd-stabilizer-conductor-error-is-bounded.md),
this would isolate the negative logarithmic main term of the linear-phase
model. Neither statement alone transports the logarithmic coalescent kernel.
