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

## Formalized conductor error

[OddStabilizerPoissonHorizon](../3-formalized/odd-stabilizer-conductor-error-is-bounded.md)
proves `Σ_{q≤Q,odd} μ²(q)σ₂(q)/φ(q)²≤64Q` and bounds the actual
Poisson-horizon cotangent error by `64 cosTransform Ω 0`.
The proof uses the multiplicative majorant `zeta*(μ²/φ)³` and the existing
harmonic bound `Σ μ²(d)/(dφ(d))≤4`. Its signed C¹ row theorem keeps
endpoint and baseline errors explicit.

## Odd-conductor main term

The corpus proves the full sum `F(Q)=Σ_{q≤Q} μ²(q)/φ(q)∼log Q`.
Its parity identity is `F(Q)=O(Q)+O(floor(Q/2))`, where O is the odd sum.
Monotonicity gives `F(Q)≤2O(Q)≤F(2Q)`, hence `O(Q)∼(1/2)log Q`.
This limit and the uniform conductor bound are formalized in the same leaf;
all four axiom audits use standard axioms, and the final direct check passes.
Neither statement alone transports the logarithmic coalescent kernel.
The [exact C² Poisson row](exact-poisson-row-for-the-odd-stabilizer.md) targets
the remaining fixed-cutoff dual terms and the sharp horizon.
