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
The [exact C² Poisson row](../3-formalized/exact-poisson-row-for-the-odd-stabilizer.md)
now identifies the fixed-cutoff correction as nonnegative primitive samples.
Equality with the negative diagonal holds exactly when all active samples vanish;
`Qb≤πm` suffices, including equality. Positive complete and finite rows occur
arbitrarily close beyond this horizon, falsifying universal rowwise negative
cancellation. The exact horizon coefficient is `−Ωhat(0)/2`. All sixteen audits
and both final direct checks pass. The [finite-aperture transport](odd-stabilizer-finite-aperture-transport.md)
and the global sum of primitive corrections remain open.
The [C⁴ aperture bounds](../3-formalized/odd-stabilizer-aperture-and-fixed-base-renormalization.md)
now control finite linear tails and short rows. At a fixed base the row/log Q
limit is zero, and the primitive correction/log Q limit is `Ωhat(0)/(2πm)`.
These seven theorems pass audits and the final direct check.
The [decay-preserving phase and lattice bounds](../3-formalized/decay-preserving-cosine-transport.md)
are also formalized: logarithmic phase error retains inverse-square decay,
and positive-frequency mass has no additive height term. The
[literal weighted-row transport](../3-formalized/literal-logarithmic-stabilizer-transport.md)
is now formalized: fixed smooth profiles have signed dual error
`≤C O(Q)[T⁻¹+(m/(TR))³]`, row bound `C O(Q)`, and logarithmic moment
`C O(Q)/T`. All eight audits and both final direct checks pass. The
[actual standard taper](../3-formalized/actual-smooth-taper-stabilizer-transport.md)
has Lipschitz constant two and endpoint variation `C O(Q)/T`, uniformly in
length and collar. The [literal pair reindexing](../3-formalized/literal-stabilizer-model-row-decomposition.md)
now retains both aperture and upper cutoff exactly, with global taper error
`C floor(X) O(Q)/T`. Global boundary summation remains open.

## Fixed-cutoff primitive-sample calculation

For the triangle taper `g(y)=L−y`, `L=log X`, choose `Q≈X/T` and
support Ω in `[T,2T]`. Since `2<π`, every positive spatial sample has base
`m≤2qT/π<X`. Summing the exact dual over odd base points should reduce the
linear model, up to lower-order quadrature and coprime-harmonic errors, to

`−β/(2π) ∫ Ω(t) Σ_{q≤Q,odd} (μ²(q)/φ(q)) (L−log(qt/π))² dt`.

The actual standard taper is `g=autocorr(φ²)`, with
`max(L−2w−|y|,0)≤g(y)≤max(L−|y|,0)` (`Zeta23.Taper.g_ge`,
`g_le_Aphi`, `Aphi_le`). Its replacement by the triangle must follow the
signed spatial/diagonal cancellation: an earlier absolute replacement can cost
`O(wX log Q)`. Retaining `∫_{log(qt/π)}^L g(y)dy` first should reduce the
replacement cost to `O(wT log²T)`. Uniform taper Lipschitz control and its
finite-row endpoint transport are now formalized.

The odd logarithmic mean predicts the leading term
`−β(∫Ω)(log Q)³/(12π)`. Thus scalar 1/4 would retain one eighth of the
unit-mean scalar-two model term. This asymptotic is not yet proved.

The [coprime-harmonic conductor average](../3-formalized/coprime-harmonic-conductor-average.md)
is formalized for arbitrary positive horizons N(q):
`Σ_{q≤Q}qμ²(q)/φ(q)² · |H_q(N(q))−(φ(q)/q)log N(q)|≤36864(1+log Q)`.
Its pointwise divisor bound is uniform even when N<q; the supporting
logarithmic moment is `Σ μ²(q)(1+log q)/φ(q)²≤576`.

Weighted taper summation and odd-base quadrature remain to convert this into
raw error `O(T log²T)`. The [odd logarithmic square moment](odd-stabilizer-log-square-mean.md)
should supply coefficient 1/6 from the existing odd mean 1/2. Aperture
boundary estimates and global summation remain open before asserting the model
calibration.
