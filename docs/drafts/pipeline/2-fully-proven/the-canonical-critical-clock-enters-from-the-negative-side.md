# The canonical critical clock enters from the negative side

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean in progress)
- **Wall:** Σ1k, equality case.
- **Statement:** For a nonzero compact C² window `H=e^{y/2}h` with `Q(H)<0`, the tilted-spline horizon energy is eventually negative on the exact clock `c_N⁸=K*(H)log N`, where its leading pencil vanishes.

Put `M=∫φ²`, `κ=(∫φ)²/M`, `M_j=∫exp(-jy)H²`, `B=7J(1)M_8`, and
`D=8(1/64)(4/π)^10 μ_q ζ(10)/M>0`, where `q(x)=(sinh²1+sin²x)^4` has period `π` and mean `μ_q`.
Write `E_N=c_N^(-1) Q(atomicTest_N)/∫atomDilate²` and `K_N=c_N⁸/log N`.
The stronger expansion is

`E_N=κQ(H)+B/K_N-D M_10/(K_N c_N²)+o(c_N^(-2))`

whenever `K_N→K>0` and `c_N≥1`. In particular, if `κQ(H)+B/K=0` and
`c_N²(K_N-K)→L`, then `c_N²E_N→-BL/K²-DM_10/K`.
The first shift of the critical multiple is `L=-DKM_10/B`. Merely specifying `K_N→K` does not select a sign; the exact clock has `L=0` and a strictly negative limit.

## Paper proof [PROVED HERE]

**1. Quadratic averaging error.** Let `a=sinh²1+1/2`. The exact trigonometric expansion is

`q(x)=a⁴+3a²/4+3/128+(-2a³-3a/8)cos(2x)+(3a²/4+1/32)cos(4x)-(a/8)cos(6x)+(1/128)cos(8x)`.

The constant term is `μ_q`, since all four cosines have zero integral over `[0,π]`. For compact C² `F`, two integrations by parts give
`λ²∫F(x)cos(jλx)dx=-j^(-2)∫F''(x)cos(jλx)dx` for each `j=2,4,6,8`.
Riemann–Lebesgue makes the right side tend to zero; its absolute value is at most `j^(-2)‖F''‖₁`. Consequently
`λ²[∫Fq(λ·)-μ_q∫F]→0`, with a uniform bound by a constant times `‖F''‖₁`.
The weights `F_j(x)=1_{x>0}h(log x)²x^(-j)` are compact C², supported in `[e^(-A),1]`.

**2. Two-term aliasing.** The exact spectrum is
`|φ̂(2πt)|²=(1/64)q(πt/4)(1+(πt/4)²)^(-4)`.
For every `z>0`,
`0≤(1+z²)^(-4)-z^(-8)+4z^(-10)≤10z^(-12)`.
For the upper bound, multiply by the positive denominators and use
`(1+v)^4(1-4v+10v²)-1=20v³+45v⁴+36v⁵+10v⁶≥0`, `v=z^(-2)`; the lower bound follows from `(1+v)^(-4)≥1-4v`.

Apply this with `z=πkc_Nx/4`. After multiplication by `c_N⁸`, the first two terms have coefficients
`(1/64)(4/π)^8 k^(-8)` and `-(4/64)(4/π)^10 k^(-10)c_N^(-2)`.
The leading numerator average has error `o(c_N^(-2))` by step 1, dominated after scaling by `Ck^(-10)`. The existing Lipschitz Riemann-sum estimate adds at most
`C[c_N²k^(-8)/N+c_N³k^(-7)/N]` after scaling by `c_N²`; its harmonic sum tends to zero.
The second numerator average converges by the existing first-order averaging theorem, with summable majorant `Ck^(-10)`. The rational remainder after scaling is bounded by `Cc_N^(-2)k^(-12)`.
These bounds use only `x≥e^(-A)` on the support and `c_N³/N→0`, which follows from `K_N→K`.
Summing the positive harmonics and their factor `2` gives

`c_N²[c_N⁸ horizonAlias_N-7M J(1)M_8]→-M D M_10`.

**3. The horizon remainder is smaller.** In `horizon_layer_sharp`, the high-frequency symbol remainder is `O(c_N^(-8))`. The explicit energy-defect bound is
`O(c_N/N+N^(-1)+sqrt(c_N/N)+(log N)^(-2)+(log N)^8/N)`.
Multiplication by `c_N²log N` sends every term to zero because `c_N⁸≈Klog N`.

For the low-frequency symbol integral split at `R=c_N^6`, below the grid `Ne^(-A)` for all large `N`. The existing Kuzmin–Landau majorant is `C(1+|τ|)^(-3/2)`, for both the discrete integrand and its limit; their tails cost `O(R^(-1/2))=O(c_N^(-3))`.
On `|τ|≤R`, the normalized horizon Dirichlet polynomial is a Riemann sum for
`h(log x)x^(-1/2+iτ)`. This compact function has Lipschitz constant `O(1+|τ|)`, giving error `O((1+R)/N)`; the atom transform differs from `∫φ` by `O(c_NR/N)`. Both transforms are uniformly bounded there. Since `|ν(τ)|≤C+log(2+|τ|)≤C'(1+R)`, the integrated product error is `O((c_N+1)R(1+R)²/N)`. Its product with `c_N²` tends to zero.
At the two fixed pole frequencies the same Riemann-sum argument gives `O(1/N)`, and the compact atom transform gives `O(c_N/N)`; the pole-product error is therefore `o(c_N^(-2))` too.
Thus `c_N²[E_N-κQ(H)-(log N/M)horizonAlias_N]→0`.

Combining steps 2–3 proves the expansion. Since `M_10>0` for nonzero continuous `H`, the exact critical clock gives a strictly negative scaled limit and hence eventual negativity. The perturbed-clock formula follows by expanding `1/K_N` at `K`.

## Lean obligations

No final Lean theorem is claimed yet. Required: quadratic numerator averaging; two-term harmonic sum; quantitative low-frequency and pole convergence; assembly and axiom audit. Existing corpus anchors: `shellSpectrum_tiltedUnitSpline`, `abs_riemann_modulated_sub_le`, `paperFT_deriv_deriv_of_compact`, `horizonDirichlet_sq_div_le`, and the explicit estimates inside `TheSecondOrderTermOfAHorizonBlock`.
