# Axis-invisible affine polynomials realize arbitrary finite index

- **ID:** AXIS-INVISIBLE-AFFINE-INDEX
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Finite-index Mautner rigidity](../1-in-progress/finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** For each integer `d≥1`, set `K_d(a,b)=γ_d(1−a⁻ᵈ)bᵈ`, where `γ_d=1` for odd `d` and `γ_d=i` for even `d`. Then `K_d` is Hermitian, vanishes on translations and dilations, and `κ(p+K_d)=d+1` for every positive-definite affine kernel `p`.

## Dependency-closed paper proof

The phase satisfies `conj(γ_d)(−1)^d=−γ_d`. For `g=(a,b)` and `h=(c,e)`,

`K_d(g⁻¹h)=γ_d(a⁻ᵈ−c⁻ᵈ)(e−b)^d`.

Set `F_j(a,b)=a⁻ᵈ(−b)^(d−j)` and `B_j(a,b)=γ_d binom(d,j)b^j`, for `0≤j≤d`. The binomial theorem gives

`K_d(g⁻¹h)=Σ_j [conj(F_j(g))B_j(h)+conj(B_j(g))F_j(h)]`.

This proves Hermitian symmetry. Adding the `d+1` feature squares `|F_j−B_j|²` leaves the positive squares `|F_j|²+|B_j|²`, so `κ(K_d)≤d+1`. Both axis readings vanish directly.

The fibre at slope two is the nonzero monomial `γ_d(1−2⁻ᵈ)b^d`. If `κ(K_d)=r`, the [formalized translation-degree law](../3-formalized/the-negative-index-bounds-zero-axis-translation-degree.md) supplies a polynomial of degree below `r` agreeing with this monomial at every rational input. Polynomial uniqueness gives `d<r`. Thus `r=d+1`, the smallest index possible for degree `d`.

Positive addition cannot increase negative index. Conversely, conjugation by dilation `N+1` multiplies `K_d` by `(N+1)^d`. Every positive-definite `p` is bounded by `p(1)`. Divide each conjugated finite Gram matrix of `p+K_d` by `(N+1)^d`; it converges entrywise to the corresponding Gram matrix of `K_d`. Lower semicontinuity of negative inertia retains all its negative directions. Hence `κ(p+K_d)=d+1`.

## Lean and scope

- `HeckeKreinToeplitz/Index/HyperbolicFeatures.lean`: `negIndex_le_of_hyperbolic_features`.
- `HeckeKreinToeplitz/Index/RescalingInvariance.lean`: `negIndex_posDef_add_of_rescaling`.
- `AdelicKreinGeometry/Haar/PowerKernels.lean`: `negIndex_mixedPowerKernel`, `negIndex_posDef_add_canonicalMixedPower`, `negIndex_haarMixedPowerState`, and the two unchanged axis readings.

All three modules pass direct `lake --old env lean` checks and are wired into their umbrellas. Axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.

With `p=haarState`, every index at least two occurs while preserving both Haar axis readings. This completes the sharp positive family exposed by the zero-axis obstruction; it does not construct a carrier with continuous Weil dilation reading or decompose an arbitrary Haar-successor kernel.
