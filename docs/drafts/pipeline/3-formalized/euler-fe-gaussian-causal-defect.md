# The Gaussian defect determines the causal tail

- **ID:** euler-fe-gaussian-causal-defect.
- **Programme:** Euler–FE transport theory.
- **Stage:** 3-formalized.
- **Type:** THEOREM (Lean).
- **Source:** obstacles-summary §2.10; literal Gaussian source constraint.
- **Statement:** Injectivity of the literal Gaussian differential defect on arbitrary
  signed causal densities, modulo the scalar identity operator.

## Statement and mechanism

Put `ψ(x)=exp(x/2−π exp(2x))`, `a(x)=π exp(2x)` and
`L=∂x−(1/2−2a(x))`. For a causal kernel `K`, set

    T_K ψ(x) = ∫₀∞ K(t)ψ(x+t)dt,
    q(u) = ½K(½log(1+u))(1+u)^(-3/4)exp(-u).

Kernels and densities may be complex. The domain is `q∈L¹(0,∞)`;
it includes every measurable exponential-order kernel. For `a(x)>1`,
substitution `u=exp(2t)−1` gives

    T_K ψ(x) = ψ(x) ∫₀∞ q(u)exp(-(a(x)−1)u)du,
    L(T_K ψ)(x) = −2a(x)ψ(x) ∫₀∞ u q(u)exp(-(a(x)−1)u)du.

The second transform is holomorphic for `Re a>1`: on each smaller half-plane,
polynomial factors times its exponential kernel are bounded, giving domination
by `|q|`. Equality on one open interval propagates throughout that half-plane.
For two kernels, put `g(u)=u(q₁(u)−q₂(u))exp(-u)`. The bound
`u exp(-cu)≤1/c` makes `g` integrable. Its Laplace transform is the
difference of the observed rate moments at parameter `s+1`, hence zero.
Laplace uniqueness, `u>0` and the nonzero exponential recover `q₁=q₂`
almost everywhere. Changing variables in the integral of `|q₁−q₂|`, whose
Jacobian is strictly positive, recovers `K₁=K₂` almost everywhere on the
whole positive ray. The scalar term `cψ` is annihilated by `L`.

Thus for every interval `(A,B)` with `A<B` and `π exp(2A)>1`, and arbitrary
scalars `c,d`, equality of `L(cψ+T_Kψ)` and `L(dψ+T_Hψ)` throughout that
interval is equivalent to `K=H` almost everywhere on `(0,∞)`.

Exponential-order admission uses the explicit bound
`|K(t)|exp(t/2−(exp(2t)−1)) ≤ C exp(1) exp((B+1/2)t−exp(2t))`.
The right side is integrable for every real exponential growth exponent `B`.

## Frontier and limits

Existing zero-division commutator results treat one Green factor; rational
tail-germ reconstruction treats finite divisors. The target concerns complete
signed causal tails and local observations of their differential defect.
It identifies the deformation excluded by the literal Gaussian seed equation.
An admissible infinite causal repair must cancel the entire non-scalar kernel;
no nonzero total density can remain invisible even on one observation interval.
It does not show that an exceptional zero of the undeformed ζ violates that
equation; same-depth replication, `LinAt C` and AAL remain open.

## Lean proof

All declarations are in `GaloisForLFunctions.EulerFETransportTheory`.

| Module | Principal declarations |
|---|---|
| `TheGaussianDefectDeterminesTheCausalTail.lean` | `hasDerivAt_gaussianRateLaplace`, `ae_eq_of_gaussianRateMoment_local` |
| `TheCausalGaussianDefect.lean` | `integrable_gaussianRateDensity_of_exponential_bound`, `causalGaussianResponse_eq_laplace`, `gaussBaseOperator_causalGaussianResponse`, `ae_eq_of_causalGaussian_defect_local`, `causalGaussian_defect_local_iff` |

Both modules pass direct `lake --old env lean` checks. Transitive axiom audits
of exponential-order admission, the exact defect formula and both recovery
theorems use only `propext`, `Classical.choice` and `Quot.sound`. Both modules
are imported by the programme umbrella; no umbrella build was run.
