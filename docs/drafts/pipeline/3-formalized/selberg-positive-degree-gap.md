# The positive-degree gap in the Selberg class

- **ID:** selberg-positive-degree-gap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ33
- **Statement:** Every extended Selberg function has presentation degree zero or at least one. In the full class, degree below one forces the Dirichlet unit, conductor parameter `Q = 1`, and root number `1`.

## Proof

Suppose `0 < d < 1`. Let `φ(z) = Σ a(n) exp(−nz)`, analytic for `Re z > 0` and periodic with period `2πi`.

**Mellin expansion.** Use the ordinary kernel `z^(−u) Γ(u)F(u)`. On `Re u = −k−1/2`, reflection bounds its norm by a majorant whose `k`th root tends to zero, times `exp(−π(1−d)|Im u|/2)`. The reflected Gamma product has total slope `d`; the denominator `Γ(k+3/2)` has slope one. Thus the left integral tends to zero for every positive real `z = x`. The horizontal integrals vanish by polynomial strip growth and Gamma decay.

Shifting from `Re u = 2` crosses the pole at one and the Gamma poles at `−j`. Their residues are
`P(z) = Res_(u=1)(z^(−u)Γ(u)F(u))` and `z^j(−1)^jF(−j)/j!`. Arbitrary pole order at one gives a polar term analytic on the slit plane. The contour identity makes the Taylor partial sums converge at every `x > 0`; convergence at every positive radius implies absolute convergence everywhere. Their sum `E` is entire. Termwise Gamma inversion and the identity theorem give `φ = E + P` on the right half-plane.

**Coefficient decay.** Put `G = E + P`. It is analytic on the upper half-plane, where the identity theorem propagates `G(z+2πi) = G(z)`. Apply Cauchy's theorem to `G(z+2πi)e^{nz}` on a rectangle with real coordinates `−R, 1` and imaginary coordinates `−π, π`. Periodicity cancels the horizontal edges. The right integral is exactly `2πa(n)` by Fourier orthogonality and absolute convergence. Compactness on the left edge gives

`|a(n)| ≤ C_R exp(−Rn)`.

Taking `R = 1` gives absolute Dirichlet convergence at zero.

**Functional-equation contradiction.** Absolute convergence at zero identifies the Dirichlet series with `F` throughout `Re s > 0`, away from one: multiply by the displayed pole-clearing factor and apply the identity theorem. It also bounds `F(1/4+it)` uniformly. Every positive Gamma scale contributes a vanishing quotient between the quarter lines, hence

`‖γ(1/4+it)‖ / ‖γ(3/4+it)‖ → 0`.

The pointwise functional equation forces `F(3/4+it) → 0`. Vertical decay on a line of absolute Dirichlet convergence forces every positive-index coefficient to vanish, contradicting the nonzero arithmetic function. Thus the gap is empty. The full-class conclusion follows from the degree-zero classification.

## Lean certificate

Namespace `GaloisForLFunctions.SelbergClass`:

- `degree_eq_zero_or_one_le`: the unconditional extended-class degree gap.
- `classification_of_degree_lt_one`: full-class unit classification below degree one.
- `degree_eq_zero_of_summable_zero`: absolute convergence at zero forces degree zero.
- `exists_exponential_coeff_bound_of_degree_lt_one`: the contour-derived coefficient bound.

Leaf: `formal/GaloisForLFunctions/SelbergClass/DegreeGap.lean`. The ordinary Mellin, continuation, Fourier, and Gamma-ratio proofs are its sibling imports. All fifteen modules are wired into `SelbergClass.lean`.

Every source passed the Lean kernel. The leaf and both subsequent source cleanups passed `lake --old env lean`; six transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. No Euler-product or Ramanujan hypothesis is needed for the extended-class gap. Positive-degree selection in Γ15 remains unresolved.
