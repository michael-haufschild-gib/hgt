# Local finiteness and separation of high cubic cusps

- **ID:** cubic-high-cusp-local-finiteness
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [exterior coercivity](cubic-quotient-exterior-coercivity.md)
- **Statement:** Near every hyperbolic point, only finitely many principal cusp rows have height at least one. An integral matrix with nonzero lower-left entry satisfies `h(Mw)h(w)≤1`; upper triangular integral matrices preserve height.

Choose the continuous upper triangular representative `g(w)`. The inverse
row operator bounds the four integral coordinates of a cusp row by
`rowBound(g(w))/sqrt(h(w))`. On a small neighborhood, the first factor is
uniformly bounded. Rows with height at least one therefore lie in a fixed
bounded subset of `ℤ⁴`. Discreteness and injectivity of cusp-row coordinates
give a finite set.

For a matrix with lower-left entry `c≠0`, the integral Eisenstein norm
gives `|c|²≥1`. The height formula
`h(M(z,v))=v/(|cz+d|²+|c|²v²)` yields the product bound. If `c=0`,
the determinant gives `ad=1`; both integral norms are at least one and
their product is one. Thus `|d|²=1`, and height is unchanged.

Lean: `MetaplecticMobiusDescent/HighCubicCuspsAreLocallyFinite.lean`,
namespace `CubicEisenstein`:

- `principal_high_locally_finite`.
- `integral_hyperbolicHeight_mul_le_one`.
- `integral_upper_triangular_height`.

Direct source and transitive audits pass with only `propext`,
`Classical.choice`, and `Quot.sound`. The local proof uses the corpus
row-coordinate bound, continuous triangular section, and integral norm
lower bound. The [invariant barrier](cubic-invariant-cusp-barrier.md) and [exterior coercivity](cubic-quotient-exterior-coercivity.md) are formalized.
