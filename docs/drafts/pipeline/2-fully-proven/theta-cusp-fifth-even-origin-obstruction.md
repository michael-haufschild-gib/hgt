# Fifth even theta source: the origin forces a positive fifth load

- **Stage:** 2-fully-proven; Lean formalization in progress.
- **Wall:** Σ6; the integrated rank-nine sign remains open.
- **Claim:** No real constant pair of fourth and fifth diagonal loads gives global pointwise positivity, including the actual weighted representative at any critical aperture.
- **Positive survivor:** Exact two-load positivity region of the full fifth block at the origin, with a sharp, strictly positive fifth-load threshold.

Write `m_j=(-1)^j D_t^(2j)[Φ(t)Φ(−t)]|₀`,
`A=[m_(i+j)]_(0≤i,j≤2)`, `b=(m₄,m₅,m₆)`,
`γ=m₈−bᵀA⁻¹b`, and `G₀=3Φ(0)²`. The native head `A` is positive
definite. The principal matrix on indices `{0,1,2,4}` has determinant
`det(A)γ`.

The complete modular source gives `m_j=M²p_j(X)` through `j=8`, with
`19.1<X<19.2` and `M>0`. Let `d=det[p_(i+j)]_(0≤i,j≤2)` and
`u=(p₄,p₅,p₆)`. The skipped determinant is

`M⁸[d p₈−uᵀ adj([p_(i+j)])u] < 0`.

This is an exact polynomial certificate: substitute `X=(191+z)/10`,
`0≤z≤1`, expand, and bound the positive coefficients of degrees 21 and 22
by their values at one. The constant term and all remaining coefficients
give strict negativity. The finite certificate passes Lean; the complete
source identity for order sixteen follows from the even seam derivatives
and the finite Leibniz formula. Hence `γ<0`.

Define `D₀=−γ/G₀>0`. A fifth-diagonal load changes this skipped determinant
to `det(A)(γ+D G₀)`, independently of the fourth load `C`. Thus positivity
of the full corrected origin matrix requires `D≥D₀>0`.

Conversely, the skipped four-dimensional head is positive definite exactly
when `D>D₀`. For any such `D`, place this head first, with coordinate 3
last. Its remaining scalar Schur coordinate `s` is finite. Choosing
`C=(|s|+Φ(0)²)/G₀>0` makes that coordinate
`s+|s|+Φ(0)²>0`. Therefore

`H₅(0)+G₀ diag(0,0,0,C,D) ≻ 0 ⇔ D>D₀ and C>−s(D)/G₀`,

and, in particular,

`(∃C, H₅(0)+G₀ diag(0,0,0,C,D) ≻ 0) ⇔ D>D₀`.

The previously proved origin/scale-seven capacity gap excludes every pair
with `D≥0`. Since the origin now forces `D>0`, it excludes all real pairs.

For the weighted source, `w=r sinh(ar)` and
`δ=K_a′−wG(r/2)` satisfy `0≤δ≤w a r Φ(r/2)²`. Its quadratic form is at
most `w` times the native corrected form plus
`a r Φ(r/2)²(|C|v₃²+|D|v₄²)`. This upper form is continuous at zero,
where the added term vanishes. Global weighted positivity therefore
forces full native origin positivity, hence `D>0`; the proved weighted
capacity gap gives the contradiction at every `0<a<1/2`.
