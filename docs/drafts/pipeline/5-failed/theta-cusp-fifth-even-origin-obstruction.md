# Fifth even theta source: the origin forces a positive fifth load

- **Stage:** 5-failed; every real constant diagonal pair refuted in Lean.
- **Wall:** Σ6; the integrated rank-nine sign remains open.
- **Claim:** No real constant pair of fourth and fifth diagonal loads gives global pointwise positivity, including the actual weighted representative at any critical aperture.
- **Positive survivor:** Exact two-load positivity region of the full fifth block at the origin, with a sharp, strictly positive fifth-load threshold; paper proof and Lean formalization complete.

Write `m_j=(-1)^j D_t^(2j)[Φ(t)Φ(−t)]|₀`,
`A=[m_(i+j)]_(0≤i,j≤2)`, `b=(m₄,m₅,m₆)`,
`γ=m₈−bᵀA⁻¹b`, and `G₀=3Φ(0)²`. The native head `A` is positive
definite. The principal matrix on indices `{0,1,2,4}` has determinant
`det(A)γ`.

The complete modular source gives `m_j=M²p_j(X)` through `j=8`, with
`19.1<X<19.2` and `M>0`. Let `d=det[p_(i+j)]_(0≤i,j≤2)` and
`u=(p₄,p₅,p₆)`. The skipped determinant is

`M⁸[d p₈−uᵀ adj([p_(i+j)])u] < 0`.

The exact polynomial certificate substitutes `X=(191+z)/10`,
`0≤z≤1`, expand, and bound the positive coefficients of degrees 21 and 22
by their values at one. The constant term and all remaining coefficients
give strict negativity. The complete source identity for order sixteen
follows from the even seam derivatives and the finite Leibniz formula.
Hence `γ<0`.

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

The same scale-seven test vector has **positive** native energy at the origin.
Its normalized energy is a degree-ten polynomial with positive coefficients
after `X=(191+z)/10`, `z≥0`; the complete even seam identities identify it
with the actual source form. Thus this vector does not extend the diagonal
obstruction to an arbitrary constant matrix correction.

Lean: `ThetaCuspSections/FifthEvenOriginObstruction.lean`, namespace
`GaloisForLFunctions.ThetaCuspSections.EvenFiveOrigin`.
`originFifthThreshold_pos` and `origin_fifth_load_required` prove the
positive origin requirement. `origin_posDef_iff` and
`exists_positive_origin_repair_iff` give the exact positive survivor.
`constant_source_repair_fails` and `constant_weighted_repair_fails` exclude
all real constant pairs. All six public axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. The canonical Lean check passes, and
the owner umbrella imports the module.

`boundary_direction_positive_at_origin` proves the additional directional
positivity; its axiom audit also contains only the same three standard axioms.

The [coupled repair](../3-formalized/theta-cusp-fifth-even-coherent-origin-tail-repair.md)
escapes this diagonal obstruction near the origin and on a cofinal tail.
Its two positive loads annihilate the scale-seven vector and preserve all
mixed integrals. The prescribed last-pair load alone fails; the two-load
common kernel is positive. These actual source statements are formalized.
The [common-coefficient route](theta-cusp-fifth-even-common-coupled-obstruction.md)
is now refuted globally. The explicit
[unequal repair](../3-formalized/theta-cusp-fifth-even-unequal-origin-repair.md)
retains the formalized origin-and-tail conclusions but fails the
[sixth-degree test](theta-cusp-fifth-even-large-coupled-load-obstruction.md).
Smaller unequal coefficients remain open.
