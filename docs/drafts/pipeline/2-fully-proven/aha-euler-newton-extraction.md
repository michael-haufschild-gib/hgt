# Euler operators extract the residue Newton coordinates

- **ID:** AHA-EULER
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/aha-adams-multiplicity-cost.md
- **Statement:** Fourier averaging of explicit shifted Euler derivatives extracts each residue Newton coefficient with normalization `d^(|P|+|α|) ∏_p α_p!`.

## Exact statement

Let `P` be a finite coordinate set, `d≥1`, and
`F(z)=Σ_n c_n ∏_p z_p^v_p(n)` a finite polynomial. Represent a residue
vector `b` by integers `0≤b_p<d`. Write `E_p=z_p ∂/∂z_p` and set

`L_(b,α)=∏_p ∏_{0≤j<α_p}(E_p−b_p−dj)`.

At the full grid of `d`th roots of unity,

`Σ_t conj(χ_b(t)) L_(b,α)F(t)`
`= d^|P| d^|α| (∏_p α_p!) Σ_{v(n)≡b (mod d)} c_n ∏_p binom(⌊v_p(n)/d⌋,α_p)`.

## Proof [PROVED HERE]

Every monomial is an eigenvector of `E_p` with eigenvalue `v_p(n)`.
Thus `L_(b,α)` multiplies its coefficient by
`∏_p ∏_{j<α_p}(v_p(n)−b_p−dj)`. These operators commute because they
are diagonal on the monomial basis.

Fourier orthogonality eliminates all monomials whose residue vector is not
`b`, and multiplies the retained sum by `d^|P|`. For a retained monomial,
write `v_p(n)=b_p+d k_p`. Its local factor is

`∏_{j<α_p} d(k_p−j)=d^α_p α_p! binom(k_p,α_p)`.

This identity also holds when `k_p<α_p`, because the product contains
the zero factor with `j=k_p`. Multiplying the coordinate identities gives
the stated normalization. Finite linearity completes the proof.

## Multiplicity interface

Each factor is a differential operator of order one. A derivation sends
the `(m+1)`st power of any ideal into its `m`th power: expand a product
of `m+1` ideal elements by Leibniz, then use additivity. Multiplication
and subtraction preserve ideal membership. Consequently a word of `k`
shifted Euler factors sends the `(m+k)`th point-ideal power into its
`m`th power. This is the precise order loss needed by AHA-JETS.

## Arithmetic consequence [PROVED HERE]

For an auxiliary supported on `0<n<2^(dr)`, membership in the `r`th
point-ideal power at every torsion point forces every Euler word of length
below `r` to evaluate to zero. The extraction identity then kills every
Newton coefficient of order below `r`; its scalar normalization is nonzero
over `ℂ`. `arithmeticNewton_vanishing_iff` forces every original coefficient
to vanish. Thus a nonzero auxiliary with full algebraic multiplicity `r`
must have support reaching `2^(dr)`.

For polynomials, full analytic mixed derivatives below order `r` vanish
exactly when all centered coefficients of total degree below `r` vanish:
the derivative is that coefficient times the nonzero multi-index factorial.
Translation identifies this coefficient condition with the `r`th power of
the origin ideal, hence with the point-ideal power before translation.
Coordinate relabeling preserves ideal powers, so the same criterion holds
on the finite prime-coordinate space. The matching boundary example is a
separate claim.

## Boundary [PROVED HERE]

The integer polynomial `(X^d−1)^r` is monic of degree `dr`. Under the
prime-two coordinate, its top frequency is `2^(dr)`. Every `d`th root of
unity is a simple root of `X^d−1` in characteristic zero, so it has exact
multiplicity `r` in the boundary polynomial. In any number of coordinates,
`(X_i^d−1)^r` belongs to the `r`th point-ideal power at every torsion point.
Thus the support threshold is attained; the argument gives no height gain.

## Scope

The ingredients are classical finite Fourier inversion, falling factorials,
and Leibniz. The contribution is the exact arithmetic normalization and its
connection to the already formalized Newton sampling interface. No gain in
integer auxiliary height or in the classical multiplicity bound is asserted.
Lean formalization follows in `ArithmeticHarmonicAnalysis/`.
