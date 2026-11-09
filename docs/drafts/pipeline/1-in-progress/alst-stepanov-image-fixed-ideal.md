# The exact image of polynomial Stepanov syzygies

- **ID:** alst-stepanov-image-fixed-ideal
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE
- **Statement:** Over `ℤ`, auxiliaries `Σ_i f_i ψ_q(g_i)` with every global mixed first-factor Euler moment below order `r` zero are exactly `(X_j^q−X_j : j∈σ)^r`, for every `q`. For `q≥2` and nonempty finite prime support with least prime `p`, their least nonzero arithmetic length is `p^(qr)`; all minimizers are `c(X_p^q−X_p)^r` with `c≠0`.

## Significance and novelty
Polynomial syzygies impose multiplicity on the full affine fixed locus,
including coordinate hyperplanes. Torsion vanishing alone costs
`p^((q−1)r)`. Thus the construction pays an extra factor `p^r` and cannot
produce torsion-only minimizers. This realizes exact (S1) without cheap
(S2); it does not distinguish ζ from other Euler products on these primes.
Corpus searches for diagonal syzygies and Adams fixed ideals found torsion
resolution and the earlier jet transfer, but no pre-existing image theorem.
The image classification and sharp filtration count together once.

## Paper proof
Write `Q(U,V)=Σ_i f_i(U)g_i(V)`. Its diagonal Euler jets are the moment
polynomials. Over the coefficient domain `ℤ[V]`, ordinary jets below `r`
vanish exactly for membership in `(U_j−V_j)^r`: translate to the origin,
then use derivative coefficients to detect every term of degree below `r`.
Positive integer factors cancel without division. Multiplication by `U_j`
is injective modulo this ideal power since `V_j≠0`; induction therefore
identifies the Euler and ordinary jet criteria, even though `V_j` is not a
unit.

The substitution `U↦X`, `V↦X^q` is surjective, using the outer variables
as a section. It sends the diagonal ideal to `(X_j^q−X_j)`. Ideal images
commute with powers, and expansion in outer monomials expresses every
bivariate polynomial as a finite paired sum. This proves both image
inclusions, including `q=0,1`.

More generally, let `G_p` have leading arithmetic monomial `X_p^q` with
coefficient one. The polynomials
`B_a=∏_p X_p^(a_p mod q)G_p^(a_p div q)` form an integral basis: subtracting
the leading coefficient strictly lowers integer arithmetic length.
Triangularity preserves length exactly. Put `N_r=spanℤ{B_a:Σ floor(a_p/q)≥r}`.
Factorization gives `N_r⊆(G_p)^r`. Conversely, multiplication by `G_p`
sends `B_a` to `B_(a+q e_p)`. Induct on `r`, expand the final factor of an
ideal product in the generators, and apply this shift to obtain
`(G_p)^r⊆N_r`.

For `G_p=X_p^q−X_p`, `q≥2`, every surviving Newton index has weight at
least `p_min^(qr)`. The pure generator power attains equality. Below this
cutoff only the index `qr e_p` can survive, since prime weights uniquely
determine exponent vectors. Hence the entire minimal filtered piece is
`ℤ·(X_p^q−X_p)^r`.

## Lean status
`ThePolynomialImageOfStepanovSyzygies.mem_adamsFixedIdeal_pow_iff_stepanov_syzygies`
passed its final plain check; its transitive axioms are `propext`,
`Classical.choice`, `Quot.sound`. Integral diagonal and Euler criteria are
verified. Generic Newton filtration and sharp cost are written but remain
under verification. Nothing is counted until all required audits pass.
