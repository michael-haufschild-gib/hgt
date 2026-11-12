# Discriminants and the complete census after Jensen folding

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1011/fable.md`, §§10.3(F), 10.5(7).
- **Statement:** Full centered Jensen discriminants are nonnegative, while
  their quotient equations retain the entire off-line divisor census.

## Exact statements

Write `μ_k=xiMoment(1/2,k)`, `m_n=μ_(2n)/μ₀`, and normalize the centered
reversed Jensen sections by `P_d=R_d/μ₀`. There are monic degree-`n` equations
`E_n,O_n` with

```
P_(2n)=E_n(X²),                 P_(2n+1)=X O_n(X²),
disc(P_(2n))=4^n m_n disc(E_n)²,
disc(P_(2n+1))=4^n ((2n+1)m_n)³ disc(O_n)².
```

Every `m_n` is positive. Full discriminants, including the unnormalized ones,
are nonnegative; their vanishing is exactly quotient inseparability.
Degree zero and repeated roots are included.

Let `Q_d` count original first-quadrant roots, `M_d` quotient non-real roots,
and `N_d` original non-real roots, all with multiplicity. Then

```
N_d = 2 M_d = 4 Q_d,
M_d is nondecreasing,
sup_d (2 M_d) = the entire off-line ξ-divisor multiplicity in ℕ∞.
```

A finite off-line divisor has size `4m` and eventually `M_d=2m`.
An infinite off-line divisor forces `M_d` to infinity. Conjugation parity on
full equations is always `(-1)^(N_d/2)=1`.

The field `K=ℚ(m_n : n≥0)` equals the coefficient field of all even quotient
equations. Odd quotient coefficients also belong to `K`. There are `s_n,t_n∈K`
with

```
disc(P_(2n))   = m_n s_n²,
disc(P_(2n+1)) = (2n+1)m_n t_n².
```

Thus the nonzero full discriminant square classes are `m_n` and `(2n+1)m_n`.
The field adjoining every full monic discriminant square root to `K` lies in
ℝ; conjugation fixes it pointwise. No nonvanishing assumption is used.

## Proof

Parity and positivity of the Riemann-kernel moment polynomial exclude nonzero
imaginary roots and partition non-real roots into free four-point orbits.
Squaring identifies first-quadrant roots with upper quotient roots. The map
is unramified away from zero, so multiplicities agree; the forced odd-degree
zero contributes no quadrant multiplicity. Conjugation doubles the upper
quotient count. Existing monotone Jensen exhaustion then gives the full
finite-or-infinite divisor alternative.

For every monic real `Q` of degree `n`, root products give
`disc(Q(X²))=4^n(-1)^n Q(0)disc(Q)²` and
`disc(XQ(X²))=4^n(-1)^n Q(0)³disc(Q)²`.
The actual quotient constant terms are `(-1)^n m_n` and
`(-1)^n(2n+1)m_n`, giving the displayed identities and collision criterion.

Every quotient coefficient is a rational multiple of a normalized moment.
Conversely `E_n(0)=(-1)^n m_n` recovers every moment generator. Discriminants
descend through coefficient maps. The square witnesses are
`2^n disc(E_n)` and `2^n(2n+1)m_n disc(O_n)`. Every complex square root of a
nonnegative real number is real, giving the whole discriminant-field result.

## Formalization

All modules lie in `formal/GaloisForLFunctions/GaloisTheoryOfZeros/` and are
wired into its umbrella:

- `FoldedDiscriminant`: universal folding identities and separability criterion.
- `JensenQuartetExhaustion`: quartet census, parity, infinite exhaustion.
- `CenteredJensenDiscriminant`: actual quotient equations, discriminants,
  nonnegativity and collision criteria.
- `FoldedJensenExhaustion`: `foldedJensenNonrealCount_eq_two_mul`,
  `iSup_two_mul_foldedJensenNonrealCount`, `folded_exhaustion_dichotomy`.
- `CenteredJensenDiscriminantField`:
  `evenQuotientCoefficientField_eq_normalizedMomentField`,
  `even_discr_moment_square`, `odd_discr_moment_square`,
  `conj_fixes_normalizedDiscriminantField`.

Source-file audits passed with `lake --old env lean`. Audited main dependency
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary and positive content

Full conjugation parity is trivial at every degree, and its discriminant
extension is real. The positive content is the exact folded census of the
infinite divisor, the exact coefficient field, and the moment square classes.

These results concern centered reversed sections. Eventual nonvanishing and
other shifted Jensen families remain open. No automorphism action on limiting
ξ zeros is inferred from the approximant fields.
