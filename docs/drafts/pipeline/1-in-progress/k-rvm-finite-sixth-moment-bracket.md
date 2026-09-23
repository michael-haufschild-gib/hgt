# K-RVM finite sixth-moment bracket

- **Stage:** 1-in-progress
- **Route:** K-RVM
- **Scientific status:** The reverse lower head, arbitrarily large upper heads, residual admission interval, and cubic tangent law are formalized. The source sixth-moment lower bracket and a continuous residual selection remain open in Lean.

Let `E = routeKQuarticHalfMass`, `F = routeKQuarticHalfEnergy`, and
`G = normalizedPrimeArchMoment 2 / 2`. The current source proofs give
`E > 0`, `F > 0`, `E² > 9F`, `F² < EG`, and `G² < F³` without RH.

For `N = floor(E²/F) + 1`, the reverse two-level head has `N - 1` copies of
`a = (E + d)/N` and one copy of `b = (E - (N - 1)d)/N`, where
`d² = (NF - E²)/(N - 1)`. Its two first power sums are exactly `E,F`, and
`0 ≤ b < a`. Thus the source has an admissible head with `N ≥ 10`. This is
proved in `XiPrimeMarkedQuarticEffectiveRank.lean` and
`FiniteThreeLevelReverseEndpoint.lean`.

The reverse third power sum `C = (N - 1)a³ + b³` satisfies the exact identity

```text
E C - F² = (N - 1) a b (a - b)².
```

Consequently the **open source lower bracket** `G ≥ C` is equivalent to

```text
E G - F² ≥ (N - 1) a b (a - b)².
```

Strict Hankel positivity `EG > F²` alone does not supply this quantitative
gap when `b > 0`. The reverse cubic is strictly below the equal-share cubic;
their doubled-cubic difference is exactly
`2(N - 1)(N - 2)(a - b)³/N²`. The positive spectral cone is preserved on a
three-level plateau interval below `E/(N - 1)` whenever its endpoints are
positive. These identities and the interval theorem are formalized in
`FiniteThreeLevelReverseEndpoint.lean`.

The upper two-level head can now be chosen above `G` at **every sufficiently
large prescribed count**; `exists_routeKFiniteHead_sixth_surplus_above` is
formalized in `XiPrimeMarkedFiniteSixthHeadBudget.lean`. Choose its count
`N` at least the reverse count and pad the reverse head with zeros. The two
heads then have the same number of slots, mass, and energy.

Fix one atom at `x` and leave `A(x)=E-x`, `B(x)=F-x²` for the other `N-1`
slots. Their Cauchy budget

```text
Q(x)=(N-1)B(x)-A(x)²
```

is concave. The exact chord identity proves `Q(x)≥0` between admitted
endpoints. A separate upper-cone gap `A(x)²-B(x)` stays nonnegative when
the upper endpoint is below `E/2`; the residual effective rank remains at
least two when it is below `E/3`. The source inequality `E²>9F` puts the
upper two-level large atom below `E/3`. The endpoint ordering follows from
the formal maximal-coordinate bound `x≤twoLevelLarge E F N` whenever
`Q(x)≥0`. These scalar statements are formalized in
`FiniteOneHeadResidualWindow.lean`.

**Continuous residual-selection candidate, Lean open.** For each `x` in
the interval, let `m(x)=ceil(A(x)²/B(x))`. Use `m(x)-1` equal larger residual
atoms and one smaller atom, padding with zeros to `N-1` slots. The cone
inequalities make these atoms nonnegative. At an integer rank `r=k`, the
branch from below has `k` equal atoms; the branch from above limits to
those same `k` atoms plus one zero. Thus the padded residual vector is
continuous across its finite rank changes. The rank ratio is
nondecreasing for `x≥F/E`, and the initial reverse atom satisfies
`a≥F/E`, so each seam is crossed at most once. On each smooth branch,
if `a(x)≥b(x)` are the residual values, first/second-moment differentiation
gives `d/dx [x³+(m-1)a³+b³] = 3(x-a)(x-b)`.
`FiniteMomentCubicTangent.lean` proves this algebraic tangent law.
Starting at the reverse head, the distinguished atom equals the residual
maximum; that maximum decreases while `x` increases, so the derivative is
nonnegative. At the final two-level large atom, the residual becomes
`N-1` equal small atoms. Formalizing the continuous selection and its
order preservation would turn the still-open source lower bracket into an
exact sixth-moment carrier by the intermediate-value theorem.

Even an exact finite sixth-moment match would leave the full moment sequence,
cofinite reserve, Xi divisor identity, and RH open.

The proposed selector has an exact integer-rank seam. At residual mass
`A>0` and energy `B=A²/k` (`k≥2`), the `k`-atom reverse branch has deviation
zero and gives `k` atoms `A/k`. The `(k+1)`-atom reverse branch has deviation
`A/k` and gives `k` atoms `A/k` plus one zero. Their padded vectors agree;
matching just their first two moments would not establish continuity.

On a nondegenerate branch with `j` equal residual atoms `a>b`, differentiating
`j a+b=E-x` and `j a²+b²=F-x²` gives

```text
a' = (b-x)/(j(a-b)),    b' = (x-a)/(a-b),
(x³+j a³+b³)' = 3(x-a)(x-b).
```

The residual rank `r=(E-x)²/(F-x²)` has
`r' = 2(E-x)(Ex-F)/(F-x²)²`. At the initial reverse head, its distinguished
maximum satisfies `x=a≥F/E`, since every initial atom is at most `a`.
Hence `r` is nondecreasing along the proposed interval. Where `x≥a`, the
formula for `a'` gives `a'≤0`; the initial equality `x=a` and continuity at
each seam prevent a first crossing into `x<a`. This is a paper argument for
cubic monotonicity across finitely many rank branches, subject to the
remaining formal endpoint, positivity, and gluing checks. It supplies no
source-specific proof of `G≥C`.
