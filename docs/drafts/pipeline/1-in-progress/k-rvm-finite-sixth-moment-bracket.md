# K-RVM finite sixth-moment bracket

- **Stage:** 1-in-progress
- **Route:** K-RVM
- **Scientific status:** An unconditional Lean theorem gives a nonnegative finite head whose first three power sums exactly match the completed source's quadratic, quartic, and sixth traces. The source lies strictly inside an explicit three-moment admission cone, and every triple in that cone has such a finite head. The full moment sequence, cofinite reserve, Xi divisor identity, and RH remain open.

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

Consequently the **source lower bracket** `G ≥ C` is equivalent to

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

Writing `k=N-1`, the defect has a universal bound from a sharp cubic factor

```text
27 k · [k a b (a-b)²] ≤ 4 F²,
```

because `4a³-27b(a-b)²=(3b-a)²(4a-3b)≥0` and `F≥k a²`.
Since the source reverse head has `k≥9`, the strengthened source inequality
`247F²≤243EG`, equivalently `247 M₁²≤243 M₀M₂` for the unhalved source
moments, proves the lower bracket. This strength does not follow from strict
Hankel positivity alone.
`FiniteReverseResidualSeam.lean` proves both the universal defect bound and
the conditional implication from this strengthened source inequality to
`G≥k a³+b³`.

The existing Stein source proof contains more information than bare Hankel
positivity. Let `R_j` denote its raw theta moments, `H=M₀M₂-M₁²`, and
`U=9R₁R₃-14R₂²`. Its exact cumulant identity and relaxed fourth-moment
concentration imply `1080 R₀² H≥U`. First-atom Stein bounds and tail
domination give a positive rational lower bound for `U/R₀²`. A separate
existing source theorem gives `M₁<17/200000`. The resulting exact rational
comparison

```text
(4/243)(17/200000)² ≤
  [9(423/5000)(441/200000)
    - 14((3005/2997)(5457/500000))²]
  / [1080((3005/2997)(18303/10000))²]
```

checks in Lean. `XiPrimeMarkedFiniteSixthLowerBracket.lean` formalizes the
transfer through raw-moment bounds, proves `247 M₁²≤243 M₀M₂` for the
actual completed source, and applies it to the positive reverse endpoint.
The unconditional theorem `exists_routeKReverseTwoLevelHead_below_sixth`
gives `C≤G` together with exact first and second power sums.

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

**Continuous finite-fold selector, Lean proved in the positive scalar cone.**
For each `x`, set `r(x)=A(x)²/B(x)`. Begin with a two-atom reverse residual
vector and add counts one at a time: at threshold `k`, retain the old branch
when `r≤k` and select the `(k+1)`-atom branch when `r>k`. The atom-level seam
proves the complete padded vectors agree when `r=k`. Finite induction using
piecewise continuity proves the selector is continuous for any continuous
`A,B` with `A>0,B>0`; `FiniteReverseResidualSelector.lean` contains this
theorem. On the admitted source interval, the residual cone bounds rank
between two and `N-1`. `FiniteReverseResidualSelector.lean` proves the fold
selects an `n` satisfying `n-1 < r ≤ n` whenever the rank lies in its finite
window. `FiniteReverseResidualBranchMoments.lean` proves the corresponding
small atom is nonnegative and the complete padded vector has exactly the
prescribed first two power sums, including when `r=n`.

The same branch module proves uniqueness of any ordered two-level head with
fixed count and first two moments. The exact identity
`(n-1)(a-b)²=nB-A²` identifies its deviation with the nonnegative square
root in the canonical reverse formula. It also proves the effective rank of
such a head lies in `[n-1,n]`, with the lower equality occurring exactly
when `b=0`. The `ordered_twoLevel_selector_eq` theorem proves any admitted
ordered two-level endpoint equals the finite selector's complete padded
vector, including this zero-atom seam.
`FiniteReverseResidualEndpointDeletion.lean` instantiates this theorem for
both source head shapes after removing the distinguished atom, proves their
common-count endpoint admission,
and transfers their exact cubic sums to the selector. The positive residual
interval follows from `FiniteOneHeadResidualWindow.lean`. The continuous
cubic observable and IVT are in `FiniteReverseResidualSixthIVT.lean`.

`XiPrimeMarkedFiniteSixthExactCarrier.lean` combines these steps with the
actual source lower and upper brackets. Its unconditional theorem
`exists_routeKFiniteSixthMatchedHead` provides a count `N≥10`, a
nonnegative distinguished atom, and `N-1` nonnegative residual atoms with
exact mass `E`, energy `F`, and cubic trace `G`. The carrier is finite and
matches only these three source moments.

`XiPrimeMarkedFiniteSixthStrictCone.lean` upgrades the endpoint relation to a
strict source gap. Its proof uses the strict source bound
`M₁ < 17/200000` together with the previously proved Stein lower margin;
this yields `247F² < 243EG`, not merely `≤`. For arbitrary real `E,F,G`,
the theorem `exists_finiteThreeMomentHead_of_strictCone` gives an exact
nonnegative unit-multiplicity carrier whenever

```text
E > 0,  F > 0,  9F < E²,  247F² < 243EG,  G² < F³.
```

The proof combines a strict reverse-head lower bracket, a strict large-count
upper bracket, and the continuous residual selector. These inequalities are
strict at the actual completed source, so its three-moment target has room
for sufficiently small changes in all three coordinates. The next source
task is to choose a positive-scale cofinite RVM/cycle reserve with its
second, fourth, and sixth trace contributions inside that room, then use the
general carrier theorem on the residual moments. This would extend literal
K-RVM incidence through order six; it would still not control the full
moment sequence or Xi divisor.

Even an exact finite sixth-moment match would leave the full moment sequence,
cofinite reserve, Xi divisor identity, and RH open.

The selector has an exact integer-rank seam. At residual mass
`A>0` and energy `B=A²/k` (`k≥2`), the `k`-atom reverse branch has deviation
zero and gives `k` atoms `A/k`. The `(k+1)`-atom reverse branch has deviation
`A/k` and gives `k` atoms `A/k` plus one zero. Their padded vectors agree;
matching just their first two moments would not establish continuity.
`FiniteReverseResidualSeam.lean` proves both deviations and all four atom
identities; `FiniteReverseResidualSelector.lean` lifts this to equality of
the padded vectors and continuity of the finite fold.

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
each seam prevent a first crossing into `x<a`. This paper monotonicity
argument is optional for the IVT step: continuity and the endpoint brackets
already suffice. The source-interval IVT is now formalized without this
monotonicity argument.
