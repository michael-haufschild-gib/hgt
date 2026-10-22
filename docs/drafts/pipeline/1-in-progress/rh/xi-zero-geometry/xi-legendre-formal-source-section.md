# A non-torsion source section in the five-channel Legendre carrier

- **ID:** RH-LFSS-20261006
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) for the explicit section; CANDIDATE for its arithmetic comparison
- **Source:** `xi-legendre-integral-cylinder-comparison.md`
- **Statement:** A quadratic marked cover carries an explicit non-torsion section of one elliptic boundary channel, with formal parameter exactly equal to its covering coordinate.

## Goal

Construct an actual section, rather than inferring a class from the existence of a nonzero cohomology group. Then determine whether its global division-cover monodromy supplies the required arithmetic comparison. A section, its infinitesimal normal term, and a nonzero nearby-cycle cohomology class are distinct objects.

## Gates

- [x] Exact source-defined section and falsifiable torsion claim.
- [x] Paper proof of the explicit section and its infinite order.
- [ ] Formalize the section, its formal-group interpretation, and the exact infinite-order statement.
- [ ] Determine the global Kummer/division-cover class, including all newly ramified points.
- [ ] Obtain an arithmetic comparison using the actual Xi/Euler source, rather than a rule valid for every analytic function.

## Explicit section and paper proof

Let `q` be an indeterminate over a characteristic-zero field, and put

```
delta = q^2/(1+q^2),
lambda = 1+delta = (1+2*q^2)/(1+q^2),
E: y^2=x*(x-1)*(x-lambda).
```

The elliptic curve is the `E_(1+delta)` channel of the five-line discriminant. Its marked point and its translate by `T=(0,0)` are

```
P = (q^2/(1+q^2), q/(1+q^2)),
Q = P+T = ((1+2*q^2)/q^2, -(1+2*q^2)/q^3).
```

Substitution verifies both curve equations. The chord through `P` and `T` gives `x(P+T)=lambda/x(P)` and `y(P+T)=-lambda*y(P)/x(P)^2`, hence exactly the displayed `Q`.

At `q=0`, the Weierstrass fibre is nodal but its identity remains smooth. The projective representative of `Q` is

```
[q*(1+2*q^2) : -(1+2*q^2) : q^3].
```

It specializes to `[0:-1:0]=O`, and its standard formal-group coordinate is the exact identity `t=-X/Y=q`. The formal group exists over the power-series ring even though the central fibre is singular, by completing the smooth identity section. Its multiplication series has linear term `[n](t)=n*t + t^2*(...)`; this follows inductively from `F(S,T)=S+T+(terms of total degree at least two)`. Evaluating at `t=q` gives `[n](Q)` a nonzero linear coefficient `n` whenever `n != 0`. Thus `Q`, and consequently `P`, has infinite order. This uses an exact coefficient identity, not a height, positive form, or estimate.

The formal-group parent is standard Weierstrass geometry: Rezk's [notes](https://www-users.cse.umn.edu/~tlawson/tmf-mirror/512-spr2001-notes.pdf), Section 11.4, describes completion at the identity, including singular Weierstrass fibres; only that geometric construction is used. The five-channel gluing calculation shows that each elliptic factor embeds in its discriminant Prym, so this also gives a non-torsion Prym section after the quadratic base change.

## Arithmetic pullback, and the limitation that must survive the audit

For the uncentered Xi source `f=xi`, put `delta_p(s)=p^(-s)*f(s)` and take the explicit cover

```
q_p^2 = delta_p/(1-delta_p).
```

The point above is then defined algebraically on this cover. Its squared formal parameter is exactly `p^(-s)*f(s)/(1-p^(-s)*f(s))`. If `f(rho+z)=j*z^m+...`, its first nonzero coefficient is `p^(-rho)*j`; no simple-zero assumption is made. The involution `q_p -> -q_p` sends `Q_p -> -Q_p`.

The cover ramifies at `delta=0,1`. The second point is a smooth fibre of this individual Legendre channel but a degeneration point of the full five-channel family. Thus this is not an unramified cover of the entire smooth base of the individual Legendre scheme; unramified-section results cannot be imported without checking that distinction. Corvaja–Zannier's 2021 paper on unramified Legendre sections has a 2025 corrigendum; neither paper is used as a premise here.

Crucially, multiplication by every nonzero integer is invertible on this characteristic-zero formal group. The same section is therefore locally divisible near `q=0`. Its non-torsion global section does **not** automatically produce a nonzero local Kummer class or a flat nearby-cycle class. The positive result is an actual geometric section with a retained normal coefficient, not the previously missing monodromy naturality theorem.

Moreover, replacing `xi` by an arbitrary nonconstant analytic function leaves the construction valid. It therefore supplies no zero-location rigidity by itself. The genuinely arithmetic next step must use the Euler product or another source-specific law absent from such arbitrary pullbacks.

## Hostile verdict and next exact question

**BRIDGE.** The section construction and formal-group argument are classical mechanisms. No significant novelty is certified. The construction improves the concrete carrier by providing a section whose normal parameter is prescribed, while exposing the distinction between global non-torsion and local divisibility.

`[OPEN CORE]`: determine the global integral division-cover extension of this section and compare it, through an explicit cylinder correspondence, with the Xi prime-deletion source. No reflection-fixed comparison is assumed. A formal coordinate change or an asserted nonzero cohomology space cannot close this gap.

## Log

- 2026-10-06 — exact section and formal-parameter proof obtained; corpus/parent audit initiated. Lean verification and global arithmetic comparison remain open.

## Global two-division cover: exact paper calculation

Work over `K=C(q)`, with `A=1+2*q^2` and `B=1+q^2`. For a point away from the two-torsion, its three two-descent coordinates are the square classes of `x`, `x-1`, and `x-lambda`. For our sections these are

| Section | Three square classes | Full field of halves |
|---|---|---|
| `P` | `(B,B,1)` | `K(sqrt(B))` |
| `Q=P+T` | `(A,B,A*B)` | `K(sqrt(A),sqrt(B))` |
| `T=(0,0)` | `(A*B,1,A*B)` | not needed here |

The exceptional coordinate for `T` is `(0-1)*(0-lambda)=lambda`, giving the last row. Multiplication of the first and third rows gives the second: the additional square root in the `Q` cover includes the contribution of the two-torsion translate. It is not extra non-torsion source information.

Here is a dependency-closed justification of the field assertion. For `R=(x,y)` with no zero descent coordinate, choose roots `r_i^2=x-e_i` with product `r_0*r_1*r_lambda=-y`. Set `s_1=sum(r_i)` and `s_2=sum_{i<j}(r_i*r_j)`. Then

```
H=(x+s_2, -y-s_1*s_2),  2H=R.
```

Conversely, the tangent line `Y=l*X+m` at a half `H=(u,v)` has intersection polynomial `(X-u)^2*(X-x)`. Evaluation at each `e_i` recovers a square root of `x-e_i` from `(l*e_i+m)/(u-e_i)`, up to a common sign. The denominator cannot vanish: otherwise `H` would be a two-torsion point and `R=O`. Thus the field of any half is precisely the field generated by the three square roots. These statements and formulas are the classical parent in Zarhin, [Division by 2 on elliptic curves](https://arxiv.org/pdf/1605.09279), Theorem 2.1 and its proof.

For `Q`, use roots `a/q`, `b/q`, `a/(q*b)` with `a^2=A`, `b^2=B`; their product is `A/q^3=-y(Q)`. The polynomials `A,B` have simple, disjoint roots. Odd orders at these roots show that `A`, `B`, and `A*B` are nonsquares. Consequently the degree is four and the deck group is `(Z/2)^2`. The cover branches exactly at `q=±i` and `q=±i/sqrt(2)`; infinity has even orders and algebraically closed residue field, hence no ramification. Riemann–Hurwitz gives `2g-2=4*(-2)+4*2=0`, so its smooth compactification has genus one. For `P` the quadratic cover has exactly two branch points and genus zero. These are exact ramification identities, not estimates.

A smaller statement can be formalized directly with the actual elliptic group law, without importing full two-descent: **there is no `R in E(C(q))` with `R+R=Q`.** Indeed `R=O` or `y(R)=0` doubles to `O`, whereas `Q` is affine. Otherwise the duplication formula gives

```
x(2R)-1 = ((x(R)^2-2*x(R)+lambda)/(2*y(R)))^2.
```

But `x(Q)-1=B/q^2`, which is not a square because `B` has order one at `q=i`. This is the exact theorem selected for Lean verification.

**Hostile verdict: BRIDGE.** The mechanism is classical two-descent. The actual group-law conclusion is useful for auditing the carrier, but is neither a new theorem of elliptic geometry nor an RH result. The deep corpus search was partial; lexical `ratOrd` search found the existing exact rational-order machinery. No completeness claim is made for that search.

**Pullback limitation.** Non-torsion persists under field extension; non-divisibility need not. A nonzero class over `C(q)` cannot be promoted to a nonzero class after the meromorphic Xi pullback without another argument. Locally at `q=0` the whole division tower is split by formal multiplication, so additional division levels do not restore a local obstruction there.

## Lean checkpoint and next geometric obstruction

2026-10-07: `HTGeometry/LegendreSourceKummer.lean` constructs the actual nonsingular point `sectionQ` and proves `sectionQ_not_double` for every point of its actual affine group. The exact rational-order obstruction and duplication identity are included. Direct `lake env lean` passed without warnings, targeted `lake build --old` passed, and three principal declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The leaf is wired into the umbrella. Global lint reports nine unrelated umbrella omissions; it is not globally clean. Infinite order, complete splitting-field identification, and non-divisibility after the Xi pullback are not claimed Lean-closed.

The local scalar charge-tower idea is already covered by `DeckChargeInvariant.lean` and `XiDeckChargeUnitGaugeClassifierUniversalityLaw.lean`; rephrasing it is rediscovery. The next exact source-geometric result is recorded in `xi-prime-source-toric-closure.md`: the full polynomial-relation ideal of `xi(s)*n^(-s)`, its infinite-generator blowup, and the exclusion of isogenies between distinct prime-marked Legendre families. Its paper proof uses the corpus's unconditional Xi hypertranscendence; formalization remains pending.
