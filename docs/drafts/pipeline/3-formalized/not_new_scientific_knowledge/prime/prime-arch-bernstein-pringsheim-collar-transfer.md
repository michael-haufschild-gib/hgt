# Prime--archimedean Bernstein Pringsheim collar transfer

- **ID:** `prime-arch-bernstein-pringsheim-collar-transfer`
- **Stage:** 3-formalized
- **Type:** top-down RH bridge / analytic-continuation criterion
- **Status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean status:** fully formalized — see the 2026-08-19 section

## Setup

Let

\[
 \Pi_n=\texttt{primeArchEndpointBernsteinPurity}(n)\ge0,
 \qquad
 \chi(z)=\sum_{n\ge0}\Pi_nz^n.                           \tag{1}
\]

The live Lean corpus proves that there is a unique exact real Abel radius `R_A` satisfying

\[
 r_0:=\frac{250000}{251001}<R_A\le1,
 \qquad
 \mathrm{RH}\iff R_A=1.                                 \tag{2}
\]

The same `R_A` is the complex power-series radius of `(1)`.  Indeed, for `|z|<R_A`, choose a real
`t` with `|z|<t<R_A`; summability of `sum Pi_n t^n` gives absolute convergence at `z`.  For every
real `t>R_A`, the defining critical-radius theorem gives divergence, so the complex radius cannot
exceed `R_A`.

## Collar hypothesis

Assume that there are a connected open set `U subset C` and a holomorphic function `F : U -> C`
such that

\[
 [r_0,1)\subset U                                      \tag{3}
\]

and `F` agrees with the germ `(1)` on a nonempty open set immediately to the left of `r_0`.  More
intrinsically, `F` is one coherent holomorphic continuation of the germ `(1)` through the entire
positive real collar `[r_0,1)`.

Then

\[
 \boxed{\text{collar hypothesis}\Longrightarrow\mathrm{RH}.}    \tag{4}
\]

The endpoint `1` itself is deliberately excluded.  No convergence or regularity at `t=1` is
required.

## Proof

Suppose RH is false.  Equation `(2)` then gives

\[
 r_0<R_A<1.                                               \tag{5}
\]

Because all Taylor coefficients `Pi_n` are nonnegative and the radius is finite and positive, the
Vivanti--Pringsheim theorem says that the positive boundary point `z=R_A` is a singular point of
the analytic germ `(1)`: the germ has no holomorphic continuation to a neighborhood of `R_A`.

But `(3)` puts `R_A` in `U`.  The agreement to the left of `r_0`, connectedness of `U`, and the
identity theorem continue the same germ along the real segment to the holomorphic germ of `F` at
`R_A`.  This is the forbidden continuation.  Hence `(5)` is impossible, `R_A=1`, and `(2)` gives
RH.

## Concrete source form

The companion paper theorem

`prime-arch-bernstein-legendre-double-source-kernel.md`

proves the unconditional value relation

\[
 \chi(t)=(L_R\otimes L_R)
 \frac1{\sqrt{1-2t(1-x-y+2xy)+t^2(1-x-y)^2}},            \tag{6}
\]

where `L_R` is the endpoint-normalized prime--Gamma moment functional.  Therefore a concrete
predecessor of RH is:

```text
the independently evaluated prime--Gamma double kernel in (6)
is holomorphic on one connected neighborhood of [r0,1)
  -> no positive Pringsheim singularity occurs before 1
  -> R_A = 1
  -> RH.
```

For a normalized reciprocal-square atom `u`, the conjugate-reflected denominator factors as

\[
 (1-(|u|+|1-u|)^2t)(1-(|u|-|1-u|)^2t).                  \tag{7}
\]

Thus the missing source theorem is exactly exclusion of a reflected algebraic pinch in the thin
collar, not a separate estimate for every `Pi_n`.

## Circularity firewall

The abstract collar hypothesis is equivalent in strength to RH if `F` is allowed to be defined by
the susceptibility series itself.  That use is forbidden.  An admissible provider must construct
`F` from an independent expression involving the continued prime--Gamma trace, the exact theta
source, or a source-side contour/integral formula, and prove its collar holomorphy before invoking
Pringsheim.

In particular, the provider may not use:

- Xi zero locations or real-rootedness;
- the attained amplitude `B` selected under false RH;
- the exact Abel radius or an RH-equivalent coefficient bound;
- a positive representing measure whose existence is already equivalent to RH;
- analytic continuation defined only by the coefficients `Pi_n`.

## Relation to the current competing route

This route is analytically orthogonal to sublinear finite-coefficient or anisotropic-mesh flux
estimates.  It asks for source holomorphy of one algebraic double-kernel value, not a growth bound
for the coefficient sequence or the Li-type quantities currently being studied elsewhere.

## Formalization target

1. Define the complex susceptibility germ on the unconditional disk.
2. Prove that `PrimeArchEndpointBernsteinAbelCriticalRadius R_A` is its complex radius.
3. Add a reusable Vivanti--Pringsheim theorem for nonnegative real coefficients.
4. Define the coherent collar-continuation predicate using the existing `ContinuesAcross` pattern
   from `U0/U0NaturalBoundary.lean`.
5. Prove `(4)` and splice it to the Legendre double-source kernel.
6. Do not formalize until targeted Lean verification is again permitted.

## Literature calibration

Vivanti--Pringsheim states that a power series with nonnegative real coefficients and finite
positive radius `R` is singular at the positive real point `R`; see Flajolet--Sedgewick,
[Analytic Combinatorics, Chapter IV](https://algo.inria.fr/flajolet/Publications/AnaCombi/anacombi.html),
or Melczer, Proposition 2.4 in
[An Invitation to Analytic Combinatorics](https://melczer.ca/files/Melczer-SubmittedManuscript.pdf).
The theorem is classical.  The project contribution is the exact splice from the formal
prime--Gamma susceptibility radius to the source-specific algebraic kernel `(6)`.

## Gates

- [x] complex radius identified from the formal real critical-radius interface
- [x] Pringsheim collar implication proved on paper
- [x] endpoint `t=1` removed from the hypothesis
- [x] concrete double-source provider interface identified
- [x] circularity firewall stated
- [ ] general Pringsheim theorem formalized in Lean
- [ ] independent prime--Gamma collar continuation
- [ ] RH

## Meromorphic strengthening

The companion theorem
`prime-arch-bernstein-half-order-pringsheim-singularity.md` strengthens the positive-boundary
singularity used here. Under false RH the susceptibility has the exact local form

\[
 \chi(t)=H(t)+\frac{A(t)}{\sqrt{1-B^2t}},\qquad A(B^{-2})>0,
\]

and in particular satisfies

\[
 \sqrt{1-B^2t}\,\chi(t)\longrightarrow c_B>0
 \quad(t\uparrow B^{-2}).
\]

A meromorphic germ has integer local order, so it cannot have this finite nonzero half-order
limit. Consequently the collar provider need only construct one coherent **single-valued
meromorphic** continuation; isolated integer-order poles are allowed. This strictly weakens the
holomorphic hypothesis in the present card.  The source-side value relation
`prime-arch-moment-pole-residue-pinch-law.md` identifies the corresponding ordinary moment pole,
its residue `-R` times multiplicity, and the exact nonzero coefficient `A(B^{-2})`.

## 2026-08-19 — unconditional Lean formalization (stage 3)

All five formalization targets are met.  `#print axioms` on each capstone reports only
`propext, Classical.choice, Quot.sound`.

**New reusable infrastructure** (mathlib has neither statement)

| Statement | Lean declaration |
|---|---|
| the analytic-continuation predicate | `GaloisForLFunctions.HTGeometry.ContinuesAcross` |
| the sum of a real power series is analytic on its disk | `analyticOnNhd_realSeriesSum` |
| the shifted (Taylor) coefficients `b_k = ∑_n C(n,k) a_n r^{n-k}` and their Tonelli laws | `shiftedCoeff`, `summable_shiftedCoeff`, `tsum_shiftedCoeff`, `summable_of_summable_shiftedCoeff`, `hasSum_shiftedCoeff_complex` |
| **Vivanti--Pringsheim** | `GaloisForLFunctions.HTGeometry.not_continuesAcross_of_nonneg` (`HTGeometry/VivantiPringsheim.lean`) |
| analytic continuation along a real segment, via a convex tube | `GaloisForLFunctions.HTGeometry.eventuallyEq_of_segment` (`HTGeometry/SegmentAnalyticContinuation.lean`) |

**The card** — `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinPringsheimCollar.lean`

| Card item | Lean declaration |
|---|---|
| the complex susceptibility germ `χ(z) = ∑_n Π_n z^n`, eq. (1) | `primeArchEndpointBernsteinSusceptibility` |
| eq. (2), the real Abel radius is the complex radius | `summable_susceptibility_of_norm_lt`, `not_summable_susceptibility_of_lt_norm` |
| `χ` is analytic on the unconditional disk | `analyticOnNhd_susceptibility` |
| Pringsheim singularity at `R_A` | `not_continuesAcross_susceptibility` |
| eq. (3), the collar hypothesis | `PrimeArchBernsteinCollarContinuation` |
| **eq. (4), collar ⟹ RH** | `riemannHypothesis_of_collarContinuation` |

The collar predicate is stated exactly as in the card: one open `U`, one holomorphic `F` on `U`,
a real base point `z₀ < r₀ = 250000/251001` at which `F` agrees with the germ, and containment of
the whole positive real collar `[z₀, 1)` in `U`.  The endpoint `t = 1` is not required anywhere,
and the circularity firewall is preserved: `F` is an arbitrary externally supplied holomorphic
function, never the susceptibility series itself.

The unconditional narrow-collar interface `250000/251001 < R_A ≤ 1` and `RH ↔ R_A = 1` is the
pre-existing `existsUnique_primeArchEndpointBernsteinAbelCriticalRadius`.

## Gates

- [x] complex radius identified from the formal real critical-radius interface
- [x] Pringsheim collar implication proved on paper
- [x] endpoint `t=1` removed from the hypothesis
- [x] concrete double-source provider interface identified
- [x] circularity firewall stated
- [x] general Pringsheim theorem formalized in Lean
- [ ] independent prime--Gamma collar continuation  *(declared future research)*
- [ ] RH  *(declared future research)*
