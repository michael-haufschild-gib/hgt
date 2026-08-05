# Quenched shortcut--annular equivalence

- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [BRIDGE] [LEAN PROOF OPEN]`
- **Parent:** `../1-in-progress/quenched-observer-spectral-action-law.md`
- **Date:** 2026-08-05

## Statement

Let `V` be an `m`-dimensional real Euclidean coefficient space and let
`H:V -> Herm(K)` be real-linear. Fix a normalized state `Phi`, a measurable
target `E` in projective state space, and define

\[
 F(y)=[e^{-iH(y)}\Phi].                                      \tag{1}
\]

For `y != 0`, let `nu_y` be Haar measure on the compact projective closure
of `s -> [e^{-isH(y)}Phi]`, and put

\[
 I(y)=-\log\nu_y(E),                                        \tag{2}
\]

with `-log 0=+infinity`. For `B>=0`, define the resolved unit-time shortcut
set

\[
 S_B=\{y\in V:F(y)\in E,\ I(y)\ge B\}.                     \tag{3}
\]

Let `X` be standard Gaussian in `V`. Then for every `t>0`,

\[
 \boxed{
 \Pr\{[e^{-itH(X)}\Phi]\in E,\ I(X)\ge B\}
 =(2\pi)^{-m/2}t^{-m}
   \int_{S_B}e^{-\|y\|^2/(2t^2)}\,dy.}                     \tag{4}
\]

Consequently:

1. if the probability in `(4)` is at most `P(t,B)`, then

\[
 \operatorname{vol}(S_B\cap B_t)
 \le (2\pi)^{m/2}e^{1/2}t^mP(t,B);                         \tag{5}
\]

2. if for all `R>=1`

\[
 \operatorname{vol}(S_B\cap B_R)\le V(R,B),               \tag{6}
\]

then

\[
 \Pr\{[e^{-itH(X)}\Phi]\in E,\ I(X)\ge B\}
 \le C_m t^{-m}\sum_{j=0}^{\infty}
 e^{-2^{2j-1}}V(2^{j+1}t,B),                               \tag{7}
\]

where `C_m=e^(1/2)(2pi)^(-m/2)`. Thus any polynomial annular bound transfers with
the same exponent.

For the frozen conjecture, `(4)` says that its exact open core is the
resolved volume-growth law

\[
 \operatorname{vol}(S_B\cap B_R)
 \le C R^m
 \exp[-(1-\eta)\min\{v\log R,B\}],                         \tag{8}
\]

up to dimension-dependent constants that must be audited in the joint
`n,R` window.

## Proof

Linearity gives `tH(x)=H(tx)`, hence

\[
 [e^{-itH(x)}\Phi]=F(tx).                                  \tag{9}
\]

For every nonzero scalar `a`, the parameter sets
`{s a:s in R}` and `R` coincide. Therefore the one-parameter projective
orbits of `H(ay)=aH(y)` and `H(y)` have the same closure, the same normalized
Haar measure, and

\[
 I(ay)=I(y).                                               \tag{10}
\]

Equations `(9)` and `(10)` show that the event at time `t` is exactly
`{x:tx in S_B}=t^(-1)S_B`. Integrating the standard Gaussian density and
changing variables `y=tx` proves `(4)`.

On `S_B cap B_t`, the exponential in `(4)` is at least `e^(-1/2)`.
Rearrangement proves `(5)`.

For `(7)`, split `S_B` into `B_(2t)` and the shells

\[
 \{2^jt<\|y\|\le2^{j+1}t\},\qquad j\ge1.
\]

On the `j`th shell the Gaussian factor is at most `e^(-2^(2j-1))`, while
its volume is at most `V(2^(j+1)t,B)`. The inner ball is handled by the
`j=0` term after enlarging the universal constant. Summation proves `(7)`.

No spectral-genericity, mixing, circuit, or locality premise is used.

## Exact insight

Quenching does not destroy the homogeneity reduction. Completed-orbit
information is itself radial-scale invariant, so rarity-resolved complexity
growth is still exactly an annular packing problem. The new filter removes
the full-dimensional gapped-eigenline floor but leaves the nonlinear
recurrence-component growth problem untouched.

## Hostile audit

- `(4)` requires measurability of `I`; in the application this must be proved
  for the finite union of closed circuit balls. If necessary, `(4)` first
  applies to measurable sublevel strata produced by finite-time Cesaro
  approximants and then passes to the completed limit.
- Constants in `(5)--(8)` are not automatically harmless when `m=m(n)`.
- The theorem is an exact reduction, not the missing annular bound.
- No claim of external novelty is made.

## Formal target

Formalize the abstract Gaussian dilation identity and the scale invariance of
the completed one-parameter orbit closure. Do not encode `(8)` as a
hypothesis and call the conjecture proved.
