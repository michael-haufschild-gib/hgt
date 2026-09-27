# Prime sieving forces bidirectional signed variation at the theta cusp

- **Stage:** 3-formalized (Lean: `GaloisForLFunctions.RHTower.ThetaSieveBidirectionalCuspVariation`, certificate `theta-sieve-bidirectional-cusp-variation-formalized.md`); literature-novelty audit open.
- **Routes:** TQFQ, SV2, O, STC, CSB.
- **Source:** literal finite prime deletions of the completed theta source, not an arbitrary perturbation.
- **Dependency:** [prime-deletion spectral escape](theta-prime-deletion-spectral-escape.md), especially its equations (1)--(3).
- **Scope:** an unconditional source-boundary theorem, not RH or zero exclusion.

## Theorem

Let `h` be the first theta atom, `k` the completed even source, and
`k_S=∏_{p∈S}(1-p^{-1/2}T_{log p})k`. Let finite prime sets `S_j` increase
through every prime, and put `δ_j=k_{S_j}-h`. For `0≤w<1/2`, define

\[
d_w=(1/2-w)\,\Gamma(w/2+5/4)\pi^{-w/2-1/4}>0.
\]

For every fixed `R>0`, the *escaped signed moments* obey

\[
\lim_{j\to\infty}\int_{x<-R} e^{wx}\delta_j(x)\,dx=d_w.
\tag{1}
\]

For `0<w<1/2`, write
`P_j(R)=∫_{x<-R}(δ_j)_+` and `N_j(R)=∫_{x<-R}(δ_j)_-`. Then

\[
\liminf_{j\to\infty}(P_j(R)+N_j(R))\ge d_w e^{wR},
\qquad
\lim_{j\to\infty}(P_j(R)-N_j(R))=d_0,
\tag{2}
\]

and consequently

\[
\liminf_{j\to\infty}\min(P_j(R),N_j(R))
\ge \tfrac12\bigl(d_we^{wR}-d_0\bigr).
\tag{3}
\]

The right side tends to infinity as `R→∞`. Thus the total positive and
negative variations of `δ_j` each diverge as `j→∞`. The same holds for
`k_{S_j}` itself: subtracting the fixed integrable seed `h` changes each
variation by at most `∫|h|`. Yet the *signed* ordinary mass
`∫k_{S_j}→0`. Cofinal prime deletion therefore creates two growing,
mutually canceling masses at the negative cusp; it cannot have a finite
signed-measure boundary limit with uniformly bounded total variation.

There is a single critical-scale consequence. `G(w)=d_w/(1/2-w)` is
continuous and strictly positive on `[0,1/2]`; let
`c=min_{[0,1/2]}G>0`. For each fixed `R>2`, take
`w_R=1/2-1/R` in (2)--(3). Then

\[
\liminf_j(P_j(R)+N_j(R))\ge {c\over eR}e^{R/2},
\qquad
\liminf_j\min(P_j(R),N_j(R))
\ge {1\over2}\left({c\over eR}e^{R/2}-d_0\right).
\tag{4}
\]

The exponent `1/2` is the actual critical half-density scale; the
`1/R` loss comes from the seed's exact zero at that endpoint. This is a
lower bound only, not an asymptotic equality.

Quantifiers matter: (2)--(3) hold for each fixed `R` after `j→∞`. They do
not assert a uniform rate in `j` and `R` simultaneously.

## Proof

The source identities in the dependency give, for every real
`0≤w<1/2`,

\[
\int_\mathbb R e^{wx}k_{S_j}(x)\,dx\longrightarrow0,
\qquad
\int_\mathbb R e^{wx}h(x)\,dx=-d_w.
\]

Hence `∫ e^{wx}δ_j→d_w`. On each compact interval, `δ_j→0` uniformly.
On the positive ray, `0≤δ_j≤k-h` because retained atoms are positive;
`e^{wx}(k-h)` is integrable for `w<1/2`. Dominated convergence gives
`∫_{x≥-R}e^{wx}δ_j→0`. Subtraction proves (1).

For `x<-R`, `e^{wx}≤e^{-wR}`, so

\[
\left|\int_{x<-R}e^{wx}\delta_j\right|
\le e^{-wR}\int_{x<-R}|\delta_j|
=e^{-wR}(P_j(R)+N_j(R)).
\]

Take `liminf` and use (1) to obtain the first half of (2). The case
`w=0` in (1) gives its second half. Since
`2 min(P,N)=P+N-|P-N|`, (3) follows. For any fixed `w>0`, choosing
`R` arbitrarily large and then `j` large proves both variation
divergences. Finally
`|∫(k_{S_j})_\pm-∫(δ_j)_\pm|≤∫|h|`, while the signed ordinary
mass of `k_{S_j}` tends to zero by the dependency. ∎

## Whole-route consequence

The existing spectral-escape theorem identified a noncompact defect; this
sharpens it from *escaped mass* to **unbounded two-sign cancellation**.
No cofinal argument in a finite-measure, positive-measure, or uniformly
`L¹`-bounded topology can transport the divisor from `k_{S_j}` to the seed.
A lawful source-to-spectrum bridge must keep the signed prime--polar--Gamma
boundary functional in a topology that permits this cancellation. Equation
(4) gives an explicit `e^{R/2}/R` two-sign lower scale that any proposed
boundary norm must accommodate.

This theorem does not bound the cancellation error or prove RH. It is a
constraint on the topology and on any attempted producer. The full
dependence on the prior paper theorem must be formalized before this result
can be called Lean-closed. Literature novelty has not been established.

## Log
- 2026-09-27 — (1)–(4) and both divergence statements formalized unconditionally; moved to 3-formalized.
