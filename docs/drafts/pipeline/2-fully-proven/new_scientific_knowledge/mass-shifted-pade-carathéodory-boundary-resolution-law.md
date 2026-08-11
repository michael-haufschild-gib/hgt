# Mass-shifted Padé Carathéodory boundary-resolution law

- **ID:** `mass-shifted-pade-carathéodory-boundary-resolution-law`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, positive-axis Padé mass
- **Type:** THEOREM + SHARP NO-GO + FRONTIER REDUCTION (paper)
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **Depends on:** `mass-shifted-moving-center-pade-worldline-law`, unconditional Xi divisor
  symmetry and endpoint gap, and `XiShiftedHankelFarRightPositiveDefinite.lean`
- **Statement:** The completed-Xi resolvent is a positive-real function on its unconditional
  right half-plane.  Its moving-center Padé approximant therefore obeys an exact hierarchy of
  Carathéodory reserve inequalities.  Nevertheless a bounded positive-axis pole with nonvanishing
  physical residue becomes an ordinary disk pole of vanishing residue and an asymptotically
  invisible finite jet; its invariant trace is a nonvanishing Julia-normalized boundary residue.

## 1. Literal positive-real resolvent

Let

\[
 c=\frac{81}{4},
 \qquad
 G(Y)=\sum_q\frac1{Y+\zeta_q},
 \qquad \operatorname{Re}\zeta_q>c,                       \tag{PCR.1}
\]

where the sum is over the complete multiplicity-exact squared centered Xi divisor.  The sum is
absolutely and locally uniformly convergent away from its poles because the squared divisor has
summable reciprocals.  For every $\operatorname{Re}Y>-c$,

\[
 \operatorname{Re}G(Y)
 =\sum_q\frac{\operatorname{Re}Y+\operatorname{Re}\zeta_q}
 {|Y+\zeta_q|^2}>0.                                      \tag{PCR.2}
\]

Thus the literal completed-Xi resolvent is unconditionally positive-real on the entire half-plane
to the right of $-c$.  No RH hypothesis enters `(PCR.2)`.

Fix a real expansion center $y>0$ and use the exact disk chart

\[
 \phi_y(Y)=\frac{Y-y}{Y+y+2c},
 \qquad
 \Phi_y(z)=\phi_y^{-1}(z)
 =\frac{y(1+z)+2cz}{1-z}.                                 \tag{PCR.3}
\]

It sends $\{\operatorname{Re}Y>-c\}$ to the unit disk, $y$ to $0$, $-c$ to $-1$, and infinity
to $1$.  Consequently

\[
 C_y(z):=G(\Phi_y(z))                                    \tag{PCR.4}
\]

has positive real part on the disk and $C_y(0)=G(y)>0$.  If

\[
 C_y(z)=\sum_{k\ge0}c_k(y)z^k,
\]

Carathéodory's coefficient inequality gives

\[
 |c_k(y)|\le2G(y)\qquad(k\ge1).                          \tag{PCR.5}
\]

## 2. Padé covariance and pole chart

In a positive degree-$n$ Hankel chamber, write the canonical Padé approximant as

\[
 R_y(Y)=\sum_{i=1}^n\frac{\rho_i}{Y-a_i},
 \qquad
 a_i=y-x_i^{-1}<y,
 \qquad \rho_i>0.                                       \tag{PCR.6}
\]

The exact Padé error has a zero of order $2n$ at $Y=y$.  Since

\[
 \Phi_y(z)-y=\frac{2(y+c)z}{1-z},
\]

the composed rational function

\[
 P_y(z):=R_y(\Phi_y(z))                                  \tag{PCR.7}
\]

matches $C_y$ through degree $2n-1$ at zero:

\[
 C_y(z)-P_y(z)=O(z^{2n}).                                \tag{PCR.8}
\]

For one Padé pole put

\[
 d_i=y+a_i+2c,
 \qquad z_i=\phi_y(a_i)=\frac{a_i-y}{d_i}.               \tag{PCR.9}
\]

When $d_i\ne0$, its exact disk expression is

\[
 \frac{\rho_i}{\Phi_y(z)-a_i}
 =\frac{\rho_i(1-z)}{d_i(z-z_i)}.                        \tag{PCR.10}
\]

Its ordinary disk residue is therefore

\[
 \widetilde\rho_i
 =\frac{2\rho_i(y+c)}{(y+a_i+2c)^2}.                     \tag{PCR.11}
\]

At the same time,

\[
 1+z_i=\frac{2(a_i+c)}{y+a_i+2c},                        \tag{PCR.12}
\]

so the Julia-normalized residue is

\[
 \boxed{
 \frac{\widetilde\rho_i}{1+z_i}
 =\frac{\rho_i(y+c)}{(a_i+c)(y+a_i+2c)}.
 }                                                        \tag{PCR.13}
\]

If $a_i$ remains in a fixed compact $K\Subset(0,\infty)$, then uniformly on $K$,

\[
 \widetilde\rho_i=\frac{2\rho_i}{y}(1+o(1)),
 \qquad
 1+z_i=\frac{2(a_i+c)}{y}(1+o(1)),                       \tag{PCR.14}
\]

but

\[
 \frac{\widetilde\rho_i}{1+z_i}
 =\frac{\rho_i}{a_i+c}(1+o(1)).                          \tag{PCR.15}
\]

Hence the Route-U target

\[
 \sum_{a_i\in K}\rho_i\longrightarrow0                 \tag{PCR.16}
\]

is equivalent, up to uniformly bounded positive factors on $K$, to vanishing of the normalized
boundary atoms

\[
 \sum_{a_i\in K}\frac{\widetilde\rho_i}{1+z_i}
 \longrightarrow0.                                      \tag{PCR.17}
\]

It is **not** equivalent to vanishing of the ordinary disk residues: `(PCR.14)` makes those tend
to zero automatically even when the physical residues tend to positive constants.

## 3. Exact Carathéodory reserve hierarchy `[PAPER-PROVED]`

For every $k\ge1$, expansion of `(PCR.10)` gives

\[
 [z^k]\frac{\rho_i}{\Phi_y(z)-a_i}
 =-\frac{2\rho_i(y+c)}{d_i^2z_i^{k+1}}.                  \tag{PCR.18}
\]

If $k=2m-1$ is odd, then $z_i^{k+1}=z_i^{2m}>0$.  All real Padé poles therefore contribute with
the **same sign**.  Combining `(PCR.5)`, `(PCR.8)`, and `(PCR.18)` yields, for
$1\le m\le n$,

\[
 \boxed{
 (y+c)\sum_{i=1}^n
 \rho_i\frac{(y+a_i+2c)^{2m-2}}{(y-a_i)^{2m}}
 \le G(y)
 =\sum_{i=1}^n\frac{\rho_i}{y-a_i}.
 }                                                        \tag{PCR.19}
\]

The exceptional algebraic case $d_i=0$ is the continuous limit of this identity; its composed
term is a polynomial of degree one and causes no problem for $m>1$.

At $m=1$, `(PCR.19)` becomes the exact reserve balance

\[
 \boxed{
 \sum_{i=1}^n\rho_i\frac{a_i+c}{(y-a_i)^2}\le0.
 }                                                        \tag{PCR.20}
\]

Thus every Padé atom to the right of $-c$ consumes positive Carathéodory budget and must be paid
for by Padé mass to the left of $-c$.  In particular, the positive-axis mass cannot exist in
isolation.  This is a literal completed-Xi correlation absent from generic shifted-moment flow.

## 4. Critical finite-jet blindness `[PAPER-PROVED]`

The reserve hierarchy does not by itself remove a bounded positive atom at the Route-U degree
scale.  Let $a\in K\Subset(0,\infty)$, let its physical residue be $\rho$, and let
$M_y=O(\sqrt y)$.  From `(PCR.9)`,

\[
 |z_a|=1-\frac{2(a+c)}{y+a+2c},
\]

and therefore, uniformly for $0\le k\le M_y$,

\[
 |z_a|^{-k}=1+O\!\left(\frac{k}{y}\right).               \tag{PCR.21}
\]

Equations `(PCR.10)` and `(PCR.18)` then give

\[
 |[z^k]P_{y,a}|=\frac{2\rho}{y}
 \left(1+O\!\left(\frac{k+1}{y}\right)\right)
 \quad(1\le k\le M_y),                                  \tag{PCR.22}
\]

and the constant coefficient is $\rho/y+O(\rho/y^2)$.  Consequently

\[
 \sum_{k=0}^{M_y}|[z^k]P_{y,a}|
 =O\!\left(\frac{M_y\rho}{y}\right)
 =O\!\left(\frac{\rho}{\sqrt y}\right)
 \longrightarrow0.                                      \tag{PCR.23}
\]

On the literal shifted-Xi source,

\[
 G(y)\sim\frac{\log y}{4\sqrt y},                        \tag{PCR.24}
\]

because the already formalized normalized zeroth moment
$2\sqrt y\,G(y)/\log\sqrt y$ tends to the zeroth arcsine moment $1$.  Thus the entire
$O(\sqrt y)$ jet footprint of one fixed physical residue is only $O(1/\log y)$ relative to the
available Carathéodory coefficient scale.

The same atom has, simultaneously,

\[
 \widetilde\rho=O(\rho/y)\to0,
 \qquad
 \frac{\widetilde\rho}{1+z_a}\to\frac{\rho}{a+c}\ne0.
 \tag{PCR.25}
\]

This is the exact resolution mismatch:

\[
 \boxed{
 \text{degree }\sqrt y\text{ sees disk scale }y^{-1/2},
 \quad
 \text{the forbidden atom lives at disk depth }y^{-1}.
 }                                                        \tag{PCR.26}
\]

Ordinary Padé convergence in capacity, ordinary disk-residue control, coefficientwise
Carathéodory bounds, and any unweighted matched-jet norm are therefore blind to the physical
residue.  A closing analytic theorem must control the Julia-normalized boundary atom `(PCR.13)`,
or equivalently a boundary derivative/Carleson quantity at $z=-1$.

## 5. Finite-head depletion has no boundary-resolution gain `[PAPER-PROVED]`

A natural repair is to remove the low squared-Xi divisor points.  If a head $S_y$ is subtracted,
the tail resolvent is positive-real on a larger half-plane
$\operatorname{Re}Y>-c_y$, where $c_y$ may tend to infinity.  Taking
$c_y\asymp\sqrt y\log y$ moves a bounded positive pole from disk depth $1/y$ to the apparently
resolvable depth $(\log y)/\sqrt y$, while the number of removed divisor points is only $o(n)$.

The gain is illusory because every removed divisor point is inserted into the rational approximant
with the opposite residue.  For the chart with parameter $c_y$, define the coefficient kernel

\[
 \mathcal K_{y,c_y,k}(a)
 :=\frac{2(y+c_y)}
 {(y+a+2c_y)^2\phi_{y,c_y}(a)^{k+1}}.                    \tag{PCR.27}
\]

The coefficient of $z^k$ contributed by $r/(Y-a)$ is exactly
$-r\mathcal K_{y,c_y,k}(a)$.  If $a$ and $b$ remain in fixed compact subsets of $\mathbb C$,
$c_y=o(y)$, and $k=O(\sqrt y)$, then

\[
 \boxed{
 \frac{\mathcal K_{y,c_y,k}(a)}
 {\mathcal K_{y,c_y,k}(b)}\longrightarrow1
 }
 \tag{PCR.28}
\]

uniformly in that range.  Indeed,

\[
 \partial_a\log\mathcal K_{y,c_y,k}(a)
 =-\frac2{y+a+2c_y}
 -(k+1)\left(\frac1{a-y}-\frac1{a+y+2c_y}\right)
 =O\!\left(\frac{k+1}{y}\right),                         \tag{PCR.29}
\]

and the right side tends to zero.

For every fixed removed divisor point $\zeta_q$, the subtracted term
$-1/(Y+\zeta_q)$ has pole $b=-\zeta_q$ and residue $-1$.  Its matched boundary jet therefore points
asymptotically in the exact opposite direction to the jet of any bounded physical pole of residue
$+1$.  More generally, any fixed number $M$ of removed divisor copies supplies asymptotic head
budget $M$ against a bounded physical residue.  Any depletion with $c_y\to\infty$ eventually
contains arbitrarily many such fixed copies.

Thus moving the positive-real boundary left does not improve any inequality extracted only from
the matched Carathéodory jet: the larger analytic half-plane and the inserted head-pole budget are
two sides of the same operation.  Finite-head depletion alone cannot force the Julia charge to
vanish by this mechanism.  This is the Padé boundary analogue of the corpus's Euler-depletion
conservativity laws.

## 6. Conjecture--failure--pivot

1. **Conjecture:** diagonal Padé convergence in capacity on the analytic positive resolvent domain
   forces positive-axis residues to vanish.
   **FALSIFIED AT THE MOVING SCALE.**  The natural disk charts degenerate with $y$;
   `(PCR.14)` sends a nonzero physical residue to an ordinary residue of size $1/y$, so its bad set
   has vanishing disk capacity automatically.
2. **Conjecture:** unconditional positive-realness of $G$ makes ordinary Padé positive-real and
   pole-free.
   **FALSIFIED AS AN INFERENCE.**  Positivity controls the Carathéodory jet, not the rational
   extension selected by Hankel Padé.  The exact surviving consequence is `(PCR.19)`.
3. **Positive survivor:** every forbidden atom has an exact left-reserve debt `(PCR.20)`, and its
   invariant size is the Julia-normalized residue `(PCR.13)`.
4. **Stronger replacement conjecture:** the literal prime--Gamma source has no cofinal
   Julia-normalized Padé atom at $z=-1$.  Unlike ordinary capacity convergence, this statement is
   exactly equivalent to the Route-U target on compact positive mass intervals.
5. **Conjecture:** remove $o(n)$ low divisor points so the tail half-plane resolves the atom by a
   matched-jet or Carathéodory estimate.  **FALSIFIED.**  Every removed point reappears as an
   opposite rational pole, and `(PCR.28)` shows that its entire matched boundary jet is
   asymptotically indistinguishable from the forbidden atom's jet.  At this level, depletion
   conserves rather than removes the boundary charge.

## 7. Hostile and literature audit

- `[CORPUS]` The shifted-Xi zeroth-moment asymptotic used in `(PCR.24)` is already Lean-proved in
  `XiShiftedHankelFarRightPositiveDefinite.lean`.  The moving Padé error and residue are paper-proved
  in the parent card.  No corpus result uses the positive-real disk chart or proves `(PCR.19)`.
- `[CORPUS]` The qualitative warning that depletion can conserve rather than remove an admission
  obstruction already appears in
  `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-gamma-six-critical-edge-coface-rigidity.md`
  and is formalized for that Deninger operator in
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/deninger/deninger-euler-depleted-meyer-periodization-extension.md`.
  The exact Padé
  boundary-jet covariance `(PCR.28)` is the source-specific survivor here; no general novelty is
  claimed for the conservativity principle.
- `[LITERATURE]` Convergence in capacity and spurious-pole theory are classical Padé parents; see
  Aptekarev--Yattselev,
  [Padé approximants for functions with branch points](https://arxiv.org/abs/1109.0332), and
  Mascarenhas,
  [Robust Padé approximants may have spurious poles](https://arxiv.org/abs/1309.5753).
  Those works do not state the moving-center Xi chart, the Julia residue `(PCR.13)`, or the reserve
  hierarchy `(PCR.19)`.
- Targeted arXiv searches found no exact source-specific collision.  Priority remains
  `[NOVELTY UNVERIFIED]`.
- No Lean declaration is started.  Formalizing a generic Carathéodory wrapper would not prove the
  literal Julia-atom vanishing and would repeat the rejected infrastructure pattern.

## No-go closure

- **Exact killing mechanism:** conformal degeneration turns $O(1)$ physical mass into $O(1/y)$
  ordinary disk residue at depth $O(1/y)$.
- **Strongest positive survivor:** exact reserve hierarchy `(PCR.19)` and invariant normalized
  residue `(PCR.13)`, together with depletion covariance `(PCR.28)`.
- **New insight:** Route U is a boundary-angular-derivative problem, not an ordinary Padé-capacity
  problem.  Every positive atom must draw a vanishingly small payment from the macroscopic
  left-pole reservoir, so bulk or unweighted estimates cannot exclude it.
- **Status:** dependency-closed paper proof; novelty unverified; no literal closure and no Lean
  credit.

## Log

- 2026-08-11 — positive-real chart, exact reserve hierarchy, conformal residue law, and critical
  finite-jet blindness proved; ordinary Padé-capacity attack retired.
- 2026-08-11 — growing finite-head depletion falsified by exact boundary-jet covariance; enlarged
  half-plane and inserted head budget shown to be one conservative operation.
