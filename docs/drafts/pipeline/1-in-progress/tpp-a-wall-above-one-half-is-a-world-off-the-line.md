# A wall above one half is a world off the line

- **ID:** tpp-verdict-worlds
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** review-1511 obstacles summary §2.18, failure row of stage 5; TPP README Q9
- **Statement:** For a source class with abscissas $A$ and a seed $s$, the wall of all levers valid on the class is $\sup(A\cap(-\infty,s])$; hence "the route ends at a wall above $\tfrac12$" holds for the class iff it has a world with abscissa in $(\tfrac12,s]$.

## Goal

Decide the statement

> RH is not accessible by tensor powers, and the estimate route ends at a wall above $\tfrac12$.

The statement has two readings, and each gets a theorem.

- **Validity.** About all levers that are true for $\zeta$. Then it is $\neg$RH (Theorem 6).
- **Sources.** About the levers a list of properties can prove. A proof from properties
  $P_1,\dots,P_m$ proves the lever for every world with these properties, so a source is a class of
  worlds, and the statement is decided by the worlds of the class (Theorems 1–2), in both
  directions.

Non-circularity: Theorems 1–5 are statements about real numbers and maps; no property of $\zeta$
enters. Theorem 6 uses $\tfrac12\le\Theta\le\tfrac78$. Theorem 7 uses the worlds of EDCS.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Setting

The calculus of EDCS: $T$ is a lever of $\theta$ if $\theta\le b\Rightarrow\theta\le T(b)$;
$\mathrm{allowed}(\mathcal T,s)=\{b\le s:\ b\le T(b)\ \forall T\in\mathcal T\}$,
$\mathrm{wall}(\mathcal T,s)=\sup\mathrm{allowed}(\mathcal T,s)$. A frame $(c,k)$, $k>1$, is the
lever $b\mapsto(c+b)/k$ with centre $c/(k-1)$; the Deligne line is $c=(k-1)/2$, the sign line
$c=k/2$ with centre $\kappa_k=k/(2(k-1))=\tfrac12+\tfrac1{2(k-1)}$.

A **source class** is a set $A\subset\mathbb R$ (the abscissas of its worlds).
$\mathcal V(A)=\{T:\ T\text{ is a lever of every }a\in A\}$.

## Theorems and proofs

**Theorem 1 (soundness).** If $\mathcal T\subseteq\mathcal V(A)$, every $a\in A$ with $a\le s$ is
allowed, so $\sup(A\cap(-\infty,s])\le\mathrm{wall}(\mathcal T,s)$.

*Proof.* $a\le T(a)$ for $T\in\mathcal T$ is the lever property at $b=a$. $\square$

**Theorem 2 (completeness).** Put $E_A(b)=\sup\big((A\cap(-\infty,b])\cup\{b-1\}\big)$.

1. $E_A$ is monotone, $E_A(b)\le b$, and $E_A\in\mathcal V(A)$.
2. $b\le E_A(b)$ iff $b$ is the least upper bound of $A\cap(-\infty,b]$.
3. If $E_A\in\mathcal T\subseteq\mathcal V(A)$ then
   $\mathrm{allowed}(\mathcal T,s)=\{b\le s:\ b=\operatorname{lub}(A\cap(-\infty,b])\}$, and if
   $A\cap(-\infty,s]\ne\emptyset$ then $\mathrm{wall}(\mathcal T,s)=\sup(A\cap(-\infty,s])$.
   This applies to $\mathcal V(A)$ and to its monotone members.

*Proof.* (1) The set defining $E_A(b)$ is nonempty and bounded by $b$. If $b\le b'$ then
$b-1\le b'-1\le E_A(b')$ and $A\cap(-\infty,b]\subseteq A\cap(-\infty,b']$, so $E_A(b)\le E_A(b')$.
For $a\in A$, $a\le b$: $a\le E_A(b)$.
(2) If $b\le E_A(b)$, then $b=E_A(b)$ is the least upper bound of the enlarged set. $b$ bounds
$A\cap(-\infty,b]$; if $u<b$ were another bound, $\max(u,b-1)<b$ would bound the enlarged set.
Conversely $E_A(b)$ bounds $A\cap(-\infty,b]$, so a least upper bound $b$ satisfies $b\le E_A(b)$.
(3) "$\subseteq$" is (2) applied to $E_A\in\mathcal T$. "$\supseteq$": for $T\in\mathcal T$ and
$a\in A$, $a\le b$, the lever property gives $a\le T(b)$; so $T(b)$ bounds $A\cap(-\infty,b]$ and
$b\le T(b)$. For the wall let $\sigma=\sup(A\cap(-\infty,s])$. By Theorem 1 $\sigma\le$ wall. An
allowed $b$ is the least upper bound of $A\cap(-\infty,b]\subseteq A\cap(-\infty,s]$, which $\sigma$
bounds, so $b\le\sigma$. $\square$

**Corollary 3 (decision).** Let $A\cap(-\infty,s]\ne\emptyset$. Then
$h<\mathrm{wall}(\mathcal V(A),s)$ iff some $a\in A$ has $h<a\le s$;
$\mathrm{wall}(\mathcal V(A),s)\le h$ iff every $a\in A$ with $a\le s$ has $a\le h$; if $h$ is a
lower bound of $A$, the wall equals $h$ iff every $a\in A$ with $a\le s$ equals $h$. For one number,
$\mathrm{wall}(\mathcal V(\{\theta\}),s)=\theta$ when $\theta\le s$.

**Theorem 4 (frames on a class).** For $k>1$ a frame with estimate floor $\sigma_0$,
$b\mapsto\max(\sigma_0,(c+b)/k)$, is a lever of $\theta$ iff $\theta\le\max(\sigma_0,c/(k-1))$.
Hence on a class:

1. a frame is valid iff no world lies right of its centre;
2. a Deligne lever of any period is valid iff $A\subseteq(-\infty,\tfrac12]$;
3. the sign lever of period $k$ is valid iff $A\subseteq(-\infty,\kappa_k]$;
4. sign levers at unboundedly many periods are valid iff $A\subseteq(-\infty,\tfrac12]$.

So one Deligne lever and the sign levers of unboundedly many periods have the same source classes.

*Proof.* The map is monotone, so the lever property is $\theta\le\max(\sigma_0,(c+\theta)/k)$, i.e.
$\theta\le\sigma_0$ or $\theta(k-1)\le c$. (2), (3): the centres are $\tfrac12$ and $\kappa_k$.
(4): $\kappa_k\downarrow\tfrac12$. $\square$

**Theorem 5 (the sign line by periods; estimate floors).** Let $P\subseteq\{2,3,\dots\}$ and
$s>\tfrac12$. Then $\mathrm{allowed}=\{b\le s:\ b\le\kappa_k\ \forall k\in P\}$ and

- if $P\subseteq[2,K]$ then $\mathrm{wall}\ge\min(s,\kappa_K)>\tfrac12$;
- $\mathrm{wall}=\tfrac12$ iff $P$ is unbounded.

For a route of floored frames $(\sigma_j,c_j,k_j)$, $k_j>1$, with levels
$L_j=\max(\sigma_j,c_j/(k_j-1))$: $\mathrm{allowed}=\{b\le s:\ b\le L_j\ \forall j\}$, and the wall
exceeds $h$ iff some $b\in(h,s]$ lies at or below every level.

*Proof.* Theorem 4 for each lever, and $\kappa_k$ decreasing to $\tfrac12$. $\square$

**Theorem 6 (the verdict for $\zeta$).**

1. $\mathrm{wall}(\mathcal V(\{\Theta\}),\tfrac78)=\Theta$; so the wall of all levers valid for
   $\zeta$ is above $\tfrac12$ iff RH fails.
2. For a class $A\ni\Theta$ with $A\subseteq[\tfrac12,\infty)$:
   $\mathrm{wall}(\mathcal V(A),\tfrac78)=\tfrac12$ iff every world of the class at or below
   $\tfrac78$ lies on the line. If some $\mathcal T\subseteq\mathcal V(A)$ has wall $\le\tfrac12$,
   RH holds; if the class has a world with abscissa in $(\tfrac12,\tfrac78]$, every
   $\mathcal T\subseteq\mathcal V(A)$ has wall above $\tfrac12$.

*Proof.* Corollary 3 with $\tfrac12\le\Theta\le\tfrac78$, and Theorem 1. $\square$

**Theorem 7 (verdicts for the worlds of the corpus).** Let $\mathcal T$ consist of levers valid on

- all cosh models (functional equation, no Dirichlet series): $\mathrm{wall}(\mathcal T,s)=s$ for
  every $s\ge\tfrac12$;
- all Euler worlds (Euler product, no functional equation):
  $\mathrm{wall}(\mathcal T,s)\ge\min(s,\tfrac23)$ for every $s>\tfrac12$;
- all shifted pairs (Euler product and functional equation, no Ramanujan bound):
  $\mathrm{wall}(\mathcal T,s)=s$ for every $s\in[\Theta,\Theta+\tfrac12)$.

*Proof.* The families realize $[\tfrac12,\infty)$, $(\tfrac12,\tfrac23)$ and
$[\Theta,\Theta+\tfrac12)$ (EDCS); Theorem 1. $\square$

## Verdict

| Reading of the statement | Decision | Where |
|---|---|---|
| All levers true for $\zeta$ | equivalent to $\neg$RH | Theorem 6.1 |
| Source = tensor moments of $\zeta$ alone, or an abelian base | true: rulers, the pole law is the width | TPP `exists_momentPoleLaw_iff`, `exists_twistPoleLaw_iff` |
| Source valid without Dirichlet series, or without functional equation, or without the Ramanujan bound | true: wall $=s$, $\ge\min(s,\tfrac23)$, $=s$ | Theorem 7 |
| Source = Gauss pairings completed factor by factor | true: wall $\tfrac35$ | EDCS `wall_gaussLevers` |
| Sign line with bounded periods | true: wall $\ge\kappa_K$ | Theorem 5 |
| Sign line with unbounded periods, or one Deligne lever, on a class | false iff the class has no world right of $\tfrac12$; one condition for both lines | Theorem 4 |
| Source using Euler product, functional equation and Ramanujan bound of $\zeta$ itself | the class is $\{\zeta\}$ in the Hamburger class (`beurlingSystem_rigidity_of_decaying_defect`), so the reading is the first row | Theorem 6 |

Consequences for the programme of §2.18.

- An "intrinsic floor of every transport" cannot be a theorem about $\zeta$ unless it is a
  disproof of RH: a floor above $\tfrac12$ for a class is a world of the class off the line.
- The stages that end at $\tfrac{13}{15},\tfrac56,\tfrac79,\tfrac23,\tfrac35$ do not enter the
  decision: they stay inside classes whose wall is known.
- Sign levers at finitely many periods never decide; all large periods and one Deligne lever are
  the same problem for the source.
- The test for a proposed source is exact: it reaches below $b$ iff it fails in every world with
  abscissa in $(b,s]$. For a source below $\tfrac23$ the worlds of Theorem 7 force the joint use
  of Euler product, functional equation and Ramanujan bound.

## Lean

- `ExponentDynamicsOfTheCriticalStrip/TheWallOfASourceClassIsTheLargestAbscissaItRealizes.lean`:
  Theorems 1–3, 4 (frames), 7.
- `TensorPowerProgramme/AWallAboveOneHalfIsAWorldOffTheLine.lean`: Theorems 4 (lines), 5, 6.

## Log
- 2026-11-15 — created in 1-in-progress with complete paper proofs
