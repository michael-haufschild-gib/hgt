# Prime phase-port recurrence and completion law

- **ID:** `cmr-prime-phase-port-recurrence-completion`
- **Stage:** 3-formalized
- **Type:** THEOREM / SIX-ORGAN SOURCE CALIBRATION
- **Status:** `[PAPER-PROVED] [BRIDGE/COMPATIBILITY] [HOSTILE REPAIR APPLIED]`
  `[ARITHMETIC/SPECTRAL/RECURRENCE/HISTORY/POSITIVE/TOPOLOGICAL]`
  `[NOT HT BY ITSELF] [NOT RH] [LEAN-FORMALIZED UNCONDITIONALLY]`
- **Formalized companion:** `prime-phase-port-recurrence-completion-law-formalized.md`
- **Parents:** `prime-port-algebraic-continuous-separation-law.md`;
  `../nomological-geometry-and-dynamics/euler-prime-orbit-prolongation-recurrence-polar-cofinal-law.md`.
- **Field card:**
  `../../1-in-progress/constraint-motive-relativity/polarized-constraint-cotangent-geometry.md`.
- **Statement:** The same arithmetic Mellin phase orbit drives a recurrent one-port reduction at
  every finite prime cutoff and a relatively compact weak-star port orbit in `ell^1`, while every unweighted
  `ell^p`, `p>1`, and `c0` completion erases that port after Hausdorff reduction. Recurrence,
  positivity, finite squared lift length, and completion survival are distinct shadows of one
  source orbit.

## Goal

Transport an independent spectral/recurrence invariant through the exact reduction--completion
square. Avoid the tunnel view in which topology is studied without time or recurrence is studied
without observer admission.

## 1. Arithmetic phase family

Let `P` be the ordinary primes and `K_0=c_00(P)`. For `t in R`, define

\[
 \varepsilon_t(x)=\sum_{p\in\mathcal P}p^{-it}x_p,
 \qquad
 I_t=\ker\varepsilon_t,
 \qquad
 \lambda_t=(p^{-it})_{p\in\mathcal P}.
\tag{PR.1}
\]

Thus `lambda_t` is the algebraic covector representing `epsilon_t`. It is obtained from the
augmentation port by the prime-log Mellin/Fourier clock.

### Theorem 1 — algebraic recurrent port

For every `t`,

\[
 I_t^\perp=\mathbb C\lambda_t,
 \qquad
 \mathbb H(K_0)//I_t\cong\mathbb H(\mathbb C).
\tag{PR.2}
\]

For every finite prime set `F`, the orbit

\[
 t\longmapsto\lambda_t|_F=(p^{-it})_{p\in F}
\tag{PR.3}
\]

is dense and recurrent in `T^F`.

#### Proof

`I_t` is a nonzero linear-functional kernel, so its annihilator in the algebraic dual is the line
spanned by that functional; explicitly differences
`p^{it}e_p-q^{it}e_q` span the kernel and force every annihilator to be proportional to
`lambda_t`. The quotient `K_0/I_t` is identified with `C` by `epsilon_t`, and the reduced
evaluation pairing is hyperbolic.

If integers `m_p` satisfy `sum_(p in F)m_p log p=0`, exponentiation and unique factorization give
`m_p=0` for every `p`. Kronecker--Weyl therefore makes `(PR.3)` dense. Simultaneous Diophantine
approximation gives arbitrarily large positive `t` for which every coordinate is arbitrarily close
to one, proving recurrence. `[PROVED HERE]`

## 2. Completion phase is uniform in time

### Theorem 2 — `ell^1` retains every time port

For every `t`, `epsilon_t` extends to `ell^1(P)` with norm one,

\[
 \overline{I_t}^{\ell^1}=\ker\varepsilon_t,
\]

and

\[
 \boxed{
 \mathbb H(\ell^1)//\overline{I_t}
 \cong\mathbb H(\mathbb C).}
\tag{PR.4}
\]

#### Proof

Since `|p^{-it}|=1`,
`|epsilon_t(x)|<=||x||_1`, and equality is attained on every basis vector. To approximate
`x in ker epsilon_t`, truncate it and correct the residual scalar in one fresh prime coordinate;
the correction has absolute value bounded by the `ell^1` tail, hence tends to zero. Thus the
closure is the continuous kernel. Its annihilator is `C lambda_t`, and its quotient is `C`.
`[PROVED HERE]`

### Theorem 3 — `ell^p/c0` erase every time port

For every `t`, `I_t` is dense in `ell^p(P)` for `1<p<infinity` and in `c0(P)`. Therefore its
continuous annihilator is zero and

\[
 \boxed{
 \mathbb H(X)//_H I_t=0,
 \qquad X=\ell^p\ (1<p<\infty)\text{ or }c_0.}
\tag{PR.5}
\]

#### Proof

For finite-support `x`, set `S=epsilon_t(x)`. Choose `N` fresh primes `q_j` and define

\[
 y_N=x-\frac{S}{N}\sum_{j=1}^{N}q_j^{it}e_{q_j}.
\tag{PR.6}
\]

Then `epsilon_t(y_N)=0`. Its correction norm is

\[
 \|x-y_N\|_p=|S|N^{1/p-1}\to0,
 \qquad
 \|x-y_N\|_\infty=|S|/N\to0.
\]

Finite-support vectors are dense in the stated spaces. The rest follows from continuous
annihilation of a dense subspace and Hausdorffization. `[PROVED HERE]`

Thus the algebraic-to-continuous separation loss is uniform in `t`: zero in `ell^1` and one erased
hyperbolic port in the other stated completions. This is expected from exact conjugacy
`I_t=U_t^{-1}I_0`, where `U_t=diag(p^(-it))` is an isometric automorphism of each stated sequence
space. The time-dependent phase law is therefore a compatibility bridge, not a new topology--time
interaction.

## 3. Infinite recurrent observer and open history

Regard `lambda_t` as a point of the product torus

\[
 \mathbb T^{\mathcal P}\subset\ell^\infty(\mathcal P).
\tag{PR.7}
\]

### Theorem 4 — weak-star recurrence

The orbit `t mapsto lambda_t` is dense in `T^P` for the product topology. On this bounded torus,
the product topology equals the weak-star topology inherited from
`ell^infinity=(ell^1)'`. Hence the orbit is relatively weak-star compact and recurrent; its
closure, not the orbit itself, is the compact torus.

Its logarithmic lift

\[
 \widetilde\lambda_t=(-t\log p)_{p\in\mathcal P}\in\mathbb R^{\mathcal P}
\tag{PR.8}
\]

is unbounded in every prime coordinate. For finite `F`, the squared Euclidean lift length

\[
 A_F(t)=t^2\sum_{p\in F}(\log p)^2
\tag{PR.9}
\]

tends to infinity along every recurrent sequence `t_j->infinity`, although
`lambda_(t_j)|_F->lambda_0|_F`.

#### Proof

Every finite coordinate projection is dense by Theorem 1. Cylinder sets form a basis of the
product topology, so the full orbit is dense. On `T^P`, weak-star convergence implies coordinate
convergence by testing standard `ell^1` basis vectors. Conversely, coordinate convergence plus
the uniform bound one implies convergence against every `ell^1` vector by dominated summation.
Thus the topologies coincide. Tychonoff compactness of the closure and the finite-coordinate
recurrence argument give recurrence. The orbit is a dense proper subgroup and is generally not
closed.

Equation `(PR.8)` has `p`-coordinate absolute value `|t|log p`, and `(PR.9)` is its finite
Euclidean squared norm. Both claims follow. `[PROVED HERE]`

## 3.1 Port jets and singular infinitesimal time

### Theorem 5 — finite jet tomography, infinite generator wall

For finite `F`, `|F|=N`, the first `N` time-jet covectors

\[
 \left.\frac{d^n}{dt^n}\lambda_t\right|_{t=0}(p)
 =(-i\log p)^n,
 \qquad 0\le n<N,
\tag{PR.9a}
\]

form a basis of `(C^F)^*`. Hence a fixed jet order `r` leaves a common invisible subspace of
dimension at least `N-r-1` when `N>r+1`.

The infinite path `t mapsto lambda_t in ell^infinity=(ell^1)'` is weak-star continuous but has no
weak-star derivative at zero with value in `ell^infinity`. More generally its `n`-th formal
derivative has coefficient `(-i log p)^n`, admitted only after passing to a weighted predual such
as

\[
 \ell^1_{\log^n}
 =\left\{x:\sum_p|x_p|(1+\log p)^n<\infty\right\}.
\tag{PR.9b}
\]

#### Proof

The matrix of `(PR.9a)` is a nonzero scalar-column multiple of the Vandermonde matrix on distinct
nodes `log p`; its determinant is nonzero. Rank--nullity gives the invisible dimension.

Weak-star continuity follows by dominated summation: for each `x in ell^1`, coordinatewise
continuity and `|p^(-it)|=1` let the limit pass through the absolutely convergent sum. If a
weak-star derivative `v in ell^infinity` existed at zero, testing against each basis vector `e_p`
would force `v_p=-i log p`, an unbounded sequence, contradiction. Weighted estimate `(PR.9b)`
makes the `n`-th coefficient functional bounded. `[PROVED HERE]`

This is an exact source version of recurrent observation with singular infinitesimal time: the
global orbit is continuous and recurrent, every finite jet system is complete at sufficient order,
but no single unweighted port chart admits its generator. Weighted preduals such as `(PR.9b)` are
examples of repairs; no uniqueness is asserted.

## 4. Positive observer and four-way independence

The port norm is

\[
 \|\lambda_t\|_{\ell^\infty}=1
\tag{PR.10}
\]

for every `t`. It is constant on the entire product torus. Therefore the following coexist:

1. recurrent observation with compact weak-star closure;
2. phase-blind positive norm;
3. unbounded logarithmic history and squared lift length;
4. topology-dependent port survival under reduction.

Theorem 5 adds another explicitly distinct datum: infinitesimal generator admission depends on a weighted
domain even where the global weak-star orbit is continuous.

The displayed countermodels prove specific nonimplications: positive norm does not determine time
or squared lift length; finite recurrence does not imply a global Hilbert port; weak-star continuity does
not imply an admitted derivative. No general logical independence theorem is claimed.

## 5. Relation to hypertranscendence and physics

This theorem does not identify HT with recurrence or noncompactness. Theorem 5 proves unbounded
finite-cutoff cotangent jet rank and a genuine generator-domain wall; analytic HT still requires a
separate theorem for all polynomial jet relations. The new result adds that the observer port and
its derivatives live in different admissibility charts.

The exact physical lesson is limited: recurrent boundary observation and positive norm do not
determine accumulated lift cost. Any Brown--Susskind or wormhole interpretation needs additional
source-derived history, generator, edge charge, and length/action data. The formulas prove only the
need for extra history data, not that it is a particular conjugate edge mode, and do not construct
a black-hole interior.

## 6. Conjecture/failure loops

### Loop A — recurrence selects a completion

**Failed:** the same finite and algebraic recurrent orbit exists in every completion phase.

**Survivor:** recurrence and completion admission are independent components of the route chart.

### Loop B — positive norm reconstructs lifted time

**Failed:** `(PR.10)` is constant while `(PR.8)--(PR.9)` are unbounded.

**Survivor:** endpoint recurrence requires an additional history/cost datum to recover accumulated
lift information. This theorem does not prove that the datum is a canonical conjugate variable.

### Loop C — Hilbert erasure destroys all phase information

**Failed:** it destroys the continuous one-port quotient, not the compatible system of finite
phase observers or the weak-star `ell^1`-dual orbit.

**Survivor:** a common field needs both its projective finite observers and the topology of their
global realization; choosing only a Hilbert endpoint loses the inverse-system history.

### Loop D — call this HT or a wormhole

**Failed as theatre:** neither differential-algebraic relation growth nor gravity reconstruction
is proved.

**Survivor:** exact acceptance gates for later realization: polynomial-prolongation comparison for
HT, and independently source-derived edge charge/action for physics.

## 7. Route-independent predictions

1. Any unweighted Hilbert route retaining `epsilon_t` as a bounded all-prime observer is false.
2. Any recurrence theorem using only finite prime phases is compatible with total global-port
   erasure; it cannot establish physical reconstruction.
3. Any positive observer factoring through `||lambda_t||_infinity` is blind to recurrence time and
   squared lift length.
4. A candidate common arithmetic/Fourier/recurrence geometry must specify whether its port lives
   in the primal space, continuous dual, weak-star compactification, or a Tate lattice; these are
   not interchangeable gauges.
5. If a physical horizon chart realizes this orbit, endpoint recurrence alone cannot reconstruct
   an interior history. A conjugate edge direction is one possible extra structure, not a
   consequence of this theorem.
6. A global time flow can exist weak-star continuously while its infinitesimal generator is absent
   from the same continuous-dual chart. Any common geometry must carry a rigged/scale domain, not
   only a compact orbit.

## 8. Literature and corpus boundary

Kronecker--Weyl, weak-star compactness, cotangent reduction, and dense-kernel arguments are
classical. The parent prime-orbit card already proves arithmetic/spectral/recurrence/prolongation
shadows, and the parent completion card proves the static port topology wall. This card's role is
their exact compatibility theorem under the same time-dependent port family. No external novelty
claim is needed.

## 9. No-go closure

- **Exact killing mechanism:** recurrence, positivity, and topology do not determine one another.
- **Strongest positive survivor:** uniform-in-time phase law `(PR.4)--(PR.5)`, weak-star
  recurrence/open-lift theorem `(PR.7)--(PR.10)`, and finite-jet/infinite-generator wall
  `(PR.9a)--(PR.9b)`.
- **New insight:** phase recurrence is compatible with multiple observer topologies and does not
  select one. The nontrivial new formula within this bridge is the weak-star
  continuity/non-differentiability wall for the literal prime-log generator.
- **Status:** dependency-closed paper proof; hostile repairs applied; Lean formalization
  complete and unconditional.

## Log

- 2026-08-09 — transported prime-log recurrence through the reduction--completion square and
  closed the `ell^1`, `ell^p`, `c0`, finite-torus, infinite weak-star, and finite lift-length claims.
- 2026-08-09 — hostile review identified exact isometric conjugacy `I_t=U_t^(-1)I_0`; demoted
  uniform phase law to compatibility bridge, corrected compactness to compact orbit closure, and
  weakened physical/independence claims.
