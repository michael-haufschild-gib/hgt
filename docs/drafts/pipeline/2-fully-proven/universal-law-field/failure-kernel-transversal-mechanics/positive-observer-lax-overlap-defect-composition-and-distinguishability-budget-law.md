# Positive-observer lax-overlap defect, composition, and distinguishability-budget law

- **ID:** ULF-FKT-OD-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** Finite positive observer aggregation is additive but only laxly preserves common
  support.  Its false-overlap defect is nonnegative, obeys an exact composition law, equals lost
  total-variation distinguishability, and vanishes for every profile pair exactly when the observer
  is injective.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [MECHANISM NOT OBJECT]
  [FALSE-OVERLAP LOCALIZATION] [LEAN-PROVED] [NOT RH]

## 1. Setup

Let `X,Y` be finite sets and let `f:X->Y` be an observer.  A profile is a real-valued function on
the source; nonnegative profiles are the intended failure-multiplicity case.  Define pushforward by

\[
  (f_!u)(y)=\sum_{x:f(x)=y}u(x),
  \tag{OD.1}
\]

and lattice meet pointwise by

\[
  (u\wedge v)(x)=\min\{u(x),v(x)\}.
  \tag{OD.2}
\]

Pushforward is additive.  It need not preserve meet.  Define its **false-overlap defect**

\[
  \boxed{
  \Omega_f(u,v)=f_!u\wedge f_!v-f_!(u\wedge v).}
  \tag{OD.3}
\]

The name records the mechanism: aggregation can make masses originating at different source points
appear common at one observer point.

## 2. Lax-overlap theorem

### Theorem 2.1

For all real profiles `u,v`,

\[
  f_!(u\wedge v)\le f_!u\wedge f_!v,
  \qquad \Omega_f(u,v)\ge0
  \tag{OD.4}
\]

pointwise.

### Proof

Since `u∧v<=u`, summing on every fibre gives `f_!(u∧v)<=f_!u`.  The same argument gives
`f_!(u∧v)<=f_!v`.  It is therefore at most their pointwise minimum.  Subtracting proves
nonnegativity.  QED.

### Exact fibre formula

For `y in Y`, put

\[
 P_y=\sum_{f(x)=y}(u(x)-v(x))_+,
 \qquad
 N_y=\sum_{f(x)=y}(v(x)-u(x))_+.
 \tag{OD.5}
\]

Then

\[
  \boxed{\Omega_f(u,v)(y)=\min(P_y,N_y).}
  \tag{OD.6}
\]

Indeed, write `c=u∧v`, `r=u-c`, and `s=v-c`.  On each source coordinate at least one of `r,s`
is zero, while `r=(u-v)_+` and `s=(v-u)_+`.  Fibrewise linearity gives

\[
 \min(f_!u,f_!v)-f_!c
 =\min(f_!r,f_!s)=\min(P_y,N_y).
\]

Consequently `Omega_f(u,v)(y)=0` exactly when the sign of `u-v` does not cross inside the fibre:

\[
 \bigl(\forall x\in f^{-1}(y),\ u(x)\le v(x)\bigr)
 \quad\text{or}\quad
 \bigl(\forall x\in f^{-1}(y),\ v(x)\le u(x)\bigr).
 \tag{OD.7}
\]

The forward implication follows because a finite sum of nonnegative terms is zero only when every
term is zero.  The reverse implication is immediate from `(OD.5)`.

## 3. Exact composition law

Let `g:Y->Z` be another finite observer.

### Theorem 3.1

\[
 \boxed{
 \Omega_{g\circ f}(u,v)
 =\Omega_g(f_!u,f_!v)+g_!\Omega_f(u,v).}
 \tag{OD.8}
\]

### Proof

Finite fibre summation gives strict functoriality `(g o f)_!=g_!f_!`.  Insert and subtract
`g_!(f_!u∧f_!v)`:

\[
\begin{aligned}
\Omega_{gf}(u,v)
 &=g_!f_!u\wedge g_!f_!v-g_!f_!(u\wedge v)\\
 &=\bigl[g_!f_!u\wedge g_!f_!v-g_!(f_!u\wedge f_!v)\bigr]\\
 &\quad+g_!\bigl[f_!u\wedge f_!v-f_!(u\wedge v)\bigr].
\end{aligned}
\]

The two summands are exactly those in `(OD.8)`.  QED.

Iterating gives, for `F_n=f_n...f_1`,

\[
 \Omega_{F_n}(u,v)
 =\sum_{j=1}^n
 (f_n...f_{j+1})_!
 \Omega_{f_j}((f_{j-1}...f_1)_!u,(f_{j-1}...f_1)_!v).
 \tag{OD.9}
\]

Every term is nonnegative.  Positive downstream processing transports or adds false overlap; it
cannot cancel it.

## 4. Exact distinguishability budget

Define unnormalized finite total variation by

\[
  \operatorname{TV}(u,v)=\frac12\sum_x|u(x)-v(x)|
  \tag{OD.10}
\]

and total defect mass by `|Omega_f|=sum_y Omega_f(y)`.

### Theorem 4.1

\[
  \boxed{
  |\Omega_f(u,v)|
  =\operatorname{TV}(u,v)-\operatorname{TV}(f_!u,f_!v).}
  \tag{OD.11}
\]

### Proof

For real numbers `a,b`,

\[
 |a-b|=a+b-2\min(a,b).
 \tag{OD.12}
\]

Summing `(OD.12)` on `X` and `Y`, using preservation of total mass by `f_!`, gives

\[
\begin{aligned}
2\bigl(\operatorname{TV}(u,v)-\operatorname{TV}(f_!u,f_!v)\bigr)
 &=2\sum_y\min(f_!u,f_!v)-2\sum_x\min(u,v)\\
 &=2\sum_y\Omega_f(u,v)(y).
\end{aligned}
\]

Divide by two.  QED.

For a chain of observers, total-variation loss therefore decomposes as the sum of stage losses.
When `u,v` are probability profiles, the cumulative budget is at most one.  Thus normalized
positive observer loss cannot by itself be an unbounded action, complexity, or lifted-history
length.

## 5. Strict observers

### Theorem 5.1

For a finite observer `f:X->Y`, the following are equivalent.

1. `f` is injective.
2. `Omega_f(u,v)=0` for every pair of real profiles `u,v`.
3. `f_!` preserves pointwise meet for every pair of real profiles.

### Proof

If `f` is injective, every fibre contains at most one source point, so fibre summation plainly
preserves minimum.  This proves `1=>3`, and `(OD.3)` gives `3=>2`.

If `f` is not injective, choose distinct `x,x'` with `f(x)=f(x')=y`.  Let `u` be unit mass at `x`
and `v` unit mass at `x'`.  Their source meet is zero, but both pushforwards have unit mass at `y`.
Hence `Omega_f(u,v)(y)=1`, contradicting item 2.  Thus `2=>1`.  QED.

This is stronger than ordinary data-processing inequality: it classifies deterministic observers
that never manufacture commonality.

## 6. Exact false-repair witness

Take source kernels `K_1={x}` and `K_2={x'}` with `x!=x'`, and identify them by an observer
`f(x)=f(x')=y`.

- A source transversal must contain both `x` and `x'`, so its minimum size is two.
- Both observed kernels are `{y}`, so the observed minimum transversal has size one.
- Their indicator profiles satisfy `Omega_f(1_{K_1},1_{K_2})(y)=1`.

Thus false overlap is operational: it is exactly the local witness that one observed repair has
been made to look shared by identification of two independent source repairs.  Pulling `{y}` back
recovers the size-two fibre-saturated source repair, agreeing with ULF-FKT-1.

## 7. Arbitrary-kernel no-go and survivor status

Every clutter is the exact minimal-kernel family of an extensive, monotone, idempotent consequence
operator; the companion failed-route card proves this directly.  Therefore no matroid, antimatroid,
Helly, or exchange law follows from static failure-kernel axioms.

The theorem above survives that no-go because it constrains typed transport, not static families.
Its mathematical delta is the exact vector and chain law locating false shared repair inside a
composite observer pipeline.

## 8. Hostile audit and sharp boundaries

1. **Established parents.** Total-variation data processing, finite sufficient statistics,
   positive lattice maps, and monomial depolarization are classical.  This card is a bridge and
   field synthesis, not a priority claim.
2. **Positivity/order is load-bearing.** The nonnegative interpretation of `Omega` uses lattice
   order.  Signed cancellation can migrate or cancel and requires separate oriented data.
3. **Pairwise is not complete.** Binary defect does not reconstruct arbitrary higher kernel
   incidence.
4. **Deterministic finite scope.** Markov kernels, measure spaces, Banach lattices, and completion
   require separate admission proofs.
5. **Not a universal route realization.** A corpus application must construct source profiles and
   observer pushforward before endpoint specialization.
6. **Bounded normalized budget.** No physical length, wormhole action, HT rank, or RH criterion is
   inferred from `(OD.11)`.

Primary parents:

- Baez--Courser, *Coarse-Graining Open Markov Processes*,
  <https://arxiv.org/abs/1710.11343>;
- Fritz, *A synthetic approach to Markov kernels, conditional independence and theorems on
  sufficient statistics*, <https://arxiv.org/abs/1908.07021>;
- Mohammadi--Pascual-Ortigosa--Saenz-de-Cabezon--Wynn, *Polarization and depolarization of monomial
  ideals with application to multistate system reliability*,
  <https://arxiv.org/abs/1807.05743>;
- Morey--Villarreal, *Edge ideals: algebraic and combinatorial properties*,
  <https://arxiv.org/abs/1012.5329>;
- Fang--Huang--Kudaybergenov--Xu, *Disjointness-preserving mappings on Calkin operator spaces and
  positive isometries*, <https://arxiv.org/abs/2607.26563>.

## 9. Lean certification

The exact finite theorem is formalized in
`GaloisForLFunctions.HTGeometry.ConstitutivePositiveOverlapDefect` and imported by the
`UniversalLawField` umbrella.  Certified surface:

- fibre pushforward composition;
- lax meet and nonnegative defect;
- exact defect composition;
- total-variation-loss identity;
- injectivity iff universal zero defect;
- the two-source false-overlap witness.

Direct foreground elaboration, formal lint, axiom print, and final umbrella build pass.  Significant
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Final build:
`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` — 11,482 jobs, green.

## Log

- 2026-08-10 — paper proof closed after arbitrary-clutter no-go and internal/external parent audit;
  promoted as positive survivor, without RH or novelty claim.
- 2026-08-10 — Lean certification closed; module wired into Universal Law Field umbrella.
