# Concurrent causal heap-accessibility law

- **ID:** `concurrent-causal-heap-accessibility-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / preparation invariant / Brown-front advance
- **Parents:** `local-circuit-heap-capacity-law.md`,
  `first-entrance-gate-renewal-prefix-law.md`,
  `static-orbit-net-no-go-and-circuit-bellman-law.md`
- **Status:** `[PAPER-PROVED] [PROVED HERE] [FRONTIER ADVANCE]
  [CLASSICAL TRACE-PROBABILITY ENGINE] [APPLICATION NOVELTY UNVERIFIED]
  [LEAN DEFERRED]`
- **Date:** 2026-08-13

## Public sentence

First arrival in a local circuit is not sequential after support-disjoint gates are identified:
distinct causal prefixes can share the same future.  A finite probability law on circuit heaps turns
the **union** of all successful causal-prefix cylinders into a bounded preparation reporter.  Its
negative logarithm is exactly the least information cost of forcing a successful causal history;
it has exact recurrence value, intrinsic dependence-graph entropy, and no ordering or shared-future
overcount.

This theorem constructs the correct concurrent first-arrival invariant.  It does not prove that a
static local Hamiltonian makes the invariant small at Brown's first-cut time.

## 1. Setup

Let

\[
 \mathcal M=\mathcal M(\Sigma,I)
\]

be the trace monoid from `local-circuit-heap-capacity-law.md`: `Sigma` is a finite alphabet of
`M` local gates, and distinct letters commute in the quotient exactly when their padded supports
are disjoint.  Let `Delta` be the maximum degree of the complementary dependence graph.  Write
`|u|` for trace length and

\[
 \mathcal Z(z)=\sum_{u\in\mathcal M}z^{|u|}.
 \tag{1}
\]

The proved pair-projection bound gives

\[
 \mathcal Z(z)\le (1-2^\Delta z)^{-M}
 \qquad(0<z<2^{-\Delta}).
 \tag{2}
\]

The left-prefix order is

\[
 u\preceq T \quad\Longleftrightarrow\quad
 T=uv\text{ for some }v\in\mathcal M,
 \qquad
 \uparrow u=\{T:u\preceq T\}.
 \tag{3}
\]

A prefix is an order ideal of the circuit heap, hence a causal partial execution rather than a
choice of linear ordering of independent gates.

## 2. Finite heap probability and exact cylinders

### Lemma A -- cancellation

The trace monoid is left and right cancellative.

### Proof

It is enough to prove left cancellation.  Suppose `uv=uw`.  Trace equality preserves the unary
multiplicity of every letter and the binary projection to every dependent pair.  In every such
free unary or binary word, the projection of `u` is a common left prefix, so free-monoid
cancellation makes the corresponding projections of `v` and `w` equal.  The pair-projection
reconstruction proved in the heap-capacity parent then gives `v=w`.  The right-hand argument is
the same. `square`

For every `z` in the convergence interval of `(1)`, define

\[
 \pi_z(T)={z^{|T|}\over\mathcal Z(z)}.
 \tag{4}
\]

This is a probability law on finite circuit heaps.

### Theorem A -- exact causal-cylinder law

For every trace `u`,

\[
 \boxed{\pi_z(\uparrow u)=z^{|u|}.}
 \tag{5}
\]

If `Pref(T)={u:u\preceq T}`, then

\[
 \boxed{\mathbb E_{\pi_z}|\operatorname{Pref}(T)|=\mathcal Z(z).}
 \tag{6}
\]

### Proof

By Lemma A, \(v\mapsto uv\) is a bijection from `mathcal M` onto `uparrow u`.  Length is additive,
so

\[
 \pi_z(\uparrow u)
 ={1\over\mathcal Z(z)}\sum_{v\in\mathcal M}z^{|uv|}
 =z^{|u|}.
\]

Every prefix `u` of `T` has a unique residual `v` with `T=uv`.  Tonelli's theorem for nonnegative
series therefore gives

\[
 \begin{aligned}
 \mathbb E_{\pi_z}|\operatorname{Pref}(T)|
 &= {1\over\mathcal Z(z)}
    \sum_T z^{|T|}\#\{(u,v):T=uv\}\\
 &= {1\over\mathcal Z(z)}
    \sum_{u,v}z^{|u|+|v|}
 =\mathcal Z(z).
 \end{aligned}
\]

This proves `(5)` and `(6)`. `square`

## 3. Causal accessibility and preparation action

Let `mathcal M` act on a metric state space `X` by circuit evaluation.  Fix a robust seed target
`A subset X` and define the ordinary robust circuit complexity

\[
 C_A(x)=\min\{|u|:x\in\operatorname{ev}(u)A\},
 \tag{7}
\]

with value `infinity` if no trace succeeds.  For a random finite heap `T`, ask whether **some causal
prefix** succeeds:

\[
 \begin{aligned}
 E_x&=\{T:\exists u\preceq T,\ x\in\operatorname{ev}(u)A\},\\
 F_{A,z}(x)&=\pi_z(E_x),\\
 J_{A,z}(x)&=-\log F_{A,z}(x).
 \end{aligned}
 \tag{8}
\]

Use `J=+infinity` when `F=0`.  The quantity `F` is the concurrent causal accessibility and `J` is
its preparation action.

### Theorem B -- exact preparation-action law

For every `x`,

\[
 \boxed{0\le F_{A,z}(x)\le1.}
 \tag{9}
\]

If `c=C_A(x)<infinity`, then

\[
 \boxed{
 z^c\le F_{A,z}(x)
 \le \pi_z\{|T|\ge c\}.}
 \tag{10}
\]

In particular, exact robust recurrence has exact value

\[
 C_A(x)=0\quad\Longrightarrow\quad F_{A,z}(x)=1,
 \quad J_{A,z}(x)=0.
 \tag{11}
\]

For every finite positive endpoint measure `nu` and integer `s>=0`,

\[
 \boxed{
 \nu\{C_A\le s\}
 \le z^{-s}\int_XF_{A,z}(x)\,d\nu(x).}
 \tag{12}
\]

Finally, if `F_{A,z}(x)>0`, then

\[
 \boxed{
 J_{A,z}(x)
 =\inf\{D(Q\Vert\pi_z):Q(E_x)=1\}.}
 \tag{13}
\]

The unique minimizer up to `pi_z`-null sets is `Q=pi_z(\,cdot\mid E_x)`.

### Proof

Equation `(9)` follows because `F` is the probability of the union in `(8)`.  If `u` is a shortest
successful trace, then `uparrow u subset E_x`; `(5)` gives the lower bound in `(10)`.  Every
successful prefix has length at least `c`, and a prefix cannot be longer than its containing heap,
which gives the upper bound.  When `c=0`, the identity trace succeeds and its cylinder is the whole
sample space, proving `(11)`.

If `C_A(x)<=s`, the lower bound in `(10)` and `0<z<1` give `F_{A,z}(x)>=z^s`.
Integrating the resulting pointwise inequality

\[
 \mathbf1_{\{C_A\le s\}}(x)\le z^{-s}F_{A,z}(x)
\]

proves `(12)`.

For `(13)`, every `Q` supported on `E_x` satisfies the chain-rule identity

\[
 D(Q\Vert\pi_z)
 =D(Q\Vert\pi_z(\,\cdot\mid E_x))-\log\pi_z(E_x).
\]

Nonnegativity and rigidity of relative entropy prove the claim. `square`

### Corollary B.1 -- quantitative complexity sandwich

For `c=C_A(x)>=1` and any `z<y` inside the convergence interval,

\[
 F_{A,z}(x)
 \le\left({z\over y}\right)^c
       {\mathcal Z(y)\over\mathcal Z(z)}.
 \tag{14}
\]

In the safe interval `0<z<2^{-Delta}`, if

\[
 2^\Delta z<{c\over M+c},
 \tag{15}
\]

then choosing `2^Delta y=c/(M+c)` yields

\[
 \boxed{
 F_{A,z}(x)
 \le (2^\Delta z)^c
       \left(1+{M\over c}\right)^c
       \left(1+{c\over M}\right)^M.}
 \tag{16}
\]

Together with `(10)`, this gives

\[
 \begin{aligned}
 &c\log {1\over2^\Delta z}
  -c\log\left(1+{M\over c}\right)
  -M\log\left(1+{c\over M}\right)\\
 &\hspace{35mm}\le J_{A,z}(x)
 \le c\log {1\over z}.
 \end{aligned}
 \tag{17}
\]

### Proof

On `|T|>=c`, `z^{|T|}<=(z/y)^c y^{|T|}`.  Sum and divide by `Z(z)` to prove `(14)`.
Use `(2)`, `Z(z)>=1`, and minimize

\[
 (z/y)^c(1-2^\Delta y)^{-M}
\]

at `2^Delta y=c/(M+c)` to obtain `(16)`.  Taking negative logarithms and combining with
`F>=z^c` proves `(17)`. `square`

## 4. Exact relation to Green incidence and first entrance

The positive heap Green reporter from the parent is

\[
 \mathcal G_{A,z}(x)
 =\sum_{u\in\mathcal M}z^{|u|}
  \mathbf1_{\operatorname{ev}(u)A}(x).
 \tag{18}
\]

For `T` distributed by `pi_z`, the expected number of successful causal prefixes is exactly
`mathcal G_{A,z}(x)`.  Hence

\[
 \boxed{F_{A,z}(x)\le\min\{1,\mathcal G_{A,z}(x)\}.}
 \tag{19}
\]

The inequality can be strict because successful causal cylinders overlap.

If the independence relation is empty, traces are ordinary words.  Minimal successful prefixes
form a prefix-free set and their cylinders are disjoint.  Then `(8)` reduces exactly to the
discounted first-entrance mass

\[
 F_{A,z}(x)
 =\sum_{u\text{ first successful}}z^{|u|}.
 \tag{20}
\]

For genuine concurrency, ordinary prefix-free summation is false.  If independent letters `a`
and `b` are both successful minimal prefixes, then

\[
 \uparrow a\cap\uparrow b=\uparrow(ab),
 \qquad
 \pi_z(\uparrow a\cup\uparrow b)=2z-z^2,
 \tag{21}
\]

whereas summing the two cylinder masses gives `2z`.  Equation `(8)`, not a tracewise Kraft sum, is
the exact concurrent replacement.

### Proof of `(19)--(21)`

The expected successful-prefix count is

\[
 {1\over\mathcal Z(z)}
 \sum_{u,v}z^{|u|+|v|}
 \mathbf1_{\operatorname{ev}(u)A}(x)
 =\mathcal G_{A,z}(x).
\]

The probability of at least one success is at most its expected count, proving `(19)`.  In a free
monoid every finite word has a linearly ordered prefix set and therefore a unique first successful
prefix, proving `(20)`.  For independent `a,b`, a trace has both prefixes exactly when it has their
two-element heap as a prefix; `(5)` then proves `(21)`. `square`

## 5. Completed-phase capacity without causal overcount

Suppose a probability target law `mu` obeys the uniform cap bound

\[
 \mu(\operatorname{ev}(u)A)\le B
 \qquad(u\in\mathcal M).
 \tag{22}
\]

### Theorem C -- causal heap-capacity law

For every `s>=0`,

\[
 \boxed{
 \mu\{C_A\le s\}
 \le Bz^{-s}\mathcal Z(z)
 \le Bz^{-s}(1-2^\Delta z)^{-M}.}
 \tag{23}
\]

For `s>=1`, choosing `z=s/[2^Delta(M+s)]` gives

\[
 \boxed{
 \mu\{C_A\le s\}
 \le B,2^{\Delta s}
       \left(1+{M\over s}\right)^s
       \left(1+{s\over M}\right)^M.}
 \tag{24}
\]

### Proof

For each heap `T`, the target points accessible through one of its causal prefixes lie in the
union of at most `|Pref(T)|` sets in `(22)`.  Tonelli, the union bound **inside one heap**, and
`(6)` give

\[
 \int_XF_{A,z}\,d\mu
 =\mathbb E_{\pi_z}\mu\!\left(
   \bigcup_{u\preceq T}\operatorname{ev}(u)A\right)
 \le B\,\mathbb E_{\pi_z}|\operatorname{Pref}(T)|
 =B\mathcal Z(z).
\]

Now use `(12)` and `(2)`.  The stated optimization is the same one-variable calculation as in
Corollary B.1. `square`

The exponent in `(24)` equals the parent heap-capacity exponent, as it must in the worst case.
The advance is not a better completed-phase exponent.  It is the bounded, first-arrival,
preparation-sensitive observable `(8)` that realizes this capacity while identifying all shared
causal futures.

## 6. Dimension-free soft accessibility

Hard tube boundaries are unnecessary.  Assume `A` is closed and fix `delta>0`.  For a closed set
`B`, put

\[
 \varphi_{B,\delta}(x)
 =\left(1-{d(x,B)\over\delta}\right)_+,
 \tag{25}
\]

and define the soft causal reporter

\[
 \boxed{
 S_{A,z,\delta}(x)
 =\mathbb E_{T\sim\pi_z}
   \max_{u\preceq T}\varphi_{\operatorname{ev}(u)A,\delta}(x).}
 \tag{26}
\]

The maximum is over a nonempty finite set because the identity is always a prefix.

### Theorem D -- soft causal-accessibility law

For all `x,y in X`,

\[
 \boxed{
 0\le F_{A,z}(x)\le S_{A,z,\delta}(x)\le1,
 \qquad
 |S_{A,z,\delta}(x)-S_{A,z,\delta}(y)|
 \le {d(x,y)\over\delta}.}
 \tag{27}
\]

If `A^(delta)={x:d(x,A)<=delta}`, then

\[
 S_{A,z,\delta}(x)\le F_{A^{(\delta)},z}(x).
 \tag{28}
\]

Consequently, for every finite positive endpoint measure `nu` and `s>=0`,

\[
 \boxed{
 \nu\{C_A\le s\}
 \le z^{-s}\int_XS_{A,z,\delta}\,d\nu.}
 \tag{29}
\]

If `mu` obeys the uniform soft-cap bound

\[
 \int_X\varphi_{\operatorname{ev}(u)A,\delta}(x)\,d\mu(x)
 \le B_\delta
 \qquad(u\in\mathcal M),
 \tag{30}
\]

then

\[
 \boxed{
 \int_XS_{A,z,\delta}\,d\mu
 \le B_\delta\mathcal Z(z).}
 \tag{31}
\]

For probability endpoint laws `nu,mu` with finite first moment,

\[
 \boxed{
 \left|\int_XS_{A,z,\delta}\,d\nu
       -\int_XS_{A,z,\delta}\,d\mu\right|
 \le {W_1(\nu,\mu)\over\delta}.}
 \tag{32}
\]

The boundary regularity in `(27)` and `(32)` is independent of circuit depth, alphabet size,
dependence degree, number of causal prefixes, and Hilbert-space dimension.

### Proof

Distance to a nonempty closed set is one-Lipschitz, and the clipped ramp in `(25)` is
`1/delta`-Lipschitz.  A finite maximum of functions with this common Lipschitz constant has the
same constant; expectation preserves it.  This proves the range and Lipschitz parts of `(27)`.
On the hard success event, one prefix score equals one, so `F<=S`.  A positive prefix score implies
membership in the `delta`-enlarged prefix target; this gives `(28)`.

If `C_A(x)<=s`, choose a successful `u` with `|u|<=s`.  On `uparrow u` the maximum in `(26)` is one,
so `(5)` gives `S(x)>=z^|u|>=z^s`; integration proves `(29)`.

For each `T`, bound the maximum in `(26)` by the sum over `Pref(T)`.  Tonelli, `(30)`, and `(6)`
give `(31)`.  Equation `(32)` is the Kantorovich--Rubinstein inequality applied to the
`1/delta`-Lipschitz function in `(27)`. `square`

If `X` is a unit sphere with its norm metric and
`Phi_H(t)=exp(-itH)chi`, Duhamel's formula adds the source-stability estimate

\[
 \boxed{
 |S_{A,z,\delta}(\Phi_H(t))-S_{A,z,\delta}(\Phi_K(t))|
 \le {|t|\over\delta}\,\|H-K\|_{\rm op}.}
 \tag{33}
\]

Indeed `||exp(-itH)-exp(-itK)||_op<=|t|||H-K||_op`, and `(27)` finishes the proof.  Thus approximate
tubes no longer force a dimension-linear or circuit-count-linear regularity remainder.  A useful
first-cut estimate must still make their mean exponentially small; smoothing does not supply that
mean estimate by itself.

## 7. Exact change to the static-Hamiltonian first-cut core

Let `nu_t` be the physical endpoint law generated at laboratory time `t` by one ordinary static
local-Hamiltonian ensemble, after the already identified recurrence and fast-forwardable-carrier
parts are separated.  Equation `(12)` reduces Brown's first-cut estimate to the single bounded
quantity

\[
 \boxed{
 \int_XF_{A,z}(x)\,d\nu_t(x)
 =\mathbb E_H\,\pi_z\{T:\exists u\preceq T,
   \ \Phi_H(t)\in\operatorname{ev}(u)A\}.}
 \tag{34}
\]

This is strictly more intrinsic than the linear heap incidence whenever different causal
preparations share completions.  It retains the occupied physical endpoint before source
integration, retains distinct source fibres and distinct circuit traces, quotients only exact
independent-gate reorderings, and is bounded by one before any replica or coarea estimate.

For approximate-tube analysis, `(29)` permits replacement of `(34)` by
`int S_(A,z,delta) dnu_t`.  Equations `(27)` and `(33)` keep its endpoint and source regularity
dimension-free.  This directly removes the previous dimension-linear boundary remainder; it does
not remove the exponential small-mean obligation.

What remains open is a **quenched physical-time decay theorem for `(34)`**, or its soft majorant,
strong enough to beat
`z^s` at `s=Theta(D)`.  No orbit-net covering number implies such decay: `(34)` asks whether actual
causal preparations hit the physical endpoint, not whether an adversarial small net covers the
static orbit.

## 8. Conjecture--failure--survivor loop

### C0 -- ordinary first-hit words remain prefix-free after commuting disjoint gates

Verdict: `[FALSIFIED]` by `(21)`.  In the trace prefix order, incomparable minimal hits can have a
common extension.

### C1 -- sum the trace-cylinder masses anyway

Verdict: `[FALSIFIED AS EXACT REPORTER]`.  It gives the Green expectation `(18)`, which double
counts every heap with several successful causal prefixes and need not have recurrence value one.

### C2 -- normalize the Green expectation by its partition function

Verdict: `[FALSIFIED]`.  Division by `Z(z)` destroys the exact cylinder identity `(5)` and makes
the value of a single preparation depend on unrelated circuits elsewhere in the monoid.

### C3 -- take the probability of the causal-prefix union

Verdict: `[PROVED SURVIVOR]`.  Theorems A--C give exact recurrence, an information projection,
complexity calibration, intrinsic heap capacity, and the free-word first-entrance reduction.

### C4 -- causal accessibility alone proves Brown's first cut

Verdict: `[FALSE AS A CONCLUSION]`.  It removes ordering and shared-future overcount and replaces
an unbounded incidence sum by the bounded preparation event `(34)`.  Static source-time decay of
that event remains the hard frontier.

### C5 -- soften each circuit tube and sum its regularity cost

Verdict: `[FALSIFIED AS NECESSARY]`.  Summing over circuits makes a boundary remainder grow with
the number of descriptions.  The max-inside-expectation reporter `(26)` has the same complexity
calibration and Lipschitz constant `1/delta`, independent of that number.

## 9. Hostile audit

1. **No growth theorem claimed.**  Theorem C reproduces the completed-phase linear-capacity
   exponent.  It does not prove the Brown ramp or its onset.
2. **Classical ingredients are credited.**  Trace monoids, Möbius generating functions, and
   Bernoulli/sub-Bernoulli trace measures predate this work.  Novelty is assigned provisionally
   only to their causal first-arrival/preparation-action use in static quantum-complexity bounds.
3. **The probability is auxiliary, not physical noise.**  `pi_z` samples candidate preparation
   heaps.  Physical randomness remains solely in `nu_t` or the source Hamiltonian in `(34)`.
4. **Finite alphabet remains load-bearing.**  Continuous gate sets need a robust parameter net and
   its entropy.  No continuous-alphabet claim is made.
5. **Only exact disjoint-support commutations are quotiented.**  Approximate commutation and hidden
   gate identities are not used.  Omitting further identities weakens but cannot invalidate upper
   bounds.
6. **The safe convergence radius is not sharp.**  `2^{-Delta}` comes from the proved pair-projection
   bound.  The exact trace growth radius or Möbius root can replace it throughout.
7. **Priority remains provisional.**  Targeted searches found trace-monoid probability theory and
   quantum-circuit enumeration by partially commutative monoids, but not `(8)`, `(13)`, `(26)`, or
   `(34)`.
   Absence from a search is not a novelty proof.
8. **Lean deferred by instruction.**  No formal source is written while the shared corpus is being
   refactored.

## 10. External boundary

- Cartier and Foata, *Problèmes combinatoires de commutation et réarrangements* (1969), supplies
  the classical trace-monoid foundation.
- Abbes and Mairesse, *Uniform and Bernoulli measures on the boundary of trace monoids*
  (arXiv:1407.5879), develops the probabilistic trace-monoid layer and Möbius valuations.  The
  finite Boltzmann law `(4)` and cylinder calculation are not claimed as standalone probability
  novelty.
- *Enumeration of Circuits with n Quantum Gates* (2024) applies partially commutative monoids to
  quantum-circuit enumeration.  Enumeration itself is not the claim here.

## Gates

- [x] cancellation and exact finite-heap cylinder law
- [x] exact expected causal-prefix count
- [x] bounded concurrent first-arrival reporter
- [x] relative-entropy preparation-action characterization
- [x] complexity sandwich and recurrence collapse
- [x] free-word reduction and explicit concurrency falsifier
- [x] completed-phase capacity recovery
- [x] dimension-free soft-tube reporter and transport stability
- [x] exact bounded first-cut target
- [x] hostile and external collision audit
- [ ] quenched decay of `(34)` for one ordinary static local-Hamiltonian ensemble
- [ ] Lean formalization after corpus refactor

## Lean progress

Modules: `GaloisForLFunctions.RHTower.CircuitTraceMonoid`,
`GaloisForLFunctions.RHTower.CircuitTraceBoltzmann`,
`GaloisForLFunctions.RHTower.CircuitCausalAccessibility`.

Formalized unconditionally:

| Card item | Lean declaration |
|---|---|
| trace monoid `(3)`, prefix order `(3)` | `Trace`, `traceMk`, `traceLen`, `TracePrefix`, `traceCylinder` |
| Lemma A cancellation | `trace_mul_left_cancel`, `trace_mul_right_cancel` |
| length grading | `traceGradeEquiv` |
| `(1)`, `(2)` | `tracePartition`, `one_le_tracePartition`, `tracePartition_le` |
| `(4)` | `traceMass` |
| `(5)` | `traceMass_traceCylinder` (via `traceCylinderEquiv`) |
| `(6)` | `tsum_tracePrefixCount` |
| `(8)` | `causalSuccessEvent`, `causalAccessibility`, `preparationAction` |
| `(9)` | `causalAccessibility_nonneg`, `causalAccessibility_le_one` |
| `(10)` | `pow_le_causalAccessibility`, `causalAccessibility_le_longHeaps` |
| `(11)` | `causalAccessibility_eq_one`, `preparationAction_eq_zero` |
| `(12)` | `measure_heapAccessible_le_causalAccessibility` |
| `(14)` | `causalAccessibility_le_ratio` |
| `(15)`, `(16)` | `causalAccessibility_le_optimal` |
| `(17)` | `preparationAction_sandwich` |
| `(18)`, `(19)` | `traceGreenReporter`, `causalAccessibility_le_traceGreenReporter` |
| `(21)` | `traceCylinder_inter_of_independent`, `traceMass_union_cylinders_of_independent` |
| `(22)`--`(24)` | `measure_heapAccessible_le_capacity`, `measure_heapAccessible_le_capacity_optimal` |

Every declaration above reports exactly `propext`, `Classical.choice`, `Quot.sound`.

Still to formalize on this card: the relative-entropy characterization `(13)`, the free-word
first-entrance reduction `(20)`, and the soft causal reporter `(25)`--`(33)`.
