# Static-orbit net no-go and circuit Bellman law

- **ID:** `static-orbit-net-no-go-and-circuit-bellman-law`
- **Stage:** 3-formalized
- **Formalized companion:** `./static-orbit-net-no-go-and-circuit-bellman-law-formalized.md`
- **Lean:** Theorems A–D formalized in `HTGeometry/EuclideanSphereCoveringBound.lean`,
  `HTGeometry/StaticOrbitNetBellmanLaw.lean` and `HTGeometry/ExactPenaltyCircuitBellman.lean`
- **Type:** theorem / geometric no-go / exact circuit-structured survivor
- **Parents:** `low-replica-complete-incidence-influence-law.md`,
  `../1-in-progress/quenched-krylov-circuit-incidence-front-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER CORRECTION] [EXTERNAL PRIORITY OPEN] [LEAN-PROVED]`
- **Date:** 2026-08-09

## Public sentence

Smoothness of a static quantum orbit cannot by itself explain circuit growth: at Brown time the
entire Hamiltonian-ensemble image has a net with only `exp(O(n^2))` points, so a geometrically tiny
target dictionary can cover every endpoint.  A valid proof must use the recursive local-gate law
that generates short circuits, not target cardinality, Jacobian volume, or coarea alone.

## Theorem A -- every Lipschitz static-orbit image has a small complete cover

Let `Omega` be a compact metric space and `F:Omega->X` an `L`-Lipschitz map into a metric space.
If `A` is an `eta`-net of `Omega`, then

\[
 Z=F(A)                                                         \tag{1}
\]

is an `L eta`-net of `F(Omega)`.  Hence

\[
 \boxed{
 N(F(\Omega),\epsilon)
 \le N(\Omega,\epsilon/L),}                                    \tag{2}
\]

where `N` denotes the metric covering number.

For the Euclidean unit sphere `S^(m-1)` and `0<eta<=2`,

\[
 \boxed{
 N(S^{m-1},\eta)\le(1+2/\eta)^m.}                              \tag{3}
\]

Consequently every `L`-Lipschitz sphere image has an `epsilon`-net of size at most

\[
 \boxed{
 \left(1+{2L\over\epsilon}\right)^m.}                          \tag{4}
\]

### Proof

For every `omega`, choose `a in A` with `d(omega,a)<=eta`; then
`d(F(omega),F(a))<=L eta`, proving `(2)`.  For `(3)`, take a maximal `eta`-separated subset of the
unit sphere.  Its ambient Euclidean balls of radius `eta/2` are disjoint and lie in the ball of
radius `1+eta/2`.  Comparing `m`-dimensional volumes gives

\[
 |A|(\eta/2)^m\le(1+\eta/2)^m,
\]

so `|A|<=(1+2/eta)^m`.  Maximality makes `A` an `eta`-net.  Substitute `eta=epsilon/L` to obtain
`(4)`; if `epsilon/L>2`, one point is enough.

## Theorem B -- application to an ordinary local-Hamiltonian shell

Let

\[
 H(\theta)=\sum_{a=1}^m\theta_aP_a,
 \qquad \theta\in S^{m-1},
 \qquad \|P_a\|_{\rm op}\le1,                                 \tag{5}
\]

and fix a unit seed `chi`.  Duhamel's inequality gives

\[
 \begin{aligned}
 \|e^{-itH(\theta)}\chi-e^{-itH(\theta')}\chi\|
 &\le |t|\,\|H(\theta)-H(\theta')\|_{\rm op}\\
 &\le |t|\sqrt m\,\|\theta-\theta'\|_2.                      \tag{6}
 \end{aligned}
\]

Therefore there is a finite target set `Z_(t,epsilon)`, consisting of actual orbit endpoints, such
that

\[
 \boxed{
 |Z_{t,\epsilon}|
 \le\left(1+{2|t|\sqrt m\over\epsilon}\right)^m}              \tag{7}
\]

and

\[
 \boxed{
 \forall\theta\in S^{m-1}\quad
 \min_{z\in Z_{t,\epsilon}}
 \|e^{-itH(\theta)}\chi-z\|\le\epsilon.}                      \tag{8}
\]

For the path-local Pauli shell, `m=Theta(n)`.  At Brown saturation time `|t|=Theta(D/poly(n))`
with `D=2^n`,

\[
 \log|Z_{t,\epsilon}|=O(m\log(t\sqrt m/\epsilon))=O(n^2)       \tag{9}
\]

at fixed error.  By contrast, a depth `s=Theta(D/log M_n)` dictionary permits
`log(M_n^(s+1))=Theta(D)` circuit words.  Thus target count and source-image covering entropy leave
exponentially more than enough labels to cover the entire physical graph.

Equation `(8)` is deliberately an adversarial geometric cover: its targets need not be shallow.
That is precisely the conclusion.  Any proposed Brown proof whose hypotheses cannot distinguish
`Z_(t,epsilon)` from the actual shallow-circuit image cannot prove circuit growth.

## Corollary -- purely geometric incidence mechanisms are incomplete

No upper bound on complete shortcut mass can follow uniformly from only

1. source dimension and source volume;
2. Lipschitz, smooth, analytic, or finite-type regularity of the endpoint map;
3. source Jacobian or pseudodeterminant lower bounds;
4. target cardinality, target covering entropy, occupied-span rank, or duplicate removal; and
5. incidence-normalized coarea bookkeeping that does not encode target preparation cost.

Indeed, the target set `(7)` has small cardinality by all of those measures and makes complete
capture mass equal to one in `(8)`.  Jacobian expansion merely shrinks each preimage sheet while
the net supplies enough occupied sheets to cover the source.  Retaining fibre multiplicity makes
this obstruction visible; it cannot remove it.

This corollary does **not** refute Jacobian or coarea estimates used together with a quantitative
local-circuit constraint.  It refutes their use as self-contained substitutes for such a
constraint.

## Theorem C -- the exact local-circuit Bellman recursion

Let `G` be a finite set of unitary gates on `V`, let `chi` be the reference state, and let `Z_s`
be the states reachable from `chi` by at most `s` gates.  Include the empty word, so

\[
 Z_0=\{\chi\},
 \qquad
 Z_{s+1}=Z_s\cup\bigcup_{g\in G}gZ_s.                           \tag{10}
\]

Define

\[
 Y_s(v)=\max_{z\in Z_s}|\langle z,v\rangle|^2.                 \tag{11}
\]

Then

\[
 \boxed{
 Y_{s+1}(v)
 =\max\left(Y_s(v),\max_{g\in G}Y_s(g^*v)\right).}             \tag{12}
\]

For every increasing function `B:[0,1]->R`, the complete bounded-incidence reporter

\[
 F_s^B(v)=B(Y_s(v))                                             \tag{13}
\]

obeys the identical max-plus Bellman law

\[
 \boxed{
 F_{s+1}^B(v)
 =\max\left(F_s^B(v),\max_{g\in G}F_s^B(g^*v)\right).}         \tag{14}
\]

Likewise, for every unitary-invariant metric `d` and

\[
 d_s(v)=\min_{z\in Z_s}d(v,z),                                 \tag{15}
\]

one has the min-plus recursion

\[
 \boxed{
 d_{s+1}(v)
 =\min\left(d_s(v),\min_{g\in G}d_s(g^*v)\right).}             \tag{16}
\]

### Proof

Insert `(10)` into `(11)` and use
`|<gz,v>|=|<z,g^*v>|` to obtain `(12)`.  Monotonicity of `B` moves it through the finite maxima,
giving `(14)`.  Unitary invariance moves `g` from the target to the argument in the same way and
gives `(16)`.

The Bellman operator preserves every common Lipschitz constant: composition with a unitary does
not change it, and finite maxima or minima preserve it.  Thus the target-cardinality-free
low-influence bounds of the parent theorem are consistent with arbitrarily deep recursion.  The
new information in `(12)--(16)` is not a better Lipschitz constant; it is the exact local
preparation law that the adversarial net `(7)` lacks.

## Theorem D -- robust Bellman calibration lower bound

Let `d` be unitary invariant and define approximate word complexity

\[
 C_\epsilon(v)=\min\{|w|:d(W_w\chi,v)\le\epsilon\}.             \tag{17}
\]

Let `Phi:V->R` satisfy

\[
 \Phi(gv)\le\Phi(v)+1\quad(g\in G),
 \qquad
 |\Phi(v)-\Phi(w)|\le Ld(v,w).                                 \tag{18}
\]

Then

\[
 \boxed{
 C_\epsilon(v)
 \ge \Phi(v)-\Phi(\chi)-L\epsilon.}                            \tag{19}
\]

### Proof

For a word `W_w` of length `ell`, iterate the gate inequality in `(18)` to get
`Phi(W_w chi)<=Phi(chi)+ell`.  If `d(W_w chi,v)<=epsilon`, metric Lipschitzness gives
`Phi(v)<=Phi(W_w chi)+L epsilon`.  Rearrangement proves `(19)` and minimization over admissible
words gives the claim.

This is the exact robust dual certificate missing from a purely geometric orbit argument.  It is
not enough to call a function a history observable: both inequalities in `(18)` must be proved
uniformly for the physical gate set and fixed operational metric.

## Conjecturing and falsification ledger

### C0 -- a strong observer-Jacobian lower tail plus occupied-image coarea closes Brown growth

**Falsified without circuit structure.**  Equations `(7)--(9)` construct a completely occupied
target image with far less entropy than the available Brown-depth circuit dictionary.  Every
Jacobian sheet may be transverse and still be covered.

### C1 -- target cardinality or metric entropy distinguishes the adversarial cover

**Falsified.**  Its logarithmic size is only `O(n^2)` at time `Theta(D/poly(n))`, whereas the
allowed circuit-word entropy is `Theta(D)`.

### C2 -- bounded complete-incidence and low influence alone force graph escape

**Falsified.**  Applying the bounded reporter to `(8)` makes it near one everywhere.  Boundedness
and phase-Haar variance become useful only after target preparation structure enters.

### C3 -- retain the recursive gate-generation law before scalarization

**Proved as the exact positive survivor.**  Equations `(12)--(16)` encode the complete circuit
union without enumerating circuit words and without admitting arbitrary orbit nets.

## New frozen core -- autonomous Bellman escape

For the ordinary fixed-shell local ensemble and its easy seed, prove at the Brown schedule

\[
 s(t)=\left\lfloor{\beta\min(B_n|t|,D)\over\log M_n}\right\rfloor \tag{20}
\]

that the target-independent-return-excised bounded reporter

\[
 \mathbb E_H\left[1_{R_{n,t}^c}
 F_{s(t)}^{\mathcal B_{r,k}}(e^{-itH}\chi)\right]              \tag{21}
\]

is small, with `r=O(log n)` at one time and `r=O(n)` for the complete Brown-time mesh.  A valid
proof must use the local Bellman generator in `(14)` relative to autonomous Hamiltonian motion.
Replacing `Z_s` by an arbitrary target set, its span, its cardinality, or an unconstrained endpoint
net is now a proved dead route.

Equation `(21)` is still equivalent to the physical no-shortcut event up to fixed error slack.  The
advance is that the indispensable missing structure has been isolated exactly: **local recursive
preparability**, not more spectral regularity.

## Hostile audit

1. **No Brown decay yet.**  The Bellman recursion identifies the required structure but does not
   prove `(21)`.
2. **Cover targets are not circuits.**  This is the point of the no-go, not a counterexample to
   Brown growth.
3. **Known ingredients.**  Sphere covering and dynamic programming are classical.  Candidate new
   content is the sharp obstruction they impose on static-H coarea/Jacobian programmes and the
   resulting exact autonomous Bellman frontier.  External priority remains open.
4. **Finite alphabet.**  Continuous gates, ancillas, measurements, and fault-tolerant protocols
   require the corresponding control-set Bellman operator.
5. **Lean pending.**  No statement enters the final manuscript until formalized after the active
   corpus refactor.

## Exact next move

The child theorem
`./exact-penalty-robust-circuit-bellman-duality.md` proves that approximate circuit complexity is
itself the maximal Lipschitz Bellman subsolution of an exact-penalty obstacle problem, with equality
at a finite penalty.  Therefore bare existence of a function satisfying the inequalities below is
equivalent to the desired lower bound and is not a reduction.

Construct an **external**, noncircular, metric-robust Bellman subsolution `Phi_(n,t)`, given by a
formula that does not evaluate the circuit sets `Z_s`, their distance functions, or circuit
complexity, satisfying

\[
 \Phi(gv)\le\Phi(v)+1\quad(g\in G),
 \qquad |\Phi(v)-\Phi(w)|\le L_n d(v,w),                        \tag{22}
\]

but

\[
 \Phi(e^{-itH}\chi)-\Phi(\chi)
 \ge c\min(B_n|t|,D)/\log M_n+L_n\epsilon                     \tag{23}
\]

with high quenched probability outside one return filtration.  Theorem D and `(22)--(23)`
immediately give the required robust circuit lower bound.  Energy, fixed linear observables, target count, and
unstructured Jacobian volume are already falsified subsolutions.  The live candidate must be a
nonlinear reuse-sensitive local-control calibration.  A lifted oriented-history variable alone is
also excluded: it does not descend to a function of the recurrent endpoint.

## Lean realization after corpus refactor

1. abstract net pushforward `(1)--(2)` and finite sphere cover `(3)--(4)`;
2. Duhamel-Lipschitz orbit cover `(5)--(8)`;
3. finite reachability recursion `(10)`;
4. max-plus overlap reporter `(12)--(14)`;
5. min-plus metric recursion `(15)--(16)`;
6. robust Bellman calibration theorem `(17)--(19)`.
