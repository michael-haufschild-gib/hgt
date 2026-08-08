# Half-sided modular conormal persistence and bounded-dilation no-go

- **ID:** `half-sided-modular-conormal-persistence-and-bounded-dilation-no-go`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / OPERATOR PERSISTENCE / TIME-TOPOLOGY NO-GO
- **Status:** `[PAPER PROOF COMPLETE] [CONDITIONAL ON STANDARD HSMI THEOREM] [BRIDGE]`
  `[NO RH CLAIM] [NO WORMHOLE CLAIM] [NO LEAN WRITTEN]`
- **Parent field:** `../../1-in-progress/constraint-relativity/completion-relativity-source-history-geometry.md`.

## Setup

Let `(N subset M,Omega)` be standard half-sided modular inclusion. Use standard Wiesbrock
translation data, normalized so `N=M(1)`: positive selfadjoint generator `P`, unitary
`U(a)=e^(iaP)`, nested algebras

\[
 M(a)=U(a)MU(a)^*,
 \qquad
 0<a<b\Longrightarrow M(b)\subset M(a),
 \tag{1}
\]

and modular dilation

\[
 \Delta_\Omega^{-it}P\Delta_\Omega^{it}=e^{2\pi t}P,
 \qquad
 \Delta_\Omega^{-it}M(a)\Delta_\Omega^{it}=M(e^{2\pi t}a).
 \tag{2}
\]

All quotients below are Banach/operator-space quotients, not quotient algebras.

## Theorem 1: conormal persistence

Define boundary defect and normal conormal

\[
 C_a=M/M(a),
 \qquad
 C_a^\vee=M(a)^\perp
 =\{\omega\in M_*:\omega|_{M(a)}=0\}.
 \tag{3}
\]

For `0<a<b` there is canonical exact persistence row

\[
 \boxed{
 0\longrightarrow M(a)/M(b)
 \longrightarrow C_b
 \longrightarrow C_a
 \longrightarrow0.}
 \tag{4}
\]

Moreover `C_a` is dual operator space with predual `C_a^vee`; modular time transports complete
filtered system by

\[
 \boxed{a\longmapsto e^{2\pi t}a.}
 \tag{5}
\]

For quotient distance

\[
 d_a(x)=\inf_{y\in M(a)}\|x-y\|,
 \tag{6}
\]

weak-star quotient duality gives

\[
 d_a(x)
 =\sup_{\substack{\omega\in C_a^\vee\\\|\omega\|\le1}}|\omega(x)|,
 \tag{7}
\]

and exact covariance law

\[
 \boxed{
 d_{e^{2\pi t}a}
 (\Delta_\Omega^{-it}x\Delta_\Omega^{it})
 =d_a(x).}
 \tag{8}
\]

### Proof

Nested subspaces in `(1)` give kernel of map `M/M(b)->M/M(a)` equal `M(a)/M(b)`, proving `(4)`.
Each `M(a)` is weak-star closed, so quotient `M/M(a)` has predual its preannihilator `(3)` and
Hahn--Banach quotient norm formula gives `(7)`. Modular conjugation is isometric and maps `M(a)`
onto `M(e^(2pi t)a)` by `(2)`, which proves `(5)` and `(8)`. QED.

## Theorem 2: finite/bounded horizon dilation collapses

If `P` in `(2)` is bounded, then

\[
 \boxed{P=0.}
 \tag{9}
\]

Therefore `U(a)=1` and inclusion is trivial. More quantitatively, for any bounded positive `P` and
unitary `V_t`,

\[
 \boxed{
 \frac{\|V_tPV_t^*-e^{2\pi t}P\|}{\|P\|}
 \ge |e^{2\pi t}-1|}
 \tag{10}
\]

when `P!=0`. Thus finite-dimensional models cannot approximate half-sided dilation uniformly in
global operator norm at nonzero time.

### Proof

Unitary conjugation preserves norm, while `(2)` gives

\[
 \|P\|=\|\Delta^{-it}P\Delta^{it}\|=e^{2\pi t}\|P\|.
\]

Choose `t!=0`; hence `P=0`. Reverse triangle inequality gives

\[
 \|V_tPV_t^*-e^{2\pi t}P\|
 \ge\left|\|V_tPV_t^*\|-\|e^{2\pi t}P\|\right|
 =|e^{2\pi t}-1|\|P\|,
\]

proving `(10)`. QED.

## Theorem 3: moment growth excludes strong recurrence

For vector `psi` in domain of `P^(n/2)`, put `psi_s=Delta^(is)psi`. Interpreting the moment as
quadratic form `||P^(n/2)psi||^2`, then

\[
 \boxed{
 \|P^{n/2}\psi_s\|^2
 =e^{2\pi ns}\|P^{n/2}\psi\|^2.}
 \tag{11}
\]

Equivalently characteristic function scales by

\[
 \langle\psi_s,e^{i\lambda P}\psi_s\rangle
 =\langle\psi,e^{i\lambda e^{2\pi s}P}\psi\rangle.
 \tag{12}
\]

If `0<||P^(1/2)psi||^2<infinity`, orbit cannot recur as `s->+infinity` in
`P^(1/2)` graph/form topology.

### Proof

Functional calculus applied to `(2)` gives the corresponding quadratic-form scaling and
`Delta^(-is)e^(i lambda P)Delta^(is)=e^(i lambda e^(2pi s)P)`. Pair with `psi` to obtain
`(11)--(12)`. For `n=1`, form seminorm of `psi_s` grows as `e^(pi s)` and cannot return to finite
initial value. QED.

## Semisimple extension collapse

Every short exact sequence

\[
 0\to C\to K\to C^*\to0
 \tag{13}
\]

of finite-dimensional complex vector spaces splits. Same holds for Hilbert spaces with bounded
maps and closed range by orthogonal complement. If von Neumann inclusion is invariant under
faithful state modular group, Takesaki theorem supplies state-preserving conditional expectation,
so operator-space sequence splits as well. Proper factor inclusion is not two-sided ideal, hence
`M/N` is not an algebra.

Therefore physical phase/gluing cannot universally be nonzero `Ext^1(C^*,C)`. In half-sided chart,
nontrivial structure is polarized pairing, unbounded generator, and persistence filtration `(3)--(8)`.

## Exact time-type dichotomy

- Finite Gibbs/prime clock is elliptic or almost periodic on compact torus and can recur.
- Half-sided horizon clock is hyperbolic dilation on noncompact scale and obeys exponential moment
  law `(11)`.
- Any finite-to-horizon completion must change topology or mode of convergence; global operator-norm
  approximation is excluded by `(10)`.

No theorem identifies `P`, `d_a`, or layer `M(a)/M(b)` with circuit complexity, Krylov complexity,
or wormhole length. Exact all-time half-sided scaling, finite-dimensional late-time saturation, and
literal equality to one wormhole-length observable cannot all hold without regime/topology change.

## Predictions and falsifiers

1. Modular rescaling of cutoff preserves optimal quotient distinguishability exactly by `(8)`.
2. Any nontrivial finite-dimensional exact HSMI model is impossible by `(9)`.
3. State/energy-window or weak-topology approximation may survive; theorem forbids only global norm.
4. Boundary gluing may be nonzero through symplectic cross-pairing even when `(13)` splits. Extension
   class alone is therefore falsified as universal physics phase.
5. Physical transfer to arithmetic requires source-framed functor matching generator and filtration,
   not only vector-space exact row.

## Literature boundary

Half-sided modular inclusions, modular translations, quotient duality, Takesaki expectations, and
holographic modular flow are established. Current primary sources checked:

- https://arxiv.org/abs/2503.21385
- https://arxiv.org/abs/2503.02944
- https://arxiv.org/abs/2601.07915
- https://arxiv.org/abs/2606.10924
- https://arxiv.org/abs/2510.22658
- https://arxiv.org/abs/2606.20220
- https://arxiv.org/abs/2412.02038

New-to-corpus bridge is formulation `(3)--(8)` as conormal persistence plus explicit bounded-dilation
and recurrence topology no-go. Parent ingredients are occupied; no priority claim.

## Lean-return note

No Lean work authorized. Operator-algebra formalization is not recommended first. Finite norm
inequality `(10)` and abstract nested-quotient row `(4)` are easiest later targets after library audit.

## Gates

- [x] dependency-closed paper proof conditional on standard HSMI input
- [x] exact measurable quotient-distance invariant
- [x] finite/bounded no-go
- [x] recurrence topology separation
- [x] extension-phase transfer falsified
- [ ] operator specialist review
- [ ] Lean formalization

## Log

- 2026-08-08 -- replaced failed operator Ext transfer by conormal persistence and modular dilation;
  proved bounded exact horizon collapse and moment-recurrence no-go.
