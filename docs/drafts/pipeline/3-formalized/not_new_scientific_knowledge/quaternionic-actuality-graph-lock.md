# A pointed quaternion locks Spin(4) to its own `1 + 3` stabilizer

- **ID:** `quaternionic-actuality-graph-lock`
- **Stage:** 3-formalized
- **Type:** EXACT BRIDGE / REPRESENTATION THEORY / NOT NEW SCIENTIFIC KNOWLEDGE
- **Parent:** `../../1-in-progress/actuality-conservation-boundary-colligation-law.md`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [PHYSICAL IDENTIFICATION OPEN]`

## Result

Let
\[
\mathbb U=\{u\in\mathbb H:\lVert u\rVert^2=1\}
\]
act on the real quaternion carrier by the standard
\(\operatorname{Spin}(4)\cong \mathbb U_L\times\mathbb U_R\) pair action
\[
(u,v)\cdot x=uxv^\ast.                                      \tag{1}
\]
Every pointed unit quaternion \(q\in\mathbb U\) selects the graph subgroup
\[
\Delta_q
=
\{(u,q^\ast u q):u\in\mathbb U\}.                           \tag{2}
\]

### Theorem — exact stabilizer graph

For unit \(u,v,q\),
\[
(u,v)\cdot q=q
\quad\Longleftrightarrow\quad
v=q^\ast u q.                                               \tag{3}
\]
The graph partner \(q^\ast u q\) is unit. Hence the stabilizer of \(q\) in
\(\mathbb U_L\times\mathbb U_R\) is exactly \(\Delta_q\), not a separately chosen diagonal.

### Proof

If \(u q v^\ast=q\), right multiplication by \(v\) and \(v^\ast v=1\) give
\[
u q=qv.
\]
Left multiplication by \(q^\ast\) and \(q^\ast q=1\) give
\[
v=q^\ast u q.
\]
Conversely, substituting \(v=q^\ast u q\) in (1) gives
\[
\begin{aligned}
u q (q^\ast u q)^\ast
&=u q q^\ast u^\ast q\\
&=u u^\ast q\\
&=q.
\end{aligned}
\]
Multiplicativity of quaternion norm gives
\[
\lVert q^\ast u q\rVert^2
=\lVert q\rVert^2\lVert u\rVert^2\lVert q\rVert^2
=1.
\]
This proves (3). \(\square\)

## Exact `1 + 3` action selected by the point

The same \(q\) gives the orthogonal decomposition
\[
\mathbb H=\mathbb Rq\oplus q^\perp,
\qquad
q^\perp=(\operatorname{Im}\mathbb H)q.                     \tag{4}
\]
The first equality is ordinary radial decomposition. The second is the already formalized
quaternionic orbit theorem.

Every element of \(\Delta_q\) fixes the radial line pointwise. For \(a\in\operatorname{Im}\mathbb
H\),
\[
\begin{aligned}
(u,q^\ast u q)\cdot(aq)
&=u(aq)(q^\ast u q)^\ast\\
&=(uau^\ast)q.                                             \tag{5}
\end{aligned}
\]
Quaternionic conjugation preserves \(\operatorname{Im}\mathbb H\). Therefore \(\Delta_q\)
preserves \(q^\perp\) and acts on it through the usual three-dimensional conjugation
representation. Thus a nonzero pointed quaternion does two jobs at once:

1. it selects the diagonal graph that fixes the point; and
2. it selects that graph's exact fixed-one plus rotated-three representation.

No arbitrary diagonal subgroup or scalar/imaginary split remains after \(q\) is given.

## What this closes—and what it does not

This theorem closes one narrow ambiguity in the active physical programme. If an objective
exceptional actualization already supplies a nonzero colourless quaternionic defect \(q\), then
the outgoing `1 + 3` compact stabilizer is forced by \(q\); it need not be selected independently.

It does **not** prove:

- that a physical event is such a quaternionic normal defect;
- that \(\Delta_q\) is a spacetime rotation group rather than an internal custodial group;
- a Lorentz cone, boosts, tetrad, causal order, Einstein dynamics, or Born probabilities;
- that event-to-event graph comparison is gravity; or
- that the weak gauge connection survives on the source while its target graph becomes a
  spacetime frame connection.

## Priority and hostile collision boundary

The mathematics is standard quaternionic stabilizer theory. Its nearest physical readings are
occupied:

- a Higgs bidoublet locks \(SU(2)_L\times SU(2)_R\) to a custodial diagonal;
- gravitational Higgs and Cartan-gravity programmes use symmetry reduction to produce geometric
  structure;
- observer fields reduce Lorentz symmetry to the spatial rotation subgroup associated with a
  chosen timelike direction; and
- Cartan connections combine a spin connection and soldering form.

Relevant primary sources include Nesti--Percacci,
[*Graviweak Unification*](https://arxiv.org/abs/0706.3307), Percacci,
[*The Higgs Phenomenon in Quantum Gravity*](https://arxiv.org/abs/0712.3545), Wise,
[*MacDowell--Mansouri gravity and Cartan geometry*](https://arxiv.org/abs/gr-qc/0611154), and
Gielen--Wise,
[*Spontaneously broken Lorentz symmetry for Hamiltonian gravity*](https://arxiv.org/abs/1111.7195).

Therefore neither graph locking nor `1 + 3` splitting is claimed as new physics. The only live
novelty is the stronger event claim in the parent card: a source-complete noninvertible
actualization may turn the four-direction quantum representation it removes into the stabilizer
and causal frame law of its own complementary record.

## Lean realization

The unconditional formalization is
[`QuaternionicActualityGraphLock.lean`](../../../../formal/GaloisForLFunctions/HTGeometry/QuaternionicActualityGraphLock.lean).
It proves:

- `quaternionGraphPartner_unit`;
- `spinFourPairAction_graph_fixes`;
- `spinFourPairAction_fixes_iff_graph`;
- `spinFourPairAction_graph_on_orbit`;
- `spinFourPairAction_graph_fixes_radial`;
- `spinFourPairAction_graph_preserves_spatial`; and
- `quaternionActualityGraphLock_one_plus_three`.

No physical identification is encoded in these declarations.

## Gates

- [x] paper proof dependency-closed
- [x] standard-mathematics collision recorded
- [x] exact theorem unconditionally formalized in Lean
- [ ] source-complete physical event selects \(q\)
- [ ] noninvertible source/target representation change derived
- [ ] Lorentzian causal and continuum landing proved
- [ ] finite prediction derived

## Log

- 2026-07-29 — extracted exact positive bridge from the source-selection attack. A nonzero
  quaternion does canonically select its graph diagonal and `1 + 3` stabilizer action, but this is
  standard custodial/observer-field mathematics. Preserved only its use inside the stronger
  noninvertible actuality law.
