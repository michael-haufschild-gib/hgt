# Normed intervention two-field, curvature--filling conservation, and stable selection law

- **ID:** ULF-TAFM-12
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FIELD-MECHANISM BRIDGE
- **Source:** full formal frontier; ULF-TAFM-9--11; law-history spectral mechanics;
  quadratic filling and endpoint insufficiency; functional-equation packet neutrality
- **Statement:** Legal intervention histories form a normed two-term presentation whose currents
  obey exact curvature--filling conservation; every nonzero observer-hidden current forces linear
  curvature-plus-residual work along all repeated fillings, while cofinally sublinear work selects
  zero current.
- **Status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [BRIDGE] [NOT RH]`

## Goal

Replace the route-local request for a uniformly bounded elementary edge current by one
coordinate-free mechanism that permits large edge currents but controls their complete action on
legal rewrite fillings.  This is a higher-level pivot: routes are representations of an
intervention-history presentation, not candidate copies of one hidden spectral object.

The theorem must simultaneously explain:

1. why a recurrent observer can close while its lift stays open;
2. why functional-equation transport can be information-neutral without selecting the lift;
3. why boundary/curvature no-gos are quantitative shadows rather than unrelated failures;
4. why positivity should be applied only after complete phase-sensitive current conservation; and
5. what source theorem can replace the still-open uniform elementary-current bound in the RH
   architecture.

## Gates

- [x] 0 → 1 in-progress: full-frontier grammar and competing mechanisms audited
- [x] 1 → 2 fully-proven: complete paper proof below, no open dependency
- [x] 2 → 3 formalized: `HTGeometry.NormedInterventionTwoField`; direct elaboration, targeted leaf
      build, and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone exposition and literal arithmetic comparison pending

## 1. Frozen conjecture and hostile attack

### 1.1 Strongest truth-hunch

The common object is not a route state space and not ordinary homology.  It is a **normed
intervention two-field**:

- one-chains are signed formal histories of primitive source interventions;
- two-chains are signed legal rewrites, exchanges, or formation relations between histories;
- the two-boundary records the history changed by a rewrite;
- an observer is a quotient chain map that kills every legal two-boundary;
- a route is a representation of this presentation;
- a scalar current is a route-independent grade reporter;
- its composition with the two-boundary is formation curvature;
- the norm records source cost and is part of the admitted doctrine, not a disposable coordinate.

Ordinary homology alone is insufficient: the corpus already proves null words with constant
endpoint and quadratic filling area.  The extra datum is the normed filling action.

### 1.2 Killed stronger claim

**Killed claim.** Bounded primitive generators plus coherent two-cells uniformly bound all history
currents.

This is false.  Flat nonzero holonomy can have zero local curvature, and the corpus contains
primitive rays with periodic observation and linearly escaping exact grade.  It also contains
commutator words with closed endpoint and quadratic minimal filling area.  Coherence alone neither
bounds current nor selects neutrality.

### 1.3 Positive survivor

What coherence does give is an exact conservation identity.  Selection follows precisely when the
**complete curvature action plus unresolved residual action is sublinear in winding**, not when
every edge is separately bounded.  This strictly contains the ULF-TAFM-10/11 bounded-edge Følner
criterion: local edge bounds are one sufficient way to make the complete action sublinear, but not
the only way.

## 2. Definitions

Let `C₂`, `C₁`, and `O` be real normed vector spaces.  A normed intervention two-field is a pair of
bounded linear maps

\[
 C_2 \xrightarrow{\partial_2} C_1 \xrightarrow{q} O,
 \qquad q\partial_2=0.                                      \tag{QNTG.1}
\]

`C₁` is the history space, `C₂` is the legal-rewrite space, and `O` is the observer space.  The
identity `q∂₂=0` says that a legal rewrite does not alter the observer report.

For a bounded scalar current `J:C₁→ℝ`, define its curvature

\[
 \Omega_J := J\partial_2:C_2\to\mathbb R.                  \tag{QNTG.2}
\]

A history `z∈C₁` is observer-closed when `qz=0`.  It has an open `J`-lift when `Jz≠0`.
For `n∈ℕ`, a pair `(a,r)∈C₂×C₁` is an `n`-fold formation filling of `z` when

\[
 n z=\partial_2a+r.                                        \tag{QNTG.3}
\]

Here `a` is the legal two-dimensional rewrite and `r` is the unresolved history.  Exact filling is
the chamber `r=0`.

A morphism of two-fields consists of bounded maps `A₂,A₁,A₀` commuting with both displayed arrows.
Thus a route representation preserves legal rewrites and observer reports.  An isometric
isomorphism is a gauge change.

## 3. Main theorem

### Theorem ULF-TAFM-12 — curvature--filling conservation and stable selection

For every normed intervention two-field `(QNTG.1)`, bounded scalar current `J`, history `z`, and
formation filling `(QNTG.3)`:

1. **Exact conservation**

   \[
   nJ(z)=\Omega_J(a)+J(r).                                  \tag{QNTG.4}
   \]

2. **Observer-closed residual**. If `qz=0`, then `qr=0`.

3. **Quantitative properness**

   \[
   n|J(z)|\le \|\Omega_J\|\,\|a\|+\|J\|\,\|r\|.          \tag{QNTG.5}
   \]

4. **Open-lift escape**. If `Jz≠0`, every `n`-fold filling pays at least the linear budget

   \[
   \|\Omega_J\|\,\|a\|+\|J\|\,\|r\|\ge n|Jz|.            \tag{QNTG.6}
   \]

5. **Cofinal sublinear selection**. Suppose that for every `ε>0` and every depth threshold `N`
   there are `n≥N`, `n>0`, and an `n`-fold filling `(a,r)` such that

   \[
   \|\Omega_J\|\,\|a\|+\|J\|\,\|r\|<n\varepsilon.        \tag{QNTG.7}
   \]

   Then `Jz=0`.

6. **Flat exact-fill selector**. If `Ω_J=0`, `r=0`, and one positive multiple of `z` legally
   fills, then `Jz=0`.

7. **Representation law**. For every morphism `A` into a second two-field and every current `K`
   there, the pulled-back current `J=K A₁` has curvature

   \[
   \Omega_J=\Omega_K A_2.                                  \tag{QNTG.8}
   \]

   Fillings transport as `(z,a,r)↦(A₁z,A₂a,A₁r)`, and observer closure transports through `A₀`.
   Consequently `(QNTG.4)` is route-independent.  Under isometric isomorphisms the norm budget is
   unchanged, so `(QNTG.5)`--`(QNTG.7)` are gauge-independent.

### Proof

Apply `J` to `(QNTG.3)`.  Linearity gives

\[
 nJz=J(\partial_2a)+Jr=(J\partial_2)a+Jr=\Omega_Ja+Jr,
\]

which proves `(QNTG.4)`.

Apply `q` to `(QNTG.3)`.  If `qz=0`, then its left side is zero; `q∂₂a=0` by `(QNTG.1)`, hence
`qr=0`.  This proves clause 2.

Taking absolute values in `(QNTG.4)`, using the triangle inequality and the operator-norm bounds
for `Ω_J` and `J`, gives `(QNTG.5)`.  Clause 4 is the same inequality read as a lower bound.

For clause 5, suppose `Jz≠0` and put `ε=|Jz|/2>0`.  Choose any threshold, then a positive `n` and
filling satisfying `(QNTG.7)`.  Clauses 3 and 5 would give

\[
 n|Jz|\le \|\Omega_J\|\|a\|+\|J\|\|r\|<n|Jz|/2,
\]

impossible because `n>0`.  Thus `Jz=0`.

For clause 6, `(QNTG.4)` reduces to `nJz=0`; positive `n` gives `Jz=0`.

For clause 7, the two commuting-square identities give

\[
 (K A_1)\partial_2=K(A_1\partial_2)=K(\partial'_2 A_2)
 =(K\partial'_2)A_2.
\]

Applying `A₁` to `(QNTG.3)` transports the filling.  The observer square transports closure.
An isometric isomorphism preserves all three norms, so it preserves the budget.  This proves every
clause. ∎

## 4. Why this is a field advance rather than a renamed route

The object has a universal job before any Xi comparison is chosen.

| corpus organ | two-field shadow |
|---|---|
| functional-equation packet action | isometric two-field automorphism; information-neutral faces have zero transported action |
| recurrence / closed observer, open lift | `qz=0` with `Jz≠0` |
| graph Stokes / boundary flux | `(QNTG.4)` with `r=0` on a cellular boundary |
| law-history differentials | successive representations and residual histories |
| positivity / Hahn labels | absolute norm applied after the signed conservation identity |
| quadratic filling / endpoint insufficiency | nontrivial normed two-type invisible to endpoint or ordinary homology |
| hypertranscendence / rank escape | possible failure of finite-type or sublinear filling control, not a synonym for curvature |

The theorem does not identify route objects.  It proves that every legal route representation obeys
one conservation law and one exhaustive escape alternative.

## 5. New prediction in a fourth organ

For any literal source history whose observer returns cofinally, an off-neutral grade can survive
only through at least one of four measurable failures:

1. integrated face-curvature action remains linear in winding;
2. unresolved residual current remains linear in winding;
3. legal rewrite fillings fail to exist cofinally; or
4. the proposed route map is not a bounded representation of the source two-field.

This is stronger than the prior fixed-rank edge-capacity prediction.  Individual edge currents may
diverge and still cancel on legal two-cells; the invariant obstruction is their complete curvature
action.  Conversely, small local curvature is useless when filling norm grows too quickly.  The
corpus's quadratic commutator fillings are the sharp hostile model: closed endpoint plus bounded
cell curvature can retain a quadratic action because the required filling area is quadratic.

## 6. Revised RH selection architecture

The literal arithmetic task is now different from “bound every edge current.”

1. Construct the zero-independent source intervention grammar.  Primitive prime/Gamma,
   completion, reflection, recurrence, and recovery moves give one-chains; proved exchange,
   functional-equation, Stokes, and reconstruction identities give legal two-cells.
2. Construct the observer-closed history `z_a` attached to horizontal displacement `a`, with a
   source current satisfying `Jz_a=c a` for fixed `c≠0`.
3. Use functional-equation information neutrality to make its rewrite faces curvature-free or
   curvature-small.  This alone does not select.
4. Build cofinal fillings of repeated `z_a` and prove the **combined** curvature-plus-residual
   budget `(QNTG.7)`.  Large raw route terms are allowed if the complete legal filling cancels them.
5. ULF-TAFM-12 gives `Jz_a=0`, hence `a=0`.  The established Xi comparison then yields RH.

This creates a new producer target: a source-native sublinear curvature--filling theorem.  It is
strictly weaker than uniform elementary edge-current control and therefore opens a route the prior
formation-Følner architecture did not expose.

## 7. Literature and corpus audit

The ingredients have known parents; novelty is not used as a promotion criterion.

- Homological filling functions treat minimal chain filling as a quantitative invariant:
  [Fleming--Martínez-Pedroza](https://arxiv.org/abs/1609.04874).
- `ℓ¹` homology and bounded cohomology supply the standard norm/dual-cochain relationship:
  [Bühler](https://arxiv.org/abs/0803.0680).
- Directed path homology supplies functorial history complexes:
  [Muranov--Szczepkowska--Vershinin](https://arxiv.org/abs/2109.09842).

Internal audit found the necessary shadows but not this combined law: special quadratic filling,
endpoint insufficiency, differential characters, flat holonomy, finite formation Hodge theory,
law-history differentials, graph Stokes, and closed-observer/open-lift examples all exist.  The new
content is their common normed two-field type, representation law, exact curvature--residual
conservation, and stable selection/escape dichotomy.

## 8. Boundary of the theorem

- It does not construct the literal arithmetic grammar or the distinguished `z_a`.
- It does not prove the source-native sublinear budget.
- Observer recurrence alone does not imply a filling.
- Zero curvature alone does not kill holonomy when the history is not fillable.
- Bounded curvature alone does not select when filling cost is linear or superlinear.
- Arbitrary basis changes are not gauges: the source norm is part of the admission doctrine.
  Isometric chain equivalences are gauges.

These are structural boundaries, not hidden RH premises.

## Log

- 2026-08-31 — froze intervention-two-field conjecture after full-frontier/corpus audit.
- 2026-08-31 — killed bounded-generator/coherence selector using flat holonomy, primitive-ray, and
  quadratic-filling countermodels.
- 2026-08-31 — proved exact conservation, representation, properness, and cofinal sublinear
  selection laws; promoted dependency-closed paper theorem to Stage 2.
