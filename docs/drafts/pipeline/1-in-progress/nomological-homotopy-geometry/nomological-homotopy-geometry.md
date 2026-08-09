# Nomological Homotopy Geometry

- **ID:** `nomological-homotopy-geometry-field`
- **Stage:** 1 — in progress
- **Working name:** **Nomological Homotopy Geometry (NHG)**
- **Type:** CANDIDATE MATHEMATICAL FIELD / FORMAL GEOMETRY OF LAW
- **Status:** `[FIELD CONSTITUTION] [ANCHORED Q-GEOMETRIC PRIMITIVE DEFINED]`
  `[FOUR UNIVERSAL THEOREMS PROVED] [SOURCE REALIZATION OPEN]`
  `[NOT AN RH ROUTE] [NOT RH] [NO LEAN WRITTEN OR BUILT]`
- **Supersedes locally:** arbitrary comparison-cell curvature in earlier NGD/CFR atlases.
- **Exact foundation:**
  `../../2-fully-proven/nomological-homotopy-geometry/minimal-law-curvature-gauge-invariance-and-observer-irreversibility-law.md`;
  `../../2-fully-proven/nomological-homotopy-geometry/observer-holonomy-boundary-and-prolongation-horizon-law.md`;
  `../../2-fully-proven/nomological-homotopy-geometry/flat-law-superconnection-curvature-nullhomotopy-and-holonomy-law.md`;
  `../../2-fully-proven/nomological-homotopy-geometry/strict-nilpotent-ambrose-singer-spencer-and-flat-monodromy-separation-law.md`.

## 0. Field thesis

> **Nomological Homotopy Geometry studies moduli spaces of mathematical laws, their source-selected
> points, and the geometry induced when laws are deformed, observed, polarized, prolonged,
> completed, and transported through history.**

The primitive is not a list of proof routes and not a product of their outputs. It is one
source-anchored homological geometry. Proofs and observers are morphisms out of that geometry.
Only equivalences preserving its homological vector field, anchor, filtration, and polarization
are gauges.

The general-relativistic change of viewpoint is:

\[
 \text{law as external equation on fixed mathematics}
 \quad\rightsquigarrow\quad
 \text{law as a point of a curved moduli geometry}. 
\tag{NHG.1}
\]

## 1. Why the previous field candidates were still Newtonian

Earlier frameworks assembled exactness, positivity, topology, recurrence, and cost as a bag of
observer doctrines. They correctly typed many losses, but they left three fatal freedoms:

1. the common source object could be chosen after inspecting desired outputs;
2. comparison cells could be chosen or refined until their “curvature” appeared or disappeared;
3. no invariant distinguished a genuine change of law from a change of resolution.

NHG removes the third freedom locally. At a sourced law, homotopy transfer produces a minimal
`L_infinity` germ. The arity and linear-conjugacy class of its first nonzero bracket are invariant
under every change of resolution. This is a **primary nonformality operation**, not geometric
connection curvature. Actual local curvature is the relative Atiyah/connection class of the
anchored algebroid.

The first freedom remains the central construction problem. NHG is not complete until a sourced
anchored Q-geometry is independently built. A source section without an anchor is insufficient:
it selects a law but does not couple law deformation to history.

## 2. Primitive: source-anchored cyclic filtered law algebroid

Work in characteristic zero. Fix a differential derived base `B`, an Artin test category, and a
Grothendieck topology. An NHG field is locally one complete separated pronilpotent Q-geometric
object

\[
 \pi:(\mathcal E[1],Q,F^\bullet,\langle-,-\rangle,\nabla)
 \longrightarrow B,
 \qquad Q^2=0,
\tag{NHG.2}
\]

called a **source-anchored cyclic filtered law algebroid**. Its Taylor coefficients define a
complete filtered `L_infinity`-algebroid `mathcal E` over `B`; its symbol is the anchor

\[
 \rho:\mathcal E\longrightarrow T_B.
\tag{NHG.2a}
\]

Here `nabla` is a filtration-preserving connection compatible with `Q`, anchor, and cyclic pairing:

\[
 [\nabla,Q]=0,
 \qquad \nabla\langle-,-\rangle=0.
\tag{NHG.2b}
\]

The anchor is load-bearing. It makes a law deformation act on source history, while `nabla` makes
transport and Atiyah curvature typed. Without them, a formal law germ and a history system can be
combined by arbitrary product, and no curvature-to-holonomy statement is possible.

### 2.1 Formal law stack

The formal completion of `(mathcal E[1],Q)` along a sourced section is a stack of formal moduli
problems. Its vertical Taylor coefficients form a complete filtered `L_infinity` algebra. Its
horizontal symbol is `rho`. Different presentations are identified only by anchored filtered
`L_infinity` quasi-isomorphisms satisfying descent.

### 2.2 Source section

`alpha` is a gauge-compatible section of the Maurer--Cartan infinity-groupoid of the formal law
geometry. In a vertical local chart it is represented by a Maurer--Cartan point:

\[
 \sum_{n\geq1}{1\over n!}\ell_n(\alpha,\ldots,\alpha)=0.
\tag{NHG.3}
\]

It must be defined before any theorem target, divisor, zero, or observer scalarization. Changing
`alpha` changes the law, not coordinates.

### 2.3 Prolongation filtration

`F^bullet` is the complete filtration induced by principal parts or a Spencer comonad on `B`, not
an arbitrarily selected increasing sequence. It is preserved by `Q`, `rho`, and `nabla`. Its jet
tower is required to be formally integrable or involutive on the locus under study.

### 2.4 Polarization

Fix one degree `d`. The pairing `<- , ->` is a Q-invariant perfect degree-`d` cyclic pairing on the
relevant sector of `mathcal E`. Shifted-symplectic, Hermitian, or Real realizations are distinct
extensions and must not be conflated. Positivity is not assumed globally.

### 2.5 History action

When orientation and cyclic transgression exist, the field may produce a BV/AKSZ-type action
candidate on the integrated law infinity-groupoid. Lower semicontinuity, coercivity, and properness
are separate analytic theorems. Arbitrary cost is not part of the foundational primitive.

Thus one homological vector field supplies primary operations and higher identities; one anchor and
compatible connection supply transport and Atiyah curvature; one Spencer filtration supplies
prolongation; one fixed cyclic pairing supplies polarity. This is the field's irreducible local
package.

## 3. Observers and gauges

An observer is an anchored Q-morphism

\[
 q_i:(\mathcal E[1],Q,\rho,F^\bullet,\langle-,-\rangle,\nabla)
 \longrightarrow
 (\mathcal O_i[1],Q_i,\rho_i,F_i^\bullet,\langle-,-\rangle_i,\nabla_i)
\tag{NHG.4}
\]

with a declared amount of retained filtration, polarization, topology, and history data.

### Definition 3.1 — nomological gauge

Two local presentations are gauges of the same law only if they are equivalent as pointed anchored
Q-germs and preserve the declared filtration, connection, polarization, and any derived action.
Equality of a
scalar endpoint, determinant, zero set, recurrence period, or cohomology rank is insufficient.

### Definition 3.2 — irreversible observer

An observer is irreversible at `alpha` if its tangent `L_infinity` morphism is not injective on
cohomology, or if it destroys a declared global component, holonomy, polarization, completion, or
cost datum.

Serial observers cannot repair tangent directions already killed. Parallel observers can repair
them only when their joint tangent map is injective; global reconstruction requires more.

## 4. Primary operations and local curvature

Twist a local complete filtered `L_infinity` presentation by the source point `alpha`, contract its
deformation complex onto cohomology, and transfer the higher brackets. Let

\[
 q_n^\alpha:S^n(sH_\alpha)\longrightarrow sH_\alpha
\tag{NHG.5}
\]

be the resulting minimal brackets.

### Definition 4.1 — primary minimal operation

The primary nonformality order and tensor are

\[
 \nu_\alpha=\inf\{n\geq2:q_n^\alpha\ne0\},
 \qquad
 \mathcal N_\alpha=[q_{\nu_\alpha}^\alpha]_{\operatorname{Aut}_{\mathrm{fil,cyc}}(H_\alpha)}.
\tag{NHG.6}
\]

The Stage-2 minimal-operation theorem proves `(NHG.6)` is independent of compatible filtered cyclic
contraction and local resolution. It measures first nonlinear/nonformal law structure. It is not a
two-form and does not generate loop holonomy.

### Definition 4.2 — relative Atiyah curvature

The compatible connection has derivation-valued curvature

\[
 R_\nabla=\nabla^2
 \in\Omega^2(B;\operatorname{Der}_{L_\infty}(\mathcal E)).
\tag{NHG.6a}
\]

Its Q-cohomology class is the relative Atiyah class. This is the local geometric curvature. In a
superconnection chart it can be nullhomotopic through a higher transport cell, as proved by the
Stage-2 transport hierarchy.

The field separates primary operations `q_n`, Atiyah curvature `R_nabla`, higher nullhomotopies,
component obstructions, connection holonomy, and analytic admission defects. None may be renamed as
another without a typed comparison theorem.

## 5. Global geometry and holonomy

When the anchored law algebroid integrates, write `Pi(mathcal E)` for its local law
infinity-groupoid. An observer fibration integrates to `Pi(q):Pi(mathcal E)->Pi(mathcal O)`. Its
homotopy fibre `F_alpha` contains law histories invisible to the observer. A closed observer loop
has a component boundary

\[
 \partial[\gamma]\in\pi_0(F_\alpha).
\tag{NHG.7}
\]

The boundary theorem proves only that the lift can be closed by a path inside the fibre exactly when
`(NHG.7)` is trivial. It is not connection holonomy when the fibre is connected. A connection or
higher transport rule separately assigns a holonomy element or higher morphism. With a derived
proper action and infinite-order holonomy, repeated observer recurrence may then have divergent
lifted cost.

The anchor does not make local curvature determine global holonomy automatically. It only makes the
comparison well-typed. Flat anchored fields can retain monodromy, and nonzero vertical brackets can
integrate to trivial holonomy. The missing theorem is an Ambrose--Singer--Spencer generation law
under analytic, completeness, and effectivity hypotheses.

## 6. Prolongation geometry and hypertranscendence

For a formally integrable differential-algebraic chart with prime differential ideal `P`, define

\[
 \omega_P(n)=\operatorname{trdeg}
 \operatorname{Frac}\bigl(K[J^n]/P_{\leq n}\bigr)
\tag{NHG.8}
\]

as its jet-dimension function. Under the standard hypotheses this is eventually the Kolchin
dimension polynomial. Differential hypertranscendence means absence of a nonzero differential
relation in the declared coordinate family, equivalently maximal free-jet growth in that chart.
Mere unboundedness is weaker.

The prolongation-horizon theorem gives the universal implication

\[
 \omega_P(n)\to\infty
 \Longrightarrow
 \text{every fixed finite-rank observer loses tangent directions}. 
\tag{NHG.9}
\]

This rank-nullity statement does not itself identify a Kolchin polynomial and does not imply
noncompact observed dynamics.

## 7. Polar geometry and positivity

If a primary operation `T=q_{nu_alpha}^alpha` lies in a finite Hermitian sector, its framed polar
shadow is

\[
 G_\alpha=T^*T.
\tag{NHG.10}
\]

This records kernel, rank, and squared singular values. By polar decomposition it forgets a full
left unitary/partial-isometry factor, not merely scalar phase. It is invariant only under the
declared Hermitian/unitary gauge, not arbitrary `L_infinity` coordinates. Thus:

> Framed Gram observation of a primary operation is a left-unitary quotient.

Full positive structures need not lose this data. The loss occurs at the specified framed Gram
observer `(NHG.10)`.

## 8. Horizons and singularities

NHG distinguishes at least seven intrinsic or typed horizons.

1. **Tangent horizon:** an observer tangent map acquires kernel.
2. **Primary-operation horizon:** the observer kills or scalarizes a minimal operation.
3. **Atiyah-curvature horizon:** relative curvature becomes nonzero, singular, or unobservable.
4. **Component horizon:** a closed observer loop has nonzero fibre-component boundary.
5. **Holonomy horizon:** connection or higher holonomy is nontrivial.
6. **Completion horizon:** direct-sum and completed/product realizations differ by a nonzero
   source-relevant boundary object.
7. **Action horizon:** finite observer motion requires unbounded or infinite derived action.

These need not coincide. A central problem of the field is to find source conditions forcing two
or more horizons to meet.

## 9. Structural axioms and dynamics gates

NHG has no scalar Einstein equation yet. These are defining compatibility axioms or analytic gates,
not claimed dynamical equations.

### Law I — source integrability

The source section satisfies the Maurer--Cartan equation `(NHG.3)` and descent over `B`.

### Axiom II — higher transport identities

The codifferential satisfies `Q^2=0`, while a flat representation-up-to-homotopy superconnection
satisfies `mathbb D^2=0`. Their components give distinct higher Jacobi and transport/Bianchi
hierarchies.

### Law III — observer covariance

Gauge-equivalent presentations transport the primary-operation tower, relative Atiyah class,
anchor, Spencer filtration, cyclic pairing, and integrated transport.

### Law IV — polar compatibility

Where a positive observer is defined, its Gram data must be the polar image of a declared unsquared
tensor. Reconstruction requires the missing partial isometry or equivalent cross-polarizations.

### Law V — history properness

For dynamical realizations, bounded observer history plus bounded derived action must have compact
source-lift fibres. This is a coercivity/properness theorem to prove, not a consequence of cyclicity.

## 10. Nomological topology

A finite family of observers is an order-`N` **nomological cover** near `alpha` only if its product
is conservative on the `N`-truncated formal moduli germ. It is a full formal cover only if this
holds at every nilpotent order and the induced descent diagram reconstructs the pointed formal
law germ.

This topology is not generated by arbitrary convenient observers. It is generated by effective
formal descent. A family that loses the primary operation or relative Atiyah class cannot cover the
structured law germ.

Global topology, nonformal components, and completion still require additional descent data.

## 11. Fundamental research questions

1. Which naturally occurring mathematical theories possess a canonical anchored formal law
   algebroid rather than only a moduli space of solutions?
2. What source structures canonically select a Q-section and its anchor?
3. Can the primary nonformality order be computed directly from generators and relations without
   choosing a resolution?
4. When does a cyclic or shifted-symplectic structure transfer to the minimal law germ?
5. Which observer families form minimal nomological covers?
6. Is there a graded Ambrose--Singer theorem relating restricted higher holonomy to soldered
   Atiyah--Spencer curvature forms?
7. Which completion boundaries are invariant under structured Morita equivalence?
8. When does prolongation growth force infinite-order holonomy rather than mere observer kernel?
9. Is there an index theorem equating spectral flow of a law event with a cyclic pairing of its
   Atiyah--Spencer class?
10. When does cyclic transgression produce a coercive action rather than only a formal functional?

## 12. Bold conjectures

### Conjecture A — soldered graded Ambrose--Singer--Spencer theorem

Let `mathcal E` be a source-generated analytic complete cyclic filtered `L_infinity`-algebroid with
source-canonical horizontal splitting, vertical projection, formally effective Spencer tower, and
nilpotent higher-groupoid integration. The restricted vertical higher-holonomy `L_infinity`
algebra is the smallest filtered cyclic subalgebra generated by parallel transports of the soldered
curvature forms, their mixed vertical components, and all covariant Spencer prolongations.

The ordinary loop-holonomy algebra is only the binary two-form sector. Full holonomy is an extension
by independent fundamental-infinity-groupoid monodromy. The strict binary Atiyah-algebroid case is
paper-proved; higher arity is open. Raw internal `q_n` cannot replace the soldered curvature forms.

### Conjecture B — polar reconstruction

For a finite-type cyclic law germ, a separating family of source-compatible Gram and cross-Gram
shadows, together with the cyclic pairing, reconstructs each primary operation up to unitary
structured gauge.

A single Gram shadow and an orientation line cannot do this in dimension greater than one.

### Conjecture C — prolongation--holonomy alternative

For a source shift acting cyclically on an effective, self-dual prolongation tower, unbounded
Kolchin growth forces either failure of every fixed finite observer cover or infinite vertical
holonomy in any conservative compact observer realization.

The zero observer and trivial source shift are explicit falsifiers without the stated hypotheses.

### Conjecture D — nomological index theorem

For a proper cyclic law event with compact-resolvent vertical complex, the spectral flow equals a
cyclic pairing between its transgressed relative Atiyah--Spencer class and the source-history class.

This conjecture is deliberately independent of any RH endpoint.

## 13. Hostile countermodels

1. A flat nonabelian deformation problem may have nonzero primary bracket `q_2`; primary operation
   is not connection curvature.
2. An abelian infinite-dimensional formal moduli problem has unbounded tangent dimension but no
   nonlinear curvature.
3. A point observer is compact and recurrent while erasing every source direction.
4. A faithful positive identity observer loses no phase; positivity alone is not a quotient.
5. The same anchored formal field can admit noncoercive and coercive analytic completions; cyclic
   structure alone does not select properness.
6. Two formal germs with the same first primary operation can differ in higher operations.
7. Taking the source section to be the desired solution makes every field equation tautological.
8. Product-packaging an `L_infinity` algebra with an unrelated history system does not create a law:
   the zero anchor survives every local bracket computation but supplies no transport relation.
9. Two anchored algebroids can have identical first minimal operation and different anchors, hence
   different histories. Primary operation is not the field state.
10. A connected fibre can have zero component boundary and nontrivial connection holonomy.
11. Fixed finite-dimensional nilpotent structure does not bound the first nonzero curvature-jet
    order uniformly.

## 14. Field acceptance gates

NHG becomes a constructed mathematical field rather than a programme only after:

1. one nontrivial source-anchored cyclic filtered law algebroid is built independently of target
   theorems;
2. its primary operation and relative Atiyah class are computed in two inequivalent presentations
   and agree as predicted;
3. at least one nonzero Atiyah--Spencer class produces a theorem not available from cohomology or
   scalar invariants alone;
4. a nontrivial anchored observer fibration has both computed tangent loss and integrated holonomy
   boundary;
5. a cyclic/polar structure is derived from source and its positive shadow verified;
6. a genuine prolongation theorem is linked to a standard Kolchin invariant;
7. one action or properness law is derived, not chosen;
8. one withheld prediction is proved in a mathematical domain not used to design the field;
9. the construction survives structured Morita/presentation change;
10. hostile review finds no refinement that gauges away the claimed invariant.

No RH proof route is part of these gates. Only after they pass may the RH corpus be used as a
high-dimensional validation problem.

## 15. Parent mathematics and field boundary

NHG deliberately assembles established machinery:

- formal moduli problems and `L_infinity` algebroids;
- homotopy transfer and minimal models;
- derived and shifted-symplectic geometry;
- representations up to homotopy and higher holonomy;
- jet/prolongation and Spencer/Kolchin theory;
- Tate/Ind--Pro completion;
- cyclic pairings, operator positivity, and proper actions.

Primary parents include:

- Lurie, *Derived Algebraic Geometry X: Formal Moduli Problems*;
- Pridham, *Unifying derived deformation theories*;
- Pantev--Toen--Vaquie--Vezzosi, *Shifted Symplectic Structures*,
  <https://arxiv.org/abs/1111.3209>;
- Arias Abad--Schaetz, *The A-infinity de Rham theorem and integration of representations up to
  homotopy*, <https://arxiv.org/abs/1011.4693>;
- Laurent-Gengoux--Lavau--Strobl, *The universal Lie infinity-algebroid of a singular foliation*,
  <https://arxiv.org/abs/1806.00475>;
- Laurent-Gengoux--Louis, *The holonomy Lie infinity-groupoid of a singular foliation I*,
  <https://arxiv.org/abs/2503.23871>;
- Maunder, *Homotopy transfer for L-infinity structures and the BV-formalism*,
  <https://arxiv.org/abs/2408.12461>.

The proposed field is the geometry of **source-selected laws and their observers**, not a claim
that these parent theories are new.

## 16. Immediate programme

1. Prove a cyclic anchored version of the first-curvature invariance theorem.
2. Define structured Morita equivalence for cyclic filtered law algebroids.
3. Prove the superconnection component laws separating chain curvature from cohomological holonomy.
4. Attack Conjecture A first in finite nilpotent anchored `L_infinity` bundles.
5. Classify when observer holonomy is generated by the complete minimal bracket tower versus
   genuinely global data.
6. Develop an index pairing for proper self-dual law events.
7. Only after these steps, use the large HGT corpus as a stress test.

## Lean-return note

No Lean file was written or built. Paper foundations must stabilize before formalization.

## Log

- 2026-08-09 — field core created after route-level regression was explicitly rejected. Arbitrary
  observer-square curvature replaced by gauge-invariant first minimal `L_infinity` curvature.
