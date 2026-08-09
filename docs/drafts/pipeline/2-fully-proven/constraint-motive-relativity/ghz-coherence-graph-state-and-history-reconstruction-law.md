# GHZ coherence-graph state and history reconstruction law

- **ID:** `cmr-ghz-coherence-graph-state-history-reconstruction`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [PHYSICAL OBSERVATION CALIBRATION]`
  `[STATE/HISTORY SEPARATION] [NOT A WORMHOLE THEOREM] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Parent physics card:**
  `../nomological-geometry-and-dynamics/framed-two-boundary-phase-fibre-recurrence-and-history-separation.md`.
- **Parent field:**
  `../../1-in-progress/constraint-motive-relativity/polarized-constraint-duality-geometry.md`.
- **Statement:** Separate two-boundary reductions erase the full framed GHZ phase torus. Pairwise
  coherence probes indexed by a graph reconstruct the global phase state exactly iff the graph is
  connected; a spanning tree is minimal and sufficient. Connected endpoint probes still do not
  reconstruct winding or executed action, while lifted edge histories recover the winding class.

## 1. Setup

For `d>=2`, let

\[
 e_j=|j\rangle_R|j\rangle_A|j\rangle_B,
 \qquad
 |\Psi_\phi\rangle=\frac1{\sqrt d}\sum_{j=0}^{d-1}e^{i\phi_j}e_j,
 \qquad
 \Omega_\phi=|\Psi_\phi\rangle\langle\Psi_\phi|.
\tag{GCR.1}
\]

The parent theorem proves that both reductions `Tr_A Omega_phi` and `Tr_B Omega_phi` are
independent of `phi`, while the common framed fibre is

\[
 \mathcal F_d=\mathbb T^d/\mathbb T_{\rm diag}\cong\mathbb T^{d-1}.
\tag{GCR.2}
\]

Let `G=(V,E)` be a finite undirected graph on `V={0,...,d-1}` and choose one orientation of each
edge. For an oriented edge `e=(j,k)`, define the cross-coherence probe

\[
 C_e(\Omega)=d\langle e_j,\Omega e_k\rangle.
\tag{GCR.3}
\]

On the phase fibre,

\[
 C_{jk}(\Omega_\phi)=e^{i(\phi_j-\phi_k)}.
\tag{GCR.4}
\]

Thus the graph observation map is

\[
 \chi_G:\mathcal F_d\longrightarrow\mathbb T^E,
 \qquad
 [z]\longmapsto(z_jz_k^{-1})_{(j,k)\in E}.
\tag{GCR.5}
\]

## 2. State reconstruction theorem

### Theorem 2.1 — exact graph criterion

If `c(G)` is the number of connected components, then

\[
 \boxed{\ker\chi_G\cong\mathbb T^{c(G)-1}.}
\tag{GCR.6}
\]

Consequently the following are equivalent:

1. the coherence probes reconstruct every point of `F_d`;
2. `chi_G` is injective;
3. `G` is connected.

Among pairwise coherence-probe families, at least `d-1` probes are necessary. Every spanning tree
uses exactly `d-1` probes and is sufficient.

### Proof

An element `[z]` lies in the kernel exactly when `z_j=z_k` along every edge. Hence `z` is constant
on each connected component. These constants form `T^{c(G)}` before quotienting the common
diagonal phase and `T^{c(G)-1}` afterward, proving `(GCR.6)`. The kernel is trivial exactly when
`c(G)=1`. Every connected graph on `d` vertices has at least `d-1` edges, and a spanning tree has
exactly `d-1`, proving minimality and sufficiency.

### Corollary 2.2 — quantitative residual fibre

Any family of `m` pairwise coherence probes leaves a residual phase fibre of dimension at least

\[
 \dim\ker\chi_G=c(G)-1\geq d-m-1.
\tag{GCR.7}
\]

Equality is attained by a forest. Thus every missing edge below the spanning-tree threshold costs
at least one continuous relative-phase direction.

## 3. Image and cycle law

### Theorem 3.1

The image of `chi_G` consists exactly of edge phases whose oriented product around every graph
cycle is `1`. For connected `G`, this cycle law and one chosen root reconstruct all vertex phases
modulo the common diagonal.

### Proof

For phases of the form `z_jz_k^(-1)`, the factors telescope around every cycle. Conversely, choose
a root in each connected component and define its phase arbitrarily. Propagate vertex phases along
a spanning forest using the observed edge ratios. Cycle product `1` makes the result independent
of path. Changing one root phase multiplies all vertices in its component by the same constant;
for connected `G` this is precisely the diagonal quotient.

## 4. History reconstruction theorem

Let `phi:[0,T]->R^d` be a lifted history whose phase state closes at `T`. Its vertex winding class
is

\[
 [m]\in\mathbb Z^d/\mathbb Z\mathbf1,
 \qquad \phi(T)-\phi(0)=\theta\mathbf1+2\pi m
\tag{GCR.8}
\]

for some `theta in R` and `m in Z^d`. Changing the diagonal lift changes `m` by an integral
multiple of `1` and leaves `[m]` fixed.

For `e=(j,k)`, the lifted edge history has winding

\[
 n_e=m_j-m_k.
\tag{GCR.9}
\]

### Theorem 4.1

The map

\[
 B_G:\mathbb Z^d/\mathbb Z\mathbf1\longrightarrow\mathbb Z^E,
 \qquad [m]\longmapsto(m_j-m_k)_{(j,k)\in E}
\tag{GCR.10}
\]

is injective iff `G` is connected. Its image is the integral cut lattice, equivalently the edge
winding vectors whose signed sum around every cycle is zero.

Thus a connected set of **lifted edge histories** reconstructs the loop class. Endpoint values do
not: every closed history returns all edge probes to their initial values regardless of winding.

### Proof

The kernel consists of integer vertex labels constant on every connected component, modulo the
global constant label. It is zero exactly when `G` is connected. Telescoping gives the cycle
constraints; integer propagation along a spanning forest proves their sufficiency.

## 5. Action remains additional data

For the Fubini--Study metric inherited from the source Hilbert space, the parent theorem gives

\[
 \mathcal A_{\min}^{[m]}(T)
 =\frac{2\pi^2}{dT}\|Pm\|^2,
 \qquad P=1-d^{-1}\mathbf1\mathbf1^T.
\tag{GCR.11}
\]

Connected lifted-edge windings determine `[m]` and hence this minimum action. They do not determine
the executed action of an arbitrary path in the same class: a nonconstant contractible excursion
can strictly change length and kinetic action without changing endpoints or winding. Executed
action is determined by the time-parametrized phase-fibre path and Fubini--Study metric; an
absolute diagonal lift is unnecessary.

## 6. Stratified-observer meaning

Separate boundary reductions form a maximally blind observer stratum: their restriction to
`F_d` is constant. Pairwise coherence probes form a graph-indexed enlargement. The exact
reconstruction threshold is connectivity, not the number of boundary marginals or a recovery
scalar.

This calibrates the source observer-density conjecture without proving it categorically:

- disconnected probe graph: nontrivial observation fibre;
- connected probe graph: point-separating global phase observation;
- connected lifted histories: winding reconstruction;
- metric path probe: executed-action reconstruction.

Point separation in this finite torus is weaker than full categorical density. No density claim is
made without a literal category and full-faithfulness proof.

## 7. Conjecture/proof/failure loops

### Loop A — two boundary marginals reconstruct the framed state

**Failed.** They are constant on the full `T^(d-1)` fibre.

**Survivor.** Relative cross-coherences are the missing native probes.

### Loop B — all pairwise coherences are necessary

**Failed.** A spanning tree of `d-1` probes is sufficient and minimal among edge probes.

### Loop C — any `d-1` probes suffice

**Failed.** They must form a connected graph; a disconnected `d-1`-edge graph leaves a
positive-dimensional kernel.

**Survivor.** Connectivity, not count alone, is the invariant.

### Loop D — reconstructed endpoint state reconstructs history

**Failed.** Closed loops of every winding have identical initial/final probe values.

**Survivor.** Lifted edge histories recover winding exactly when the graph is connected; executed
action still needs the metric path.

### Loop E — the phase fibre is a wormhole interior

**Failed as an inference.** The theorem constructs no gravity, edge charge, Lorentzian metric,
entropy, or bulk reconstruction map.

**Survivor.** If reconstruction is implemented through pairwise coherences, a proposed
two-boundary interior realization must explain which probes supply a connected graph. An
alternative realization must supply other phase-sensitive probes. Either case still needs history,
metric/cost, and an independent bulk map.

## 8. Predictions and falsifiers

1. Fewer than `d-1` pairwise coherence probes cannot reconstruct a framed rank-`d` GHZ phase.
2. Exactly `d-1` probes reconstruct iff their underlying graph is a tree.
3. A disconnected graph with `c` components leaves exactly `c-1` torus directions invisible.
4. Endpoint phase reconstruction never determines nonzero winding or executed action of a closed
   history.
5. Any model claiming reconstruction of this framed GHZ phase state from only the two marginals,
   their CMI, or recovery error fails this test. Within the pairwise-coherence scheme, state
   reconstruction requires a connected graph; winding and action additionally require history and
   metric data. Identifying any such data with bulk physics requires a separate bulk map.

## 9. No-go closure

- **Failed conjecture:** boundary completeness or recovery data determine relative phase history.
- **Exact killing mechanism:** partial trace deletes every off-diagonal phase; disconnected
  coherence graphs retain componentwise phase gauge.
- **Strongest positive survivor:** connected graph is necessary and sufficient for state and
  winding reconstruction from the corresponding edge probes; path action remains a higher layer.
- **Scope:** unconditional finite-dimensional theorem; no Lean written or built; no gravity or RH
  claim.

## Log

- 2026-08-09 — proved graph-connectivity state-reconstruction criterion.
- 2026-08-09 — proved integral edge-winding reconstruction and cycle law.
- 2026-08-09 — separated endpoint state, winding, and executed action.
