# Static--circuit two-memory orthogonality law

- **ID:** `static-circuit-two-memory-orthogonality-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / universal moment decomposition / recurrence realignment
- **Parents:** `centralizer-centered-circuit-collision-and-design-barrier-law.md`,
  `all-replica-static-centralizer-planar-separation-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY PROVISIONAL] [LEAN DEFERRED]`
- **Date:** 2026-08-10

## Public sentence

Quantum complexity does not require a system to forget how it was generated.  Static dynamics and
shallow circuits may both retain large, permanently non-Haar memories; a state is hard precisely
when those two memories fail to recognize one another.  A recurrence is their forced realignment.

## 1. Abstract setup

Let `V` be a finite-dimensional complex Hilbert space.  Let `Pi` be an orthogonal projection with
range `N`.  For every Hamiltonian label `H`, let `L_H=L_H^*` and let

\[
 P_H=\mathbf 1_{\{0\}}(L_H)                                                \tag{1}
\]

be the orthogonal projection onto `ker L_H`.  Assume

\[
 \mathcal N\subseteq\ker L_H                                               \tag{2}
\]

for every `H`.  Hence `Pi P_H=P_H Pi=Pi`.

Let `T:V->V` be a linear contraction satisfying

\[
 \Pi T=\Pi.                                                               \tag{3}
\]

In the circuit application, `T` is the one-gate moment channel and `(3)` follows because Haar
twirling is unchanged by precomposition with any gate.  Fix `x in V`.  Define four exact sectors:

\[
\begin{aligned}
 u&=\Pi x &&\text{(universal Haar/permutation sector)},\\
 c_H&=(P_H-\Pi)x &&\text{(quenched spectral memory)},\\
 r_H(t)&=(e^{-itL_H}-P_H)x &&\text{(oscillatory time memory)},\\
 q_s&=(T^s-\Pi)x &&\text{(depth-`s` circuit-preparation memory)}.
\end{aligned}                                                             \tag{4}
\]

The word “memory” in `(4)` has exact algebraic content: each vector is the component retained after
one specified conditional expectation is removed.  No information-theoretic interpretation is used
as a premise.

## 2. Exact orthogonal decomposition

### Theorem A -- two-memory collision law

For every `H`, real `t`, and integer `s>=0`,

\[
\begin{aligned}
 e^{-itL_H}x&=u+c_H+r_H(t),\\
 T^s x&=u+q_s,                                                            \tag{5}
\end{aligned}
\]

and

\[
 u\perp c_H,\qquad u\perp r_H(t),\qquad u\perp q_s,
 \qquad c_H\perp r_H(t).                                                  \tag{6}
\]

Consequently

\[
 \boxed{
 \langle e^{-itL_H}x,T^s x\rangle
 =\|u\|^2+\langle c_H,q_s\rangle
            +\langle r_H(t),q_s\rangle .}                                \tag{7}
\]

The completed static baseline is exactly

\[
 \boxed{
 \langle P_Hx,T^s x\rangle
 =\|u\|^2+\langle c_H,q_s\rangle,}                                       \tag{8}
\]

and the entire physical-time correction is the single cross-alignment

\[
 \boxed{
 \langle(e^{-itL_H}-P_H)x,T^s x\rangle
 =\langle r_H(t),q_s\rangle.}                                             \tag{9}
\]

### Proof

Because `N subset ker L_H`, the two orthogonal projections are nested:
`Pi P_H=P_H Pi=Pi`.  Thus

\[
 \Pi(P_H-\Pi)=0,
 \qquad P_H(e^{-itL_H}-P_H)=0.                                            \tag{10}
\]

Functional calculus gives

\[
 e^{-itL_H}=P_H+e^{-itL_H}(I-P_H),                                       \tag{11}
\]

which proves the first line of `(5)` and the first, second and fourth orthogonalities in `(6)`.
Equation `(3)` implies `Pi T^s=Pi` by induction, so `Pi q_s=0`; this proves the second line of `(5)`
and the remaining orthogonality.  Expanding the inner products now gives `(7)`--`(9)`.

### Corollary A.1 -- static nonmixing is compatible with zero collision defect

The quenched static defect has the exact conserved norm

\[
 \boxed{
 \|c_H\|^2+\|r_H(t)\|^2=\|(I-\Pi)x\|^2}                                  \tag{12}
\]

for every `t`.  In particular, neither component needs to become small for the dynamic correction
`(9)` to vanish; only their relative pairing with `q_s` matters.

### Proof

The vectors `c_H=(P_H-Pi)x` and `(I-P_H)x` are orthogonal and sum to `(I-Pi)x`.  Unitarity of
`e^(-itL_H)` on `(ker L_H)^perp` gives
`||r_H(t)||=||(I-P_H)x||`.  Pythagoras proves `(12)`.

This is the exact point missed by every norm-mixing route.  A persistent static defect is not an
obstruction to circuit hardness unless it aligns with the circuit-preparation defect.

## 3. Ensemble form and the non-Haar plateau

Let `mu` be any probability law on the Hamiltonian labels and define Bochner averages

\[
 \bar c=\int c_H\,d\mu(H),\qquad
 \bar r(t)=\int r_H(t)\,d\mu(H).                                          \tag{13}
\]

Finite dimension makes these integrals elementary.  Averaging `(7)` gives

\[
 \boxed{
 \int\langle e^{-itL_H}x,T^s x\rangle\,d\mu(H)
 =\|u\|^2+\langle\bar c,q_s\rangle
             +\langle\bar r(t),q_s\rangle.}                              \tag{14}
\]

The three terms have distinct meanings:

1. `||u||^2` is the universal Haar/permutation floor;
2. `<bar c,q_s>` is the time-independent alignment of the ensemble's moving spectral centralizers
   with the shallow-circuit moment;
3. `<bar r(t),q_s>` is the only time-dependent static-versus-circuit defect.

When signed angular dephasing applies, `bar r(t)->0`, while `bar c` can remain nonzero.  Thus the
long-time static ensemble may remain separated from Haar in moment norm even though its collision
with the shallow-circuit body has reached the completed plateau.  This is an exact mechanism for
“complexity without randomness”; it is not a claim that every non-Haar ensemble is complex.

## 4. Circuit specialization

Let `K` be a finite-dimensional state Hilbert space, let `rho_0` be a pure seed density, and set

\[
 V_r=\operatorname{End}(K^{\otimes r}),\qquad x_r=\rho_0^{\otimes r}.      \tag{15}
\]

For a time-independent Hamiltonian `H`, take `L_(H,r)=ad_(H_[r])` and `P_(H,r)` as in the parent
card.  Let `G` be a finite inverse-closed gate alphabet of cardinality `M>=2`, containing the
identity, and let

\[
 (T_rX)={1\over M}\sum_{g\in G}
    g^{\otimes r}X(g^*)^{\otimes r}.                                      \tag{16}
\]

Then

\[
 T_r^s x_r={1\over M^s}\sum_{w\in G^s}\sigma_w^{\otimes r},              \tag{17}
\]

where `sigma_w` is the pure state prepared by word `w`.  Let `Pi_r` be the Haar twirl for the compact
closure of the gate group.  It obeys `Pi_r T_r=Pi_r`, and its range is contained in every
`ker L_(H,r)` when that closure is the full unitary group.

Writing

\[
 f_w(H,t)=\operatorname{Tr}(\rho_t\sigma_w)\in[0,1],
 \qquad \rho_t=e^{-itH}\rho_0e^{itH},                                    \tag{18}
\]

the collision is

\[
 A_{s,r}(H,t)
 :=\langle e^{-itL_{H,r}}x_r,T_r^s x_r\rangle
 ={1\over M^s}\sum_{w\in G^s} f_w(H,t)^r.                               \tag{19}
\]

### Theorem B -- complete circuit collision has exactly three sectors

Define `u_r,c_(H,r),r_(H,r)(t),q_(s,r)` by `(4)` with
`(Pi,P_H,L_H,T,x)=(Pi_r,P_(H,r),L_(H,r),T_r,x_r)`.  Then

\[
 \boxed{
 A_{s,r}(H,t)
 =\|u_r\|^2
  +\langle c_{H,r},q_{s,r}\rangle
  +\langle r_{H,r}(t),q_{s,r}\rangle.}                                  \tag{20}
\]

Every circuit of length at most `s` occurs in `(19)` after identity padding.  Hence, for every
threshold `0<a<=1`,

\[
 \boxed{
 \max_{|w|\le s}f_w(H,t)\ge a
 \quad\Longrightarrow\quad
 \langle r_{H,r}(t),q_{s,r}\rangle
 \ge {a^r\over M^s}-B_{s,r}(H),}                                        \tag{21}
\]

where

\[
 B_{s,r}(H)=\|u_r\|^2+\langle c_{H,r},q_{s,r}\rangle
 =\langle P_{H,r}x_r,T_r^s x_r\rangle.                                  \tag{22}
\]

Conversely,

\[
 \boxed{
 B_{s,r}(H)+\langle r_{H,r}(t),q_{s,r}\rangle<{a^r\over M^s}
 \quad\Longrightarrow\quad
 C_a(\rho_t)>s,}                                                         \tag{23}
\]

where `C_a(\rho_t)>s` means no length-at-most-`s` target has squared fidelity at least `a`.

### Proof

Equation `(20)` is Theorem A.  If one padded word has fidelity at least `a`, its summand in `(19)`
is at least `a^r/M^s`.  Subtract `(22)` and use `(20)` to obtain `(21)`.  The contrapositive gives
`(23)`.

Theorem B is not a union bound followed by an interpretation.  Equation `(20)` is an identity for
the one-gate moment channel, and `(21)` proves that every actual shortcut forces a quantitatively
positive alignment of the two nonuniversal memory sectors.

### Corollary B.1 -- a shortcut has a minimum memory angle

The circuit specialization lives in the real Hilbert subspace of Hermitian moment operators, so
all three terms in `(20)` are real.  Whenever `r_(H,r)(t)` and `q_(s,r)` are nonzero, define their
normalized alignment by

\[
 \cos\Theta_{H,s,r}(t)
 ={\langle r_{H,r}(t),q_{s,r}\rangle
   \over\|r_{H,r}(t)\|\,\|q_{s,r}\|}.                         \tag{23a}
\]

Let `0<=beta<1`.  If some length-at-most-`s` circuit has fidelity at least `a` and

\[
 B_{s,r}(H)\le\beta {a^r\over M^s},
\]

then

\[
 \boxed{
 \cos\Theta_{H,s,r}(t)
 \ge{(1-\beta)a^r
       \over M^s\|r_{H,r}(t)\|\,\|q_{s,r}\|}>0.}              \tag{23b}
\]

At an exact recurrence the same conclusion holds with `a=1`, provided
`B_(s,r)(H)<=beta/M^s`.  Conversely, strict failure of `(23b)` excludes every such shortcut under
the displayed baseline bound.

### Proof

Subtract the baseline bound from `(21)` and divide by the two positive norms.  At recurrence use
`(26)` below.  The converse is the contrapositive.  Thus “orthogonality” is not metaphorical: once
the completed baseline is below capture scale, every easy state occupies an explicit positive
angular cap, while hardness is exclusion from that cap.

## 5. Recurrence is forced memory realignment

The identity word belongs to every padded dictionary.  Let

\[
 F_0(H,t)=\operatorname{Tr}(\rho_t\rho_0).                                \tag{24}
\]

### Theorem C -- recurrence-alignment law

For every `H,t,s,r`,

\[
 \boxed{
 \langle r_{H,r}(t),q_{s,r}\rangle
 \ge {F_0(H,t)^r\over M^s}-B_{s,r}(H).}                                  \tag{25}
\]

At an exact recurrence `rho_t=rho_0`,

\[
 \boxed{
 \langle r_{H,r}(t),q_{s,r}\rangle
 \ge {1\over M^s}-B_{s,r}(H).}                                          \tag{26}
\]

More generally, for an ensemble event `E` on which some depth-`s` target has fidelity at least `a`,

\[
 \boxed{
 \left\langle\int r_{H,r}(t)\,d\mu(H),q_{s,r}\right\rangle
 \ge {a^r\mu(E)\over M^s}-\int B_{s,r}(H)\,d\mu(H).}                    \tag{27}
\]

### Proof

The identity word contributes `F_0(H,t)^r/M^s` to `(19)`, proving `(25)` through `(20)`--`(22)`.
Equation `(26)` is its exact-recurrence specialization.  On `E`, the complete collision is at least
`a^r/M^s`; it is nonnegative off `E`.  Integrate, use `(14)`, and subtract the averaged baseline to
obtain `(27)`.

Thus recurrence is not merely compatible with the decomposition.  Whenever the completed baseline
is small, an easy return mathematically forces the oscillatory static memory to realign with the
circuit-preparation memory by the exact amount in `(25)`--`(27)`.

## 6. All-replica zero-temperature reconstruction

The complete maximum can be recovered without a circuitwise union.  For fixed `H,t,s`, normalized
finite-set `L^p` convergence gives

\[
 \boxed{
 \max_{w\in G^s}f_w(H,t)
 =\lim_{r\to\infty}A_{s,r}(H,t)^{1/r}.}                                  \tag{28}
\]

Indeed, with `Y=max_w f_w`,

\[
 M^{-s}Y^r\le A_{s,r}(H,t)\le Y^r,                                      \tag{29}
\]

and `M^(-s/r)->1`.  Combining `(20)` and `(28)` gives the exact memory-sector reconstruction

\[
 \boxed{
 \max_{|w|\le s}f_w(H,t)
 =\lim_{r\to\infty}
 \left(
  \|u_r\|^2+\langle c_{H,r},q_{s,r}\rangle
  +\langle r_{H,r}(t),q_{s,r}\rangle
 \right)^{1/r}.}                                                         \tag{30}
\]

The expression inside the root is nonnegative because it is exactly `(19)`, even though the final
alignment term can have either sign.  Equation `(30)` is a zero-temperature replica identity, not
a finite-replica estimate.  Ensemble averaging and `r->infinity` may not be interchanged: rare easy
Hamiltonians dominate an essential supremum.  Any typical-growth theorem must keep the quenched or
return-excised quantifiers explicit.

## 7. Conjecturing protocol

### C0 -- Brown complexity requires convergence of static dynamics to Haar randomness

**Verdict:** `[FALSIFIED]`.

The parent centralizer law proves a persistent moving-centralizer sector for every static
Hamiltonian.  Externally, constant-local time-independent Hamiltonians remain efficiently
distinguishable from Haar at every time.  Existing completed-phase plateau theorems nevertheless
produce full-scale circuit hardness.

### C1 -- persistent non-Haar norm obstructs maximal complexity

**Verdict:** `[FALSIFIED EXACTLY]` by `(7)`, `(12)`, and `(20)`.

The static defect norm can remain constant while its circuit collision correction is zero.  The
preparation moment can also remain far from its Haar design by the parent's support-rank barrier.
Only the cross-alignments enter circuit collision.

### C2 -- prove Brown growth by separately shrinking the two memory norms

**Verdict:** `[FALSIFIED AS A REPRESENTATION]`.

Quenched static norm is conserved by `(12)`.  Circuit-moment norm cannot reach the one-word scale
before capacity because of the exact design square-root barrier.  Separate mixing is stronger than
the event and false at the required scale.

### C3 -- complexity is relative memory orthogonality

**Verdict:** `[EXACT DECOMPOSITION AND RECURRENCE LAW PAPER-PROVED; BROWN-RATE CLAIM OPEN]`.

Theorems A--C prove the representation and its falsifiable return prediction.  The live conjectural
content is quantitative:

> **Autonomous memory-orthogonality conjecture.**  For the ordinary fixed-locality static ensemble,
> after one target-independent return and shortcut-carrier excision, the positive alignment
> `<bar r_(t,r),q_(s,r)>` falls below the one-word threshold left after the completed baseline,
> uniformly on the geometric Brown skeleton whenever `s<a Lambda t/poly(n)`.  At the first spectral
> return it crosses back above that threshold as forced by `(27)`.

This conjecture is not admitted as a result.  It is stronger than “complexity is not randomness”:
it identifies one explicit pair of memory sectors, an exact threshold, and a forced recurrence
realignment.  It is not yet proved that ordinary local Hamiltonians produce the required angle.

## 8. Universal shadow map

| Existing theorem, obstruction, or physical claim | Exact shadow of the two-memory law |
|---|---|
| Completed spectral-phase plateau | Small frozen alignment `||u_r||^2+<c_(H,r),q_(s,r)>`. |
| Static moving-centralizer obstruction | Nonzero `c_(H,r)`; plateau is not Haar mixing. |
| Quenched centered-norm no-go | Conserved `||r_(H,r)(t)||`; only its angle with `q_(s,r)` matters. |
| Circuit design square-root barrier | Large `||q_(s,r)||`; only directional cancellation can reach one-word scale. |
| Gate Bellman/Green law | `q_(s,r)` is generated by the actual one-gate channel, not an arbitrary target net. |
| Brown growth | Suppression of the dynamic alignment below `(23)` along the depth--time skeleton. |
| Complexity plateau | Both alignments remain below capture scale for almost all completed time. |
| Quantum recurrence | Forced positive realignment `(25)`--`(27)`. |
| Permanent local/Haar distinguishability | Persistent static memory can coexist with small circuit alignment. |

The ontological reversal is precise: randomness is not the resource whose production complexity
measures.  Complexity measures incompatibility between the system's retained spectral memory and
the preparation memory of the allowed gate dynamics.

## 9. Hostile audit

1. **The decomposition is elementary algebra.**  Orthogonal projections, moment channels and
   finite `L^p` convergence are standard.  Novelty is not claimed for those ingredients separately.
2. **No Brown rate.**  The autonomous memory-orthogonality conjecture remains exactly the hard
   static-Hamiltonian lower bound.  Replacing “complexity growth” by “angle decay” is progress only
   because `(20)` removes false norm/design targets and `(25)` fixes recurrence behavior; it is not
   itself a solution.
3. **Annealed cancellation is weaker than a quenched law.**  Equation `(14)` controls an ensemble
   collision.  A high-probability simultaneous-time theorem requires finite-replica tail estimates
   after fixed exceptional-set excision.
4. **Large defects alone say nothing.**  The theorem does not assert that any two non-Haar ensembles
   are mutually hard.  Their cross-alignment is the entire issue.
5. **Exact recurrence may be absent at nonzero finite time.**  Equations `(25)` and `(27)` cover
   approximate recurrence.  Finite-dimensional quasiperiodicity supplies arbitrarily accurate
   returns under the separate spectral hypotheses already formalized in the corpus.
6. **Restricted gate groups change `Pi_r`.**  The projection must be the Haar twirl of the compact
   closure of the actual gate group.  Full-unitary permutation language requires universality.
7. **External priority.**  Guo--Sasieta--Swingle prove that complexity and design generation have
   different time scales for Brownian models.  Isospectral-twirling literature separates spectral
   and eigenvector data.  Random-circuit moment literature studies convergence to permutation fixed
   spaces.  Targeted search found no exact static-centralizer/circuit-defect decomposition with the
   shortcut threshold `(21)` and forced recurrence realignment `(25)`.  Priority remains
   provisional pending specialist review.
8. **Lean status.**  The theorem is dependency-closed on paper.  No final manuscript may use it as
   AI-proved until the exact finite-Hilbert-space statement passes Lean and axiom audit after the
   active corpus refactor.

## 10. External boundary checked

- Guo, Sasieta and Swingle, *Complexity is not Enough for Randomness*, arXiv:2405.17546, treats
  Brownian time-dependent systems and design time; it does not state the two-memory identity for one
  static Hamiltonian or the recurrence realignment law.
- Haferkamp, *Random quantum circuits are approximate unitary t-designs in depth
  O(n t^(5+o(1)))*, arXiv:2203.16571, bounds moment-channel spectral gaps; the parent's rank barrier
  proves that global design norm is the wrong scale for one-word Brown detection.
- Leone, Oliviero and Hamma, *Isospectral twirling and quantum chaos*, arXiv:2011.06011, organizes
  chaos probes by isospectral twirls but does not couple the moving spectral centralizer to a
  shallow-circuit preparation moment.
- Cui et al., *Random unitaries from Hamiltonian dynamics*, arXiv:2510.08434, proves efficient
  non-Haar distinguishability for constant-local static dynamics at every time.  That theorem is
  compatible with, but does not imply, small circuit-memory alignment.

## 11. Lean plan after refactor

1. nested orthogonal-projection lemmas `(5)`--`(12)`;
2. finite gate-moment iteration `(16)`--`(19)`;
3. three-sector circuit identity and shortcut implication `(20)`--`(23)`;
4. recurrence realignment `(25)`--`(27)`;
5. finite-family `L^p` limit `(28)`--`(30)`;
6. one targeted module check, axiom audit, umbrella wiring, and final targeted module build.
