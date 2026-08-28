# Prime-edge observer formation, Hodge reconstruction, functional equation, recurrence, and bilateral properness law

- **ID:** ULF-DOFM-3
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / LITERAL SOURCE FUSION LAW
- **Programme:** `../../../1-in-progress/universal-law-field/derived-observer-formation-mechanics/field-programme.md`
- **Arithmetic parent:** `../../../3-formalized/universal-law-field/source-formation-harmonic-mechanics/prime-exponent-source-edge-refinement-energy-and-criticality-law.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LITERAL MÖBIUS SOURCE]`
  `[FORMATION HOMOLOGY] [JOINT RECONSTRUCTION] [HODGE ENERGY IDENTITY]`
  `[FUNCTIONAL-EQUATION ISOMETRY] [RECURRENT SHADOW/OPEN HISTORY]`
  `[BILATERAL PROPERNESS SELECTOR] [HT COEXISTENCE] [NOT RH]`
  `[LEAN-FORMALIZED] [AXIOM-AUDITED]`
- **Statement:** A finite block of literal prime-exponent source edges, observed by one character,
  has formation homology equal to the zero-sum edge-packet sector.  Coarse endpoint plus this
  harmonic class reconstructs the complete packet, its Hodge norm is exactly the source refinement
  excess, functional-equation reversal is information-neutral on the class, parity recurrence is
  endpoint closure with linearly growing harmonic history, and bilateral cofinal Hodge action is
  finite exactly at zero radial drift.

## 1. Literal source block

Fix integers `m>=1` and `r>=2`.  Let

\[
 E_{m,r}=\mathbb R^{r+1}
 \tag{PEH.1}
\]

with ordered basis `v_0,...,v_r`, where `v_j` marks the prime-exponent vertex `m+j`.  Define
oriented edge vectors

\[
 b_j=v_j-v_{j+1},
 \qquad 0\le j<r,
 \tag{PEH.2}
\]

and formation legs

\[
 W_j=\mathbb R b_j.
 \tag{PEH.3}
\]

These are the finite-dimensional coefficient vectors of the formalized literal source edges
`primeExponentEdge (m+j)`.  At canonical depth `12`, the theorem
`rankTwelveFiniteAbscissaSource_prime_edge` identifies them coefficient-for-coefficient with the
normalized finite-abscissa Möbius source channels.

### Lemma 1.1 -- edge independence

The vectors `b_0,...,b_{r-1}` are linearly independent.  Consequently distinct formation legs have
zero intersection.

### Proof

If `sum_j c_j b_j=0`, the `v_0` coefficient gives `c_0=0`.  The `v_j` coefficient for
`1<=j<r` is `c_j-c_{j-1}`, so induction gives every `c_j=0`; the terminal coefficient then also
vanishes.  QED.

## 2. Character observation and formation homology

For real `q`, define the character observer

\[
 \ell_q(v_j)=q^{m+j}.
 \tag{PEH.4}
\]

Its edge response is

\[
 d_j(q):=\ell_q(b_j)=q^{m+j}(1-q).
 \tag{PEH.5}
\]

Assume first `q ne 0,1`.  Then every edge response is nonzero, so

\[
 \ell_q(W_j)=\mathbb R.
 \tag{PEH.6}
\]

Since all higher intersections of distinct source legs are zero, the observer-formation complex is

\[
 0\longrightarrow\mathbb R^r
 \xrightarrow{\;\Sigma\;}\mathbb R\longrightarrow0,
 \qquad
 \Sigma(x_0,\ldots,x_{r-1})=\sum_jx_j,
 \tag{PEH.7}
\]

in degrees zero and minus one.

### Theorem 2.1 -- literal formation charge

For every `q ne 0,1`,

\[
 \boxed{
 \mathsf H_0(\ell_q;W_0,\ldots,W_{r-1})
 =\ker\Sigma
 =\left\{x\in\mathbb R^r:\sum_jx_j=0\right\},}
 \tag{PEH.8}
\]

all other formation homology vanishes, and

\[
 \boxed{\dim\mathsf H_0=r-1.}
 \tag{PEH.9}
\]

### Proof

Equation `(PEH.7)` has no positive-degree terms, and `Sigma` is surjective.  Its only homology is
therefore `ker Sigma` in degree zero.  Rank-nullity gives dimension `r-1`.  QED.

This is not a relabelling of edge independence.  Source legs are independent, yet the one-dimensional
observer sends every leg onto the same target line.  Formation homology is the exact family of
target packet variations invisible to the coarse sum.

## 3. Joint reconstruction and exact conservation

Give `R^r` its standard inner product and write `1=(1,...,1)`.  Define

\[
 P_r x=x-\frac{\Sigma x}{r}\,\mathbf1.
 \tag{PEH.10}
\]

Then `P_r` is the orthogonal projection onto the formation-homology carrier `ker Sigma`.

For a packet `d=(d_j)`, define its endpoint and harmonic charge by

\[
 s(d)=\Sigma d,
 \qquad
 h(d)=P_rd.
 \tag{PEH.11}
\]

### Theorem 3.1 -- joint packet reconstruction

The map

\[
 d\longmapsto(s(d),h(d))
 \tag{PEH.12}
\]

is an isomorphism

\[
 \mathbb R^r\simeq\mathbb R\oplus\ker\Sigma
 \tag{PEH.13}
\]

with inverse

\[
 \boxed{d=h+\frac{s}{r}\mathbf1.}
 \tag{PEH.14}
\]

It obeys the exact energy conservation law

\[
 \boxed{
 \|d\|_2^2=\frac{s(d)^2}{r}+\|h(d)\|_2^2.}
 \tag{PEH.15}
\]

### Proof

By definition `Sigma(P_rd)=0` and `d=P_rd+(Sigma d/r)1`, proving reconstruction.  The two summands
are orthogonal because `ker Sigma` is perpendicular to `1`.  Pythagoras gives `(PEH.15)`.  QED.

Equation `(PEH.15)` is exactly the formalized `refinement_energy_pythagoras` theorem: coarse
endpoint energy and source refinement excess are the two orthogonal pieces of one packet.

### Corollary 3.2 -- Hodge realization

The formation complex Laplacian on degree zero is `Sigma* Sigma`, its kernel is `ker Sigma`, and
`P_r` is its harmonic projector.  Therefore

\[
 \boxed{
 \text{source refinement excess}=\text{Hodge energy of formation homology}.}
 \tag{PEH.16}
\]

Positivity is not an independent producer in this chart.  It is the metric shadow of the exact
formation/reconstruction splitting.

## 4. Two-edge criticality

For `r=2`,

\[
 d_0=q^m(1-q),
 \qquad
 d_1=q^{m+1}(1-q).
 \tag{PEH.17}
\]

### Corollary 4.1 -- fourth-power Hodge charge

\[
 \boxed{
 \|h(d(q))\|_2^2
 =\frac12(d_0-d_1)^2
 =\frac12q^{2m}(1-q)^4.}
 \tag{PEH.18}
\]

For `q>0`, this vanishes exactly at `q=1`.  For `q=p^nu` with prime `p`, it vanishes exactly at
`nu=0`.

### Proof

The orthogonal projection of `(d_0,d_1)` onto the zero-sum line is
`((d_0-d_1)/2,(d_1-d_0)/2)`.  Its squared norm is `(d_0-d_1)^2/2`.  From `(PEH.17)`,

\[
 d_0-d_1=q^m(1-q)^2.
\]

This proves `(PEH.18)`.  Positivity of `q` and injectivity of the prime radial character give the
two zero-locus statements.  QED.

Thus the fourth-power criticality already formalized in Source Formation Harmonic Mechanics is
twice the Hodge energy of a one-dimensional observer-formation class.

## 5. Functional-equation reversal

Define vertex reversal and signed packet reversal by

\[
 J_rv_j=v_{r-j},
 \qquad
 (S_rx)_j=-x_{r-1-j}.
 \tag{PEH.19}
\]

Then

\[
 J_rb_j=-b_{r-1-j}.
 \tag{PEH.20}
\]

### Theorem 5.1 -- split functional-equation lift

For `q>0`,

\[
 \boxed{
 \ell_qJ_r=q^{2m+r}\ell_{q^{-1}},
 \qquad
 S_rd(q)=q^{2m+r}d(q^{-1}).}
 \tag{PEH.21}
\]

Moreover,

\[
 \boxed{
 S_r(\ker\Sigma)=\ker\Sigma,
 \qquad
 P_rS_r=S_rP_r,
 \qquad
 \|S_rh\|_2=\|h\|_2.}
 \tag{PEH.22}
\]

On reconstruction data, reversal acts by

\[
 \boxed{(s,h)\longmapsto(-s,S_rh).}
 \tag{PEH.23}
\]

It is therefore information-neutral: it preserves the complete recovered packet norm and the
formation-charge norm.  The reciprocal character contributes only the global metric-line factor
`q^(2m+r)` in `(PEH.21)`.

### Proof

On a vertex,

\[
 \ell_q(J_rv_j)=q^{m+r-j}
 =q^{2m+r}q^{-(m+j)}
 =q^{2m+r}\ell_{q^{-1}}(v_j),
\]

proving the first identity.  Apply it to `b_j` and use `(PEH.20)` for the second.  Signed reversal
is orthogonal and sends `1` to `-1`; hence it preserves the perpendicular space `ker Sigma`,
commutes with its orthogonal projector, and sends the endpoint sum to its negative.  The norm and
reconstruction statements follow.  QED.

### Corollary 5.2 -- functional equation cannot select the charge

For every nonzero formation class `h`, `S_rh` is again nonzero with equal norm.  Functional-equation
reversal transports the charge but cannot annihilate it.  This is the literal prime-edge instance
of the packet information-neutrality theorem.

## 6. Recurrent observer and open harmonic history

Set `q=-1` and take an even aperture `r=2n`.  Then

\[
 d_j(-1)=2(-1)^{m+j}.
 \tag{PEH.24}
\]

### Theorem 6.1 -- closed endpoint, open formation history

\[
 \boxed{
 s(d(-1))=0,
 \qquad
 h(d(-1))=d(-1),
 \qquad
 \|h(d(-1))\|_2^2=4r=8n.}
 \tag{PEH.25}
\]

The endpoint observer closes after every even block, while the harmonic formation history diverges
linearly in aperture.  Its `l1` variation is `2r=4n`.

### Proof

The alternating packet has equally many `2` and `-2` entries, so its sum is zero.  It therefore
already lies in `ker Sigma`, and its squared Euclidean norm is `r*4`.  Its `l1` norm is `r*2`.
QED.

This proves the precise geometry behind “closed observer projection with open lifted history” in
this source chart: the open lift is the Hodge carrier of formation homology, not an unspecified
covering-space metaphor.

## 7. Bilateral cofinal properness

For positive `q`, fix a source depth `M>=1`, take the two-edge Hodge charge beginning at every
depth `m>=M`, and define

\[
 A_m(q)=\frac12q^{2m}(1-q)^4.
 \tag{PEH.26}
\]

This is the literal value `(PEH.18)`.  Define the bilateral action

\[
 \mathcal A_{\rm bi}^{(M)}(q)
 =\sum_{m\ge M}A_m(q)+\sum_{m\ge M}A_m(q^{-1})
 \in[0,+\infty].
 \tag{PEH.27}
\]

### Theorem 7.1 -- global formation properness selector

For every `q>0`,

\[
 \boxed{
 \mathcal A_{\rm bi}^{(M)}(q)<\infty
 \quad\Longleftrightarrow\quad
 q=1
 \quad\Longleftrightarrow\quad
 A_m(q)=0\text{ for every }m.}
 \tag{PEH.28}
\]

For a prime-radial character `q=p^nu`, finite bilateral action is equivalent to `nu=0`.

### Proof

If `q=1`, every term is zero.  If `0<q<1`, the first series is geometric and finite, while
`q^{-1}>1`, so the terms of the reflected series do not tend to zero.  If `q>1`, the first series
already has terms not tending to zero.  Thus both series are finite exactly at `q=1`.  Equation
`(PEH.18)` gives the last equivalence, and injectivity of `nu mapsto p^nu` gives the radial
statement.  QED.

This is a literal realization of DOFM Law X: nonzero coherent formation charge has infinite
bilateral cofinal Hodge action.  No fitted positive weights or post-zero divisor data enter.

## 8. Hypertranscendence and unbounded formation rank

At depth `12`, the formalized arithmetic source supplies all edge channels in `(PEH.2)` and proves
their analytic realizations differentially independent over the full zeta differential field.
Theorem 2.1 gives, for every finite aperture `r` and every nontrivial character observer,

\[
 \dim\mathsf H_0=r-1.
 \tag{PEH.29}
\]

Hence the same literal source simultaneously has:

1. maximal countable differential rank in its analytic realization;
2. unbounded observer-formation homology rank under scalar character execution;
3. exact endpoint-plus-harmonic joint reconstruction;
4. a positive Hodge energy shadow;
5. functional-equation information neutrality;
6. recurrent endpoint closure with open harmonic history;
7. bilateral properness selecting zero radial drift.

This proves coexistence and one exact common mechanism.  It does **not** prove the universal claim
that every hypertranscendental family has unbounded formation homology for every legal observer.

## 9. Four-organ prediction and conservation ledger

The theorem was derived from the incidence and observer complexes.  It predicts the following
identities in the other source organs without inserting their target formulas:

| Organ | Forced quantity |
|---|---|
| coherent endpoint | `s=Sigma d` |
| positive refinement | `||h||^2=||d||^2-s^2/r` |
| functional equation | `(s,h) mapsto (-s,S_rh)` plus one metric-line scale |
| recurrence/history | closed endpoint means the entire packet lies in formation homology |
| cofinal admission | bilateral sum of two-edge Hodge charge is finite iff radial charge vanishes |
| analytic HT | apertures expose formation carriers of unbounded rank `r-1` |

The exact conservation identity is `(PEH.15)`, and the joint reconstruction formula is
`(PEH.14)`.  No one scalar shadow determines the packet; the endpoint and formation class together
do.

## 10. Hostile scope

1. **Not every observer gives `(PEH.8)`.**  The character must be nonzero on every admitted edge.
   At `q=1` all edge images vanish and the observed formation complex collapses.
2. **Formation rank does not select radial drift.**  Its dimension is `r-1` for every
   `q ne 0,1`.  Selection comes from bilateral cofinal Hodge action, not finite rank.
3. **Functional equation is neutral.**  Reversal is an isometry of the charge.  It cannot supply
   the missing vanishing law.
4. **One-sided action is insufficient.**  It is finite for every `0<q<1`.  Reciprocal reflection
   is load-bearing.
5. **No automatic RH theorem.**  Substituting `q=p^(2 Re rho-1)` makes `(PEH.28)` a pointwise
   critical-line criterion.  The corpus does not prove unconditional bilateral admission for every
   Xi divisor copy; assuming it would assume the missing selector.
6. **No universal HT equivalence.**  The theorem gives one literal source realization and a field
   prediction, not a classification of differential transcendence.

## 11. Collision and significance audit

Every ingredient separately is classical or already formalized internally:

- path incidence and the zero-sum decomposition;
- orthogonal projection/ANOVA and Pythagoras;
- reversal symmetry;
- geometric-series summability;
- the literal Möbius source edges, differential independence, recurrence, and bilateral selector
  in `SourceFormationHarmonicMechanics.lean`.

The exact new-to-corpus content is the **single homological identification**:

\[
 \boxed{
 \text{refinement excess}
 =\text{Hodge norm of observer-formation homology},
 \qquad
 \text{packet}=\text{endpoint}\oplus\text{formation class}.}
 \tag{PEH.30}
\]

It turns the prior five-shadow certificate into one reconstructive mechanism and makes the global
selector a properness theorem for a transported homology class.  Honest label:
`[CLASSICAL INGREDIENTS] [NEW-TO-CORPUS LITERAL FUSION] [FIELD-LEVEL PROGRESS]`.

## 12. Research consequence

This closes four requirements of the field gate on one pre-zero arithmetic source:

1. common intervention/generation grammar -- prime-edge formation plus character observation;
2. fusion across incidence, positive energy, functional equation, recurrence/history, and HT;
3. joint reconstruction and exact energy conservation;
4. a source-derived bilateral properness selector for radial drift.

What remains for RH is now narrower and typed.  One must construct a **global source admission
theorem** transporting the two-edge Hodge class noncontractingly to every multiplicity-resolved Xi
copy while keeping both reciprocal orientations.  The functional equation supplies the isometric
transport but, by Theorem 5.1, not the admission.  This is the formation-theoretic form of the
current horizontal-selector wall.

## 13. Lean status

Fully certified in
`HTGeometry.PrimeEdgeObserverFormationHodge`.  The module proves literal consecutive-edge
independence and trivial pairwise leg intersections; identifies formation homology with the
zero-sum kernel and proves the coarse cokernel vanishes; constructs endpoint-plus-charge linear
reconstruction with exact Pythagorean conservation; realizes the fusion-adjoint Laplacian and its
harmonic projector; proves vertex and signed packet reversal, reciprocal character transport,
energy preservation, and nonannihilation; computes the two-edge fourth-power charge and its prime
radial zero locus; certifies even recurrent closure with `l2` and `l1` growth; proves shifted
bilateral cofinal summability exactly at unit character and zero radial drift; and combines
depth-`12` differential independence with unbounded formation rank.

Direct project-path elaboration and targeted leaf build
`lake build GaloisForLFunctions.HTGeometry.PrimeEdgeObserverFormationHodge` pass.  Module is wired
into `HTGeometry.UniversalLawField` and `HTGeometry`; neither umbrella was built.  Twenty audited
created declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Repository
lint reaches the module and reports no defect in it; nonzero status comes from unrelated
shared-worktree umbrella-reachability failures.  No RH claim is made.

## Gates

- [x] 0 -> 1: literal source block, observer complex, and formation carrier
- [x] 1 -> 2: joint reconstruction, Hodge identity, FE isometry, recurrence, and bilateral selector
- [x] 2 -> 3: Lean certification of the homology/Hodge/reversal fusion
- [ ] 3 -> 4: unconditional global Xi admission of the bilateral Hodge class

## Log

- 2026-08-14 -- literal prime-edge source reinterpreted as one observer-formation Hodge mechanism;
  endpoint-plus-charge reconstruction and bilateral homological properness proved on paper.
- 2026-08-29 -- formalized the full literal fusion law in
  `HTGeometry.PrimeEdgeObserverFormationHodge`; direct elaboration, targeted leaf build, lint
  reachability, and batched axiom audit completed; promoted to Stage 3.
