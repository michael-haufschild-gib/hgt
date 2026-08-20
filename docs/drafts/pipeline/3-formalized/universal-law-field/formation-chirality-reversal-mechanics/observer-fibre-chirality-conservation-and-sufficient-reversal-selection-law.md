# Observer-fibre chirality conservation and sufficient-reversal selection law

- **ID:** ULF-FCRM-2
- **Stage:** 3-formalized
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ConstitutiveObserverFibreChirality`,
  `GaloisForLFunctions.HTGeometry.KLFactorizationSufficiency`
- **Type:** FORMATION / OBSERVER / HIDDEN-HISTORY CONSERVATION THEOREM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [CLASSICAL CHAIN-RULE PARENT]
  [CHIRALITY CONSERVATION] [SERIAL CURRENT COMPOSITION] [SUFFICIENT-OBSERVER SELECTION]
  [FOUR-ORGAN FUSION] [FOURTH-ORGAN PREDICTION]
  [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [NOT RH]

## 1. Exact question

Positive-jump information chronology proves that an involution cannot exchange two distinct source
formations. A physical receiver is not the source space: it is an observer of it. Data processing can
erase chirality, so source selection does not automatically descend.

The missing mechanism is an exact conservation law for where the information arrow goes under an
observer. The primitive is not a new geometric object. It is the interaction of:

1. directed formation work;
2. observer marginalization;
3. conditional fibre laws;
4. finite-order reversal.

## 2. Finite observer chart

Let \(X,Y\) be nonempty finite sets, let \(q:X\to Y\) be surjective, and let \(P,R\) be strictly
positive probability laws on \(X\). Write

\[
 P_Y(y)=\sum_{q(x)=y}P(x),\qquad
 R_Y(y)=\sum_{q(x)=y}R(x),
\tag{OFCC.1}
\]

and define conditional fibre laws

\[
 P^y(x)=\frac{P(x)}{P_Y(y)},\qquad
 R^y(x)=\frac{R(x)}{R_Y(y)}
 \qquad(q(x)=y).
\tag{OFCC.2}
\]

For laws \(A,B\) on one finite space put

\[
 \chi(A,B)=D(A\Vert B)-D(B\Vert A).
\tag{OFCC.3}
\]

Define the conditional-fibre chirality

\[
 \mathfrak F_q(P,R)=
 \sum_{y\in Y}
 \left[
 P_Y(y)D(P^y\Vert R^y)
 -R_Y(y)D(R^y\Vert P^y)
 \right].
\tag{OFCC.4}
\]

### Theorem 2.1 -- exact observer-fibre conservation

\[
 \boxed{
 \chi(P,R)=\chi(P_Y,R_Y)+\mathfrak F_q(P,R).}
\tag{OFCC.5}
\]

Thus observation does not destroy the directed information arrow without residue. It transfers the
unobserved part to a signed conditional-fibre term.

#### Proof

For \(q(x)=y\),

\[
 \log\frac{P(x)}{R(x)}
 =
 \log\frac{P_Y(y)}{R_Y(y)}
 +
 \log\frac{P^y(x)}{R^y(x)}.
\]

Multiply by \(P(x)\), sum first over each fibre and then over \(Y\). This gives the relative-entropy
chain rule

\[
 D(P\Vert R)
 =
 D(P_Y\Vert R_Y)
 +\sum_yP_Y(y)D(P^y\Vert R^y).
\]

Interchanging \(P,R\) gives the reverse chain rule. Subtracting them proves (OFCC.5). QED.

### Theorem 2.2 -- serial observer-current composition

Let \(r:Y\to Z\) be another surjective finite observer. Write \(P_Z=(r\circ q)_*P\),
\(R_Z=(r\circ q)_*R\). Then

\[
 \boxed{
 \mathfrak F_{r\circ q}(P,R)
 =\mathfrak F_q(P,R)+\mathfrak F_r(P_Y,R_Y).}
\tag{OFCC.5a}
\]

More generally, for a chain

\[
 X_0\xrightarrow{q_1}X_1\xrightarrow{q_2}\cdots
 \xrightarrow{q_n}X_n
\]

and successive marginals \(P_i,R_i\),

\[
 \boxed{
 \chi(P_0,R_0)=\chi(P_n,R_n)
 +\sum_{i=1}^n\mathfrak F_{q_i}(P_{i-1},R_{i-1}).}
\tag{OFCC.5b}
\]

Thus conditional-fibre chirality is a signed observer current: it composes additively and locates
the exact stage at which information orientation leaves the visible state. Unlike total-variation
loss, individual stage currents need not be nonnegative.

#### Proof

Apply Theorem 2.1 to \(q\), to \(r\) on the marginal pair, and to \(r\circ q\):

\[
\begin{aligned}
 \chi(P,R)
 &=\chi(P_Y,R_Y)+\mathfrak F_q(P,R)\\
 &=\chi(P_Z,R_Z)+\mathfrak F_r(P_Y,R_Y)+\mathfrak F_q(P,R),\\
 \chi(P,R)&=\chi(P_Z,R_Z)+\mathfrak F_{r\circ q}(P,R).
\end{aligned}
\]

Subtracting the common terminal term proves (OFCC.5a). Induction proves (OFCC.5b). QED.

## 3. Reversal pushes chronology into hidden history

### Theorem 3.1 -- reversible observation orients the fibre

Let \(\vartheta:Y\to Y\) be an involution satisfying

\[
 \vartheta_*P_Y=R_Y.
\tag{OFCC.6}
\]

Then

\[
 \boxed{\chi(P_Y,R_Y)=0,\qquad
 \mathfrak F_q(P,R)=\chi(P,R).}
\tag{OFCC.7}
\]

In particular, if \(\chi(P,R)>0\), every reversible observer has strictly positive conditional-fibre
chirality.

#### Proof

Involutivity gives \(\vartheta_*R_Y=P_Y\). Relative entropy is invariant under a bijection, hence

\[
 D(P_Y\Vert R_Y)
 =D(\vartheta_*P_Y\Vert\vartheta_*R_Y)
 =D(R_Y\Vert P_Y).
\]

The first equality in (OFCC.7) follows. Substitute it into (OFCC.5) for the second. QED.

This is the exact hidden-history law: a reversible projected history can coexist with an irreversible
source only because the entire information arrow survives in observer fibres.

### Corollary 3.2 -- localization of irreversibility in an observer tower

In the chain of Theorem 2.2, suppose an involution exchanges \(P_n,R_n\). Then

\[
 \boxed{
 \chi(P_0,R_0)=
 \sum_{i=1}^n\mathfrak F_{q_i}(P_{i-1},R_{i-1}).}
\tag{OFCC.7a}
\]

If \(\chi(P_0,R_0)>0\), at least one stage has strictly positive fibre chirality. For a chain of
length \(n\), at least one stage satisfies

\[
 \mathfrak F_{q_i}(P_{i-1},R_{i-1})\ge \frac{\chi(P_0,R_0)}n.
\tag{OFCC.7b}
\]

This is a falsifiable fourth-organ prediction: any multi-stage construction ending in an exact
reversal must expose a quantitatively oriented hidden stage unless the source formation is neutral.

#### Proof

The terminal chirality vanishes by Theorem 3.1. Substitute into (OFCC.5b). If every summand were
strictly smaller than the average in (OFCC.7b), their sum would be smaller than
\(\chi(P_0,R_0)\). QED.

## 4. Sufficiency closes selection

Call \(q\) **pair-sufficient** for \(P,R\) if

\[
 P^y=R^y\qquad(y\in Y).
\tag{OFCC.8}
\]

Equivalently, the likelihood ratio \(P(x)/R(x)\) is constant on every fibre of \(q\).

### Theorem 4.1 -- sufficient reversible observation selects zero chronology

If \(q\) is pair-sufficient and an involution exchanges \(P_Y,R_Y\), then

\[
 \boxed{\chi(P,R)=0.}
\tag{OFCC.9}
\]

For any strictly chronologically ordered family \(\{P_t\}_{t\in I}\), meaning

\[
 s<t\Longleftrightarrow\chi(P_s,P_t)>0,
\tag{OFCC.10}
\]

a pair-sufficient observer whose two endpoint laws are exchanged by an involution forces \(s=t\).
For centered endpoints \(s=c-a,t=c+a\) with \(a\ge0\), it forces \(a=0\).

#### Proof

Pair sufficiency makes every conditional divergence in (OFCC.4) zero, hence
\(\mathfrak F_q(P,R)=0\). Theorem 3.1 then gives \(\chi(P,R)=0\). Apply (OFCC.10). QED.

## 5. Source realization and comparison reduction

For an Esscher family

\[
 dP_t=Z(t)^{-1}e^{-tQ}\,d\mu,
\]

the likelihood ratio of two endpoints is

\[
 \frac{dP_s}{dP_t}
 =\frac{Z(t)}{Z(s)}e^{(t-s)Q}.
\tag{OFCC.11}
\]

It factors through the scalar statistic \(Q\). Therefore \(Q\) is pair-sufficient for every admitted
pair. The forward and reverse KL divergences of the full law equal those of its \(Q\)-pushforward.

This conclusion does not depend on finiteness of the source space. In general, if
\(dP/dR=g\circ q\), then for every measurable \(B\) in the observer space,

\[
 q_*P(B)=\int_{q^{-1}B}g(q(x))\,dR(x)
 =\int_B g(y)\,d(q_*R)(y).
\]

Hence \(d(q_*P)/d(q_*R)=g\), and integrating its logarithm gives
\(D(P\Vert R)=D(q_*P\Vert q_*R)\). Mutual absolute continuity applies the same argument to
\(dR/dP=1/(g\circ q)\), proving equality in the reverse direction as well.

In the abelian-zeta source,

\[
 Q(A)=\log|\operatorname{soc}A|.
\tag{OFCC.12}
\]

The positive-jump chronology theorem in the parent card proves

\[
 s<t\Longleftrightarrow
 D(P_s\Vert P_t)>D(P_t\Vert P_s).
\tag{OFCC.13}
\]

Consequently a measurable involution exchanging the two scalar socle-log laws already forces
\(s=t\). A comparison need not reconstruct every finite abelian group, every Euler coefficient, or
the complete class law. It is enough to transport the sufficient scalar formation statistic and its
two endpoint laws.

This is new leverage relative to the previous RH gate: **full coefficient faithfulness is stronger
than necessary for reversal selection**.

## 6. Four-organ fusion and prediction

| organ | law | role |
|---|---|---|
| formation | positive-jump KL chronology | supplies ordered source arrow |
| observer descent | relative-entropy chain rule | conserves arrow across projection |
| hidden history | conditional-fibre chirality | stores exactly what projection erases |
| reversal | involutive KL symmetry | kills observed arrow |
| sufficiency | fibre-law equality | forbids hidden storage and selects neutrality |

The serial identity also fuses two already certified universal mechanisms without identifying
their values:

| observer law | conserved balance | polarity |
|---|---|---|
| positive overlap defect | source total variation = observed total variation + stage losses | nonnegative |
| competitive path history | relative-law variation = visible variation + collapsed-fibre work | nonnegative |
| formation chirality | source directed KL difference = observed difference + fibre currents | signed |

The common law is **observer loss becomes a composable vertical current**. Positivity, path
variation, and likelihood orientation are different coefficient systems for that law; no scalar
identification between them is asserted.

The prediction for every proposed reflected completion is exact:

- if its reflected endpoint laws are involutively exchanged and the displacement is nonzero, then
  its source comparison cannot be pair-sufficient;
- quantitatively, its conditional fibres must carry exactly the positive source chirality;
- if an independent theorem proves pair sufficiency, reflection forces zero displacement.

Thus a reversible route endpoint at nonzero displacement is not merely “lossy.” It has a typed,
quantitative hidden-history obligation.

## 7. Parent mathematics and significance boundary

The relative-entropy chain rule and sufficient statistics are classical; see Cover--Thomas,
*Elements of Information Theory*, Chapter 2. Fritz, *A synthetic approach to Markov kernels,
conditional independence and theorems on sufficient statistics* (arXiv:1908.07021), gives a
coordinate-free categorical parent for conditioning and sufficiency.

Accordingly, Theorems 2.1--4.1 are a [BRIDGE], not a claim of new abstract information theory.
The mathematical delta is the exact fusion with source-derived positive-jump chronology and the
resulting reduction of the comparison gate from full-source faithfulness to one sufficient statistic.

## 8. Hostile loops

1. **Every observer preserves chronology. -- False.** A constant observer has zero observed
   chirality for every pair. Survivor: the missing arrow is exactly \(\mathfrak F_q\).
2. **Data processing orders the two directional losses. -- False.** Both KL divergences decrease,
   but their decreases need not be ordered. Survivor: retain their signed conditional difference,
   not one unsigned contraction bound.
3. **Target involutivity selects the source. -- False.** It only makes observed chirality zero.
   Survivor: selection follows exactly under pair sufficiency.
4. **Full coefficient reconstruction is necessary. -- False.** An Esscher likelihood ratio factors
   through \(Q\), so the scalar sufficient statistic preserves both directed costs.
5. **Fibre chirality is curvature. -- Unsupported.** The theorem constructs a conditional
   information balance, no connection or two-dimensional holonomy.
6. **Pair sufficiency is automatic from a named physical observable. -- False.** It must be proved
   by likelihood-ratio factorization or an equality case of data processing before specialization.
7. **Every stage current is nonnegative. -- False.** The signed conditional losses can have either
   sign even though their terminal sum is fixed. Survivor: (OFCC.5b) is the exact invariant, and a
   positive total forces at least one quantitatively positive stage by Corollary 3.2.

## 9. RH-facing gate

For centered physical displacement \(a(\rho)=|2\Re\rho-1|\), reversal selection now needs only:

1. a pre-zero map to the scalar socle-log formation statistic;
2. an involution exchanging the two centered scalar endpoint laws;
3. pair sufficiency, equivalently preservation of both directed KL divergences.

Those premises imply \(a(\rho)=0\) by Theorem 4.1 and the parent chronology theorem. None is asserted
here.

## 10. Gates

- [x] Internal and external parent audit.
- [x] Counterexamples to arbitrary-observer and arbitrary-reversal claims.
- [x] Dependency-closed finite conservation and sufficiency proofs.
- [x] Exact source sufficient-statistic realization.
- [x] Exact serial composition and observer-tower localization theorem.
- [x] Lean formalization of conservation, serial composition, conditional-KL identification,
  sufficient reversal, and abstract chronology selection.
- [x] Lean formalization of the §5 sufficient-statistic reduction: factored likelihood ratios are
  KL pair-sufficient (`isKLPairSufficient_of_density_comp`), with the exponential/Esscher family as
  the certified instance (`esscherLaw_eq_withDensity_comp`, `esscher_isKLPairSufficient`).
- [ ] Lean construction of the Abelian-zeta source as the abstract strict chronology interface
  (construction target, not a proved statement of this card).
