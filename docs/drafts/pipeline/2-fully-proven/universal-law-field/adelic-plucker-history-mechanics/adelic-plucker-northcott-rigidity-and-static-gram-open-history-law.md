# Adelic Plücker--Northcott rigidity and static-Gram/open-history law

- **ID:** ULF-APHM-2
- **Stage:** 2-fully-proven
- **Type:** CROSS-ORGAN FUSION / RECONSTRUCTION / ADELIC CONSERVATION / FOURTH-ORGAN PREDICTION
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [NUMBER-FIELD SOURCE]
  [MATROID EXCHANGE] [NORTHCOTT RIGIDITY] [STATIC POSITIVE OBSERVER]
  [LINEARLY OPEN ARITHMETIC HISTORY] [NOT RH]

## 1. Setup

Let `K` be a number field with normalized places `v` and local weights `n_v`, so the product
formula is

\[
 \sum_v n_v\log|x|_v=0\qquad(x\in K^\times).
 \tag{APN.1}
\]

Let `T in K^(r × n)` have rank `r`, with `1 <= r <= n`.  Write `E={1,...,n}` and

\[
 \mathcal B=\{B\subset E:|B|=r,\ p_B:=\det T_B\ne0\}.
 \tag{APN.2}
\]

This is the basis set of the represented column matroid.  Let `u_i in K^×` and define

\[
 T_m=T\operatorname{diag}(u_1^m,\ldots,u_n^m),
 \qquad u_B=\prod_{i\in B}u_i,
 \qquad p_B(m)=p_Bu_B^m.
 \tag{APN.3}
\]

Let `P_m=[p_B(m)]_(B in mathcal B)` be the projective Plücker packet and `h(P_m)` its absolute
logarithmic projective height.

Fix an active label `b` and define the complete relative response height

\[
 \mathcal H_b(m)=\sum_{i\in E_{\mathrm{act}}}
 h\!\left(\left(\frac{u_i}{u_b}\right)^m\right),
 \tag{APN.3a}
\]

where `E_act` is the set of nonloop labels.  This is projectively invariant under common scaling
of all intervention characters.  It is also coefficient-free: the initial minors choose the
active relation chart, while `mathcal H_b` measures only its generated diagonal history.

Two bases are adjacent when `B'=B-{i}+{j}` for `i in B`, `j notin B`.  The basis graph is
connected: if `B != C`, basis exchange supplies `j in C\B` and `i in B\C` with
`B-i+j` a basis, reducing `|B\C|`; induction reaches `C`.

## 2. Exchange response and adelic conservation

### Theorem 2.1 — exact response and relative reconstruction

For every adjacent exchange `B'=B-i+j`,

\[
 \boxed{
 \mathcal R_{B,i,j}(m)
 :=\frac{p_{B'}(m)p_B(0)}{p_B(m)p_{B'}(0)}
 =\left(\frac{u_j}{u_i}\right)^m.}
 \tag{APN.4}
\]

Consequently the `m=1` exchange responses reconstruct every ratio `u_j/u_i` on an edge of the
**element-exchange graph**.  Products along paths reconstruct all ratios inside each connected
component of that graph, independently of path because they come from the already existing vertex
labels `u_i`.  This reconstruction graph is distinct from the basis graph used below.

#### Proof

Since `u_(B-i+j)=u_B u_j/u_i`,

\[
 \frac{p_{B'}u_{B'}^m\,p_B}{p_Bu_B^m\,p_{B'}}
 =\left(\frac{u_{B'}}{u_B}\right)^m
 =\left(\frac{u_j}{u_i}\right)^m.
\]

The reconstruction statement is multiplication of these edge ratios. ∎

### Theorem 2.2 — all-place conservation

Every exchange response satisfies

\[
 \boxed{\sum_v n_v\log|\mathcal R_{B,i,j}(m)|_v=0.}
 \tag{APN.5}
\]

#### Proof

Equation `(APN.4)` lies in `K^×`; apply `(APN.1)`. ∎

This is the conservation law joining the relation organ (basis exchange), the intervention organ
(relative diagonal character), and the arithmetic organ (all places).  No positive norm or
completion is used.

## 3. Northcott classification

### Theorem 3.0 — exact complete-height law

For every `m>=0`,

\[
 \boxed{\mathcal H_b(m)=m\mathcal H_b(1).}
 \tag{APN.5a}
\]

Moreover, the following are equivalent:

1. `mathcal H_b(1)=0`;
2. `mathcal H_b(m)` is bounded for `m>=0`;
3. every relative character `u_i/u_b` is a root of unity;
4. the normalized relative packet `((u_i/u_b)^m)_i` is periodic from time zero.

#### Proof

Height homogeneity gives `h(x^m)=m h(x)` termwise, proving `(APN.5a)`.  Every summand is
nonnegative, and Kronecker's height-zero theorem says it vanishes exactly on roots of unity.  A
finite family of torsion characters has a common exponent, giving periodicity.  Conversely any
positive period kills every relative character.  Finally, exact linear growth makes boundedness
equivalent to zero initial height. ∎

### Theorem 3.1 — bounded history, finite history, and torsion exchange are equivalent

The following are equivalent:

1. `sup_m h(P_m) < infinity`;
2. the projective orbit `{P_m:m>=0}` is finite;
3. every adjacent exchange ratio `u_j/u_i` is a root of unity.

When they hold, the projective orbit is periodic from time zero.

#### Proof

`(2) => (1)` is immediate.  For `(1) => (2)`, every `P_m` is a `K`-rational point of the fixed
projective space `P^(|B|-1)`.  Northcott finiteness says a bounded-height subset of that fixed
number-field locus is finite.

For `(2) => (3)`, choose `a<b` with `P_a=P_b` and set `d=b-a>0`.  Projective equality supplies
`c in K^×` such that `p_Bu_B^b=c p_Bu_B^a` for every basis.  Since `p_B != 0`,
`u_B^d=c`.  For adjacent `B'=B-i+j`, division gives

\[
 \left(\frac{u_j}{u_i}\right)^d=1.
\]

For `(3) => (2)`, finitely many exchange edges admit one common positive exponent `d` killing all
their ratios.  Hence `u_B^d=u_(B')^d` on adjacent bases.  Connectivity of the basis graph gives one
`c in K^×` with `u_B^d=c` for all bases.  Therefore

\[
 p_B(m+d)=p_Bu_B^{m+d}=c\,p_Bu_B^m
\]

for every `B`, so `P_(m+d)=P_m`. ∎

### Theorem 3.2 — quantitative height escape

For an adjacent exchange `B'=B-i+j`, put

\[
 \alpha=p_{B'}/p_B,
 \qquad \beta=u_j/u_i.
\]

Then for every `m>=0`,

\[
 \boxed{h(P_m)\ge m h(\beta)-h(\alpha).}
 \tag{APN.6}
\]

If `beta` is not a root of unity, then `h(beta)>0` by Kronecker's height-zero theorem, and the
projective history escapes at least linearly.

The complete relative height gives the coefficient-free stronger estimate

\[
 \mathcal H_b(m)\ge m h(u_j/u_i)
 \tag{APN.6a}
\]

whenever that exchange ratio is reconstructed inside the active component.

#### Proof

The ratio of the `B'` and `B` coordinates of `P_m` is `alpha beta^m`.  Projective height dominates
the height of any coordinate ratio, so

\[
 h(P_m)\ge h(\alpha\beta^m).
\]

The standard height inequalities give

\[
 m h(\beta)=h(\beta^m)
 =h(\alpha^{-1}(\alpha\beta^m))
 \le h(\alpha)+h(\alpha\beta^m).
\]

Rearrangement proves `(APN.6)`.  Kronecker gives the final assertion. ∎

## 4. Withheld fourth organ: positive Gram blindness

Fix an embedding `sigma:K -> C`, apply it entrywise to `T`, and assume

\[
 |\sigma(u_i)|=1\qquad(1\le i\le n).
 \tag{APN.7}
\]

### Theorem 4.1 — static Gram with linearly open arithmetic history

For every `m`,

\[
 \boxed{\sigma(T_m)\sigma(T_m)^*=\sigma(T)\sigma(T)^*.}
 \tag{APN.8}
\]

Thus every positive Gram determinant, singular value, Moore--Penrose filling energy, and capacity
derived from this matrix is constant.  If one adjacent ratio `u_j/u_i` is not a root of unity,
the lifted Plücker history is nevertheless infinite and satisfies the linear lower bound
`(APN.6)`.

#### Proof

Let `D_m=diag(sigma(u_i)^m)`.  Assumption `(APN.7)` gives `D_mD_m^*=I`.  Hence

\[
 \sigma(T_m)\sigma(T_m)^*
 =\sigma(T)D_mD_m^*\sigma(T)^*
 =\sigma(T)\sigma(T)^*.
\]

The remaining claims follow from Theorem 3.2. ∎

This theorem was not used to prove the Northcott classification.  It is the predicted fourth-organ
law: exact recurrence—indeed stationarity—of the positive observer can coexist with proper escape
of the arithmetic source lift.

## 5. Explicit sharp witness

Take `K=Q(i)`,

\[
 z=\frac{3+4i}{5},\qquad
 T=\begin{pmatrix}1&0&1\\0&1&1\end{pmatrix},
 \qquad u=(1,z,1).
 \tag{APN.9}
\]

All three maximal minors are nonzero, so the basis matroid is the connected uniform matroid
`U_(2,3)`.  Under the standard complex embedding, `|z|=1`; therefore every Gram observer is
constant.  But `z` is not a root of unity: the only roots of unity in `Q(i)` are
`{±1,±i}`, and `z` is none of them.  The Plücker packets are

\[
 P_m=[z^m:1:-z^m],
 \tag{APN.10}
\]

so their heights diverge at least linearly.

This witnesses every load-bearing boundary: fixed number field, connected relation support,
unit-modulus positive observer, non-torsion arithmetic lift, and open height history.

## 6. Sharp countermodels and scope

1. **Disconnected/unused labels.**  An element on no basis is invisible.  Reconstruction concerns
   exchange-connected active labels only.
2. **Unbounded degree.**  Roots of unity of growing degree have zero height and infinite union.
   Fixed `K` is load-bearing for Northcott finiteness.
3. **One-place blindness.**  Unit modulus at one embedding does not mean height zero; other
   embeddings and finite places retain the history.
4. **No HT inference.**  The witness is an exponential orbit satisfying a first-order recurrence.
   Height escape does not imply hypertranscendence.
5. **No RH inference.**  No Xi zero has been placed in the fixed-number-field Plücker family.
6. **Classical ingredients.**  Matroid basis exchange, torus actions on Grassmannians, product
   formula, Weil height, Northcott, and Cauchy--Binet/Gram invariance are classical.  The theorem's
   field use is their forced source-history fusion.

## 7. Consequence for universal-law-field design

A positive Archimedean realization is not a faithful law-history completion even when it preserves
every singular value.  A faithful cofinal theory must carry at least one of:

- the complete adelic Plücker packet;
- a source-natural equivalent of its projective height;
- an explicit degree/height escape flag.

This supplies a precise noncompactness mechanism independent of hypertranscendence and prevents the
field from identifying positivity with complete phase/history quotient.

## 8. Literature and corpus boundary

Classical parents include torus orbits in Grassmannians and their matroid polytopes, matroids over
valuation rings, Weil heights, and Northcott finiteness.  The corpus parent
`valuated-plucker-gram-capacity-exchange-law.md` proves local valuated exchange, the Gram square
law, filling capacity, and phase erasure.  The present theorem adds exact exchange-character
reconstruction, all-place conservation, Northcott classification, quantitative height escape, and
the static-Gram/open-height prediction.

## 9. Lean plan

Formalize only after hostile paper audit.  Required surface:

1. finite basis support and adjacent exchange response;
2. finite-orbit iff torsion-edge classification using connected basis graph;
3. fixed-number-field height/finite-orbit implication;
4. concrete `Q(i)` static-Gram/open-orbit witness;
5. umbrella import and axiom audit.

No RH declaration belongs in this module.
