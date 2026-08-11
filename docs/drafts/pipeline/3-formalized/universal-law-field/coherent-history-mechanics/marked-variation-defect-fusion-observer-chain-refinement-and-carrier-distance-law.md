# Marked-variation defect fusion, observer chain, refinement, and carrier-distance law

- **ID:** ULF-MVD-1
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [FINITE POSITIVE-KERNEL CHART]
  [GENERATION-OBSERVATION INTERCHANGE] [THREE-ORGAN FUSION]
  [FOURTH-ORGAN PREDICTION]
  [LEAN-CERTIFIED] [NOT RH]

## 1. Positive kernels and marked packets

Let `X,Y` be finite sets.  A **positive kernel** from `X` to `Y` is a family

\[
 T=(T_{yx})_{y\in Y,x\in X},\qquad T_{yx}\in\mathbb R_{\ge0},
\]

acting on complex functions by

\[
 (Tf)(y)=\sum_{x\in X}T_{yx}f(x).
 \tag{MV.1}
\]

Let `I` be finite and let `a=(a_i)_(i in I)` be a packet of complex functions on `X`.  Define

\[
 C_T(a)=T\left(\sum_i a_i\right),\qquad
 E_T(a)=T\left(\sum_i|a_i|\right),
 \tag{MV.2}
\]

and the **marked-variation defect**

\[
 \boxed{\mathfrak D_T(a)=E_T(a)-|C_T(a)|.}
 \tag{MV.3}
\]

All absolute values and inequalities below are coordinatewise.

### Lemma 1.1 — positive-kernel modulus inequality

For every complex `f`,

\[
 |Tf|\le T|f|.
 \tag{MV.4}
\]

### Proof

At `y`, the triangle inequality gives

\[
 \left|\sum_xT_{yx}f(x)\right|
 \le\sum_xT_{yx}|f(x)|,
\]

because every coefficient is nonnegative.  This is `(MV.4)`.  QED.

### Theorem 1.2 — positivity and reconstruction

For every marked packet,

\[
 \boxed{\mathfrak D_T(a)\ge0,\qquad
 E_T(a)=|C_T(a)|+\mathfrak D_T(a).}
 \tag{MV.5}
\]

### Proof

By the triangle inequality and Lemma 1.1,

\[
 |C_T(a)|
 =\left|T\sum_i a_i\right|
 \le T\left|\sum_i a_i\right|
 \le T\sum_i|a_i|
 =E_T(a).
\]

The equality in `(MV.5)` is the definition rearranged.  QED.

Thus coherent output and defect jointly reconstruct the pushed positive envelope.  They do not
reconstruct individual source histories.

## 2. Generation fusion law

For complex functions `u,v` on one finite set, put

\[
 \mathfrak I(u,v)=|u|+|v|-|u+v|\ge0.
 \tag{MV.6}
\]

Let `a` and `b` be two disjoint marked packets on `X`; write `a sqcup b` for their union.

### Theorem 2.1 — exact marked fusion

\[
 \boxed{
 \mathfrak D_T(a\sqcup b)
 =\mathfrak D_T(a)+\mathfrak D_T(b)
  +\mathfrak I(C_T(a),C_T(b)).}
 \tag{MV.7}
\]

Every term on the right is nonnegative.

### Proof

Envelope and coherent execution are additive before the final modulus:

\[
 E_T(a\sqcup b)=E_T(a)+E_T(b),\qquad
 C_T(a\sqcup b)=C_T(a)+C_T(b).
\]

Therefore the right side of `(MV.7)` is

\[
 E_T(a)-|C_T(a)|+E_T(b)-|C_T(b)|
 +|C_T(a)|+|C_T(b)|-|C_T(a)+C_T(b)|,
\]

which is exactly `E_T(a sqcup b)-|C_T(a sqcup b)|`.  Nonnegativity follows from Theorem 1.2 and
the triangle inequality.  QED.

Equation `(MV.7)` separates within-packet cancellation from between-packet interference.  It is
not a scalar analogy: it is an equality of positive functions at every observer output.

## 3. Observer chain law

Let `S` be a positive kernel from `Y` to a finite set `Z`.  For a single complex function `u` on
`Y`, define

\[
 \delta_S(u)=S|u|-|Su|\ge0.
 \tag{MV.8}
\]

### Theorem 3.1 — exact observer chain rule

For every packet `a`,

\[
 \boxed{
 \mathfrak D_{ST}(a)
 =S\mathfrak D_T(a)+\delta_S(C_T(a)).}
 \tag{MV.9}
\]

### Proof

Using positivity and linearity,

\[
\begin{aligned}
 S\mathfrak D_T(a)+\delta_S(C_T(a))
 &=S(E_T(a)-|C_T(a)|)+S|C_T(a)|-|SC_T(a)|\\
 &=SE_T(a)-|SC_T(a)|\\
 &=E_{ST}(a)-|C_{ST}(a)|\\
 &=\mathfrak D_{ST}(a).
\end{aligned}
\]

QED.

No later positive observer can cancel an earlier defect against a negative term: it transports the
defect positively and adds a new nonnegative loss.  A non-order-faithful observer may still erase a
positive defect by sending it to zero; that is an observer-kernel loss, not cancellation or
recovery.

### Theorem 3.2 — rowwise phase classification of zero observer loss

For a fixed `z in Z`,

\[
 \delta_S(u)(z)=0
 \tag{MV.9a}
\]

if and only if all nonzero complex numbers

\[
 \{u(y):S_{zy}>0\}
\]

have one common phase.  Consequently `delta_S(u)=0` exactly when this phase-alignment condition
holds on every observer row.

### Proof

At `z`, equality means

\[
 \left|\sum_y S_{zy}u(y)\right|=\sum_y S_{zy}|u(y)|.
\]

Apply the finite equality case of the complex triangle inequality to the terms
`S_(zy)u(y)`.  Multiplication by a positive real scalar preserves phase, and zero-weight terms do
not contribute.  Hence equality holds exactly under the stated common-phase condition.  QED.

Thus zero loss is not merely a scalar plateau: it reconstructs the phase foliation seen by each
positive observer row.

## 4. Refinement law and phase-alignment rigidity

Let `J` be finite, let `r:J->I`, and let `b=(b_j)_(j in J)` refine `a` in the sense that

\[
 a_i=\sum_{j:r(j)=i}b_j
 \qquad(i\in I).
 \tag{MV.10}
\]

Put

\[
 H_r(b)=\sum_{i\in I}
 \left(\sum_{j:r(j)=i}|b_j|-|a_i|\right)\ge0.
 \tag{MV.11}
\]

### Theorem 4.1 — exact refinement increment

\[
 \boxed{
 \mathfrak D_T(b)-\mathfrak D_T(a)=T H_r(b)\ge0.}
 \tag{MV.12}
\]

### Proof

Equation `(MV.10)` makes the total coherent sums of the two packets equal.  Hence their final
modulus terms cancel on subtraction.  Their envelope difference is

\[
 T\left(\sum_j|b_j|-\sum_i|a_i|\right)=TH_r(b).
\]

Every summand of `(MV.11)` is nonnegative by the triangle inequality, and `T` is positive.  QED.

### Theorem 4.2 — generation-observation interchange square

Let `S:Y->Z` be another positive kernel.  For every refinement `(MV.10)`,

\[
 \boxed{
 \mathfrak D_{ST}(b)
 =S\mathfrak D_T(a)+STH_r(b)+\delta_S(C_T(a)).}
 \tag{MV.12a}
\]

Equivalently, refining before the observer chain or after the first observer produces the same
transported refinement increment:

\[
 \boxed{
 \mathfrak D_{ST}(b)-\mathfrak D_{ST}(a)
 =S\bigl(\mathfrak D_T(b)-\mathfrak D_T(a)\bigr)
 =STH_r(b).}
 \tag{MV.12b}
\]

### Proof

The coherent sums of `a` and `b` agree, so `C_T(a)=C_T(b)`.  Apply the observer chain rule to
`b`, then use `(MV.12)`:

\[
\begin{aligned}
 \mathfrak D_{ST}(b)
 &=S\mathfrak D_T(b)+\delta_S(C_T(b))\\
 &=S\bigl(\mathfrak D_T(a)+TH_r(b)\bigr)+\delta_S(C_T(a)).
\end{aligned}
\]

This is `(MV.12a)`.  Subtract the observer-chain identity for `a` to obtain `(MV.12b)`.  QED.

Equation `(MV.12a)` is the first genuine fusion law of the field chart.  It separates one observed
defect into three typed nonnegative mechanisms: inherited source variation, newborn variation, and
observer-created phase loss.  None of the three can be inferred from their sum alone.

Call `T` **order-faithful** when `Tf=0` for `f>=0` implies `f=0`.

### Corollary 4.3 — plateau rigidity

If `T` is order-faithful, then refinement leaves the defect unchanged exactly when, for every
`i` and every coordinate `x`, the nonzero numbers

\[
 \{b_j(x):r(j)=i\}
\]

have one common phase.

### Proof

By `(MV.12)` and order faithfulness, equality of defects is equivalent to `H_r(b)=0`.  Since every
summand in `(MV.11)` is nonnegative, this holds exactly when

\[
 \left|\sum_{j:r(j)=i}b_j(x)\right|
 =\sum_{j:r(j)=i}|b_j(x)|
\]

for every `(i,x)`.

For completeness, let `z_j` be one such finite family.  If their sum is zero, equality forces every
`z_j=0`.  Otherwise put `u=(sum z_j)/|sum z_j|`.  Then

\[
 0=\sum_j|z_j|-\left|\sum_jz_j\right|
  =\sum_j\bigl(|z_j|-\operatorname{Re}(\overline u z_j)\bigr).
\]

Each summand is nonnegative, so each is zero.  Hence `conj(u) z_j` is a nonnegative real number for
every nonzero `z_j`; all nonzero terms have phase `u`.  The converse is immediate.  QED.

Thus a faithful observer can see a refinement plateau only when the newborn histories are
phase-aligned with the history they refine.

## 5. Serial conservation and recurrence rigidity

Let

\[
 X_0\xrightarrow{T_1}X_1\xrightarrow{T_2}\cdots
 \xrightarrow{T_n}X_n
 \tag{MV.13}
\]

be positive kernels.  Put `P_0=id`, `P_k=T_k...T_1`,

\[
 c_0=\sum_i a_i,\qquad c_k=T_kc_{k-1},
\]

and

\[
 d_0=\sum_i|a_i|-|c_0|,\qquad
 d_k=T_k|c_{k-1}|-|c_k|\quad(k\ge1).
 \tag{MV.14}
\]

All `d_k` are nonnegative.

### Theorem 5.1 — transported defect conservation

\[
 \boxed{
 \mathfrak D_{P_n}(a)
 =P_nd_0+
 \sum_{k=1}^{n}T_nT_{n-1}\cdots T_{k+1}d_k,}
 \tag{MV.15}
\]

where the empty tail after `d_n` is the identity.

### Proof

For one stage, insert and subtract `T_1|c_0|`:

\[
 \mathfrak D_{T_1}(a)
 =T_1\left(\sum_i|a_i|-|c_0|\right)
  +T_1|c_0|-|c_1|
 =T_1d_0+d_1.
\]

Assume `(MV.15)` through stage `n`.  Applying Theorem 3.1 with `S=T_(n+1)` gives

\[
 \mathfrak D_{P_{n+1}}(a)
 =T_{n+1}\mathfrak D_{P_n}(a)+d_{n+1}.
\]

Substitute the inductive expansion and distribute `T_(n+1)`.  This is `(MV.15)` at `n+1`.
QED.

A positive kernel is **mass-preserving** when its columns sum to one.  Write

\[
 \|f\|_1=\sum_x|f(x)|,
 \qquad M(a)=\sum_i\|a_i\|_1.
\]

### Corollary 5.2 — scalar defect budget

If every `T_k` is mass-preserving, then

\[
 \boxed{
 M(a)-\|c_n\|_1
 =\bigl(M(a)-\|c_0\|_1\bigr)
  +\sum_{k=1}^{n}
   \bigl(\|c_{k-1}\|_1-\|c_k\|_1\bigr).}
 \tag{MV.16}
\]

Every summand is nonnegative.

### Proof

Mass preservation on nonnegative functions gives

\[
 \sum d_0=M(a)-\|c_0\|_1,
 \qquad
 \sum d_k=\|c_{k-1}\|_1-\|c_k\|_1.
\]

It also preserves the mass of every transported nonnegative `d_k`.  Taking total mass in
`(MV.15)` proves `(MV.16)`.  QED.

### Corollary 5.2a — exact realizability selection budget

For one mass-preserving positive kernel `T:X->Y`,

\[
 \boxed{
 \sum_{y\in Y}\mathfrak D_T(a)(y)
 =M(a)-\|C_T(a)\|_1.}
 \tag{MV.16s}
\]

Consequently

\[
 \boxed{\|C_T(a)\|_1\le M(a).}
 \tag{MV.16t}
\]

If a proposed target coherent output has `ell^1` mass strictly larger than the marked source
variation mass, then no such mass-preserving positive marked-history realization exists.

### Proof

This is `(MV.16)` with one observer stage, or directly: mass preservation sends
`sum_i |a_i|` to the same total mass, and summing the definition of `mathfrak D_T` gives
`(MV.16s)`.  Nonnegativity of the defect gives `(MV.16t)`.  QED.

### Corollary 5.3 — finite budget for macroscopic loss events

Put

\[
 \ell_k=\|c_{k-1}\|_1-\|c_k\|_1\ge0.
\]

For every `epsilon>0` and every `n`,

\[
 \boxed{
 \varepsilon\,\#\{1\le k\le n:\ell_k\ge\varepsilon\}
 \le\sum_{k=1}^n\ell_k
 \le\|c_0\|_1.}
 \tag{MV.16a}
\]

Hence an infinite mass-preserving observer chain has only finitely many loss events of any fixed
positive size.

### Proof

Each selected index contributes at least `epsilon` to the nonnegative sum.  The telescoping part of
`(MV.16)` gives

\[
 \sum_{k=1}^n\ell_k=\|c_0\|_1-\|c_n\|_1\le\|c_0\|_1.
\]

QED.

### Theorem 5.4 — recurrent observer rigidity

Assume now that every `X_k` is the same finite set `X`, so the coherent states can be compared in
one `ell^1(X)`, and let the mass-preserving chain be infinite.  If a sequence
`n_j -> infinity` satisfies

\[
 \|c_{n_j}-c_0\|_1\longrightarrow0,
 \tag{MV.17}
\]

then every observer-loss increment vanishes:

\[
 \boxed{d_k=0\quad\text{for every }k\ge1.}
 \tag{MV.18}
\]

Initial marked interference `d_0` need not vanish.

### Proof

The modulus inequality makes `||c_k||_1` nonincreasing.  Norm convergence in `(MV.17)` implies
`||c_(n_j)||_1 -> ||c_0||_1`.  A nonincreasing sequence with a subsequence converging to its first
term is constant.  Hence

\[
 \|c_{k-1}\|_1-\|c_k\|_1=0
\]

for every `k`.  This difference is the total mass of the nonnegative function `d_k`, so `d_k=0`.
QED.

Closed recurrence in the variation topology therefore excludes newly accumulated observer loss.
The recurrent-shadow/open-history phenomenon of finite CHM must be powered by marked generation or
refinement, not by a chain of mass-preserving observations alone.

## 6. Genuine source histories versus observer splice histories

Let `X_0,X_1,X_2` and `B_0,B_1,B_2` be finite, with observers

\[
 q_i:X_i\longrightarrow B_i.
\]

Let `A:X_1 x X_0 -> C` and `B:X_2 x X_1 -> C` be amplitude kernels.  Define observed block sums

\[
 \overline A_{\beta\alpha}
 =\sum_{q_1(y)=\beta,\ q_0(x)=\alpha}A_{yx},
 \qquad
 \overline B_{\gamma\beta}
 =\sum_{q_2(z)=\gamma,\ q_1(y)=\beta}B_{zy}.
 \tag{MV.19}
\]

For fixed observed endpoints `(alpha,gamma)`, define

\[
 G_{\gamma\alpha}
 =\sum_{q_2(z)=\gamma,\ q_0(x)=\alpha}
   \sum_{y\in X_1}B_{zy}A_{yx},
 \tag{MV.20}
\]

and

\[
 S_{\gamma\alpha}
 =\sum_{\substack{q_2(z)=\gamma,\ q_0(x)=\alpha\\
                   q_1(y)=q_1(y'),\ y\ne y'}}
    B_{zy}A_{y'x}.
 \tag{MV.21}
\]

`G` sums genuine histories with one common hidden midpoint.  `S` sums splice histories formed by
joining two different hidden midpoints that have the same observation.

Define `G^+` and `S^+` by replacing every product in `(MV.20)`--`(MV.21)` with
`|B_(zy)| |A_(y'x)|`.

### Theorem 6.1 — source/splice execution conservation

\[
 \boxed{
  \overline B\,\overline A=G+S,
  \qquad
  \overline{|B|}\,\overline{|A|}=G^++S^+.}
 \tag{MV.22}
\]

Moreover, entrywise,

\[
 \boxed{
 G^++S^+-|G+S|
 =(G^+-|G|)+(S^+-|S|)
  +( |G|+|S|-|G+S|).}
 \tag{MV.23}
\]

All three terms on the right are nonnegative.

### Proof

Expand the product `bar(B) bar(A)`.  A term is indexed by

\[
 (z,y,y',x)
\]

with the required outer endpoint labels and `q_1(y)=q_1(y')`.  These terms partition disjointly
into `y=y'`, which is exactly `(MV.20)`, and `y ne y'`, which is `(MV.21)`.  This proves the first
identity in `(MV.22)`.  The same partition after taking absolute edge weights proves the second.

Equation `(MV.23)` follows by adding and subtracting `|G|+|S|`.  The first two terms are
nonnegative by the triangle inequality inside each history class; the third is the triangle
defect between the two coherent class sums.  QED.

Thus the total positive execution debt has three separately typed parts:

1. cancellation among genuine source histories;
2. cancellation among observer-manufactured splice histories;
3. interference between the genuine and splice sectors.

No scalar total defect determines these three components.

## 7. Fourth-organ theorem: exact source-carrier distance

Let a finite history set `H` be partitioned into nonempty genuine histories `H_g` and splice
histories `H_s`.  Give every history a weight `w_h>=0`, with total `V=sum_h w_h>0`.  Let

\[
 \pi(h)=w_h/V,
 \qquad r=\pi(H_s).
 \tag{MV.24}
\]

Use total variation distance

\[
 d_{TV}(\pi,\nu)=\frac12\sum_{h\in H}|\pi(h)-\nu(h)|.
\]

### Theorem 7.1 — nearest genuine carrier

\[
 \boxed{
 \inf_{\nu:\ \nu(H_g)=1}d_{TV}(\pi,\nu)=r.}
 \tag{MV.25}
\]

If `pi(H_g)>0`, the normalized restriction `pi(.|H_g)` attains the infimum.  If
`pi(H_g)=0`, every probability supported on `H_g` has distance one, which again equals `r`.

### Proof

For every `nu` supported on `H_g`, the variational characterization of total variation gives

\[
 d_{TV}(\pi,\nu)\ge|\pi(H_s)-\nu(H_s)|=r.
\]

If `r<1`, put `nu(h)=pi(h)/(1-r)` on `H_g` and zero on `H_s`.  The absolute difference has mass
`r` on `H_s` and total mass `r` on `H_g`; half their sum is `r`.  If `r=1`, disjoint support gives
distance one for every genuine-supported `nu`.  QED.

### Corollary 7.2 — cofinal source-faithfulness criterion

For any sequence of finite stagewise carriers `pi_n`, the distance from `pi_n` to the set of
genuine-history-supported carriers tends to zero exactly when its normalized splice mass tends to
zero.

This is an exact prediction in the positive-carrier organ.  Weak compactness, tightness, moment
determinacy, or positivity of the stagewise carrier cannot establish source faithfulness without
controlling splice density.

## 8. Mechanism fusion across the frontier classes

The theorem supplies one law package, not five renamed obstructions.

| organ | exact theorem coordinate |
|---|---|
| source generation / descent | newborn term `STH_r(b)` and splice sector `S` |
| oscillatory cancellation | inherited defect and `G^+-|G|` |
| adaptive orientation | rowwise phase law `(MV.9a)` and `|G|+|S|-|G+S|` |
| whole-space coercivity / recurrence | selection budget `(MV.16s)`, loss count `(MV.16a)`, rigidity `(MV.18)` |
| positive carrier | exact distance `(MV.25)` |

Literal route maps are not asserted here.  The table states what any proposed marked-history
realization must prove and what quantitative witness refutes it.

## 9. Hostile proof and significance audit

1. **Not universal linearization.**  Nonlinear, relational, adaptive, and higher-arity source laws
   need not possess a native positive-kernel chart.
2. **Not source reconstruction.**  `(C,D)` reconstructs only the pushed envelope.
3. **Not curvature.**  The observer law is an exact cocycle identity.
4. **Not automatic compactness.**  Finite kernels do not settle cofinal tightness or uniform
   integrability.
5. **Not phase selection.**  Defect is phase-blind after measuring the amount of cancellation; an
   oriented phase packet is independent data.
6. **Not RH.**  No arithmetic source process, Xi handoff, or contractive two-head envelope is
   constructed.

The component mathematics belongs to positive-operator theory, Markov/lumping theory, weighted
path semantics, and total-variation geometry.  This card evaluates only mathematical correctness,
explanatory compression, and predictive force; it makes no priority claim.

## 10. Positive survivor and next gate

Any proposed proof route that composes after observation must now pass two independent tests:

1. its stagewise path carrier has asymptotically zero splice density;
2. its genuine marked packet has a controlled variation defect.

Passing only positivity or compactness can no longer certify source fidelity.  Passing only
coherent cancellation can no longer certify positive admission.

The next field theorem must extend `(MV.15)` to a literal locally finite arithmetic history current
and identify whether its cofinal failure is lack of finite variation, loss of order faithfulness,
or nonvanishing splice density.  Until then, the universal arithmetic realization remains Stage 1.

## 11. Formalization boundary

Lean module
`GaloisForLFunctions.HTGeometry.MarkedVariationDynamics` certifies:

1. finite positive kernels, composition, and modulus inequality;
2. marked defect positivity/reconstruction;
3. packet fusion and observer chain identities;
4. conservative refinement increment and generation-observation interchange;
5. scalar serial conservation, macroscopic-loss bound, and exact-return rigidity;
6. scalar genuine/splice/interference conservation;
7. exact finite total-variation carrier distance by a universal lower bound and attaining witness;
8. unconditional fusion capstone with no route or RH premise.

Stage-3 record:
`docs/drafts/pipeline/3-formalized/universal-law-field/coherent-history-mechanics/marked-variation-defect-fusion-observer-chain-refinement-and-carrier-distance-law-formalized.md`.

The former paper-only backlog is now closed as well:

- rowwise common-phase equality classification: `weighted_norm_sum_eq_iff`,
  `norm_sum_eq_sum_norm_iff`, and `HTGeometry.positiveObserverLoss_eq_zero_iff`;
- parent-indexed refinement plateau classification: `ParentIndexedRefinement.excess_eq_zero_iff`;
- subsequential infinite-chain recurrence: `observerLoss_zero_of_subseq_return`;
- explicit matrix block-sum expansion: `observedBlock_mul_eq_genuine_add_splice` and
  `observedBlock_abs_mul_eq_genuine_add_splice`.
- 2026-08-11 -- plateau rigidity, subsequential recurrence rigidity, and the block-sum expansion certified; card promoted to stage 3.
