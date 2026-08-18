# Compact formation, semi-Fredholm transduction, joint recovery, and carrier--defect bifurcation

- **ID:** ULF-FLPM-3
- **Stage:** 2 — fully proven on paper
- **Type:** UNIVERSAL FORMATION / GLOBAL PROPERNESS / JOINT RECONSTRUCTION THEOREM
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM, NOT ROUTE]`
  `[COMPACT-COFINAL FUSION] [EXPLICIT JOINT RECOVERY] [CARRIER--DEFECT SPLIT]`
  `[FUNCTIONAL-EQUATION NEUTRALITY] [CORE LEAN-FORMALIZED] [NOT RH]`
- **Parents:**
  `source-response-laplacian-properness-pluecker-and-adaptive-escape-law.md`,
  `../primitive-formation-rigidity-mechanics/finite-type-prime-formation-faithful-compact-nonproper-and-infinite-boundary-interception-law.md`,
  `../packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md`

## 1. Mechanism found

The corpus had two apparently conflicting exact conclusions.

1. Faithful finite-type prime formation is compact and therefore not globally proper. Any
   unlocking boundary response must be noncompact and intercept every adaptive prime-null
   sequence.
2. Several RH-equivalent Calkin criteria ask a seam-weighted prime--archimedean response to become
   compact at the selected locus.

The conflict comes from asking one channel to do two incompatible jobs. A response that supplies
global formation properness cannot disappear at selection. The disappearing operator must be a
**defect channel carried by a separate structural transducer**.

The resulting law has three parts:

```text
compact local formation A
  + cofinal structural transducer R
  + selected relative defect delta R.
```

The structural channel `R` covers all but finitely many source directions. The compact channel
`A` reconstructs exactly those finitely many residual directions. The relative channel
`delta R` vanishes at the selected law without destroying the retained carrier `R`.

This is a mechanism, not a new receiver object.

## 2. Setup

Let `H,Y,Z` be real or complex Hilbert spaces, with `H` infinite-dimensional. Let

\[
 A:H\longrightarrow Y,
 \qquad
 R:H\longrightarrow Z
 \tag{CST.1}
\]

be bounded linear maps and assume `A` is compact. Define the fused formation map

\[
 T=(A,R):H\longrightarrow Y\oplus Z,
 \qquad
 Tx=(Ax,Rx).
 \tag{CST.2}
\]

Write

\[
 N=\ker R,
 \qquad
 m(T)=\inf_{\|x\|=1}\|Tx\|.
 \tag{CST.3}
\]

Call `R` an **admissible cofinal transducer** when `ran R` is closed and `N` is
finite-dimensional. This is the upper semi-Fredholm condition, stated without quotient language.

## 3. Global formation/properness theorem

### Theorem 3.1 — compact--cofinal fusion classification

The following are equivalent.

1. `T=(A,R)` is bounded below: there is `c>0` such that

   \[
   \|Ax\|^2+\|Rx\|^2\ge c^2\|x\|^2
   \qquad(x\in H).
   \tag{CST.4}
   \]

2. `R` is an admissible cofinal transducer and the finite residual restriction

   \[
   A|_N:N\longrightarrow Y
   \tag{CST.5}
   \]

   is injective.

Thus a compact formation channel can repair a cofinal response only on its finite-dimensional
kernel. It cannot repair an infinite uncovered sector or a nonclosed-range decay.

### Proof: necessity

Assume `(CST.4)`.

On `N=ker R`, `(CST.4)` becomes

\[
 \|Ax\|\ge c\|x\|.
 \tag{CST.6}
\]

Hence `A|_N` is injective. Since `A|_N` is compact and bounded below, the closed unit ball of `N`
is compact. Therefore `N` is finite-dimensional.

It remains to prove that `ran R` is closed. If not, the standard closed-range criterion gives unit
vectors

\[
 x_n\in N^\perp,
 \qquad
 \|Rx_n\|\longrightarrow0.
 \tag{CST.7}
\]

Compactness of `A` supplies a subsequence, still denoted `x_n`, for which `Ax_n` converges. For
large `n,m`, `(CST.4)` applied to `x_n-x_m` gives

\[
 c\|x_n-x_m\|
 \le
 \bigl(\|A(x_n-x_m)\|^2+\|R(x_n-x_m)\|^2\bigr)^{1/2}
 \longrightarrow0.
 \tag{CST.8}
\]

Thus `x_n` converges to some `x in N^perp` with `||x||=1` and `Rx=0`, a contradiction. Hence
`ran R` is closed.

### Proof: sufficiency

Assume `ran R` is closed, `N` is finite-dimensional, and `A|_N` is injective. If `T` were not
bounded below, there would be unit vectors `x_n` with

\[
 Ax_n\longrightarrow0,
 \qquad
 Rx_n\longrightarrow0.
 \tag{CST.9}
\]

Closed range gives a constant `b>0` such that

\[
 \|Rx\|\ge b\|x\|
 \qquad(x\in N^\perp).
 \tag{CST.10}
\]

Writing `x_n=u_n+v_n` with `u_n in N` and `v_n in N^perp`, `(CST.10)` gives `v_n->0`. Hence
`||u_n||->1`. Finite dimensionality supplies a subsequence `u_n->u in N` with `||u||=1`.
Equation `(CST.9)` then gives `Au=0`, contradicting injectivity of `A|_N`. Therefore `T` is bounded
below. QED.

## 4. Exact joint reconstruction

The proof contains a stronger constructive statement.

Let `Q_N:H->N` be the orthogonal projection. Since `R|_(N^perp)` is a bounded bijection onto the
closed space `ran R`, its inverse extends by zero on `(ran R)^perp` to a bounded map

\[
 S:Z\longrightarrow H,
 \qquad
 SR=1-Q_N.
 \tag{CST.11}
\]

Because `N` is finite-dimensional and `A|_N` is injective, its inverse on `A(N)` extends by zero on
`A(N)^perp` to a bounded map

\[
 J:Y\longrightarrow N,
 \qquad
 JA Q_N=Q_N.
 \tag{CST.12}
\]

Define

\[
 \boxed{
 \mathcal L(y,z)=Sz+J\bigl(y-ASz\bigr).}
 \tag{CST.13}
\]

### Theorem 4.1 — joint recovery identity

`mathcal L` is a bounded left inverse of `T`:

\[
 \boxed{\mathcal L(Ax,Rx)=x\qquad(x\in H).}
 \tag{CST.14}
\]

### Proof

Using `(CST.11)`,

\[
 SRx=x-Q_Nx.
 \]

Therefore

\[
 Ax-ASRx=AQ_Nx.
 \]

Equation `(CST.12)` now gives

\[
 \mathcal L(Ax,Rx)
 =x-Q_Nx+Q_Nx=x.
 \]

QED.

This is the first exact global fusion law in this mechanics: the cofinal channel recovers the
infinite complement, the compact channel recovers the finite residual kernel, and neither channel
alone need be faithful.

## 5. Quantitative essential obstruction

Assume `(CST.4)` with constant `c>0`. Let `K:H->Z` be any compact operator. Choose an orthonormal
sequence `e_n` in `H`. Both `Ae_n` and `Ke_n` tend to zero. Hence

\[
 c
 \le\liminf_n\|Re_n\|
 \le\|R-K\|.
 \tag{CST.15}
\]

Taking the infimum over compact `K` gives

\[
 \boxed{
 \operatorname{dist}(R,\mathcal K(H,Z))\ge c.}
 \tag{CST.16}
\]

Consequences:

1. `R` is noncompact with a quantitative essential margin;
2. a finite-rank or compact boundary response cannot unlock properness;
3. if `R=BA` for bounded `B`, then `R` is compact and properness is impossible;
4. a fixed completion whose source derivative is zero cannot unlock properness;
5. infinite rank alone is insufficient: `R` must also have closed range and finite kernel.

The last point sharpens the previous infinite-rank necessity. Essential norm measures survival of
at least one cofinal direction. Global properness requires control of every direction modulo a
finite residual kernel.

## 6. Carrier--defect bifurcation

Let `delta` be a real or complex scalar and define

\[
 D_\delta=\delta R,
 \qquad
 \Psi_\delta x=(Ax,Rx,D_\delta x).
 \tag{CST.17}
\]

### Theorem 6.1 — retained carrier and vanishing defect

Assume the equivalent conditions of Theorem 3.1.

1. `Psi_delta` is bounded below for every `delta`. The recovery map `(CST.13)`, applied to the
   first two coordinates, is a left inverse independently of `delta`.
2. Since `H` is infinite-dimensional, `R` is noncompact. Therefore

   \[
   \boxed{D_\delta\text{ is compact}\iff\delta=0.}
   \tag{CST.18}
   \]

3. The exact Calkin-distance response is

   \[
   \boxed{
   \operatorname{dist}(D_\delta,\mathcal K)
   =|\delta|\operatorname{dist}(R,\mathcal K).}
   \tag{CST.19}
   \]

4. If the structural coordinate `R` is omitted and only `(A,D_delta)` is retained, then it is
   bounded below for every `delta!=0`, but at `delta=0` it reduces to compact `A` and cannot be
   bounded below on infinite-dimensional `H`.

### Proof

The first clause follows because

\[
 \|\Psi_\delta x\|^2
 =\|Ax\|^2+(1+|\delta|^2)\|Rx\|^2
 \ge\|Tx\|^2.
 \tag{CST.20}
\]

If `R` were compact, `(CST.16)` would contradict `c>0`. For `delta!=0`, scalar multiplication by
`delta` is an automorphism of the compact ideal, proving `(CST.18)` and `(CST.19)`; the zero case is
immediate. For `delta!=0`, the norms of `(A,R)` and `(A,delta R)` are equivalent. At `delta=0`, the
map is `A`, which is compact and cannot be bounded below on an infinite-dimensional space. QED.

### Interpretation

Formation and selection are different laws.

```text
R                 structural carrier; must remain essentially present
delta R           relative law defect; may vanish in the Calkin quotient
A                 compact local chart; repairs only finite residual kernel.
```

Demanding compactness of the carrier destroys properness. Demanding noncompactness of the defect
destroys selection. Retaining both resolves the apparent contradiction.

## 7. Functional-equation and recovery neutrality

Let `U:H->H`, `V:Y->Y`, and `W:Z->Z` be unitary operators and put

\[
 A'=VAU^*,
 \qquad
 R'=WRU^*,
 \qquad
 T'=(A',R').
 \tag{CST.21}
\]

Then

\[
 T'=(V\oplus W)TU^*.
 \tag{CST.22}
\]

Hence:

1. `m(T')=m(T)`;
2. `ker R'=U(ker R)` and its dimension is unchanged;
3. closed range and compactness are unchanged;
4. `dist(R',K)=dist(R,K)` for the compact ideal;
5. the transformed joint recovery is

   \[
   \mathcal L'=U\mathcal L(V^*\oplus W^*).
   \tag{CST.23}
   \]

If a functional equation sends `delta` to `delta'` with `|delta'|=|delta|`, it preserves both the
formation margin and defect information exactly.

The common-recovery packet theorem supplies the statistical analogue: lifting both packets through
one recovery kernel preserves KL and Jeffreys information exactly. Therefore functional-equation
packet formation is an isometric gauge transport of the carrier--defect law. It neither creates a
missing transducer nor improves its properness.

## 8. Four-organ fusion and prediction

The theorem separates four corpus organs without identifying them artificially.

### 8.1 Finite-type prime formation

The prime sampling map is compact and injective but has nonclosed range. It plays the role of `A`.
Theorem 3.1 says it can contribute exact coefficient faithfulness while repairing only a finite
kernel left by the cofinal transducer. It cannot itself supply global properness.

### 8.2 Completed-flux / fixed Gamma formation

A fixed archimedean completion is an affine translation of the prime flux. Under interventions of
Euler coefficients its archimedean derivative is zero. It therefore contributes no `R` in
`(CST.2)`. Its infinite Taylor jet may classify the completed source, but static source-image
membership is not transduction and cannot satisfy `(CST.4)`.

### 8.3 Functional-equation packet formation

The common recovery-kernel lift preserves information. Equations `(CST.21)--(CST.23)` show the
operator version: an isometric FE lift conjugates the formation law and leaves all properness and
defect invariants unchanged. This explains information neutrality without declaring FE useless: it
transports a producer once one exists, but cannot produce it.

### 8.4 Sonin/Calkin organ — new exact obligation

The Sonin corpus already proves positive essential norm and Calkin partial-isometry laws for the
prime--archimedean corners. Those results certify noncompact survival, not global formation
properness. The new predicted theorem is one of the following equivalent formation statements.

1. A source-generated family of Sonin corners has a combined analysis map with closed range and
   finite kernel.
2. Its combined Gram operator has a positive lower bound modulo a finite-dimensional sector.
3. Its Calkin initial support projections cover the identity.
4. Every adaptive prime-null sequence is intercepted by at least one shell channel.

A single positive essential norm does not imply any of these. Thus the next Sonin theorem is a
**Calkin frame-coverage theorem**, not another noncompactness or essential-norm computation.

### 8.5 Cauchy seam / recurrence organs

The infinite-dimensional Cauchy quotient proves that finite repair is impossible; Theorem 3.1
predicts the stronger test: the resulting response must have closed range and finite kernel.
Similarly, an open recurrence lift may carry unbounded history while still admitting adaptive
near-zero velocities. A recurrence cost unlocks selection only when its analysis operator obeys a
uniform lower frame bound.

This is a theorem in a fourth organ predicted from the fusion law, not a restatement of any one
route endpoint.

## 9. Sharp countermodels

### 9.1 Noncompact does not imply proper

Let `H=H_1 direct-sum H_2` with both summands infinite-dimensional and let `R` be projection onto
`H_1`. Then `R` has essential norm one but infinite-dimensional kernel `H_2`. For every compact
`A`, the pair `(A,R)` fails to be bounded below. Thus essential norm is the wrong global invariant.

### 9.2 Infinite rank does not imply proper

On `ell^2`, let `Re_n=n^(-1)e_n`. It is injective and infinite-rank but compact with nonclosed
range. No compact `A` repairs it.

### 9.3 Finite residual kernel is repairable

Let `R` be the projection killing only `span{e_1,...,e_k}` and let `A` embed that finite span into
`Y`. Then `(A,R)` is bounded below and `(CST.13)` reconstructs every vector exactly.

### 9.4 Vanishing sole carrier destroys selected formation

For the preceding `R`, `(A,delta R)` is proper for `delta!=0` and nonproper at `delta=0`. Adding the
retained `R` coordinate makes `Psi_delta` proper for every `delta` while `delta R` still detects
the unique selected value by compactness.

## 10. Literature boundary

The abstract operator theory is classical. Upper semi-Fredholm operators are precisely operators
left-invertible modulo compacts; essential minimum modulus is positive precisely in this chamber.
Operator-valued frame theory treats analysis operators and partial-isometry parametrizations. See:

- Bouldin, *The essential minimum modulus*, Indiana Univ. Math. J. 30 (1981);
- Skhiri, [*On the essential minimum modulus of linear operators in Banach spaces*](https://doi.org/10.14232/actasm-014-538-8);
- Kaftal--Larson--Zhang, [*Operator valued frames*](https://arxiv.org/abs/0707.3272);
- Ivkovic, [*Semi-Fredholm Theory on Hilbert C*-modules*](https://arxiv.org/abs/1906.03319).

Field content is the interpretation and coupled law: compact coefficient-faithful formation,
cofinal semi-Fredholm transduction, finite residual recovery, a separately vanishing defect, and
information-neutral FE transport. No parent theorem supplies the HGT source producer.

## 11. Exact boundary and next gate

This theorem does **not** construct the source-generated `R`. It proves the global formation and
properness theorem such an `R` must satisfy and supplies its exact recovery formula.

The next non-theatrical gate is:

> Construct one pre-zero source response family whose combined Calkin support covers every
> adaptive source direction, prove its finite residual kernel is read injectively by the compact
> prime channel, and identify a separate FE-covariant scalar defect multiplying that retained
> carrier.

Only after this gate is closed may compactness of the defect be used as a selection law.

## 12. Formal status

The core global mechanism is formalized in
`formal/GaloisForLFunctions/HTGeometry/ConstitutiveCompactCofinalFusion.lean` and wired into
`HTGeometry/UniversalLawField`. Lean proves:

1. necessity and sufficiency in Theorem 3.1;
2. existence of the bounded common recovery kernel in Theorem 4.1;
3. quantitative joint bounded-below recovery;
4. exact lift of any invertible functional-equation coordinate action through that kernel;
5. carrier--defect recovery independently of the scalar defect coordinate.

The compact-ideal distance identities `(CST.15)--(CST.19)` remain paper-only, so this card stays in
Stage 2 rather than being promoted wholesale.

## Gates

- [x] source-independent mechanism stated;
- [x] compact--cofinal properness classified exactly;
- [x] joint reconstruction formula proved;
- [x] quantitative compact-ideal margin proved;
- [x] carrier--defect bifurcation proved;
- [x] FE/recovery information neutrality proved;
- [x] three-organ fusion and fourth-organ prediction stated;
- [x] sharp noncompact/infinite-rank countermodels supplied;
- [x] core Lean formalization and umbrella wiring;
- [ ] literal pre-zero Calkin frame-coverage producer;
- [ ] source-derived selected defect compactness;
- [ ] RH consequence.

## Log

- 2026-08-12 — exact compact--cofinal fusion classification, joint recovery, carrier--defect
  bifurcation, and FE neutrality proved. Essential norm versus global properness separated;
  Calkin frame coverage isolated as fourth-organ prediction.
- 2026-08-18 — Theorems 3.1 and 4.1, functional-equation recovery neutrality, and structural
  carrier--defect recovery formalized in Lean and wired into the universal-law-field umbrella.
