# Split-formation parallax, ternary interference, reconstruction, and global properness law

- **ID:** ULF-CPM-1
- **Stage:** 3-formalized
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ConstitutiveSplitFormationParallax`,
  `GaloisForLFunctions.HTGeometry.SplitFormationParallaxDistanceBound`
- **Type:** MECHANISM THEOREM / GENERATED COMPARISON / GLOBAL FORMATION PROPERNESS
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]`
  `[COMPARISONS GENERATED, NOT SUPPLIED] [EXACT HIDDEN-RESIDUAL RECONSTRUCTION]`
  `[FOUR-FORMATION COHERENCE] [GLOBAL PROPERNESS] [NOT RH] [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS]`
- **Source:** whole-frontier intervention grammar, common-recovery flatness, formation holonomy,
  ternary formation interference, and fusion-frame properness

## 1. Pivot

Common recovery produces flat ambient comparisons

\[
  f_jp_i:Z\longrightarrow Z.
\]

That fact repeatedly stalled the field programme: a comparison factored through recovery cannot
create a new source law.  The mistake was to compare the formed carriers only in the ambient
space.  Each split formation also induces a **compressed source comparison**

\[
  C_{ji}=p_jf_i:X\longrightarrow X.
\tag{CPM.1}
\]

These compressed comparisons are not transitive.  Their failure is not an arbitrary vertical
transport.  It is forced by the complement erased by the intermediate formation.  A sufficiently
complete family of formations reconstructs that complement exactly.

This gives a mechanism:

\[
 \boxed{
 \textsf{split form}
 \to\textsf{compress}
 \to\textsf{interfere}
 \to\textsf{reconstruct hidden residual}
 \to\textsf{properly select its neutral kernel}.}
\tag{CPM.2}
\]

## 2. Algebraic setup

Let \(R\) be a commutative ring and let \(X,Z\) be \(R\)-modules.  Let \(I\) be a finite
nonempty index set.  For every \(i\in I\), suppose we are given a split formation

\[
 X\xrightarrow{f_i}Z\xrightarrow{p_i}X,
 \qquad p_if_i=1_X.
\tag{CPM.3}
\]

Write

\[
 e_i=f_ip_i:Z\to Z,
 \qquad C_{ji}=p_jf_i:X\to X.
\tag{CPM.4}
\]

The idempotent \(e_i\) is regenerate-after-recovery in formation \(i\).  The map \(C_{ji}\)
asks what formation \(j\) recovers from a source formed by \(i\).

Define the hidden residual of \(i\) relative to \(j\) by

\[
 R_{ji}=(1_Z-e_j)f_i=f_i-f_jC_{ji}:X\to Z,
\tag{CPM.5}
\]

and the ternary interference read by formation \(k\) by

\[
 \Omega_{kji}=C_{ki}-C_{kj}C_{ji}:X\to X.
\tag{CPM.6}
\]

No comparison, defect, current, or work has been added to the split formations.  Every object in
`(CPM.4)`--`(CPM.6)` is generated from \((f_i,p_i)\).

## 3. Generated parallax and interference theorem

### Theorem 3.1

For all \(i,j,k\in I\):

1. \(e_i^2=e_i\), \(C_{ii}=1_X\), and \(p_jR_{ji}=0\);
2. source formation splits exactly as
   \[
    \boxed{f_i=f_jC_{ji}+R_{ji};}
   \tag{CPM.7}
   \]
3. ternary interference is the observation of the hidden residual:
   \[
    \boxed{\Omega_{kji}=p_kR_{ji}=p_k(1_Z-e_j)f_i;}
   \tag{CPM.8}
   \]
4. compressed comparisons are transitive through \(j\) exactly when every \(k\)-reporter kills
   the \(j\)-hidden residual of \(i\).

### Proof

The split equation gives

\[
 e_i^2=f_i(p_if_i)p_i=f_ip_i=e_i,
 \qquad C_{ii}=p_if_i=1_X.
\]

Also

\[
 p_jR_{ji}=p_jf_i-(p_jf_j)C_{ji}=C_{ji}-C_{ji}=0.
\]

Equation `(CPM.7)` is the definition of \(R_{ji}\).  Finally,

\[
 \begin{aligned}
 p_kR_{ji}
 &=p_kf_i-p_kf_jp_jf_i\\
 &=C_{ki}-C_{kj}C_{ji}
 =\Omega_{kji},
 \end{aligned}
\]

which proves `(CPM.8)` and the last claim.  QED.

### Meaning

Two-leg comparison \(C_{ji}\) is not the full law.  The first genuinely new response is ternary:
one formation creates a residual, a second declares it hidden, and a third reads it.  The ternary
class is therefore neither a fitted curvature nor an independent slot.

## 4. Four-formation coherence

### Theorem 4.1 -- exact interference conservation

For all \(i,j,k,\ell\in I\),

\[
 \boxed{
 C_{\ell k}\Omega_{kji}+\Omega_{\ell ki}
 =\Omega_{\ell ji}+\Omega_{\ell kj}C_{ji}.}
\tag{CPM.9}
\]

### Proof

Expand the left side:

\[
 \begin{aligned}
 C_{\ell k}(C_{ki}-C_{kj}C_{ji})
 +(C_{\ell i}-C_{\ell k}C_{ki})
 =C_{\ell i}-C_{\ell k}C_{kj}C_{ji}.
 \end{aligned}
\]

Expand the right side:

\[
 \begin{aligned}
 (C_{\ell i}-C_{\ell j}C_{ji})
 +(C_{\ell j}-C_{\ell k}C_{kj})C_{ji}
 =C_{\ell i}-C_{\ell k}C_{kj}C_{ji}.
 \end{aligned}
\]

The expressions agree.  QED.

Equation `(CPM.9)` is the exact fourth-organ prediction: after three compressed comparisons are
known, a fourth interference cannot be chosen independently.

## 5. Formation saturation reconstructs hidden law

The algebraic analogue of a Parseval fusion-frame resolution is

\[
 \boxed{\sum_{k\in I}f_kp_k=1_Z.}
\tag{CPM.10}
\]

It says that the complete formation family jointly reconstructs the ambient carrier.  Individual
recoveries may be lossy.

### Theorem 5.1 -- hidden-residual reconstruction

Assume `(CPM.10)`.  Then for all \(i,j\in I\),

\[
 \boxed{
 R_{ji}=\sum_{k\in I}f_k\Omega_{kji}.}
\tag{CPM.11}
\]

Consequently the following are equivalent:

1. \(R_{ji}=0\);
2. \(f_i=f_jC_{ji}\);
3. \(\Omega_{kji}=0\) for every \(k\in I\).

### Proof

By `(CPM.8)` and `(CPM.10)`,

\[
 \sum_kf_k\Omega_{kji}
 =\sum_kf_kp_kR_{ji}
 =R_{ji}.
\]

Equivalence of the first two statements is `(CPM.7)`.  The first implies the third by `(CPM.8)`.
The third implies the first by `(CPM.11)`.  QED.

This is joint reconstruction, not only detection.  Ternary responses recover the complete law
lost by the intermediate formation.

### Corollary 5.2 -- missing-formation prediction

Fix \(m\in I\).  Under `(CPM.10)`,

\[
 \boxed{
 f_m\Omega_{mji}
 =R_{ji}-\sum_{k\ne m}f_k\Omega_{kji}.}
\tag{CPM.12}
\]

Hence all but one organ determine the formed contribution of the withheld organ.  If \(f_m\) is
injective, they determine \(\Omega_{mji}\) itself.

This is the exact withheld-fourth-organ prediction required by the field acceptance gate.

## 6. Positive conservation and global properness

Now let \(X,Z\) be Hilbert spaces.  Assume each \(f_k:X\to Z\) is an isometry and
\(p_k=f_k^*\).  Then \(e_k=f_kf_k^*\) is the orthogonal projection onto
\(E_k=\operatorname{ran}f_k\).

For fixed \(j\), let \(V_j=E_j^\perp\).  Suppose the formation family is a fusion frame on
\(V_j\): there are \(0<A\le B<\infty\) such that

\[
 A\|z\|^2
 \le\sum_{k\in I}\|f_k^*z\|^2
 \le B\|z\|^2
 \qquad(z\in V_j).
\tag{CPM.13}
\]

### Theorem 6.1 -- positive hidden-current conservation

For every \(x\in X\),

\[
 \boxed{
 \|R_{ji}x\|^2
 =\|x\|^2-\|C_{ji}x\|^2,}
\tag{CPM.14}
\]

and

\[
 \boxed{
 A\bigl(\|x\|^2-\|C_{ji}x\|^2\bigr)
 \le\sum_k\|\Omega_{kji}x\|^2
 \le B\bigl(\|x\|^2-\|C_{ji}x\|^2\bigr).}
\tag{CPM.15}
\]

If the family is Parseval on \(V_j\), then `(CPM.15)` is the exact identity

\[
 \boxed{
 \sum_k\|\Omega_{kji}x\|^2
 =\|R_{ji}x\|^2
 =\|x\|^2-\|C_{ji}x\|^2.}
\tag{CPM.16}
\]

### Proof

The orthogonal decomposition

\[
 f_ix=e_jf_ix+(1-e_j)f_ix=f_jC_{ji}x+R_{ji}x
\]

gives `(CPM.14)` because \(f_i,f_j\) are isometries.  The vector \(R_{ji}x\) lies in \(V_j\),
and `(CPM.8)` says

\[
 f_k^*R_{ji}x=\Omega_{kji}x.
\]

Apply `(CPM.13)` and then `(CPM.14)`.  Parseval gives equality.  QED.

### Theorem 6.2 -- proper selection of the neutral overlap

Let

\[
 N_{ji}=\ker R_{ji}
 =\{x:f_ix\in E_j\}.
\tag{CPM.17}
\]

Assume that \(R_{ji}\) is bounded below by \(\alpha>0\) on \(N_{ji}^\perp\).  Then

\[
 \boxed{
 \sum_k\|\Omega_{kji}x\|^2
 \ge A\alpha^2\operatorname{dist}(x,N_{ji})^2.}
\tag{CPM.18}
\]

If one execution block is repeated \(q\) times, its accumulated work is

\[
 \mathcal W_q(x)=q\sum_k\|\Omega_{kji}x\|^2.
\tag{CPM.19}
\]

Therefore

\[
 \boxed{
 \sup_q\mathcal W_q(x)<\infty
 \quad\Longleftrightarrow\quad x\in N_{ji}.}
\tag{CPM.20}
\]

### Proof

Apply `(CPM.15)` to the orthogonal component of \(x\) in \(N_{ji}^\perp\), use the lower bound
for \(R_{ji}\), and note that \(R_{ji}\) kills \(N_{ji}\).  This proves `(CPM.18)`.  The work in
`(CPM.19)` is nonnegative and independent of the repetition number.  It remains bounded in \(q\)
exactly when the one-block value is zero.  By `(CPM.15)`, that is equivalent to \(R_{ji}x=0\),
hence to \(x\in N_{ji}\).  QED.

If a source theorem identifies \(N_{ji}\) with the critical/neutral source sector, `(CPM.20)` is a
global selection theorem.  The present theorem constructs the mechanism and exact properness gate;
it does not insert that identification.

## 7. Common gauge and functional-equation neutrality

Let \(U:X\to X\) and \(V:Z\to Z\) be unitary, and replace

\[
 f_i\mapsto Vf_iU^{-1},
 \qquad p_i\mapsto Up_iV^{-1}
\tag{CPM.21}
\]

for every \(i\).  Then

\[
 C_{ji}\mapsto UC_{ji}U^{-1},
 \quad R_{ji}\mapsto VR_{ji}U^{-1},
 \quad \Omega_{kji}\mapsto U\Omega_{kji}U^{-1}.
\tag{CPM.22}
\]

All kernels, norms, reconstruction identities, and properness constants are unchanged.  Thus a
functional-equation action lifting through the **same** source and carrier gauge is
information-neutral.  Selection comes from nonzero relative formation parallax and its proper
ternary response, not from the common lift.

## 8. Exact finite calibration

Let \(X=\mathbb R\), \(Z=\mathbb R^2\), and define

\[
 f_1(x)=(x,0),\quad p_1(a,b)=a,
 \qquad
 f_2(x)=(0,x),\quad p_2(a,b)=b.
\tag{CPM.23}
\]

Then \(p_rf_r=1\) and

\[
 f_1p_1+f_2p_2=1_Z.
\tag{CPM.24}
\]

For \(i=1,j=2\),

\[
 C_{21}=0,qquad R_{21}=f_1,qquad
 \Omega_{121}=1_X,qquad \Omega_{221}=0.
\tag{CPM.25}
\]

Thus one intermediate formation erases the entire source, the other formation reconstructs it as a
ternary interference class, and `(CPM.11)` reads

\[
 f_1=f_1\cdot1+f_2\cdot0.
\]

The calibration is deliberately elementary.  Its role is to prove nonvacuity and sharpness, not to
stand in for an arithmetic realization.

## 9. Hostile boundaries

1. **No formation saturation, no reconstruction.**  The formula `Omega=pR` remains true, but a
   family of recoveries that is not jointly faithful can erase a nonzero residual.
2. **Pair data do not suffice.**  The contractions \(C_{ji}\) do not determine \(R_{ji}\) as a
   marked carrier map; minimal residual realizations retain a unitary purification gauge.
3. **Positive energy loses transport phase.**  The Gram sum in `(CPM.15)` determines hidden norm,
   not the full ordered comparison system.  The algebraic reconstruction `(CPM.11)` retains the
   formation maps and is strictly stronger.
4. **Injectivity is not properness.**  In infinite dimension a jointly faithful family may have no
   positive lower fusion-frame bound.  Adaptive residuals can then have unit norm and vanishing
   reported energy.
5. **Common recovery is flat.**  If all formations coincide, every residual and every ternary
   interference vanishes.  Repackaging one split formation cannot generate the mechanism.
6. **Arbitrary formations are theatre.**  The theorem becomes RH-relevant only when the source
   generates the formations before divisor specialization.
7. **No automatic hypertranscendence.**  Failure of finite formation saturation may accompany an
   infinite prolongation tower, but no equivalence is asserted.
8. **No RH conclusion.**  A literal pre-zero source must still identify one physical residual,
   prove saturation/properness, force its ternary reporters to vanish or have bounded repeated
   work, and identify its neutral kernel with the critical line.

## 10. Relation to established mathematics

The algebraic formulas use split idempotents and associativity.  The positive theorem uses defect
operators, Naimark complements, fusion frames, and observability Gramians.  Those are established
parents.  The field content is their constitutive ordering:

1. split formations generate compressed comparisons;
2. nontransitivity generates ternary interference;
3. a formation resolution reconstructs the hidden residual exactly;
4. positive saturation converts reconstruction into global properness;
5. repeated formation work selects the neutral overlap.

This ordering repairs the principal weakness of Formation Holonomy Mechanics: vertical comparison
is no longer inserted.  It is the forced complement response `(CPM.8)`.

Primary parents:

- Calderbank--Casazza--Heinecke--Kutyniok--Pezeshki,
  *Fusion Frames: Existence and Construction*, <https://arxiv.org/abs/0906.5606>;
- Christensen--Hasannasab, *A survey on frame representations via dynamical sampling*,
  <https://arxiv.org/abs/2201.00038>;
- standard Sz.-Nagy--Foias defect-operator and Naimark-dilation theory.

## 11. Field consequence and next gate

The route-independent law is now:

\[
 \boxed{
 \text{law content is the complement lost by one formation and reconstructed by the ternary
 responses of the others}.}
\tag{CPM.26}
\]

This explains why single routes stall: one observer cannot report its own erased complement.
Independent routes become useful only after their formations are proved to resolve one common
source carrier.  Then their ternary interference is not analogy; it is a reconstruction basis.

The next arithmetic theorem must not ask for another endpoint object.  It must construct three or
more literal pre-zero split formations \((f_i,p_i)\), prove a coefficient-faithful version of
`(CPM.10)` or `(CPM.13)`, and identify one existing route obstruction as the residual
`(1-f_jp_j)f_i`.  Equation `(CPM.12)` then predicts the withheld organ response before it is
calculated.  Only after that prediction passes may `(CPM.20)` be used for RH selection.

## 12. Lean certification

Formal module:

- `GaloisForLFunctions.HTGeometry.ConstitutiveSplitFormationParallax`

Lean closes the generated comparison identity `(CPM.8)`, four-formation coherence `(CPM.9)`,
resolving-family reconstruction `(CPM.11)`, withheld-organ prediction `(CPM.12)`, neutral-kernel
equivalence, Hilbert defect identity `(CPM.14)`, fusion-frame bounds `(CPM.15)`, Parseval
conservation `(CPM.16)`, and exact bounded repeated-work selection.  The quantitative distance
estimate `(CPM.18)` is now Lean-closed as well, in the leaf
`GaloisForLFunctions.HTGeometry.SplitFormationParallaxDistanceBound`
(`neutralOverlap`, `norm_hiddenResidual_ge_dist`, `parallaxEnergy_ge_dist_sq`).

Verification used scratch elaboration, direct leaf elaboration, and only the targeted leaf build.
The module is imported by `HTGeometry.UniversalLawField`; that umbrella was not built.  Audited
capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
