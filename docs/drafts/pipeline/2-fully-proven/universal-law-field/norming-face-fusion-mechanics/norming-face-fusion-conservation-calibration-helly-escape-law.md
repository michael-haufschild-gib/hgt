# Norming-face fusion conservation, calibration, Helly witness, and escape law

- **ID:** `ulf-nffm-fusion-calibration-helly-escape`
- **Stage:** 2 — fully proven on paper
- **Type:** ROUTE-INDEPENDENT FUSION / CONSERVATION / DIMENSION-ESCAPE THEOREM
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [THREE-GAUGE FUSION]`
  `[EXACT CONSERVATION] [FOURTH-ORGAN PREDICTION] [LEAN-CERTIFIED CORE] [NOT RH]`

## 1. Setup

Let `V` be a real normed vector space and let `I` be a finite set. A generated packet is a family
`v_i in V`. Put

\[
E_I(v)=\sum_{i\in I}\|v_i\|,\qquad
s_I(v)=\sum_{i\in I}v_i,\qquad
\Delta_I(v)=E_I(v)-\|s_I(v)\|.
\tag{NF.1}
\]

Let `B_(V*)={phi in V*:||phi||<=1}`. Define

\[
\rho_\phi(x)=\|x\|-\phi(x),\qquad
N(x)=\{\phi\in B_{V^*}:\phi(x)=\|x\|\}.
\tag{NF.2}
\]

Hahn--Banach makes every `N(x)` nonempty, including `N(0)=B_(V*)`.

## 2. Calibration theorem

### Theorem 2.1 — exact variational fusion law

For every generated packet,

\[
\boxed{
\Delta_I(v)=
\min_{\phi\in B_{V^*}}\sum_{i\in I}\rho_\phi(v_i).}
\tag{NF.3}
\]

Every residual in the sum is nonnegative. A norming functional for `s_I(v)` attains the minimum.

#### Proof

For `||phi||<=1`,

\[
\phi(x)\le |\phi(x)|\le\|x\|,
\]

so `rho_phi(x)>=0`. Also

\[
\sum_i\rho_\phi(v_i)
=E_I(v)-\phi(s_I(v))
\ge E_I(v)-\|s_I(v)\|
=\Delta_I(v).
\]

Hahn--Banach supplies `phi_0` with `||phi_0||<=1` and
`phi_0(s_I(v))=||s_I(v)||`, yielding equality. QED.

### Theorem 2.2 — joint calibration criterion

The following are equivalent:

1. `Delta_I(v)=0`;
2. `intersection_(i in I) N(v_i)` is nonempty;
3. one `phi in B_(V*)` satisfies `phi(v_i)=||v_i||` for every `i`.

#### Proof

Items 2 and 3 are definitions. If 3 holds, then

\[
\|s_I(v)\|\ge\phi(s_I(v))=\sum_i\|v_i\|\ge\|s_I(v)\|,
\]

so `Delta_I(v)=0`. Conversely, assume `Delta_I(v)=0` and choose a norming functional `phi_0`
for `s_I(v)`. Theorem 2.1 gives

\[
0=\sum_i\rho_{\phi_0}(v_i).
\]

All summands are nonnegative, so every summand vanishes. Thus `phi_0` norms every `v_i`. QED.

## 3. Conservation and observer exchange

### Theorem 3.1 — exact refinement conservation

Let `(B_j)_(j in J)` partition `I`, and put `s_j=sum_(i in B_j)v_i`. Then

\[
\boxed{
\Delta_I(v)=
\sum_{j\in J}\Delta_{B_j}(v)+\Delta_J((s_j)_j).}
\tag{NF.4}
\]

#### Proof

Expand the right side:

\[
\sum_j\left(\sum_{i\in B_j}\|v_i\|-\|s_j\|\right)
+\sum_j\|s_j\|-\left\|\sum_js_j\right\|
=\sum_i\|v_i\|-\left\|\sum_iv_i\right\|.
\]

QED.

### Theorem 3.2 — exact observer-exchange identity

Let `T:V->W` be a linear contraction and define `L_T(x)=||x||-||Tx||>=0`. Then

\[
\boxed{
\Delta_I(v)-\Delta_I(Tv)
=\sum_iL_T(v_i)-L_T(s_I(v)).}
\tag{NF.5}
\]

#### Proof

Use linearity `T(s_I(v))=sum_iTv_i` and expand both sides. QED.

No sign follows for the left side. An observer can erase or create apparent incompatibility; the
right side is the exact conserved exchange.

## 4. Finite witness theorem

Assume now that `V` is finite-dimensional of dimension `d`.

### Lemma 4.1

Every `N(x)` is a nonempty compact convex exposed face of the dual unit ball.

#### Proof

Nonemptiness is Hahn--Banach. It is the intersection of the compact dual unit ball with the closed
affine hyperplane `phi(x)=||x||`, hence compact and convex. If
`t phi+(1-t) psi` lies in `N(x)` for `0<t<1`, both `phi(x)` and `psi(x)` are at most `||x||`; their
strict convex combination equals `||x||`, so both equal `||x||`. Thus it is a face. QED.

### Theorem 4.2 — bounded calibration-witness arity

If `Delta_I(v)>0`, there is `J subset I` with

\[
1\le |J|\le d+1,
\qquad
\Delta_J(v)>0.
\tag{NF.6}
\]

Equivalently, if every subpacket of cardinality at most `d+1` fuses perfectly, the whole packet
fuses perfectly.

#### Proof

By Theorem 2.2, `Delta_I(v)>0` says `intersection_(i in I)N(v_i)` is empty. Apply finite Helly to
the compact convex sets `N(v_i)` in the `d`-dimensional dual. Some subfamily of at most `d+1` has
empty intersection. Theorem 2.2 converts this back to positive fusion defect. The witness cannot
be empty because the dual unit ball is nonempty. QED.

### Corollary 4.3 — minimal obstruction dimension bound

If `I` is minimally defective—`Delta_I(v)>0` but every proper subpacket has zero defect—then

\[
\boxed{|I|\le d+1,\qquad d\ge |I|-1.}
\tag{NF.7}
\]

## 5. Fourth-organ theorem: cofinal calibration escape

### Theorem 5.1

Let `(V_n,v^(n))` be finite-dimensional generated packets, each minimally defective. If their
cardinalities tend to infinity, then

\[
\dim V_n\longrightarrow\infty
\quad\text{along the same cofinal family.}
\tag{NF.8}
\]

In particular, they cannot all embed isometrically into one finite-dimensional normed receiver
while preserving packet sums and norms. Any common normed receiver is infinite-dimensional, and
its closed unit ball is not compact in norm topology.

#### Proof

Corollary 4.3 gives `dim V_n>=|I_n|-1`. The first claim follows. An isometric linear embedding
preserves norms, sums, defects, and common-calibrator failure, so a finite-dimensional common
receiver would give a uniform dimension bound, contradiction. Riesz's finite-dimensionality
criterion says a normed space with compact closed unit ball is finite-dimensional. QED.

This is the predicted theorem in the cofinal/noncompactness organ: irreducibly growing generation
arity forces receiver-dimension escape. It does not identify hypertranscendence with
noncompactness; it gives the exact additional hypothesis under which one forces the other.

## 6. Three structurally different specializations

### 6.1 Oscillatory cancellation

For `V=C_R`, dual calibrators are `phi_u(z)=Re(conj(u)z)`, `|u|<=1`. Therefore

\[
\Delta=\sum_i|a_i|-\left|\sum_ia_i\right|,
\]

and perfect fusion holds exactly when all nonzero amplitudes have the same phase.

### 6.2 Boundary incidence and capacity

Let `P` be a finite port set, `V=ell_1(P)`, and
`v_e=q_e(delta_(h(e))-delta_(t(e)))` with `q_e>0`. Then

\[
\Delta=2\sum_e q_e-\|\operatorname{div}q\|_1.
\tag{NF.9}
\]

A dual `ell_infinity` calibrator norms every edge exactly iff it equals `-1` on every active tail
and `+1` on every active head. Thus one middle vertex in a directed two-edge path is an exact
incompatibility witness.

### 6.3 Signed spectral response

Let `V` be self-adjoint `d by d` matrices with trace norm. Its dual calibrators are self-adjoint
operator-norm contractions under trace pairing. For

\[
A_i=s_i u_i u_i^*,\qquad s_i\ne0,
\]

one common calibrator exists exactly when the span of the `u_i` with `s_i>0` is orthogonal to the
span of those with `s_i<0`.

Indeed saturation forces `Qu_i=sign(s_i)u_i`; the `+1` and `-1` eigenspaces of self-adjoint `Q`
are orthogonal. Conversely, orthogonal spans define such a contraction by `+1`, `-1`, and `0` on
the positive, negative, and remaining orthogonal subspaces. Therefore trace-norm fusion defect is
an exact signed null-face incompatibility energy.

These are not isomorphic route targets. They are three representations of Theorems 2.1--3.2.

## 7. Sharp boundaries

1. The theorem needs one shared norm. Arbitrary monotone failure systems realize arbitrary
   clutters and have no Helly law.
2. Strictly positive weights may be absorbed into `v_i`; zero-weight effects must be removed.
3. Defect positivity has no universal positive lower bound. Nearly aligned complex phases give
   arbitrarily small positive defect.
4. Helly gives an upper witness bound, not a claim that `d+1` is sharp for every norming-face
   system.
5. Infinite-dimensional receivers need not have finite witnesses of uniformly bounded size.
6. The observer identity gives no monotonicity without additional geometry.
7. No arithmetic source packet or RH selector is asserted.

## 8. RH consequence still required

The theorem supplies the mechanism and a falsifiable design gate. RH would follow from a separate
source theorem with all four ingredients:

1. a pre-divisor packet containing coefficient-faithful effects in at least three live organs;
2. one source norm and compatible calibrator transport across their comparisons;
3. finite-packet perfect fusion or a uniform cofinal calibration law;
4. proof that every off-critical divisor creates a finite positive-defect witness.

Then Theorem 2.2 contradicts the off-critical witness. None of these arithmetic realization
claims is smuggled into the abstract theorem.

## 9. Parent mathematics

Hahn--Banach, support faces, triangle-equality criteria, Helly's theorem, and Riesz's compact-ball
criterion are classical. The result is a dependency-closed synthesis and a route-independent
mechanism theorem. Quantitative infinite-dimensional analogues require extra Banach geometry; see
[Ivanov 2024](https://arxiv.org/abs/2409.05744),
[Ivanov 2026](https://arxiv.org/abs/2603.22743), and
[Ivanov--Kadets 2026](https://arxiv.org/abs/2607.04093).

## 10. Lean certification

`GaloisForLFunctions.HTGeometry.NormingFaceFusion` certifies:

1. nonnegative local residuals and fusion defect;
2. Hahn--Banach attainment of the exact variational defect;
3. perfect fusion iff one common norming calibrator exists;
4. convexity and nonemptiness of norming faces;
5. finite Helly reconstruction from packets of size at most `dim(V)+1`;
6. minimal defective-packet cardinality and calibration-dimension lower bounds;
7. exact observer-exchange identity;
8. exact binary refinement conservation.

The matrix, incidence, and complex specializations remain paper corollaries of the certified
coordinate-free theorem. No project axiom, `sorry`, computation certificate, or RH premise is
used.
