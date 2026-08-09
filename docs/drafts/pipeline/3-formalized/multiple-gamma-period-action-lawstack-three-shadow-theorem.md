# Multiple-Gamma period-action lawstack three-shadow theorem

- **ID:** `clg-multiple-gamma-period-action-lawstack-three-shadow`
- **Stage:** 3-formalized
- **Status:** `[PAPER-PROVED] [NON-RH LAWSTACK THEOREM] [CLASSICAL STACK INGREDIENTS]`
  `[LEAN-FORMALIZED] [AXIOM-AUDITED] [UMBRELLA-WIRED]`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionAnalyticLaw`,
  `GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionLaw`,
  `GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionRankLaw`,
  `GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionProperLaw`, and
  `GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionLawstack`
- **Purpose:** replace an observer-dependent incidence operator by one canonical source action
  groupoid intrinsically producing isotropy, coarse topology, marked excess, and an affine
  involution; compare these to independently proved multiple-Gamma DA depth and normalized
  reflection.

## 1. Source action groupoid

For finite `m>=1`, put

\[
 \tau_0=i,
 \qquad
 \tau_1^{(m)}=2i+\frac\pi m,
\]

and at the boundary put `tau_1^(infinity)=2i`. Define

\[
 p_m:\mathbb Z^3\longrightarrow\mathbb C,
 \qquad
 p_m(a,b,c)=a+b\tau_0+c\tau_1^{(m)}.
\tag{1}
\]

Let `mathcal G_m=Z^3 semidirect C` be the translation action groupoid with

\[
 s(n,z)=z,
 \qquad
 t(n,z)=z+p_m(n),
\tag{2}
\]

and let

\[
 \mathfrak P_m=[\mathbb C/\mathbb Z^3]_{p_m}
\tag{3}
\]

be its topological quotient stack. It is a Picard stack presented by the two-term topological
complex `[Z^3 -> C]`, with `Z^3` in degree `-1`.

Write

\[
 L_m=\ker p_m,
 \qquad
 \Lambda_m=\operatorname{im}p_m.
\tag{4}
\]

The effective rational period space and its real span are

\[
 V_m=(\mathbb Z^3/L_m)\otimes_\mathbb Z\mathbb Q,
 \qquad
 W_m=\operatorname{span}_\mathbb R(\Lambda_m)\subset\mathbb C,
\]

and define the marked period excess

\[
 e(\mathfrak P_m)=\dim_\mathbb Q V_m-\dim_\mathbb R W_m.
\tag{5}
\]

This excess uses the marked period realization `(1)`; it is not claimed to be an invariant of the
unmarked underlying topological stack.

## 2. Lawstack theorem

### Theorem 2.1

For every finite `m` and for the boundary `m=infinity`:

1. the stabilizer group of every object of `P_m` is canonically `L_m`;
2. the coarse orbit group is canonically `C/Lambda_m`;
3. for finite `m`,

   \[
    L_m=0,
    \qquad
    \overline{\Lambda_m}=\mathbb R+i\mathbb Z,
    \qquad
    e(\mathfrak P_m)=1;
   \tag{6}
   \]

   hence the action is faithful but nonproper and `C/Lambda_m` is neither `T_1` nor Hausdorff;
4. at the boundary,

   \[
    L_\infty=\mathbb Z(0,-2,1),
    \qquad
    \Lambda_\infty=\mathbb Z+i\mathbb Z,
    \qquad
    e(\mathfrak P_\infty)=0;
   \tag{7}
   \]

   the coarse orbit group is a compact Hausdorff complex torus, while the full stack has isotropy
   `Z`; after effective rigidification by `L_infinity`, the `Z^2` translation action is proper and
   cocompact;
5. with

   \[
    c_m=\tau_0+\tau_1^{(m)},
    \qquad
    r_m(z)=c_m-z,
   \tag{8}
   \]

   the pair `(n,z)->(-n,r_m(z))` is an involutive automorphism of `mathcal G_m` and therefore of
   `P_m`;
6. if `Gamma_m(z)` is the corresponding normalized two-period Nishizawa multiple elliptic Gamma
   function, an independent special-function theorem gives the numerical equality

   \[
    d_{\rm DA}(\Gamma_m)=e(\mathfrak P_m).
   \tag{9}
   \]

   Thus finite `m` is hypertranscendental of transverse depth one, whereas the boundary is
   differentially algebraic of depth zero. Independently, the imported parity/normalization
   theorem gives the reflection law
   `Gamma_m(c_m-z)=Gamma_m(z)^{-1}` on the regular locus. The groupoid involution is compatible
   with the same affine reflection, but does not by itself determine the function normalization.

Consequently one canonical construction, evaluated on the cofinal marked collection, has three
intrinsic quantities that change simultaneously, plus a compatible affine involution:

\[
 \boxed{
 \begin{gathered}
 \text{stabilizer rank},\quad
 \text{coarse separation},\quad
 \text{marked excess}=\text{independently proved DA depth},\\
 \text{with a compatible affine involution}
 \end{gathered}}
\tag{10}
\]

### Corollary 2.2 — cofinal law-rank complementarity

Across the finite-to-boundary family,

\[
 \boxed{
 d_{\rm DA}(\Gamma_m)
 +\operatorname{rank}_{\mathbb Z}
   \operatorname{Stab}(\mathfrak P_m)
 =1.}
\tag{11}
\]

At finite `m`, the one unit appears as hypertranscendental period excess and coarse
nonseparatedness, with no isotropy. At the boundary it appears as one integral stabilizer/relation,
while differential depth vanishes and the coarse quotient becomes Hausdorff. This is an exact rank
ledger across a cofinal collection. No transport functor between the finite stacks and boundary
stack has been constructed, so “transmutation” is a conjectural dynamical interpretation rather
than part of the theorem.

## 3. Proof

For a translation action, an arrow `n:z->z` is exactly an element satisfying `p_m(n)=0`.
Therefore every stabilizer is `L_m`. Orbits are the cosets `z+Lambda_m`, proving Items 1--2.

For finite `m`, if

\[
 a+bi+c\left(2i+\frac\pi m\right)=0
\]

with integers, its real part is `a+c pi/m=0`. Irrationality of `pi` gives `a=c=0`, and then
`b=0`. Hence `L_m=0` and `rank_Q Lambda_m=3`. Moreover

\[
 \Lambda_m=left(\mathbb Z+\frac\pi m\mathbb Z\right)+i\mathbb Z.
\]

The first factor is dense in `R`, so its closure is `R+iZ`. In particular `Lambda_m` is not
closed. A quotient of a topological group by a subgroup is `T_1` exactly when the subgroup is
closed, and for topological groups this is also the Hausdorff criterion. Thus `C/Lambda_m` is not
`T_1` and not Hausdorff.

The action is not proper. Indeed choose distinct `n_j in Z^3` with `p_m(n_j)->0`. Then
`(s,t)(n_j,0)=(0,p_m(n_j))` remains in a compact subset of `C^2`, while `(n_j,0)` has no convergent
subsequence in `Z^3 times C`. This proves Item 3 except the excess. Since `W_m=C` as a real vector
space, `(5)` gives `e=3-2=1`.

At the boundary,

\[
 p_\infty(a,b,c)=a+(b+2c)i,
\]

so `L_infinity=Z(0,-2,1)` and `Lambda_infinity=Z+iZ`. The latter is a lattice. Its quotient is a
compact Hausdorff complex torus. The original `Z^3` action retains kernel `L_infinity`, whereas
the effective quotient `Z^3/L_infinity congruent Z^2` acts properly discontinuously and
cocompactly. Now `dim_Q V_infinity=2` and `dim_R W_infinity=2`, so `e=0`. This proves Item 4.

Finally,

\[
 r_m(z+p_m(n))
 =c_m-z-p_m(n)
 =r_m(z)+p_m(-n),
\]

so `(8)` is a groupoid involution. The imported multiple-Gamma period-excess theorem gives `(9)`,
and the imported even-rank parity/normalization theorem separately gives the reflection identity.
This proves Items 5--6
and `(10)`. ∎

For Corollary 2.2, combine `(6)--(9)` with
`Stab(P_m)=L_m`: the two sides are respectively `1+0` and `0+1`. ∎

### Theorem 2.3 — general period-action conservation law

Let `p:Z^N->V` be a homomorphism into a finite-dimensional real vector space, suppose the real
span of its image has constant dimension `d`, and set

\[
 L=\ker p,
 \qquad
 e(p)=\operatorname{rank}_{\mathbb Z}(\operatorname{im}p)-d.
\]

Then

\[
 \boxed{e(p)+\operatorname{rank}_{\mathbb Z}L=N-d.}
\tag{12}
\]

#### Proof

The exact sequence

\[
 0\longrightarrow L\longrightarrow\mathbb Z^N
 \longrightarrow\operatorname{im}p\longrightarrow0
\]

gives `rank(im p)=N-rank(L)`. Substitute this into the definition of `e(p)`. ∎

Equation `(12)` is presentation-invariant under `GL_N(Z)` changes of source basis and invertible
real-linear changes of target coordinates. Whenever an independent special-function theorem identifies
differential depth with `e(p)`, it becomes a conservation law between hypertranscendental freedom
and integral isotropy. Such an identification is proved for the multiple-Gamma family above, not
for arbitrary hypertranscendental functions.

## 4. Why this improves the incidence calibration

The previous diagonal incidence operator

\[
 x(\lambda)\longmapsto\frac{\lambda}{1+|\lambda|}x(\lambda)
\]

correctly detects discreteness, but its weight is not forced by period arithmetic. The marked
translation lawstack needs no such choice:

- `L_m` is intrinsic isotropy;
- `C/Lambda_m` is the canonical coarse orbit object;
- closedness of `Lambda_m` is the canonical separation criterion;
- `e(P_m)` is determined by the marked effective period realization;
- the affine base reflection lifts to a literal groupoid automorphism.

Thus the arbitrary-weight countermodel kills the operator as foundation but does not kill the
marked action-stack construction. This is the first exact non-RH example in which two
nonisomorphic organs—stack isotropy and coarse separation—are forced by one source presentation,
while a third independently established HT invariant is numerically equal to the marked excess.
No functor from marked action stacks to differential-algebraic special functions is constructed.

## 5. Scope and hostile limits

1. The theorem uses a classical translation quotient stack. It establishes a working local model,
   not an entire new field.
2. The marked excess is not recoverable from an unmarked topological stack; the period
   realization is essential source structure.
3. No shifted symplectic form, harmonic metric, positive quotient, history action, or
   `lambda`-connection is constructed.
4. Nonproperness at finite `m` and isotropy at the boundary are different singularities; they must
   not both be renamed “curvature.”
5. The theorem proves no RH statement and uses no Xi zero.
6. General hypertranscendence need not equal nonseparatedness. Equality `(9)` is a theorem for this
   multiple-Gamma hierarchy and a conjectural pattern elsewhere.
7. Replacing `Gamma_m` by a nonzero scalar multiple leaves the marked period lawstack and DA depth
   unchanged but generally changes the normalized reflection equation. Thus reflection is extra
   normalized function data, not induced by the action stack alone.
8. The finite packets plus boundary form a cofinal collection. A specialization/transport law
   upgrading rank complementarity to dynamical migration remains open.

## 6. Field prediction exposed by the theorem

A coordinate-free geometry for hypertranscendental laws should treat a route as a realization of
a marked derived/action lawstack. Its no-gos need not be scalar curvature: they stratify into
isotropy, nonseparated coarse quotient, nonproperness, nontrivial holonomy, derived thickness, and
failure of an observer functor to be conservative. A genuine field theorem must state which of
these strata one source deformation can exchange and which are independent.

## 7. Corpus and formal support

The differential-depth equality and reflection identity are imported from:

- `pipeline/3-formalized/all-parameter-multiple-elliptic-gamma-dichotomy.md`;
- `pipeline/3-formalized/new_scientific_knowledge/gamma/multiple-gamma-period-excess-closure-phase-transition.md`;
- `pipeline/3-formalized/multiple-elliptic-gamma-parity-inversion.md`.

Those files and their Lean corpus supplied the independently proved analytic inputs. The new Lean
modules formalize the marked action, topology, literal rationalized ranks, topological groupoid,
properness transition, conservation law, and collected finite/boundary conclusions.

## 8. Formalization result

Formalized exactly and unconditionally. The capstone contains literal topological groupoid source,
target, identity, inverse, composition, continuity and groupoid laws; coarse-orbit equivalence with
`C / range(p)`; involutive homeomorphic reflection automorphisms; exact finite and boundary theorem
bundles; proper/cocompact effective boundary action; literal rationalized source/stabilizer ranks;
DA-depth equalities and normalized product reflections; and Theorem 2.3 with real-span dimension
plus source-basis and real-linear target-coordinate invariance.

Verification:

- [x] each new module passes `lake env lean <file>`;
- [x] capstone passes `lake build +GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionLawstack`;
- [x] `GaloisForLFunctions/HTGeometry.lean` passes direct elaboration with capstone imported;
- [x] targeted forbidden-declaration scan finds no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`;
- [x] `#print axioms` on capstone, properness, groupoid, complementarity, and conservation theorems
  reports only `propext`, `Classical.choice`, and `Quot.sound`;
- [x] no stale task-owned Lean process remains;
- [x] repository lint declaration checks pass these modules; global reachability gate remains red
  only for five unrelated pre-existing HTGeometry modules:
  `EuclideanDiagonalGappedForm`, `NonidentityPauliWordCount`, `PauliEnsembleBoxNorm`,
  `PauliZGappedHamiltonian`, and `PauliZSetLabels`.

## Log

- 2026-08-09 — all dependency-closed claims formalized, capstone built, umbrella elaborated, axioms
  audited, and card promoted to Stage 3.
