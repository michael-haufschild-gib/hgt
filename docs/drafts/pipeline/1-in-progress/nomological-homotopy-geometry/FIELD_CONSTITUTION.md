# Nomological Homotopy Geometry — field constitution

- **Stage:** 1 — field construction
- **Status:** [ROUTE-FREE FOUNDATION] [COORDINATE-FREE PRIMITIVE]
  [NO CORPUS CALIBRATION ADMITTED] [NOT RH] [NO LEAN WRITTEN OR BUILT]

## 1. Subject

Nomological Homotopy Geometry (NHG) studies laws as geometric fields rather than equations imposed
from outside a fixed mathematical universe. Its basic questions are:

1. what is a coordinate change of a law;
2. what is an actual deformation of a law;
3. what information an observer forgets;
4. how local law curvature integrates to global history;
5. when positive observation is a choice of real phase;
6. when finite observation closes while lifted source history remains open.

The field is not defined by examples. Examples are representations of the field constitution below.

## 2. Geometric primitive

Fix a differential or derived base \(B\). A local NHG field is a source-marked complete filtered
cyclic \(Q\)-algebroid

\[
 \mathfrak X=(\mathcal A\to B,Q,\rho,F^\bullet,
 \langle-,-\rangle,\alpha,\nabla),
\tag{FC.1}
\]

where:

- \(Q\) is a homological vector field, \(Q^2=0\);
- \(\rho:\mathcal A\to T_B\) is the anchor;
- \(F^\bullet\) is a complete principal-parts/Spencer filtration;
- \(\langle-,-\rangle\) is one fixed-degree perfect cyclic pairing;
- \(\alpha\) is a source-selected Maurer--Cartan section;
- \(\nabla\) is a filtered cyclic \(Q\)-connection.

The compatibility equations are

\[
 [\nabla,Q]=0,
 \qquad \nabla\langle-,-\rangle=0,
 \qquad \rho Q=Q_B\rho.
\tag{FC.2}
\]

The connection may be treated in first-order, Palatini form. A source-derived Levi--Civita or
constitutive selection of \(\nabla\) is a dynamics problem, not hidden in the definition.

The anchor is essential. It couples internal law deformation to motion on the history base. An
unanchored product of a deformation complex and a time system is not an NHG field.

## 3. General covariance and equivalence principle

A **nomological gauge** is an equivalence of pointed anchored filtered cyclic \(Q\)-algebroids. It
must preserve source marking, connection up to coherent gauge, Spencer filtration, pairing, and
integrated transport.

A proof, representation, or measurement is an **observer**

\[
 q:\mathfrak X\longrightarrow\mathfrak Y
\tag{FC.3}
\]

in this structured category. It is a local gauge only on a stratum where \(q\) is an equivalence.
No agreement of scalar invariants, spectra, zero sets, endpoints, or recurrence periods can replace
this condition.

> **Nomological equivalence principle.** Local descriptions are gauges exactly when their
> structured homotopy law-fibres are contractible. Every noncontractible law-fibre is retained
> geometry, not a coordinate artefact.

This principle prevents a favoured proof language from defining the field.

## 4. One defect object

For every observer in (FC.3), define its **relative law-fibre**

\[
 \mathfrak K_q:=\operatorname{hofib}(q).
\tag{FC.4}
\]

This is the single carrier of observer loss. The following are functorial constructions from
\(\mathfrak K_q\), not independent fields added to the theory:

| Derived face of \(\mathfrak K_q\) | Geometric meaning |
|---|---|
| tangent complex \(\mathbb T\mathfrak K_q\) | infinitesimal law directions erased by \(q\) |
| relative Atiyah class | local failure of flat source-compatible transport |
| curvature Postnikov tower | successive nullhomotopy and higher-transgression obstructions |
| integration \(\Pi_\infty(\mathfrak K_q)\) | invisible histories and vertical higher holonomy |
| Spencer tower \(J^\infty\mathfrak K_q\) | prolonged law freedom and differential growth |
| Cartan-polarization bundle | positive real phases compatible with the cyclic pairing |
| completion comparison | algebraic histories erased or created at an analytic boundary |

If a proposed invariant cannot be constructed functorially from \(\mathfrak X\), an observer \(q\),
or their relative law-fibre, it is not an NHG invariant.

## 5. Local observer geometry

On a regular polarized chart, let the linearized law bundle split orthogonally as

\[
 E=K\oplus H,
\tag{FC.5}
\]

where \(K\) linearizes the relative law-fibre and \(H\) is the observed sector. The compatible
connection has block form

\[
 \nabla^E=
 \begin{pmatrix}
  \nabla^K & \mathsf B\\
  \mathsf A & \nabla^H
 \end{pmatrix},
 \qquad \mathsf A=-\mathsf B^\dagger.
\tag{FC.6}
\]

Its curvature satisfies the exact nomological Gauss--Codazzi--Ricci identities

\[
 R^E=
 \begin{pmatrix}
  R^K+\mathsf B\wedge\mathsf A & d_\nabla\mathsf B\\
  d_\nabla\mathsf A & R^H+\mathsf A\wedge\mathsf B
 \end{pmatrix}.
\tag{FC.7}
\]

Thus observed curvature, hidden curvature, and observer coupling are not separate metaphors. They
are blocks of one source connection. If the total connection is flat, apparent observed curvature
is quadratic in the second fundamental law. If \(\mathsf B=0\), the observer splitting is parallel
and local history cannot leak between observed and hidden sectors.

This is the field's first GR-like structural law: change of observer changes the decomposition of
one curvature tensor, not the underlying field.

## 6. Internal law operations versus geometric curvature

The minimal transferred operations

\[
 q_n:S^n(sH_\alpha)\to sH_\alpha
\tag{FC.8}
\]

measure intrinsic nonlinearity and nonformality of the sourced law germ. Their first nonzero arity
and structured conjugacy class are gauge invariants. They are not differential two-forms and do
not generate loop holonomy by themselves.

Geometric curvature is the relative Atiyah class of \(\nabla\), together with its higher
nullhomotopies and soldered Spencer prolongations. A theorem connecting (FC.8) to curvature must
construct the missing anchor, horizontal soldering, and transgression. Naming both objects
"curvature" is forbidden.

## 7. Five derived geometries

### 7.1 Holonomy geometry

Restricted vertical holonomy is generated locally by transported Atiyah--Spencer curvature only
under an Ambrose--Singer--Spencer theorem. Full holonomy additionally retains flat global
monodromy. Component boundary, connection holonomy, and higher holonomy are distinct invariants.

### 7.2 Prolongation geometry

At a formally smooth differential chart, unbounded Kolchin growth produces an inverse-limit
Spencer tangent with infinitely many nonzero vertical kernels. This pro-object is not locally
compact, and every fixed finite-order observer kills an infinite tail. Hypertranscendence enters
NHG here: as maximal free-jet growth, not as ordinary orbit density or curvature.

### 7.3 Polar geometry

For a cyclic form of signature \((p,q)\), positive phases form the Cartan bundle with fibre

\[
 O(p,q)/(O(p)\times O(q)).
\tag{FC.9}
\]

Positivity is a reduction of indefinite gauge, not automatic information loss. Gram observation is
a quotient by left partial isometry; cross-Gram data recover relative phase up to one common output
gauge. A parallel positive phase exists exactly when holonomy fixes a Cartan reduction.

### 7.4 Recurrence geometry

An observed recurrent loop lifts to a path in the total law groupoid. The lift can remain open by
three intrinsic mechanisms: nontrivial fibre-component boundary, noncompact vertical holonomy, or
escape in a nonlocally compact Spencer/completion fibre. If the source-lift map together with its
derived action is proper, recurrent observation plus escaping lift forces divergent action.

### 7.5 Singular geometry

NHG singularities are failures of structured equivalence: tangent rank loss, non-effective
curvature descent, polarization breakdown, nonclosed completion, or nonproper lifted history.
Their types are not interchangeable, but all occur inside the geometry of (FC.4).

## 8. Structural equations and dynamics

NHG distinguishes identities from dynamics.

1. \(Q^2=0\), the Maurer--Cartan equation, and Bianchi identities are integrability identities.
2. Gauge covariance is an equivalence principle.
3. A cyclic Hamiltonian supplies a formal variational functional when transgression data exist.
4. Coercivity, properness, and a source constitutive relation are additional theorems.

There is no universal scalar field equation. A genuine NHG dynamics is a natural sourced section of
a relative obstruction bundle, or equivalently a gauge-covariant constitutive map

\[
 \mathcal T:J^\infty\alpha\longrightarrow
 \Omega^{\ge2}\bigl(B;\operatorname{Der}_Q\mathcal A\bigr)
\tag{FC.10}
\]

satisfying the higher Bianchi compatibility. It is accepted only if derived from the source law,
a variational principle, or a universal property. Choosing \(\mathcal T\) to fit a target is theatre.

## 9. Route-independent theorem programme

The field's first theorem programme is:

1. **Nomological Gauss--Codazzi--Ricci:** prove (FC.7) and its filtered cyclic derived extension.
2. **Soldered Ambrose--Singer--Spencer:** generate restricted higher holonomy from the relative
   curvature Postnikov tower and effective Spencer jets.
3. **Kolchin--Atiyah comparison:** relate the Kolchin dimension polynomial to ranks and supports of
   relative Atiyah--Spencer classes.
4. **Polar reconstruction:** reconstruct unsquared law tensors from a separating cross-polar
   observer family up to structured compact gauge.
5. **Nomological index theorem:** pair spectral flow of a proper law event with a transgressed
   Atiyah--Spencer/history class.
6. **Proper recurrence theorem:** characterize when recurrent observer histories have precompact,
   holonomic, or infinite-action lifts.

## 10. Falsifiable predictions

1. No genuinely lossy observer can become a gauge after further serial observation.
2. Every finite observer of a hypertranscendental formally smooth law chart has an infinite
   invisible Spencer tail.
3. Flat total law geometry can induce curved observed geometry only through nonzero second
   fundamental law.
4. Parallel positivity exists exactly on compact-holonomy-reducible strata.
5. Closed observer recurrence with open lift is impossible when the vertical law-fibre is compact,
   holonomy is compact, and source-lift action is proper.
6. A scalar positive shadow cannot reconstruct a multidimensional unsquared law tensor; a complete
   cross-polar packet can.
7. Local curvature data never determine flat global monodromy.
8. No scalar invariant can classify the full relative law-fibre across tangent, holonomy,
   prolongation, polarization, and completion horizons.

## 11. Hard acceptance boundary

No external proof corpus may be used to define or repair NHG primitives until the following are
closed internally:

1. structured category and Morita notion;
2. derived observer-fibre construction;
3. nonlinear version of (FC.7);
4. one source-derived constitutive map or proper action;
5. one nontrivial theorem connecting three derived faces of the same relative law-fibre —
   **closed in the flat Cartan model**, which couples holonomy, polarization, recurrence, and
   proper lifted cost;
6. hostile falsification against native, non-arithmetic model geometries.

Only after these gates close may external routes be admitted as tests. They may falsify NHG; they
may not redefine it.
