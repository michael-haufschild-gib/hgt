# Flat Cartan holonomy, recurrent observation, and open polar-history law

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [NATIVE NHG MODEL] [FOUR-FACE COUPLING]
  [HOLONOMY] [POLARIZATION] [RECURRENCE] [PROPER COST]
  [NOT RH] [NO LEAN WRITTEN OR BUILT]

## 1. Setup

Let

\[
 B=
 \begin{pmatrix}
  1&0\\
  0&-1
 \end{pmatrix},
 \qquad
 J=
 \begin{pmatrix}
  0&1\\
  1&0
 \end{pmatrix},
 \qquad
 g_s=e^{sJ}=
 \begin{pmatrix}
  \cosh s&\sinh s\\
  \sinh s&\cosh s
 \end{pmatrix}.
\tag{CHR.1}
\]

Then \(g_s^TBg_s=B\). Let \(V=\mathbb R^2\) with cyclic quadratic form \(B\). On the trivial
bundle \(E=S^1\times V\), with coordinate \(\phi\in\mathbb R/\mathbb Z\), define

\[
 \nabla^a=d-aJ\,d\phi.
\tag{CHR.2}
\]

Its holonomy around the positive generator of \(S^1\) is \(g_a\).

Let \(\theta_0=B\) and

\[
 \theta_u=g_u\theta_0g_u^{-1},
 \qquad u\in\mathbb R.
\tag{CHR.3}
\]

Each \(\theta_u\) is a Cartan involution for \(B\), and

\[
 G_u(v,w)=B(v,\theta_uw)
\tag{CHR.4}
\]

is positive definite.

## 2. Theorem

### Theorem 2.1 — one field, four derived faces

For every \(a\in\mathbb R\):

1. \(\nabla^a\) is flat.
2. Its global holonomy is the cyclic subgroup
   \[
   \operatorname{Hol}(\nabla^a)=\langle g_a\rangle.
   \tag{CHR.5}
   \]
3. Parallel transport acts on the Cartan-polarization line by
   \[
   g_a\theta_ug_a^{-1}=\theta_{u+a}.
   \tag{CHR.6}
   \]
4. A parallel positive polarization exists if and only if \(a=0\).
5. If \(a\neq0\), the observed quotient
   \[
   \mathcal P_a=\mathbb R/a\mathbb Z
   \tag{CHR.7}
   \]
   is a compact circle. The history \(u_n=u_0+na\) projects to a closed, hence recurrent,
   observer history, while its marked lift escapes to infinity.
6. With the normalized invariant line metric \(du^2\), the lifted path
   \(u(t)=u_0+at\) has length \(|a|T\) and quadratic local action
   \[
   \mathcal A_a(T)=\int_0^T|\dot u(t)|^2\,dt=a^2T.
   \tag{CHR.8}
   \]
   Thus repeated closed observer loops have divergent lifted length and action.
7. Relative to the initial polarization \(u_0=0\), the positive metric at \(u\) has eigenvalues
   \(e^{2u}\) and \(e^{-2u}\), so
   \[
   \operatorname{cond}(G_u)=e^{4|u|}.
   \tag{CHR.9}
   \]
   Along the lifted recurrent history, polar conditioning diverges exponentially.

Hence local curvature vanishes while global holonomy, polarization obstruction, recurrent quotient,
open lifted history, and divergent proper cost are all nontrivial faces of one law bundle.

## 3. Proof

Because the base is one-dimensional,

\[
 R_{\nabla^a}=d(-aJ\,d\phi)+(-aJ\,d\phi)\wedge(-aJ\,d\phi)=0.
\]

The parallel equation is \(\dot v-aJv=0\), so transport through one turn is \(e^{aJ}=g_a\).
This proves (1) and (2).

The boosts commute. Therefore

\[
 g_a\theta_ug_a^{-1}
 =g_{a+u}\theta_0g_{-(a+u)}
 =\theta_{u+a}.
\]

The map \(u\mapsto\theta_u\) is injective. A parallel polarization is a fixed point of the
holonomy action, so it exists exactly when \(a=0\). This proves (3) and (4).

For \(a\neq0\), translation by \(a\) acts properly and cocompactly on \(\mathbb R\), giving the
circle (CHR.7). Every \(u_n\) has the same image, while \(|u_n|\to\infty\). Formula (CHR.8) follows
from \(\dot u=a\).

Direct multiplication gives

\[
 B\theta_u=
 \begin{pmatrix}
  \cosh(2u)&-\sinh(2u)\\
  -\sinh(2u)&\cosh(2u)
 \end{pmatrix}.
\tag{CHR.10}
\]

Its eigenvalues are \(e^{2u}\) and \(e^{-2u}\), proving (CHR.9).

## 4. Structural consequences

### 4.1 Local curvature does not determine global law history

All connections \(\nabla^a\) have zero curvature, but their marked holonomy and polar dynamics
depend on \(a\). Any local field theory that discards global monodromy is incomplete.

### 4.2 Positivity is a holonomy reduction

The positive-polarization fibre is contractible, so an unstructured section exists. The obstruction
is not ordinary topology. It is parallel and equivariant selection: noncompact boost holonomy has
no fixed Cartan phase.

### 4.3 Recurrence is relative

The observer history closes only after quotienting by vertical holonomy. Its marked lift is open.
Thus recurrence is not a property of a trajectory alone; it is a property of an observer map and a
choice of retained history marking.

### 4.4 Properness makes escape measurable

The function \(u\mapsto u^2\) is proper on the lifted polarization line. Therefore compact observed
history with unbounded lift necessarily crosses unbounded polar cost. This is the simplest exact
NHG proper-recurrence model.

## 5. Sharp scope

1. This is a flat global-holonomy model, not a local-curvature model.
2. The quotient (CHR.7) is part of the observer definition. The unquotiented history is not
   recurrent.
3. A different cost need not scale as (CHR.8); the theorem uses the invariant quadratic line
   metric.
4. Compact holonomy would admit a fixed Cartan reduction after conjugation; the noncompact boost is
   load-bearing.
5. No claim is made that every recurrent observation has an open lift. Proper compact fibres give
   the opposite behaviour.
6. No arithmetic, spectral-zero, black-hole, wormhole, or endpoint interpretation is used.

## Lean formalization status

- **Status:** `[LEAN IMPLEMENTED] [LEAF CHECK PASSED] [FINAL AXIOM/UMBRELLA AUDIT PENDING]`
- **Pipeline location:** unchanged in Stage 2, per explicit instruction; this card has not been moved.
- **Module:**
  `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/FlatCartanHolonomy.lean`
- **Formalized content:** split cyclic form; Lorentz boost linear equivalences and additive
  one-parameter law; exact preservation of the split form; constant one-dimensional Cartan
  connection curvature; boost parallel-transport equation and one-turn endpoint; circle monodromy
  representation and exact cyclic holonomy range; Cartan involutions, transport law, injective
  polarization parameter, and fixed-point obstruction; positive-definite polarized metric with
  exact expanding/contracting eigenlines; spectral condition number `exp (4 * |u|)`; compact
  additive-circle quotient; closed observed history with escaping marked lift; interval-integral
  length and quadratic action formulas and their divergence; exponential conditioning divergence;
  closed capstone `flatCartan_fourFaceLaw` collecting all seven faces for every `a ≠ 0`.
- **Verification:**
  `lake env lean GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/FlatCartanHolonomy.lean`
  completed in foreground with exit code `0` and no warnings.
- **Remaining audit:** final umbrella `lake build` and `#print axioms` audit are intentionally
  deferred to the repository-wide final audit required by the task.
