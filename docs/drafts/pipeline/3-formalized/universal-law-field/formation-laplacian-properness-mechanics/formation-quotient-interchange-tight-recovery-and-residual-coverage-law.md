# Formation--quotient interchange, tight recovery, and residual coverage law

- **Stage:** 3-formalized

- **ID:** `ULF-FLPM-4`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-PROVED]`
- **Type:** THEOREM (Lean)
- **Scope:** Hilbert-space formation mechanics; no RH implication

## 0. Result

Local quotient data do not determine global formation.

A complete orthogonal resolution and its dual polarization produce an exact tight formation
operator

\[
  \mathcal Bx=((P_i x)_i,(Q_i x)_i),
  \qquad \mathcal B^*\mathcal B=2I,
\]

with decoder \(\frac12\mathcal B^*\).  A duality involution swaps the two polarization legs and
conjugates the whole recovery system, so it is information-neutral.

However, replacing each local channel by another channel with the same Calkin support can destroy
the lower frame bound, create an infinite-dimensional common kernel, or even make the assembled
analysis operator undefined.  The obstruction is that formation does not commute with quotienting
by compact operators.  A family of compact local residuals can assemble into a noncompact global
residual.

The exact survivor is a global Gram law.  If the assembled residual \(G\) exists and

\[
  \lVert G\rVert<c
\]

relative to a tight carrier of strength \(c\), then the formed channel has lower bound
\(\sqrt{c-\lVert G\rVert}\) and an explicit decoder.  More generally, compact local information can
repair the formed channel exactly when its Gram has closed range and finite-dimensional kernel and
the local packet is injective on that kernel.

This closes the distinction between:

1. **local Calkin survival** -- every channel is noncompact modulo local compacts;
2. **global formation coverage** -- all channels jointly intercept every escaping direction;
3. **selection** -- a relative defect channel may vanish while the retained carrier stays proper.

Only item 2 is the global producer required by formation/properness mechanics.

## 1. Abstract two-polarization resolution

Let \(H\) be a complex Hilbert space and \(I\) a countable set.  Let
\((P_i)_{i\in I}\) be an orthogonal resolution of the identity:

1. \(P_i=P_i^*=P_i^2\);
2. \(P_iP_j=0\) for \(i\ne j\);
3. for every \(x\in H\),
   \[
     x=\sum_{i\in I}P_i x,
     \qquad
     \sum_{i\in I}\lVert P_i x\rVert^2=\lVert x\rVert^2.
     \tag{1.1}
   \]

Let \(J:H\to H\) be a unitary involution, so \(J^*=J^{-1}=J\), and define

\[
  Q_i=JP_iJ.
  \tag{1.2}
\]

Then \((Q_i)\) is another orthogonal resolution of the identity.

Put

\[
  \mathscr K=\ell^2(I;H)\oplus\ell^2(I;H)
\]

and define the two-polarization formation map

\[
  \mathcal B:H\longrightarrow\mathscr K,
  \qquad
  \mathcal Bx=((P_i x)_i,(Q_i x)_i).
  \tag{1.3}
\]

### Theorem 1.1 -- tight formation and exact recovery

The map \(\mathcal B\) is bounded and satisfies

\[
  \langle \mathcal Bx,\mathcal By\rangle=2\langle x,y\rangle,
  \qquad
  \lVert\mathcal Bx\rVert^2=2\lVert x\rVert^2,
  \qquad
  \mathcal B^*\mathcal B=2I.
  \tag{1.4}
\]

Its range is closed, its kernel is zero, and

\[
  \mathcal L=\frac12\mathcal B^*
  \tag{1.5}
\]

is a bounded left inverse.  Explicitly, on the natural synthesis domain,

\[
  \mathcal L((y_i)_i,(z_i)_i)
  =\frac12\sum_i(P_i y_i+Q_i z_i),
  \qquad
  \mathcal L\mathcal B=I.
  \tag{1.6}
\]

#### Proof

Both resolutions obey Parseval.  Therefore

\[
 \langle\mathcal Bx,\mathcal By\rangle
 =\sum_i\langle P_ix,P_iy\rangle+
   \sum_i\langle Q_ix,Q_iy\rangle
 =2\langle x,y\rangle.
\]

Taking \(x=y\) proves the norm identity and bounded-below estimate.  The adjoint identity follows
from polarization.  A bounded-below operator has zero kernel and closed range, and (1.5) gives
\(\mathcal L\mathcal B=I\).  Formula (1.6) is the adjoint/synthesis formula.  QED.

### Definition 1.2 -- formation Laplacian

For any formed channel \(R:H\to\mathscr Y\), define

\[
  \Delta_R=R^*R.
  \tag{1.7}
\]

The tight carrier has the exact conservation law

\[
  \boxed{\Delta_{\mathcal B}=2I.}
  \tag{1.8}
\]

This is a genuine reconstruction identity, not a scalar analogy: it gives the decoder, the lower
frame bound, closed range, and exact conservation of all inner products.

## 2. Functional-equation action is information-neutral

Define

\[
  \mathcal W((y_i)_i,(z_i)_i)=((Jz_i)_i,(Jy_i)_i).
  \tag{2.1}
\]

### Theorem 2.1 -- duality lift and decoder covariance

The map \(\mathcal W\) is a unitary involution and

\[
  \boxed{\mathcal W\mathcal B=\mathcal BJ,}
  \qquad
  \boxed{\mathcal L\mathcal W=J\mathcal L.}
  \tag{2.2}
\]

Consequently the duality action preserves:

1. the formation Laplacian;
2. the lower and upper frame bounds;
3. the common recovery kernel;
4. all Hilbert distances and Gram matrices;
5. every information functional depending only on the recovered packet or on unitary-invariant
   pair data.

In particular, duality transports formation and recovery but does not manufacture coverage or
erase distinguishability.

#### Proof

Since \(J\) is a unitary involution, so is \(\mathcal W\).  Using \(Q_i=JP_iJ\),

\[
  JQ_i=P_iJ,
  \qquad
  JP_i=Q_iJ.
\]

Hence

\[
 \mathcal W\mathcal Bx=((JQ_ix)_i,(JP_ix)_i)
 =((P_iJx)_i,(Q_iJx)_i)=\mathcal BJx.
\]

Taking adjoints gives \(\mathcal B^*\mathcal W=J\mathcal B^*\), and multiplication by \(1/2\)
gives decoder covariance.  All listed invariances follow.  QED.

### Corollary 2.2 -- compact local packets do not alter global coverage

Let \(A:H\to Y\) be compact and set \(T=(A,\mathcal B)\).  Then

\[
  \lVert Tx\rVert^2\ge 2\lVert x\rVert^2.
  \tag{2.3}
\]

Thus the local packet may add finite or compact information, but global properness is already
carried by \(\mathcal B\).  Under unitary actions \(U,V,\mathcal W\), replacing
\((A,\mathcal B)\) by \((VAU^*,\mathcal W\mathcal BU^*)\) conjugates the decoder and changes no
information bound.

## 3. Literal all-scale Sonin resolution

Fix \(a>0\) and \(r>1\).  On the even subspace of \(L^2(\mathbb R)\), let

\[
  I_n=\{x\in\mathbb R:a r^n<|x|\le a r^{n+1}\},
  \qquad n\in\mathbb Z,
  \tag{3.1}
\]

and let \(P_n\) be multiplication by \(1_{I_n}\).  The annuli are disjoint and cover
\(\mathbb R\setminus\{0\}\), whose omitted point has measure zero.  Hence

\[
  \sum_{n\in\mathbb Z}P_n=I
  \quad\text{strongly},
  \qquad
  \sum_n\lVert P_nx\rVert^2=\lVert x\rVert^2.
  \tag{3.2}
\]

Let \(J\) be the even Fourier unitary and put \(Q_n=JP_nJ\).  Then (1.3)--(2.2) apply.

This is the bilateral completion of the already formalized finite-shell facts:

- disjoint physical shells annihilate;
- finite shell sums telescope;
- finite shell energies satisfy Pythagoras;
- the Fourier unitary transports the same statements to the conjugate polarization.

The bilateral limit uses only monotone convergence for the indicators and Plancherel for \(J\).

### Warning 3.1 -- this carrier alone is not arithmetic

The tight shell carrier is a universal observer resolution.  It proves that a proper carrier is
available, but it does not prove that the arithmetic source generates the retained carrier or that
the RH-bearing relative defect couples to it.  Declaring this generic resolution to be the missing
producer would be tautological.

The nontrivial question is whether the literal source corners assemble with the same global lower
bound.  Pointwise Calkin equivalence is insufficient, as the next section proves.

## 4. Formation does not commute with the compact quotient

Let

\[
  H=\bigoplus_{n\ge0}H_n
\]

where every \(H_n\) is infinite-dimensional.  Let \(S_n\) be the coordinate projection onto
\(H_n\).  Then \((S_n)\) is an orthogonal resolution of the identity and every \(S_n\) is
noncompact.

Choose a unit vector \(e_n\in H_n\) and let \(E_n\) be the rank-one projection onto
\(\mathbb C e_n\).

### Countertheorem 4.1 -- local Calkin coverage can have infinite global kernel

Define

\[
  C_n=S_n-E_n.
  \tag{4.1}
\]

Then:

1. \(C_n=C_n^*=C_n^2\);
2. \(C_n^*C_n-S_n=-E_n\) is rank-one and compact;
3. therefore \([C_n^*C_n]=[S_n]\) in the Calkin algebra for every \(n\);
4. the assembled analysis map \(Cx=(C_nx)_n\) is bounded;
5. nevertheless
   \[
     \ker C=\overline{\operatorname{span}}\{e_n:n\ge0\},
     \tag{4.2}
   \]
   which is infinite-dimensional;
6. the assembled residual is
   \[
     \sum_n(C_n^*C_n-S_n)=-E,
     \tag{4.3}
   \]
   where \(E\) is the projection onto the space in (4.2), so it is noncompact and has norm and
   essential norm one.

#### Proof

Since \(E_n\le S_n\), \(S_n-E_n\) is an orthogonal projection.  The local Calkin identity is
immediate.  Orthogonality gives

\[
  \sum_n\lVert C_nx\rVert^2
  =\lVert x\rVert^2-\sum_n|\langle x,e_n\rangle|^2.
  \tag{4.4}
\]

This vanishes exactly on the closed span of the \(e_n\).  The strong sum of the \(E_n\) is the
infinite-rank projection \(E\), which is noncompact.  QED.

Thus complete local Calkin support does not imply semi-Fredholm formation, finite kernel, or joint
recovery.

### Countertheorem 4.2 -- local Calkin data need not even form a Bessel family

Fix a unit vector \(e\in H_0\), and for each \(n\ge1\) choose a unit vector \(f_n\in H_n\).  Let

\[
  T_nx=\langle x,e\rangle f_n,
  \qquad
  D_n=S_n+T_n
  \quad(n\ge1).
  \tag{4.5}
\]

Then \(D_n^*D_n-S_n\) has finite rank for every \(n\), so again

\[
  [D_n^*D_n]=[S_n]
  \tag{4.6}
\]

locally.  But

\[
  D_ne=f_n,
  \qquad
  \sum_{n\ge1}\lVert D_ne\rVert^2=\infty.
  \tag{4.7}
\]

Therefore \(x\mapsto(D_nx)_n\) is not a bounded analysis operator.

#### Proof

Since \(S_nT_n=T_n\), \(T_n^*S_n=T_n^*\), and \(T_n^*T_n=E_e\),

\[
  D_n^*D_n-S_n=T_n+T_n^*+E_e,
\]

which has finite rank.  Equation (4.7) is immediate.  QED.

### Theorem 4.3 -- diagonal formation of compact residuals retains essential size

Let \(K\ne0\) be compact on a Hilbert space \(H_0\), and let \(U_n,V_n\) be unitaries.  Put

\[
  K_n=V_nKU_n^*.
\]

The diagonal operator

\[
  \mathbf K:\ell^2(\mathbb N;H_0)\to\ell^2(\mathbb N;H_0),
  \qquad
  \mathbf K(x_n)=(K_nx_n),
  \tag{4.8}
\]

is bounded with

\[
  \lVert\mathbf K\rVert=\lVert K\rVert,
  \qquad
  \lVert\mathbf K\rVert_{\mathrm{ess}}=\lVert K\rVert,
  \tag{4.9}
\]

and is noncompact, although every coordinate \(K_n\) is compact.

#### Proof

The norm upper bound follows coordinatewise; unit vectors supported in one coordinate and chosen
near a norming vector for \(K_n\) give equality.  Choose unit \(v\) with \(\lVert Kv\rVert>0\),
and put \(x^{(n)}\) equal to \(U_nv\) in coordinate \(n\) and zero elsewhere.  The sequence
\((x^{(n)})\) is orthonormal, while \(\mathbf Kx^{(n)}\) have disjoint supports and common positive
norm \(\lVert Kv\rVert\).  Hence \(\mathbf K\) is not compact.

For any compact \(C\), pass to a subsequence with \(Cx^{(n)}\to0\).  Then

\[
  \lVert\mathbf K-C\rVert
  \ge\limsup_n\lVert(\mathbf K-C)x^{(n)}\rVert
  =\lVert Kv\rVert.
\]

Taking \(v\) arbitrarily close to norming and using \(C=0\) proves (4.9).  QED.

This is the exact formation--quotient interchange defect:

\[
  \boxed{
  \text{quotient each coordinate, then form}
  \;\ne\;
  \text{form, then quotient}.}
  \tag{4.10}
\]

## 5. Global residual coverage theorem

Let \((S_i)_{i\in I}\) be positive operators on \(H\) with strong sum

\[
  \sum_i S_i=cI,
  \qquad c>0.
  \tag{5.1}
\]

Let \(C_i:H\to Y_i\) be bounded maps.  For finite \(F\subset I\), define the Gram residual

\[
  G_F=\sum_{i\in F}(C_i^*C_i-S_i).
  \tag{5.2}
\]

### Theorem 5.1 -- uniform Gram formation

Assume \(G_F\) converges in the weak operator topology along finite subsets to a bounded
self-adjoint operator \(G\).  Then \((C_i)\) is automatically a Bessel family, the positive
operator \(cI+G\) is its Gram operator, and the analysis operator

\[
  C:H\to\bigoplus_iY_i,
  \qquad Cx=(C_ix)_i
  \tag{5.3}
\]

satisfies

\[
  C^*C=cI+G,
  \qquad
  \sum_i\lVert C_ix\rVert^2
  =c\lVert x\rVert^2+\langle Gx,x\rangle.
  \tag{5.4}
\]

In particular, if

\[
  \lVert G\rVert<c,
  \tag{5.5}
\]

then

\[
  (c-\lVert G\rVert)\lVert x\rVert^2
  \le\sum_i\lVert C_ix\rVert^2
  \le(c+\lVert G\rVert)\lVert x\rVert^2.
  \tag{5.6}
\]

Thus \(C\) is bounded below, has closed range and zero kernel, and has canonical decoder

\[
  \mathcal L_C=(C^*C)^{-1}C^*.
  \tag{5.7}
\]

#### Proof

For every finite \(F\),

\[
  \sum_{i\in F}\lVert C_ix\rVert^2
  =\left\langle\left(\sum_{i\in F}S_i+G_F\right)x,x\right\rangle.
\]

Pass to the directed limit.  The left side is monotone in \(F\), the carrier sum tends strongly
to \(cI\), and the residual tends weakly to \(G\).  This gives (5.4).  In particular

\[
  0\le c\lVert x\rVert^2+\langle Gx,x\rangle
  \le(c+\lVert G\rVert)\lVert x\rVert^2,
\]

so the family is Bessel and \(cI+G\) is positive.  Self-adjointness and (5.5) give

\[
  -\lVert G\rVert I\le G\le\lVert G\rVert I,
\]

which proves (5.6).  The lower bound makes \(C^*C\) positive invertible and gives (5.7).  QED.

### Theorem 5.2 -- finite local repair of a global residual kernel

Assume only that \(C\) in (5.3) is bounded.  Let \(A:H\to Y\) be compact.  Then

\[
  T=(A,C):H\to Y\oplus\bigoplus_iY_i
  \tag{5.8}
\]

is bounded below if and only if:

1. \(\operatorname{ran}C\) is closed;
2. \(\ker C\) is finite-dimensional;
3. \(A|_{\ker C}\) is injective.

Equivalently, the Gram \(cI+G=C^*C\) may lose only finitely many directions, and the compact packet
must separate exactly those directions.  The explicit decoder is the common-kernel decoder of
`ULF-FLPM-3`.

This is strictly stronger than local Calkin noncompactness or positive essential norm.

### Theorem 5.3 -- block-formation semi-Fredholm classification

Let \((H_n)\) and \((Y_n)\) be countable Hilbert families, and let

\[
  T_n:H_n\to Y_n,
  \qquad
  \sup_n\lVert T_n\rVert<\infty.
  \tag{5.9}
\]

The block formation

\[
  \mathbf T=\bigoplus_nT_n:
  \bigoplus_nH_n\longrightarrow\bigoplus_nY_n
  \tag{5.10}
\]

is bounded.  For a bounded operator \(T\), write

\[
  \gamma(T)=inf\{\lVert Tx\rVert:x\in(\ker T)^\perp,\ \lVert x\rVert=1\}
  \tag{5.11}
\]

for its reduced minimum modulus, with the convention \(\gamma(T)=+\infty\) when
\((\ker T)^\perp=0\).  Then:

\[
  \boxed{\ker\mathbf T=\bigoplus_n\ker T_n,}
  \tag{5.12}
\]

\[
  \boxed{
  \operatorname{ran}\mathbf T\text{ is closed}
  \iff\inf_n\gamma(T_n)>0,}
  \tag{5.13}
\]

and

\[
  \boxed{
  \mathbf T\text{ has closed range and finite-dimensional kernel}
  \iff
  \inf_n\gamma(T_n)>0
  \ \text{and}\ 
  \sum_n\dim\ker T_n<\infty.}
  \tag{5.14}
\]

When every kernel is zero, the Moore--Penrose/left inverses \(T_n^\dagger\) assemble to a bounded
decoder exactly when

\[
  \sup_n\lVert T_n^\dagger\rVert
  =\left(\inf_n\gamma(T_n)\right)^{-1}<\infty.
  \tag{5.15}
\]

#### Proof

Equation (5.12) follows coordinatewise.  Its orthogonal complement is

\[
  (\ker\mathbf T)^\perp
  =\bigoplus_n(\ker T_n)^\perp.
\]

If \(\gamma_*:=\inf_n\gamma(T_n)>0\), then for every
\(x=(x_n)\in(\ker\mathbf T)^\perp\),

\[
  \lVert\mathbf Tx\rVert^2
  =\sum_n\lVert T_nx_n\rVert^2
  \ge\gamma_*^2\sum_n\lVert x_n\rVert^2
  =\gamma_*^2\lVert x\rVert^2.
\]

Hence \(\mathbf T\) is bounded below on the kernel complement and has closed range.

Conversely, if \(\mathbf T\) has closed range, it is bounded below by some \(\gamma>0\) on
\((\ker\mathbf T)^\perp\).  Apply this estimate to vectors supported in one coordinate to get
\(\gamma(T_n)\ge\gamma\) for every \(n\), proving (5.13).  Equation (5.14) now follows from
(5.12), because the Hilbert direct sum of the kernels is finite-dimensional exactly when the sum
of their dimensions is finite.  Formula (5.15) is the same reduced-minimum identity applied
coordinatewise.  QED.

### Countertheorem 5.4 -- local Fredholmness has two independent cofinal failures

Let every \(H_n\) be infinite-dimensional, let \(e_n\in H_n\) be unit, and write \(E_n\) for its
rank-one projection.

1. Put \(T_n=I-E_n\).  Then \(T_n-I=-E_n\) is compact and every \(T_n\) has closed range and
   one-dimensional kernel, but \(\bigoplus_nT_n\) has infinite-dimensional kernel.
2. Put
   \[
     R_n=I-(1-1/(n+1))E_n.
   \]
   Then \(R_n-I\) is rank-one, every \(R_n\) is invertible, and every local Calkin class is the
   identity.  Nevertheless
   \[
     \gamma(R_n)=\frac1{n+1}\longrightarrow0,
   \]
   so \(\bigoplus_nR_n\) has nonclosed range and no bounded decoder.

Thus local Fredholmness, zero local index, invertibility of every block, and equality of every
local Calkin class still do not imply global formation properness.

### Corollary 5.5 -- exact source-shell gate

Suppose a source supplies principal shell projections \(S_n\) and positive Gram blocks \(D_n\)
such that

\[
  D_n-S_n\ \text{is compact}.
  \tag{5.16}
\]

On the shell space \(H_n=S_nH\), define the compressed block

\[
  B_n=S_nD_nS_n|_{H_n}:H_n\to H_n.
\]

Each \(B_n\) is identity plus compact and therefore Fredholm; its kernel is finite-dimensional and
its range is closed.  The countable source formation \(\bigoplus_nB_n\) is upper semi-Fredholm
exactly when

\[
  \boxed{
  \inf_n\gamma(B_n)>0,
  \qquad
  \sum_n\dim\ker B_n<\infty.}
  \tag{5.17}
\]

These are the **uniform gap** and **finite exceptional multiplicity** laws.  They are the two
source estimates missing from pointwise Calkin coverage.

## 6. Functional-equation covariance of the global residual

Let \(U:H\to H\) and \(V_i:Y_i\to Y_{\sigma(i)}\) be unitary, where \(\sigma\) permutes \(I\).
Define

\[
  C'_{\sigma(i)}=V_iC_iU^*,
  \qquad
  S'_{\sigma(i)}=US_iU^*.
  \tag{6.1}
\]

### Theorem 6.1 -- information-neutral residual transport

The formed analysis operators and residuals satisfy

\[
  C'=\mathbf VCU^*,
  \qquad
  G'=UGU^*,
  \qquad
  C'^*C'=U(C^*C)U^*.
  \tag{6.2}
\]

Therefore duality preserves formation existence, Bessel and frame bounds, closed range, kernel
dimension, compact distance, residual norm, and decoder conditioning.  It transports a producer
but cannot create one.  This is the global formation counterpart of the common-recovery packet
information-isometry theorem.

## 7. Exact consequence for the Sonin/Calkin frontier

For fixed prime scale \(p>1\) and bilateral apertures \(a_n=ap^n\), the formal corpus proves for
each \(n\) that the one-scale Sonin corner \(L_n\) has local Gram

\[
  L_n^*L_n =_{\mathcal K}
  S_n,
  \qquad
  S_n=P_n+Q_n,
  \tag{7.1}
\]

where \(P_n\) and \(Q_n\) are physical and Fourier shell projections.  It also proves each
residual

\[
  K_n=L_n^*L_n-S_n
  \tag{7.2}
\]

is compact, indeed Hilbert--Schmidt at every fixed aperture.

Equations (4.1)--(4.10) prove that these pointwise facts do **not** imply that

\[
  x\longmapsto(L_nx)_n
  \tag{7.3}
\]

is bounded, semi-Fredholm, or proper.  Nor do they imply that the assembled residual is compact.

The missing source theorem is now exact:

> **Global Sonin formation gate.** Prove that the corner family (7.3) is Bessel and that the
> directed Gram residuals \(\sum_{n\in F}K_n\) converge to a bounded self-adjoint \(G\) for which
> \(2I+G\) has closed range and finite-dimensional kernel. Then prove that the compact arithmetic
> packet is injective on that kernel. A stronger sufficient result is \(\lVert G\rVert<2\).

There is an equivalent shell-block gate.  Compress each local Gram to its principal shell,

\[
  B_n=S_n(L_n^*L_n)S_n|_{S_nH}.
\]

Every \(B_n\) is identity plus compact and hence locally Fredholm.  The block formation is globally
upper semi-Fredholm exactly when

\[
  \inf_n\gamma(B_n)>0,
  \qquad
  \sum_n\dim\ker B_n<\infty.
  \tag{7.4}
\]

Thus the source problem has been reduced to two numerical/operator statements: a uniform reduced
spectral gap and finite total exceptional multiplicity.  Functional equation can only permute and
unitarily conjugate these blocks, so it preserves both conditions.

This is a genuine global formation/properness statement.  It cannot be replaced by:

- nonzero essential norm of each corner;
- pointwise Calkin partial-isometry identities;
- Hilbert--Schmidt membership at every fixed aperture;
- functional-equation symmetry;
- finite-aperture invertibility.

### Fourth-organ prediction

Any other route with finite or compact local packets and a cofinal boundary family must exhibit the
same dichotomy:

1. local compact residuals that are summable/strictly controlled after formation, yielding a
   global frame and decoder; or
2. persistent compact residuals that become a noncompact formation defect, producing an infinite
   hidden kernel or destroying Bessel admission.

Thus the next theorem in Cauchy-seam, recurrence-history, and cofinal jet organs is not merely
"infinitely many reporters exist."  It is a uniform Gram/recovery law of the form (5.4)--(5.8).

## 8. Carrier--defect bifurcation and selection

Suppose \(C\) passes Theorem 5.1 or 5.2 and let \(D_\delta=\delta C\) be a relative defect channel.
Retain both channels:

\[
  \Psi_\delta=(A,C,D_\delta).
  \tag{8.1}
\]

Then global properness is independent of \(\delta\), while

\[
  D_\delta=0\iff\delta=0
  \quad(C\ne0).
  \tag{8.2}
\]

This resolves the apparent conflict between:

- a noncompact retained carrier required for global formation; and
- a compact/zero relative defect required at a selected locus.

They are different channels.  Dropping the retained carrier and keeping only \(\delta C\) makes
properness collapse at \(\delta=0\); retaining \(C\) permits the relative defect to vanish without
information loss.

The remaining RH problem is not to rediscover a carrier.  It is to construct, before zero
specialization, a source-normalized comparison proving that the physical relative defect is the
unique admissible \(D_\delta\) coupled to the globally formed carrier.

## 9. Hostile limits

1. The generic tight resolution is not by itself arithmetic and cannot count as the missing source
   producer.
2. Pointwise compact equivalence is not stable under countable formation.
3. Pointwise Hilbert--Schmidt bounds without a summable/global estimate do not imply Bessel
   formation.
4. Functional equation is an isometry/conjugacy, not a selector.
5. A positive essential norm is only survival modulo compacts; it is not a lower frame bound.
6. The bound \(\lVert G\rVert<c\) is sufficient, not necessary.  The sharp condition is closed
   range with finite kernel, plus finite-kernel separation by the compact packet.
7. No RH implication is claimed until the literal source supplies both the global residual theorem
   and the selected relative comparison.

## 10. Provenance and formal status

Paper proof is dependency-closed.  Fully formalized, unconditionally: see the Lean certificate
below.  Existing Lean parents provide:

- finite shell orthogonality and telescoping;
- finite Pythagorean shell energy;
- local Sonin Calkin partial-isometry identities;
- exact local essential norms;
- fixed-aperture Hilbert--Schmidt residuals;
- packet functional-equation information isometry.

New formal work, all completed (together with the projection lift of the Calkin shell
`P_n + Q_n` used to define the compressed blocks of §7):

1. abstract countable tight-formation decoder;
2. the two formation--quotient countermodels;
3. diagonal compact-family essential norm;
4. global Gram residual theorem;
5. unitary residual covariance.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.TwoPolarizationTightFormation`, `GaloisForLFunctions.HTGeometry.SoninShellTightResolution`, `GaloisForLFunctions.HTGeometry.FormationQuotientCountermodels`, `GaloisForLFunctions.HTGeometry.GlobalGramResidualCoverage`, `GaloisForLFunctions.HTGeometry.BlockFormationSemiFredholm`, `GaloisForLFunctions.HTGeometry.LocalFredholmCofinalFailures`, `GaloisForLFunctions.HTGeometry.ProjectionSumCalkinLift`, `GaloisForLFunctions.HTGeometry.SoninShellBlockGate`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.TwoPolarizationTightFormation` (§§1–2),
`GaloisForLFunctions.HTGeometry.SoninShellTightResolution` (§3),
`GaloisForLFunctions.HTGeometry.FormationQuotientCountermodels` (§4),
`GaloisForLFunctions.HTGeometry.GlobalGramResidualCoverage` (Theorems 5.1, 5.2, 6.1, §8),
`GaloisForLFunctions.HTGeometry.BlockFormationSemiFredholm` (Theorem 5.3 and block covariance),
`GaloisForLFunctions.HTGeometry.LocalFredholmCofinalFailures` (Countertheorem 5.4, Corollary 5.5),
`GaloisForLFunctions.HTGeometry.ProjectionSumCalkinLift` (lift of the Calkin shell projection) and
`GaloisForLFunctions.HTGeometry.SoninShellBlockGate` (§7).  New names live in the
namespace TightFormation under GaloisForLFunctions.HTGeometry (prefix `TightFormation.` below).  Corpus inputs: the even
Sonin carrier and its cutoffs (`RHTower.evenSubspace`, `RHTower.evenIndicatorCutoff`,
`RHTower.evenFourierCutoff`, `RHTower.evenFourierTransform`, `RHTower.evenIndicatorCutoff_mul_min`,
`RHTower.evenFourierCutoff_eq_reflectedCutoff`), dominated convergence for bounded multipliers
(`MeasureTheory.tendsto_lpBoundedMulCLM_apply`), the one-scale corner Gram identity and its
Hilbert--Schmidt residual (`RHTower.evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell`,
`RHTower.evenTwoPolarizationShell_isCalkinProjection`,
`RHTower.centralSoninDilationCornerResidual_isHilbertSchmidt`), the essential norm
(`RHTower.essentialNorm`, `RHTower.essentialNorm_unitaryPush`), the compact--cofinal fusion of
`ULF-FLPM-3` (`compactCofinal_jointlyBoundedBelow_iff`, `exists_commonRecovery_of_cofinalTransducer`,
`carrierDefectPacket`), closed range via transverse lower bounds
(`ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range`), Riesz theory
(`isFredholmOp_one_add_compact`), finite-codimensional contraction sectors of compact operators
(`exists_finiteCodimensional_strictContractionKernel_of_isCompactOperator`) and the shell cross-term
compactness (`RHTower.isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff`).

| Claim | Lean declaration |
|-|-|
| (1.1) orthogonal resolutions of the identity; Parseval `Σ‖P_i x‖² = ‖x‖²` | `TightFormation.ProjectionFamily`, `TightFormation.OrthogonalResolution`, `TightFormation.OrthogonalResolution.hasSum_inner`, `TightFormation.OrthogonalResolution.hasSum_norm_sq` |
| (1.2) `Q_i = J P_i J` is again an orthogonal resolution | `TightFormation.OrthogonalResolution.conj`, `TightFormation.OrthogonalResolution.conj_apply` |
| (1.3) the two-polarization formation `B x = ((P_i x), (Q_i x))` into `ℓ²(I;H) ⊕ ℓ²(I;H)` | `TightFormation.FormationSpace`, `TightFormation.OrthogonalResolution.analysis`, `TightFormation.formation`, `TightFormation.formation_apply` |
| Theorem 1.1, (1.4) `⟨Bx, By⟩ = 2⟨x, y⟩`, `‖Bx‖² = 2‖x‖²`, `B*B = 2I` | `TightFormation.inner_formation`, `TightFormation.norm_sq_formation`, `TightFormation.norm_formation`, `TightFormation.adjoint_formation_comp` |
| Theorem 1.1, (1.5) zero kernel, closed range, decoder `L = ½B*` with `LB = I` | `TightFormation.decoder`, `TightFormation.decoder_formation`, `TightFormation.formation_injective`, `TightFormation.isClosed_range_formation` |
| Theorem 1.1, (1.6) synthesis `L((y_i),(z_i)) = ½ Σ_i (P_i y_i + Q_i z_i)` | `TightFormation.decoder_apply`, `TightFormation.OrthogonalResolution.summable_apply_lp`, `TightFormation.OrthogonalResolution.inner_analysis` |
| Definition 1.2, (1.7)–(1.8) `Δ_R = R*R`, `Δ_B = 2I` | `TightFormation.formationLaplacian`, `TightFormation.formationLaplacian_formation` |
| (2.1) the duality `W((y_i),(z_i)) = ((J z_i),(J y_i))` is a unitary involution | `TightFormation.duality`, `TightFormation.duality_apply`, `TightFormation.duality_involutive`, `TightFormation.norm_dualityLin` |
| Theorem 2.1, (2.2) `WB = BJ`, `B*W = JB*`, `LW = JL` | `TightFormation.duality_formation`, `TightFormation.adjoint_formation_duality`, `TightFormation.decoder_duality` |
| Theorem 2.1, preserved Laplacian, frame bounds, kernel, Gram data and recovered packet | `TightFormation.duality_invariants` |
| Corollary 2.2, (2.3) `‖Ax‖² + ‖Bx‖² ≥ 2‖x‖²`, transport by `(VAU*, WBU*)` with conjugated decoder | `TightFormation.norm_sq_packet_ge`, `TightFormation.transport_packet` |
| (3.1)–(3.2) bilateral annular shells `P_n` on the even subspace: orthogonal family, finite telescoping, strong sum `Σ_n P_n = I`, `Σ_n‖P_n x‖² = ‖x‖²` | `TightFormation.shellRadius`, `TightFormation.physicalShell`, `TightFormation.physicalShellFamily`, `TightFormation.sum_physicalShell`, `TightFormation.tendsto_indicatorCutoff_central_atTop`, `TightFormation.tendsto_indicatorCutoff_central_zero`, `TightFormation.physicalShell_approx`, `TightFormation.soninShellResolution`, `TightFormation.ProjectionFamily.hasSum_of_approx` |
| §3 the even Fourier unitary `J`, `Q_n = J P_n J` = Fourier shells, and (1.3)–(2.2) for the Sonin shells | `TightFormation.evenFourierUnitary`, `TightFormation.evenFourierUnitary_involutive`, `TightFormation.soninShellResolution_conj_apply`, `TightFormation.soninFormation`, `TightFormation.soninShell_tight_formation` |
| §4 setting: coordinate projections `S_n` and unit vectors `e_n` of `⊕_n H_n` | `TightFormation.coordProj`, `TightFormation.coordProj_apply`, `TightFormation.adjoint_coordProj`, `TightFormation.coordUnit`, `TightFormation.orthonormal_coordUnit`, `TightFormation.rankOne`, `TightFormation.isCompactOperator_rankOne`, `TightFormation.adjoint_rankOne` |
| Countertheorem 4.1 (1), (4.1) `C_n = S_n - E_n = C_n* = C_n²` | `TightFormation.calkinChannel`, `TightFormation.calkinChannel_apply`, `TightFormation.isStarProjection_calkinChannel` |
| Countertheorem 4.1 (2)–(3) `C_n*C_n - S_n = -E_n` rank one, compact | `TightFormation.calkinChannel_gram_sub`, `TightFormation.isCompactOperator_calkinChannel_gram_sub` |
| Countertheorem 4.1 (4), (4.4) bounded analysis map, `Σ_n‖C_n x‖² = ‖x‖² - Σ_n|⟨e_n,x_n⟩|²` | `TightFormation.calkinAnalysis`, `TightFormation.calkinAnalysis_apply`, `TightFormation.hasSum_norm_sq_calkinChannel`, `TightFormation.norm_sq_sub_inner_smul` |
| Countertheorem 4.1 (5), (4.2) `ker C` = closed span of the `e_n`, infinite-dimensional | `TightFormation.ker_calkinAnalysis`, `TightFormation.not_finiteDimensional_ker_calkinAnalysis` |
| Countertheorem 4.1 (6), (4.3) `Σ_n (C_n*C_n - S_n) = -E`, `E` the projection onto `ker C`, noncompact, norm and essential norm one | `TightFormation.residualProj`, `TightFormation.hasSum_calkinChannel_gram_sub`, `TightFormation.residualProj_projects`, `TightFormation.residualProj_size` |
| Countertheorem 4.2, (4.5)–(4.6) `D_n = S_n + T_n`, `D_n*D_n - S_n = T_n + T_n* + E_e` finite rank | `TightFormation.crossTerm`, `TightFormation.besselBreakingChannel`, `TightFormation.besselBreakingChannel_gram_sub`, `TightFormation.isCompactOperator_besselBreakingChannel_gram_sub` |
| Countertheorem 4.2, (4.7) `D_n e = f_n`, `Σ‖D_n e‖² = ∞`, no bounded analysis operator | `TightFormation.besselBreakingChannel_apply_e`, `TightFormation.not_bessel_besselBreakingChannel` |
| Theorem 4.3, (4.8)–(4.10) the diagonal of compact blocks `V_n K U_n*`: `‖𝐊‖ = ‖𝐊‖_ess = ‖K‖`, not compact | `TightFormation.conjBlock`, `TightFormation.diagonalFormation`, `TightFormation.isCompactOperator_conjBlock`, `TightFormation.norm_le_norm_diagonalFormation_sub`, `TightFormation.diagonalFormation_essential` |
| §4 compact perturbation lower bound along orthonormal sequences | `TightFormation.le_norm_sub_of_orthonormal`, `TightFormation.le_essentialNorm_of_orthonormal`, `TightFormation.not_isCompactOperator_of_orthonormal` |
| (5.1)–(5.2) carriers with `Σ_i S_i = cI`, Gram residuals `G_F`, weak limit | `TightFormation.gramResidual`, `TightFormation.HasWeakGramLimit`, `TightFormation.inner_gramResidual`, `TightFormation.hasWeakGramLimit_iff` |
| Theorem 5.1, (5.3)–(5.4) Bessel family, `C*C = cI + G`, `Σ_i‖C_i x‖² = c‖x‖² + ⟨Gx,x⟩`, `cI + G ≥ 0` | `TightFormation.hasSum_inner_channel`, `TightFormation.hasSum_norm_sq_channel`, `TightFormation.channel_bessel`, `TightFormation.gramAnalysis`, `TightFormation.gramAnalysis_apply`, `TightFormation.inner_gramAnalysis`, `TightFormation.adjoint_gramAnalysis_comp` |
| Theorem 5.1, (5.5)–(5.7) if `‖G‖ < c`: frame bounds, bounded below, zero kernel, closed range, decoder `(C*C)⁻¹C*` | `TightFormation.channel_frame_bounds`, `TightFormation.isUnit_gram`, `TightFormation.gramDecoder`, `TightFormation.gramAnalysis_proper` |
| Theorem 5.2, (5.8) `(A, C)` bounded below iff `ran C` closed, `ker C` finite-dimensional, `A` injective on `ker C`; Gram form; common-kernel decoder | `TightFormation.IsPacketBoundedBelow`, `TightFormation.isPacketBoundedBelow_iff`, `TightFormation.packetBoundedBelow_iff`, `TightFormation.isClosed_range_adjoint_comp_self`, `TightFormation.isClosed_range_adjoint_comp_self_iff`, `TightFormation.packetBoundedBelow_iff_gram`, `TightFormation.exists_packetDecoder` |
| (5.9)–(5.11) block formation `⊕_n T_n` and the reduced minimum modulus `γ` | `TightFormation.blockFormation`, `TightFormation.blockFormation_apply`, `TightFormation.reducedMinModulus`, `TightFormation.le_reducedMinModulus_iff`, `TightFormation.pos_iInf_reducedMinModulus_iff` |
| Theorem 5.3, (5.12) `ker 𝐓 = ⊕_n ker T_n` and its orthogonal complement | `TightFormation.mem_ker_blockFormation`, `TightFormation.single_mem_ker_orthogonal`, `TightFormation.coord_mem_ker_orthogonal` |
| Theorem 5.3, (5.13) `ran 𝐓` closed iff `inf_n γ(T_n) > 0` | `TightFormation.isClosed_range_blockFormation_iff` |
| Theorem 5.3, (5.14) closed range and finite kernel iff `inf γ > 0` and `Σ_n dim ker T_n < ∞` | `TightFormation.kernelAssembly`, `TightFormation.kernelAssembly_injective`, `TightFormation.finiteDimensional_ker_blockFormation_iff`, `TightFormation.blockFormation_upperSemiFredholm_iff` |
| Theorem 5.3, (5.15) Moore–Penrose inverses, `‖T_n†‖ = γ(T_n)⁻¹`, bounded decoder iff `sup‖T_n†‖ = (inf γ)⁻¹ < ∞` | `TightFormation.moorePenrose`, `TightFormation.moorePenrose_apply_self`, `TightFormation.norm_moorePenrose_le`, `TightFormation.nnnorm_moorePenrose_eq`, `TightFormation.blockDecoder_iff`, `TightFormation.blockDecoder_comp` |
| Countertheorem 5.4 (1) `T_n = I - E_n`: compact perturbation, closed range, one-dimensional kernel; `⊕T_n` infinite kernel | `TightFormation.kernelBlock`, `TightFormation.kernelBlock_local`, `TightFormation.not_finiteDimensional_ker_kernelBlock` |
| Countertheorem 5.4 (2) `R_n = I - (1 - 1/(n+1))E_n`: invertible, Calkin class `I`, `γ(R_n) = 1/(n+1)`; `⊕R_n` nonclosed range, no bounded decoder | `TightFormation.gapBlock`, `TightFormation.gapBlock_inverse`, `TightFormation.gapBlock_local`, `TightFormation.gapBlock_global` |
| Corollary 5.5, (5.16)–(5.17) compressed blocks `B_n = S_n D_n S_n|` are identity plus compact, Fredholm; `⊕B_n` upper semi-Fredholm iff uniform gap and finite exceptional multiplicity | `TightFormation.compressedBlock`, `TightFormation.compressedBlock_sub_one`, `TightFormation.compressedBlock_fredholm`, `TightFormation.sourceShellGate` |
| (6.1) transported channels and carriers `C'_{σ(i)} = V_i C_i U*`, `S'_{σ(i)} = U S_i U*` | `TightFormation.transport_carrier`, `TightFormation.transport_weakGramLimit` |
| Theorem 6.1, (6.2) `C' = VCU*`, `G' = UGU*`, `C'*C' = U(C*C)U*`; preserved frame bounds, residual norm, essential norm, kernel and its dimension, closed range, decoder conditioning | `TightFormation.residual_transport` |
| §5–§7 the uniform gap and finite multiplicity are invariant under unitary conjugation and permutation of blocks | `TightFormation.reducedMinModulus_conj`, `TightFormation.blockConditions_conj`, `TightFormation.cardinal_sum_comp_equiv` |
| (7.1)–(7.2) the one-scale corners `L_n` at `a_n = a pⁿ`: `L_n*L_n - (P_n + Q_n)` compact | `TightFormation.soninCorner`, `TightFormation.fourierShell`, `TightFormation.isCompactOperator_soninCorner_gram_sub`, `RHTower.centralSoninDilationCornerResidual_isHilbertSchmidt` |
| §7 the principal shell: `P_n Q_n` compact, so `S_n = P_n + Q_n` lifts to an orthogonal projection `Π_n` with `Π_n - S_n` compact | `TightFormation.isStarProjection_physicalShell`, `TightFormation.isStarProjection_fourierShell`, `TightFormation.isCompactOperator_physicalShell_comp_fourierShell`, `TightFormation.exists_isStarProjection_compact_sub_add`, `TightFormation.soninShellProjection`, `TightFormation.soninShellProjection_spec`, `TightFormation.starProjection_soninShellSpace` |
| §7 every shell block `B_n = Π_n(L_n*L_n)Π_n|` is identity plus compact, hence locally Fredholm | `TightFormation.isCompactOperator_soninGram_sub_shell`, `TightFormation.norm_soninCorner_le`, `TightFormation.norm_soninGram_le`, `TightFormation.soninShellBlock`, `TightFormation.soninShellBlock_fredholm` |
| (7.4) the shell-block gate: `⊕_n B_n` upper semi-Fredholm iff `inf γ(B_n) > 0` and `Σ dim ker B_n < ∞` | `TightFormation.soninShellFormation`, `TightFormation.soninShellGate` |
| §7 pointwise Calkin facts do not imply Bessel admission, semi-Fredholmness or compact residual | `TightFormation.not_bessel_besselBreakingChannel`, `TightFormation.not_finiteDimensional_ker_calkinAnalysis`, `TightFormation.residualProj_size`, `TightFormation.diagonalFormation_essential` |
| §8, (8.1) `Ψ_δ = (A, C, δC)` bounded below for every `δ` iff `(A, C)` is | `TightFormation.carrierDefect_boundedBelow_iff`, `carrierDefectPacket`, `carrierDefectRecovery_recovers` |
| §8, (8.2) `D_δ = 0` iff `δ = 0`; without the carrier the compact packet is never bounded below on infinite-dimensional `H` | `TightFormation.defect_eq_zero_iff`, `TightFormation.not_boundedBelow_compact` |

Warning 3.1, the global Sonin formation gate in §7 (an open source target), the fourth-organ
prediction, §9 and §10 are commentary and state what is not claimed.

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
