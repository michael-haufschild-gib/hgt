# Universal monodromy Cartier torsion and the Fitting-energy law

- **ID:** `universal-monodromy-cartier-torsion-fitting-energy-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / NEW CORPUS CONSEQUENCE / DERIVED SELECTION GEOMETRY
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED, UNCONDITIONAL] [NOT RH]`
- **Novelty status:** the algebraic ingredients and the broad monodromy-torsion/Fitting/tangent-cone
  package are classical.  The exact Riemann-source/physical/Stokes factorization proved here is not
  stated in the audited corpus.  External priority for that conjunction remains provisional.
- **Parents:**
  - `../../4-publication-ready/riemann-arithmetic-source-dagger-route/main.tex`;
  - `../../4-publication-ready/riemann-source-orientation-transgression/main.tex`;
  - `../../4-publication-ready/polarized-stokes-microlocal-witt-law/submission.tex`;
  - `../../4-publication-ready/riemann-source-modular-superselection/main-universal.tex`.

## 1. Purpose

The latest arithmetic dagger route gives a fibrewise dichotomy.  Its minimal stable boundary is
zero on the critical line and the whole physical two-leg target off it.  The Stokes route gives a
positive reflected energy which vanishes on the same locus, while source-orientation results say
that the unsquared orientation is singular and relative.

This card identifies the scheme-theoretic object whose different shadows are those three facts.
The object is not another divisor carrier.  It is a Cartier torsion module over the universal
monodromy parameter.  Ordinary positive energy is exactly its zeroth Fitting discriminant and
therefore necessarily squares away its orientation.

## 2. Universal two-path family

Let `k` be a field of characteristic zero and put

\[
 R=k[q,q^{-1}],\qquad X=\operatorname{Spec}R=\mathbb G_{m,k},
 \qquad I=(q-1),\qquad H=V(I)\subset X.
\tag{2.1}
\]

Let `U=R^2`.  Define the source reflection, physical paracyclic rotation, and coefficient-faithful
landing by

\[
 \tau(x,y)=(y,x),\qquad T_q(x,y)=(y,qx),\qquad L=c\,\operatorname{id}_U,
\tag{2.2}
\]

where `c in R^x` is a unit.  The two-path defect and its minimal `T_q`-stable boundary are

\[
 \Delta_q=T_qL-L\tau,
 \qquad
 B_{\min}=\operatorname{im}\Delta_q+operatorname{im}(T_q\Delta_q).
\tag{2.3}
\]

Define the **incompatibility module**

\[
                         \mathcal Q=U/B_{\min}.
\tag{2.4}
\]

It is the universal quotient left after imposing the smallest physical boundary which contains
both ordered comparison defects.

## 3. Cartier incompatibility theorem

### Theorem 3.1

With `(2.1)`--`(2.4)`,

\[
 \boxed{
 B_{\min}=I R^2,
 \qquad
 \mathcal Q\cong(R/I)^2.
 }
\tag{3.1}
\]

Consequently

\[
 \operatorname{Ann}_R(\mathcal Q)=I,
 \qquad
 \operatorname{Fitt}_0^R(\mathcal Q)=I^2.
\tag{3.2}
\]

Thus `\mathcal Q` is rank-two Cartier torsion supported exactly on the identity divisor `H`.

### Proof

Direct calculation gives

\[
 \Delta_q(x,y)=c(0,(q-1)x),
 \qquad
 T_q\Delta_q(x,y)=c((q-1)x,0).
\tag{3.3}
\]

Because `c` is a unit, the two ranges are `IRe_2` and `IRe_1`.  Their sum is `IR^2`, proving the
first identity in `(3.1)`.  Quotienting coordinatewise proves the second.

Every element of `\mathcal Q` is killed by `I`, and either standard basis class has annihilator
exactly `I`, proving the annihilator formula.  A presentation is

\[
 R^2\xrightarrow{(q-1)I_2}R^2\longrightarrow\mathcal Q\longrightarrow0.
\tag{3.4}
\]

The determinant of the presentation matrix is `(q-1)^2`; hence the zeroth Fitting ideal is `I^2`.
`QED`

## 4. Regular-reader exclusion and derived-fibre theorem

### Theorem 4.1

Let `P` be an `I`-torsion-free `R`-module.  Then

\[
                      \operatorname{Hom}_R(\mathcal Q,P)=0.
\tag{4.1}
\]

Moreover

\[
 \boxed{
 \operatorname{Ext}^1_R(\mathcal Q,R)\cong\mathcal Q,
 \qquad
 \operatorname{Tor}_1^R(\mathcal Q,R/I)\cong(k)^2.
 }
\tag{4.2}
\]

All higher `Ext` and `Tor` groups computed from `(3.4)` vanish.

### Proof

If `f:\mathcal Q\to P` and `z\in\mathcal Q`, then

\[
 (q-1)f(z)=f((q-1)z)=0.
\]

`I`-torsion-freeness gives `f(z)=0`, proving `(4.1)`.

Multiplication by `q-1` is injective on `R^2`, so `(3.4)` extends to the free resolution

\[
 0\longrightarrow R^2\xrightarrow{(q-1)I_2}R^2
 \longrightarrow\mathcal Q\longrightarrow0.
\tag{4.3}
\]

Applying `Hom_R(-,R)` makes `Ext^1` the cokernel of the same multiplication map, namely
`(R/I)^2=\mathcal Q`.  Tensoring `(4.3)` with `R/I` turns the multiplication map into zero, so its
kernel is `(R/I)^2=k^2`, proving the `Tor_1` formula.  Resolution length one gives the higher
vanishing. `QED`

### Corollary 4.2 — specialization and image do not commute

Let `k_lambda=R/(q-lambda)` for `lambda in k^x`.  The image of the specialized defect is

\[
 B_{\min}(\lambda)=
 \begin{cases}
 0,&\lambda=1,\\
 k_\lambda^2,&\lambda\neq1.
 \end{cases}
\tag{4.4}
\]

However

\[
 B_{\min}\otimes_R k_1
 =I R^2/I^2R^2\cong k^2,
\tag{4.5}
\]

and its map to `U\otimes_R k_1` is zero.  The whole kernel in `(4.5)` is precisely
`Tor_1^R(\mathcal Q,k_1)`.  Hence ordinary specialization sees zero boundary at the identity while
derived specialization retains the complete normal defect.

### Proof

Specializing `(3.3)` replaces `q-1` by `lambda-1`, proving `(4.4)`.  Formula `(4.5)` is the standard
Cartier conormal identity `I/I^2`, twice.  The tensor sequence of `(4.3)` identifies its kernel with
the `Tor_1` group computed in Theorem 4.1. `QED`

## 4A. Literal cyclic source and the unique orientation quotient

The full physical landing in Sections 2--4 has two independent input legs.  The literal cyclic
source is more structured: it already has an anti-diagonal cyclic boundary.  Keeping these two
levels separate is essential.

Let `S` be an `R`-module with involution `\tau_S`, and let

\[
 \varepsilon:S\longrightarrow R
\tag{4A.1}
\]

be a surjective `\tau_S`-invariant trace.  Define the source-pointed landing

\[
 C(x)=\varepsilon(x)e_1,
 \qquad
 L_{\rm src}=cC,
\tag{4A.2}
\]

and put

\[
 \Delta_{\rm src}=T_qL_{\rm src}-L_{\rm src}\tau_S,
 \qquad
 B_{\rm src}=\operatorname{im}\Delta_{\rm src}
              +\operatorname{im}(T_q\Delta_{\rm src}),
 \qquad
 \mathcal Q_{\rm src}=U/B_{\rm src}.
\tag{4A.3}
\]

### Theorem 4A.1 — source-oriented Cartier line

One has

\[
 \Delta_{\rm src}(x)
 =c\varepsilon(x)(-1,q),
 \qquad
 T_q\Delta_{\rm src}(x)
 =cq\varepsilon(x)(1,-1).
\tag{4A.4}
\]

The map

\[
 \phi:U\longrightarrow R/I,
 \qquad
 \phi(x,y)=x+y\pmod I
\tag{4A.5}
\]

induces an isomorphism

\[
 \boxed{\mathcal Q_{\rm src}\cong R/I.}
\tag{4A.6}
\]

Therefore

\[
 \operatorname{Ann}(\mathcal Q_{\rm src})=I,
 \qquad
 \operatorname{Fitt}_0(\mathcal Q_{\rm src})=I,
\tag{4A.7}
\]

\[
 \operatorname{Hom}_R(\mathcal Q_{\rm src},P)=0
\tag{4A.8}
\]

for every `I`-torsion-free `P`, and

\[
 \operatorname{Ext}^1_R(\mathcal Q_{\rm src},R)\cong R/I,
 \qquad
 \operatorname{Tor}_1^R(\mathcal Q_{\rm src},R/I)\cong k.
\tag{4A.9}
\]

At `q=1`, the specialized boundary is exactly the anti-diagonal line and the quotient is one
absolute orientation line.

### Proof

Trace invariance gives `\varepsilon(\tau_Sx)=\varepsilon(x)`.  Applying `(2.2)` to `(4A.2)` proves
`(4A.4)`.  Because the trace is onto and `c,q` are units, `B_{\rm src}` is generated by

\[
 v_1=(-1,q),\qquad v_2=(q,-q).
\tag{4A.10}
\]

Both lie in `\ker\phi`: their coordinate sums are `q-1` and zero modulo `I`.  Conversely, suppose
`(x,y)\in\ker\phi`, so `x+y=(q-1)t`.  Since

\[
 qx+y=(x+y)+(q-1)x
\]

is divisible by `q-1`, the elements

\[
 b={qx+y\over q(q-1)}\in R,
 \qquad
 a=b+{y\over q}\in R
\]

satisfy `av_1+bv_2=(x,y)`.  Thus `\ker\phi=B_{\rm src}`.  Surjectivity of `\phi` proves `(4A.6)`.

The annihilator and Fitting formulas follow from the one-generator resolution

\[
 0\longrightarrow R\xrightarrow{q-1}R
 \longrightarrow\mathcal Q_{\rm src}\longrightarrow0.
\]

The `Hom`, `Ext`, and `Tor` statements follow as in Theorem 4.1.  At `q=1`, both generators in
`(4A.10)` span `k(-1,1)`, leaving the coordinate-sum orientation line. `QED`

### Corollary 4A.2 — physical two-leg versus source orientation

Reduction modulo `I` gives an exact sequence

\[
 0\longrightarrow (R/I)(1,-1)
 \longrightarrow \mathcal Q=(R/I)^2
 \xrightarrow{\;x+y\;}\mathcal Q_{\rm src}=R/I
 \longrightarrow0.
\tag{4A.11}
\]

Thus the physical identity fibre has two legs, while literal cyclic incidence kills the
anti-diagonal and leaves one absolute orientation port.  In particular,

\[
 \operatorname{Fitt}_0(\mathcal Q)
 =\operatorname{Fitt}_0(\mathcal Q_{\rm src})^2=I^2.
\tag{4A.12}
\]

### Proof

The coordinate-sum map on `(R/I)^2` is onto and has anti-diagonal kernel.  The Fitting identity is
Theorem 3.1 together with `(4A.7)`. `QED`

## 5. Reflection orientation and the Fitting-energy identity

Let `\sigma:R\to R` be reflection, `\sigma(q)=q^{-1}`.

### Theorem 5.1

Reflection preserves `I`, acts by `-1` on the conormal line `I/I^2`, and fixes its square.  More
precisely,

\[
 \sigma(q-1)=q^{-1}-1=-q^{-1}(q-1)
              \equiv -(q-1)\pmod{I^2}.
\tag{5.1}
\]

The reflected two-leg energy

\[
 E(q)=-(q-1)(q^{-1}-1)
     =q+q^{-1}-2
     ={(q-1)^2\over q}
\tag{5.2}
\]

satisfies the equality of principal ideals

\[
 \boxed{(E(q))=I^2=\operatorname{Fitt}_0^R(\mathcal Q).}
\tag{5.3}
\]

Thus the positive reflected energy is exactly the Fitting-discriminant shadow of the full
two-leg Cartier incompatibility module.  By Corollary 4A.2, it is also the square of the Fitting
ideal of the literal source orientation line.

### Proof

Equation `(5.1)` follows from the displayed factorization and `q^{-1}=1 mod I`.  Equation `(5.2)`
is direct expansion.  Since `q` is a unit in `R`, `(E(q))=((q-1)^2)=I^2`; Theorem 3.1 supplies the
last equality. `QED`

### Corollary 5.2 — rank-powered central port

For an integer `M>=1`, put

\[
 E_M(q)=q^M+q^{-M}-2={(q^M-1)^2\over q^M}.
\tag{5.4}
\]

In the local ring `R_I`,

\[
 (q^M-1)=(q-1),\qquad (E_M)=I^2.
\tag{5.5}
\]

The induced map on `I/I^2` multiplies the oriented normal coordinate by `M`, while the energy sees
its square.

### Proof

Factor

\[
 q^M-1=(q-1)(1+q+\cdots+q^{M-1}).
\]

The second factor restricts to the nonzero scalar `M` on `H` and is therefore a unit in `R_I` in
characteristic zero.  This proves the ideal statements.  Modulo `I^2`, binomial expansion gives
`q^M-1\equiv M(q-1)\pmod{I^2}`, proving the conormal assertion. `QED`

### Corollary 5.3 — ambidexterity curvature is the source conormal

Let

\[
 K(q)=q-q^{-1}={(q-1)(q+1)\over q}.
\tag{5.6}
\]

In the local ring `R_I`,

\[
 \boxed{
 (K)=I=\operatorname{Fitt}_0(\mathcal Q_{\rm src}),
 \qquad
 (K^2)=(E)=\operatorname{Fitt}_0(\mathcal Q).
 }
\tag{5.7}
\]

More precisely,

\[
 K(q)^2={ (q+1)^2\over q}\,E(q),
\tag{5.8}
\]

and `(q+1)^2/q` is a unit at `q=1`.  Modulo `I^2`,

\[
 K(q)\equiv2(q-1).
\tag{5.9}
\]

Thus the framed source--reporter ambidexterity curvature
`chi-chi^{-1}` is an unsquared generator of the same source Cartier orientation whose
reflection-positive Stokes energy is the squared Fitting shadow.

### Proof

Equations `(5.6)` and `(5.8)` are direct factorizations.  In characteristic zero, `q+1` restricts
to `2` on `H`, hence is a unit in `R_I`.  The ideal identities follow from Theorem 4A.1 and
Theorem 5.1.  Expanding `q^{-1}` modulo `(q-1)^2` proves `(5.9)`. `QED`

### Theorem 5.4 — selection coframe and induced normal metric

The normal-cone algebra of the identity wall is

\[
 \operatorname{gr}_I R
 =\bigoplus_{j\geq0}I^j/I^{j+1}
 \cong k[e],
 \qquad e=[q-1]\in I/I^2.
\tag{5.10}
\]

Reflection acts by

\[
                             \sigma(e)=-e.
\tag{5.11}
\]

The initial normal forms of source curvature and positive energy are

\[
 \operatorname{in}_I(K)=2e,
 \qquad
 \operatorname{in}_I(E)=e^2.
\tag{5.12}
\]

For the rank-powered port,

\[
 \operatorname{in}_I(q^M-1)=Me,
 \qquad
 \operatorname{in}_I(E_M)=M^2e^2.
\tag{5.13}
\]

Thus the literal source supplies an oriented conormal coframe, while the reflected positive
observer receives its induced quadratic normal metric.  The metric is invariant under orientation
reversal and cannot reconstruct the sign of the coframe.

### Proof

Because `R` is regular of dimension one at `I`, each `I^j/I^{j+1}` is generated by the class of
`(q-1)^j`, giving `(5.10)`.  Equation `(5.11)` is Theorem 5.1.  Equations `(5.12)` follow from
`(5.2)` and `(5.9)`, taking the lowest nonzero `I`-adic term.  Corollary 5.2 gives `(5.13)`.
Reflection sends `e` to `-e` and fixes `e^2`, proving the last assertion. `QED`

## 6. Exterior-source and breadth laws

The Cartier theorem explains singularity in the monodromy direction.  The source-orientation and
modular-superselection papers impose two independent constraints: multiplication must remain
vector-valued before scalarization, and countably uniform source response is nonclosable.  Both
have closed abstract forms.

Let `E=ku\oplus W`, let `S:W\to Z` be injective, and define the alternating exterior response

\[
 \beta(au+w,bu+v)=aS(v)-bS(w).
\tag{6.1}
\]

For `\Lambda:Z\to k^m`, put `\omega_\Lambda=\Lambda\beta`.

### Theorem 6.1 — finite-port fracture

If `\Lambda S\neq0`, then

\[
 \operatorname{Rad}\omega_\Lambda=0\oplus\ker(\Lambda S).
\tag{6.2}
\]

If `Lambda S=0`, the radical is all of `E`.  Consequently nondegeneracy requires `Lambda S` to be
injective, and `m<dim W` forces degeneracy.  Every nonzero `omega_Lambda` is intrinsically
two-leg: it cannot be written as a sum of functions of the first and second variables separately.

### Proof

If `(a,w)` is radical, varying `v` in `(6.1)` gives `a Lambda S(v)=0` for every `v`.  When
`\Lambda S\neq0`, this forces `a=0`.  Varying `b` then gives `\Lambda S(w)=0`.  The converse is
immediate.  The zero case is tautological.  Rank-nullity gives the port bound.

For the final claim, `omega_Lambda` vanishes on each coordinate axis.  A separable sum agreeing
with it must therefore have both one-variable pieces constant with opposite constants, hence must
vanish identically. `QED`

### Theorem 6.2 — uniform breadth singularity

Suppose `u wedge w_n` are orthonormal exterior atoms and a linear response `kappa` satisfies

\[
                       \kappa(u\wedge w_n)=c\neq0
\tag{6.3}
\]

for every `n`.  Its norm on the first `N` atoms is exactly `|c|\sqrt N`.  On the finite-support
domain it is nonclosable.

### Proof

The coefficient vector of the restricted functional is `(c,...,c)`, whose Euclidean norm is
`|c|\sqrt N`.  Put

\[
 v_N={1\over N}\sum_{n=1}^N u\wedge w_n.
\]

Then `\|v_N\|=N^{-1/2}\to0`, while `\kappa(v_N)=c`.  The graph therefore contains a sequence tending
to `(0,c)` with `c\neq0`, so the operator is not closable. `QED`

## 7. Exact Riemann/Stokes specialization

The full two-leg theorem becomes the published physical boundary family after the pullback

\[
 q=\delta_n(\rho)=n^{2\operatorname{Re}\rho-1},
 \qquad c=c_\rho\neq0.
\tag{7.1}
\]

Then Corollary 4.2 gives exactly

\[
 B_{\min,\rho}=0\quad\text{if }\operatorname{Re}\rho=\tfrac12,
 \qquad
 B_{\min,\rho}=\mathbb C^2\quad\text{otherwise}.
\tag{7.2}
\]

The literal cyclic source first quotients the anti-diagonal cyclic boundary as in Theorem 4A.1.
Its remaining coordinate-sum orientation has unsquared normal equation

\[
 \operatorname{Res}(D_{n,\rho}x)
 =(q-1)c_\rho\varepsilon_0^{(1)}(x).
\tag{7.3}
\]

The Stokes central determinant replaces `q` by `q^M`.  Corollary 5.2 shows that it has the same
local Cartier support and scales the conormal by physical rank `M`.  Its reflected positive energy
is the Fitting ideal of the corresponding rank-two torsion quotient.

This yields an exact hierarchy:

```text
literal arithmetic residue       (q-1)c epsilon       unsquared, oriented
source orientation sheaf          R/(q-1)               one Cartier port after cyclic boundary
physical two-leg sheaf            (R/(q-1))^2          two reflected legs before source quotient
derived boundary reader           Ext^1 / Tor_1         conormal/base-change record
Stokes reflected energy           (q-1)^2/q            square of source Fitting ideal
regular scalar/Hilbert reader      Hom(Q,P)=0            necessarily blind
```

## 8. What is explained, and what is not

### Unconditional explanatory gain

1. The fibrewise zero/full physical boundary jump is a coherent-family phenomenon: it is the
   specialization of one Cartier torsion sheaf, not an ad hoc dichotomy.
2. Literal cyclic incidence removes the anti-diagonal at the identity fibre and leaves exactly one
   source orientation line.  Physical two-leg and arithmetic source quotients are not conflated.
3. Regular readers fail for an algebraic reason stronger than boundedness: every map from the
   incompatibility module to a torsion-free reader is zero.
4. Singular Bockstein, residue, `Ext`, and `Tor` readers are not optional decorations.  They are
   the natural derived dual and derived fibre of the universal quotient.
5. The positive Stokes/Hodge energy does not provide an independent selector.  It is exactly the
   square of the source-orientation Fitting ideal and therefore records squared normal distance.
6. Reflection reverses the conormal orientation but fixes its Fitting square, explaining why
   unsquared-before-positive and two-oriented-leg rules recur.
7. Breadth nonclosability and depth Cartier torsion are independent axes: the former costs
   `sqrt(N)` across labels; the latter is supported on `q=1` and costs a derived base change.

### Remaining RH-bearing theorem

Nothing above proves that the actual completed-Xi source section factors through `H`, or that the
physical defect is null-homologous in the literal arithmetic cyclic complex.  Under `(7.1)`, that
statement is

\[
 q=1\quad\text{at every divisor point},
\]

which is RH.  The new theorem classifies the only type of object capable of carrying the missing
selection information; it does not manufacture the source boundary which annihilates it.

## 8A. Support-selection no-go and the ambient-dynamics boundary

This section closes a tempting but circular next move: use the derived class itself to force the
Riemann section onto its support.  The class records a collision after it occurs; internal
operations on it cannot select the collision.

### Theorem 8A.1 — arbitrary derived pullback

Let `A` be a commutative `k`-algebra and let `f:\operatorname{Spec}A\to X` correspond to a unit
`u=f^\sharp(q)\in A^\times`.  Then

\[
 Lf^*\mathcal Q_{\mathrm{src}}
 \simeq [A\xrightarrow{\ u-1\ }A],
 \qquad
 Lf^*\mathcal Q
 \simeq [A^2\xrightarrow{\ (u-1)\operatorname{id}\ }A^2],
\tag{8A.1}
\]

with the displayed complexes in cohomological degrees `-1,0`.  Hence

\[
 H^{-1}(Lf^*\mathcal Q_{\mathrm{src}})=\operatorname{Ann}_A(u-1),
 \qquad
 H^0(Lf^*\mathcal Q_{\mathrm{src}})=A/(u-1),
\tag{8A.2}
\]

and the physical groups are two copies of these groups.

In particular, for a field extension `K/k` and a point `q=\lambda\in K^\times`, one has

\[
 Lf_\lambda^*\mathcal Q_{\mathrm{src}}
 \simeq
 \begin{cases}
  0,&\lambda\ne1,\\
  K\oplus K[1],&\lambda=1,
 \end{cases}
\qquad
 Lf_\lambda^*\mathcal Q
 \simeq
 \begin{cases}
  0,&\lambda\ne1,\\
  K^2\oplus K^2[1],&\lambda=1.
 \end{cases}
\tag{8A.3}
\]

#### Proof

Use the free resolution

\[
 0\longrightarrow R\xrightarrow{q-1}R\longrightarrow R/I\longrightarrow0.
\]

Tensoring it with `A` replaces `q-1` by `u-1` and gives `(8A.1)`.  Kernel and cokernel give
`(8A.2)`.  For a field point, multiplication by `\lambda-1` is invertible when `\lambda\ne1`
and is zero when `\lambda=1`.  The physical statement follows from
`\mathcal Q\cong(R/I)^2`.  No flatness assumption is used.  QED.

### Theorem 8A.2 — internal support preservation

Let `\mathscr T_H` be the smallest thick subcategory of `D^b_{\mathrm{coh}}(R)` containing
`\mathcal Q_{\mathrm{src}}` and closed under derived tensor and derived `\operatorname{Hom}` with
perfect `R`-complexes.  Every cohomology module of every object of `\mathscr T_H` is supported on
`H`.  Moreover,

\[
 \operatorname{End}_R(\mathcal Q_{\mathrm{src}})\cong R/I.
\tag{8A.4}
\]

Consequently:

1. an endomorphism, Bockstein, `Ext`, `Tor`, Fitting construction, cone, dual, or perfect twist
   formed only after passage to `\mathcal Q_{\mathrm{src}}` cannot move or enlarge its support;
2. after pullback to a point `q=\lambda\ne1`, every such derived object is zero, so every internal
   equality between its morphisms holds vacuously;
3. requiring an internal class to be nonzero at a field point is equivalent to requiring
   `\lambda=1` and therefore is not an independent selection mechanism.

#### Proof

Outside `H`, `q-1` is a unit and `\mathcal Q_{\mathrm{src}}` localizes to zero.  Localization is
exact and commutes with finite sums, shifts, cones, direct summands, perfect tensor products, and
perfect derived duals.  Induction over the construction of `\mathscr T_H` therefore proves the
support statement.  An `R`-linear endomorphism of `R/I` is determined by the image of `1`; every
element of `R/I` is annihilated by `I`, so every choice is multiplication by a unique element of
`R/I`.  This proves `(8A.4)`.  The three consequences follow from the support statement and
Theorem 8A.1.  Fitting ideals are included only as invariants of the same supported coherent
modules, not as additional derived operations.  QED.

### Corollary 8A.3 — exact anti-circularity at Riemann fibres

At the Riemann specialization `q=\delta_n(\rho)`, the assertion

\[
 Lf_\rho^*\mathcal Q_{\mathrm{src}}\ne0
\tag{8A.5}
\]

is equivalent to `\delta_n(\rho)=1`, hence to
`\operatorname{Re}\rho=\tfrac12`.  Proving `(8A.5)` for every completed-Xi divisor point is RH,
not a route to RH.

Thus the derived selection sheaf is **kinematics**.  Any noncircular dynamics must be defined on
the ambient `R`-family or on a pre-quotient arithmetic source complex and must imply `q-1=0`
while independently preserving a nonzero source witness such as the ordinary-prime trace-one
class.  A law written only in `\operatorname{End}(\mathcal Q_{\mathrm{src}})` or its derived
category cannot do this.

#### Proof

For `n>1`, `\delta_n(\rho)=n^{2\operatorname{Re}\rho-1}=1` exactly when
`2\operatorname{Re}\rho-1=0`.  Apply `(8A.3)`.  QED.

## 9. Falsifiers and hostile audit

The theorem package is falsified by any of:

1. a faithful physical two-leg family with `(2.2)` whose minimal stable boundary is not `IR^2`;
2. a nonzero map from `\mathcal Q` to an `I`-torsion-free reader;
3. a derived identity fibre whose `Tor_1` dimension is not two;
4. a reflected energy whose principal ideal differs from the Fitting ideal after the stated
   central-port pullback;
5. a nonzero scalarized exterior response with fewer ports than `dim W` and zero radical;
6. a bounded or closable uniform-response functional satisfying `(6.3)` on infinitely many
   orthogonal labels.

`[NOVELTY FIREWALL]` Cartier divisors, Fitting ideals, `Ext`, `Tor`, Bockstein maps, Green
splittings, and exterior products are classical.  The candidate-new result is the exact joint
identification `(3.1)`--`(5.3)` for the already constructed Riemann/Stokes source family and the
resulting proof that its positive energy is a determinant shadow of its singular relative class.
This is new corpus knowledge, not yet an external priority claim.

There is a closer classical collision.  Alexander modules already put monodromy torsion over a
Laurent ring, use Fitting ideals to define characteristic varieties, and identify tangent cones at
the identity with resonance data; universal monodromy modules already factor torsion invariants of
many fibres.  Coframe geometry also classically treats a coframe as prior to its induced metric.
Therefore the phrases **monodromy torsion**, **Fitting support**, **identity tangent cone**, and
**coframe before metric** carry no novelty.  Only the exact source-line/physical-extension/
ambidexterity-curvature/Stokes-energy factorization and the no-go in Section 8A survive this
collision as corpus-specific results.

`[ANTI-CIRCULARITY FIREWALL]` Pulling the universal sheaf back along the Xi divisor only
re-expresses the known location question.  A future RH advance must construct a pre-divisor
arithmetic morphism into the `Ext^1` class and prove an independent cyclic boundary identity.  It
may not assume support on `H`, vanishing of `(q-1)`, positivity of the Fitting energy, or survival of
the special fibre.

## 10. Lean formalization

Modules, all under `GaloisForLFunctions/HTGeometry/DerivedSelectionGeometry/` and namespace
`GaloisForLFunctions.HTGeometry.DerivedSelection`:

`IdentityWall`, `TwoPathIncompatibility`, `SourceOrientation`, `SourceNormalEquation`,
`RegularReaderExclusion`, `ReflectionEnergy`, `LocalPort`, `FibreDichotomy`, `ExteriorResponse`,
`FittingPresentation`, `FittingInvariance`, `FittingEnergy`, `TwoTermResolution`, `DerivedFibre`,
`QuotientDerived`, `IncompatDerived`, `NormalDefect`, `DerivedPullback`, `RiemannPullback`,
`SupportSelection`, `NormalCone`.

| Paper item | Lean declaration |
|---|---|
| `(2.1)` | `MonodromyRing`, `monodromyParam`, `wallEquation`, `identityIdeal`, `evalOne`, `ker_evalOne`, `identityFibreEquiv` |
| `(2.2)` | `srcRefl`, `paracyclicRot`, `landing` |
| `(2.3)` | `twoPathDefect`, `rotDefect`, `minStableBoundary` |
| `(2.4)` | `incompatModule` |
| `(3.3)` | `twoPathDefect_apply`, `rotDefect_apply`, `range_twoPathDefect`, `range_rotDefect` |
| `(3.1)` | `minStableBoundary_eq`, `monodromy_minStableBoundary_eq`, `incompatEquiv`, `monodromyIncompatEquiv` |
| `(3.2)` | `annihilator_incompatModule`, `monodromy_annihilator_incompatModule`, `fittingIdealZero_incompatModule` |
| `(3.4)` | `wallSmul`, `range_wallSmul`, `range_wallSmul_eq_minStableBoundary`, `presShortComplex`, `presShortComplex_shortExact` |
| `(4.1)` | `linearMap_eq_zero_of_annihilator_torsionFree`, `hom_incompatModule_eq_zero`, `subsingleton_hom_incompatModule`, `domain_torsionFree` |
| `(4.3)` | `twoTermResolution`, `presResolution` |
| `(4.2)` `Ext` | `extOneIso`, `extOneSmulIso`, `extOneIncompatIso` |
| `(4.2)` `Tor` | `torOneIso`, `torOneSmulIso`, `torOneIncompatIso`, `identityFibreSqKEquiv` |
| `(4.2)` higher vanishing | `isZero_ext_add_two`, `isZero_tor_add_two`, `isZero_extIncompat_add_two`, `isZero_torIncompat_add_two` |
| `(4.4)` | `minStableBoundary_eq_bot_of_eq_one`, `minStableBoundary_eq_top_of_ne_one`, `minStableBoundary_eq_bot_iff`, `minStableBoundary_eq_top_iff` |
| `(4.5)` | `tensor_subtype_minStableBoundary_eq_zero`, `freeBoundaryEquiv`, `boundaryTensorEquiv`, `boundaryTensorIsoTorOne` |
| `(4A.1)`--`(4A.3)` | `srcLanding`, `srcDefect`, `srcRotDefect`, `srcBoundary`, `srcIncompatModule`, `exists_srcData` |
| `(4A.4)` | `srcDefect_apply`, `srcRotDefect_apply` |
| `(4A.10)` | `range_srcDefect`, `range_srcRotDefect` |
| `(4A.5)`, `(4A.6)` | `coordSum`, `mem_ker_coordSum`, `srcBoundary_eq_ker_coordSum`, `srcIncompatEquiv` |
| `(4A.7)` | `annihilator_srcIncompatModule`, `fittingIdealZero_srcIncompatModule` |
| `(4A.8)` | `hom_srcIncompatModule_eq_zero`, `subsingleton_hom_srcIncompatModule` |
| `(4A.9)` | `extOneSrcIso`, `torOneSrcIso`, `identityFibreKEquiv`, `isZero_extSrc_add_two`, `isZero_torSrc_add_two` |
| Thm 4A.1, identity fibre | `srcBoundary_eq_antidiagonal_of_eq_one` |
| `(4A.11)` | `wallSquare_le_ker_coordSum`, `coordSumQuot`, `coordSumQuot_surjective`, `antidiagonal`, `antidiagonal_injective`, `ker_coordSumQuot` |
| `(4A.12)` | `fittingIdealZero_incompatModule_eq_sq` |
| `(5.1)` | `monodromyRefl_wallEquation`, `monodromyRefl_mem_identityIdeal`, `monodromyRefl_wall_add_mem_sq`, `wallConormalClass`, `toCotangent_monodromyRefl_wall` |
| `(5.2)` | `reflEnergy`, `mul_reflEnergy`, `reflEnergy_eq`, `monodromyEnergy`, `monodromyRefl_energy` |
| `(5.3)` | `reflEnergy_mem_sq`, `span_reflEnergy_eq`, `span_monodromyEnergy_eq`, `span_monodromyEnergy_eq_fittingIdealZero` |
| `(5.4)` | `monodromyEnergyPow`, `mul_reflEnergy_pow`, `monodromy_mul_energyPow`, `span_monodromyEnergyPow_eq` |
| `(5.5)` | `wallEquation_mul_portCofactor`, `evalOne_portCofactor`, `identityIdeal_isMaximal`, `portCofactor_notMem_identityIdeal`, `span_pow_sub_one_localized`, `span_energyPow_localized` |
| `(5.6)`, `(5.8)` | `ambiCurvature`, `ambiCurvature_eq`, `mul_ambiCurvature_sq`, `monodromy_mul_curvature_sq` |
| `(5.7)` | `span_curvature_localized`, `monodromyParam_add_one_notMem_identityIdeal` |
| `(5.9)` | `ambiCurvature_sub_two_wall`, `monodromyCurvature_sub_two_wall_mem_sq` |
| `(5.10)` | `filtSub`, `gradedPiece`, `inI`, `gradedMul`, `pieceGen`, `ker_pieceGen`, `pieceEquiv`, `pieceEquiv_mul`, `normalConePieceEquiv` |
| `(5.11)` | `inI_monodromyRefl_wall` |
| `(5.12)` | `inI_curvature`, `inI_energy` |
| `(5.13)` | `inI_pow_sub_one`, `inI_energyPow` |
| initial forms nonzero | `not_isUnit_wallEquation`, `inI_wall_ne_zero` |
| `(6.1)`, `(6.2)` | `extResponse`, `scalarResponse`, `ker_scalarResponse`, `ker_scalarResponse_of_comp_eq_zero`, `ker_scalarResponse_ne_bot_of_finrank_lt`, `comp_eq_zero_of_separable` |
| `(6.3)` | `abs_apply_le`, `abs_apply_sum_range`, `breadthVector`, `apply_breadthVector`, `breadthVector_tendsto_zero`, `graph_mem_closure`, `not_continuous` |
| `(7.1)` | `riemannSpecial`, `specializeHom`, `specializeHom_monodromyParam`, `exists_riemann_specialization` |
| `(7.2)` | `riemannSpecial_eq_one_iff`, `minStableBoundary_riemann_eq_bot_iff`, `minStableBoundary_riemann_eq_top_iff` |
| `(7.3)` | `coordSum_srcDefect` |
| `(8A.1)`, `(8A.2)` | `smul_ideal_eq_span`, `tensorPullbackEquiv`, `mem_ker_smul_algebra_iff`, `torOnePullbackIso`, `isZero_torPullback_add_two` |
| `(8A.3)` field points | `ker_smul_field_eq_bot`, `ker_smul_field_eq_top`, `span_sub_one_eq_top`, `span_sub_one_eq_bot`, `derivedPullback_nontrivial_iff` |
| `(8A.4)` | `end_apply_eq_mul`, `endQuotEquiv` |
| Thm 8A.2 support | `smul_eq_zero_sub`, `smul_eq_zero_quotient`, `smul_eq_zero_prod`, `smul_eq_zero_pi`, `smul_eq_zero_tensor_left`, `smul_eq_zero_tensor_right`, `smul_eq_zero_hom_source`, `smul_eq_zero_hom_target`, `smul_eq_zero_quotRange`, `smul_eq_zero_kerSmul`, `subsingleton_localizedModule`, `subsingleton_localizedModule_atPrime` |
| Cor 8A.3 | `riemann_pullback_nontrivial_iff` |

New reusable infrastructure built for this card, absent from mathlib:

- **Zeroth Fitting ideal of a module.**  `presDetIdeal` (determinant ideal of a finite generating
  family), `presDetIdeal_extendGen`, `presDetIdeal_reindexGen`, `presDetIdeal_eq_of_surjective`
  (presentation independence), `fittingIdealZero`, `fittingIdealZero_eq_presDetIdeal`,
  `fittingIdealZero_congr`, `fittingIdealZero_quotient`, `fittingIdealZero_quotient_sq`.
- **Two-term projective resolutions.**  `twoTermCplx`, `twoTermPi`, `twoTermResolution`: a short
  exact sequence with projective left terms is a length-one projective resolution of its cokernel;
  `presShortComplex`, `presResolution` specialise this to a presentation of modules.
- **Derived functors from a two-term resolution.**  `homologyIsoQuotRange`, `homologyIsoKer`,
  `kerEquivOfComp`, `extOneIso`, `isZero_ext_add_two`, `torOneIso`, `isZero_tor_add_two`, and the
  regular-scalar specialisations `extOneSmulIso`, `torOneSmulIso`, `extCongrLeft`, `torCongrLeft`.
- **Associated graded ring of an ideal filtration.**  `filtSub`, `gradedPiece`, `inI`,
  `gradedMulPre`, `gradedMulLeft`, `gradedMul`, together with `pieceEquiv` and `pieceEquiv_mul`
  identifying `gr_I R` with `(R ⧸ I)[e]` for a principal ideal generated by a regular element.

Every numbered statement of the card is unconditional in Lean.  The only hypotheses carried by the
declarations are the data of the family itself — `c` a unit, `q` a unit, the trace `ε` surjective
and `τ_S`-invariant, `q-1` regular, characteristic zero where the card uses it — and each of these
is discharged on the universal monodromy line by `isUnit_monodromyParam`, `exists_srcData`,
`monodromy_isSMulRegular` and the `CharZero` instance.  `#print axioms` on every declaration in the
table reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] universal two-path family and its minimal stable boundary
- [x] Cartier incompatibility theorem `(3.1)`--`(3.2)`
- [x] regular-reader exclusion `(4.1)`, `(4A.8)`
- [x] derived dual and derived fibre `(4.2)`, `(4A.9)`, `(4.5)`
- [x] literal cyclic source and its unique orientation quotient `(4A.6)`--`(4A.12)`
- [x] reflection orientation and the Fitting-energy identity `(5.1)`--`(5.3)`
- [x] rank-powered central port and ambidexterity curvature `(5.4)`--`(5.9)`
- [x] selection coframe and induced normal metric `(5.10)`--`(5.13)`
- [x] exterior-source and breadth laws `(6.1)`--`(6.3)`
- [x] exact Riemann/Stokes specialization `(7.1)`--`(7.3)`
- [x] support-selection no-go `(8A.1)`--`(8A.4)`
- [x] Lean formalization
- [ ] RH

## Log

- 2026-08-09 — paper proof completed; card entered stage 2.
- 2026-08-09 — full unconditional Lean layer built and umbrella-wired; twenty-one modules under
  `HTGeometry/DerivedSelectionGeometry/`.  Four reusable layers absent from mathlib were
  constructed on the way: zeroth Fitting ideals with presentation independence, two-term
  projective resolutions, `Ext`/`Tor` computed from them, and the associated graded ring of an
  ideal filtration.  Card promoted to stage 3.
