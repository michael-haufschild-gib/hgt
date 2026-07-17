# HT capacity-field Ward holonomy and the four-unit RH bound

- **ID:** `ht-capacity-ward-holonomy-rh`
- **Stage:** 1-in-progress
- **Type:** `[BOLD CONJECTURE] [GENERAL HT GEOMETRY -> RH] [ANTI-CAUSAL WARD ROUTE]`
- **Scientific status:** `[CONJECTURE] [BOTH ENDS PROVED] [EXCEPTIONAL GREEN--HODGE TRANSGRESSION OPEN] [NOT SONIN] [NOT RH YET]`
- **General HT inputs:**
  - `../2-fully-proven/new_scientific_knowledge/hypertranscendental-clock-capacity-innovation-theorem.md`;
  - `derived-self-dual-clock-splitting-stack.md`;
  - `self-dual-decorated-clock-boundary.md`;
  - `source-polarized-laurent-pluecker-tangent-ward-law.md`;
  - `../3-formalized/cofinal-cholesky-carrier-selection-threshold-law.md`;
  - `source-anomaly-boundary-colligation-field.md`;
  - `../3-formalized/mobius-gamma-contact-transgression-four-unit-charge.md`;
  - `../3-formalized/mobius-mellin-gamma-normal-cone.md`;
  - `../2-fully-proven/mobius-pluecker-normal-cone-diagonal-lift.md`;
  - `../2-fully-proven/ht-exceptional-divisor-hardy-green-metric.md`.
- **Zeta inputs:**
  - `../2-fully-proven/squarefree-euler-modular-corona-curvature-colligation.md`;
  - `../2-fully-proven/squarefree-fixed-current-right-half-ward-localization.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/infinitesimal-euler-leakage-cauchy-energy-threshold.md`;
  - `../3-formalized/not_new_scientific_knowledge/ccm-complex-polar-prime-mellin-colligation.md`.

## The conjecture

The completed squarefree Euler source carries two positive-coordinate systems which are not related
by an ordinary bounded operator.

1. The **safe Fisher chart** is the positive squarefree Gibbs determinant line.  Its calibrated
   tangent has limiting squared norm exactly four.
2. The **continued corona chart** is the right-half-plane Hardy Cauchy frame of the completed fixed
   current.  Its normal boundary vector is the strict anti-causal profile `ell_E`.

The two charts are representations of one source-calibrated HT capacity field.  Analytic
continuation is the nontrivial transition between them.

The current decisive form is not an ordinary operator colligation, mapping-cone cohomology, or a
Quillen determinant-line norm.  The finite squarefree determinant line is an exterior-horizon
occupation line, and its Fisher vector is the orthogonal one-quasiparticle Pluecker tangent.  At
the Euler boundary the normalized states leave every fixed vacuum Fock representation while the
critically rescaled tangent keeps exactly four units of norm.  The Laurent residue central
extension must transport that tangent through the source-rigged Tate boundary and split it into
causal and anti-causal one-particle components.

The full general-HT conjecture and its falsifiers are in
`source-polarized-laurent-pluecker-tangent-ward-law.md`.  Its squarefree specialization is

```text
Hol_sq^Pl(chi_sq^crit)=c_sq directSum P_anti Q_sq,
4=||c_sq||^2+||P_anti Q_sq||_2^2.                        (0)
```

Since `P_anti Q_sq=ell_E` is proved, `(0)` is the anti-causal Ward estimate and yields RH.  The
older anomaly-cone, depth-one, Hodge, and Quillen formulations below are retained as attacks which
force the Pluecker--Tate form; none is the live carrier by itself.

The topology-to-current identification is now exact and is anchored to the unconditional
hypertranscendence theorem for zeta:

```text
d log(-zeta^(-2))=2A
  -> Q_Xi=Q_arch+2A
  -> Q_sq=Q_Xi-4A(2s).                                   (0a0)
```

The first chart is the genuine reciprocal projective horizon of the HT source.  Gamma completion
supplies the self-dual Hardy orientation and reallocates the known Euler pole; the last correction
is strict-right holomorphic and supplies the positive squarefree capacity chart.  Put

```text
X_sq=Xi/zeta(2s),       u_sq=X_sq^(-1).
```

The direct and reciprocal projective HT horizons have transition `u_sq'/X_sq'=-X_sq^(-2)`, and

```text
d log(-X_sq^(-2))=Q_sq,
P_anti d log(-X_sq^(-2))=ell_E.                           (0a)
```

This is proved in
`../2-fully-proven/not_new_scientific_knowledge/projective-reciprocal-horizon-ward-seam.md`, with
the differential-field core in `RHTower/ProjectiveHorizonWardSeam.lean`.  Therefore the open step
is no longer to guess which HT topological class maps to the Ward current.  It is to construct the
source-rigged boundary trace of the escaping Pluecker tangent and prove that harmonic projection
of the proved seam `(0a)` is nonexpansive from the four-unit capacity metric to Hardy `L2`.

The Hardy-side trace is already a source-defined extended positive quantity:

```text
T_HT(g_sq)
 =limsup_(u downarrow 0)u^(-1)||Q_u H_(d log g_sq)||_(S_2)^2
 =||ell_E||_2^2.                                         (0b)
```

Thus only its Pluecker-capacity lift and the comparison `T_HT(g_sq)<=4` remain open.

The source/Gamma comparison is now exact without identifying their variables.  Mellin--Gaussian
radialization sends the critical score to

```text
F_rad(s)=(2-s)Gamma_R(s)
        =2[Gamma_R(s)-pi Gamma_R(s+2)].                  (0c)
```

On this distinguished vector, inverse completion cancels the Gamma factor and leaves

```text
F_rad(s)/C(s)=-4/s+2/(s-1).                              (0d)
```

The anti pole in `(0d)` has exactly four units of Hardy energy.  This replaces the earlier formal
Gamma-conormal cross-pair, which did not supply a source-natural map.

The completed Möbius transfer itself vanishes at the Euler boundary.  Its deformation-to-the-
normal-cone is

```text
T_tilde_sigma(s)=T_sigma(s)/(sigma-1)
                =1/[G(sigma)X_sq(s)],
G(sigma)=(sigma-1)zeta(sigma),
T_tilde_1(s)=X_sq(s)^(-1).                               (0e)
```

Thus `(0a)` is the projective connection of the exceptional section in `(0e)`.  Lean also proves
that the two-variable family is separated rank one, so all finite base--spectral mixed curvature
vanishes.  Moreover ordinary Fubini--Study/Jensen geometry has the wrong singular scale: a divisor
point approaching the critical line has vanishing Jensen charge but divergent Hardy--Green
energy.  The Ward vector must therefore be the **exceptional Laurent-corona transgression** of a
positive Pluecker/Rees capacity extension; it cannot be a finite cap product, ordinary curvature,
or Poincare--Lelong mass.

The exceptional section itself is already reached by actual finite source objects: along a nested
cofinal prime-aperture / pole-collision diagonal, the rescaled finite reciprocal Pluecker transfers
converge locally uniformly on `Re s>1` to `1/Z_sq(s)`, and after Gamma completion to
`X_sq(s)^(-1)`.  The remaining theorem is therefore metric continuation of a constructed finite
lift, not existence of an analytic exceptional section.

> **[CONJECTURE -- HT EXCEPTIONAL GREEN--HODGE HOLONOMY]** The exact Euler--Gamma source selects a
> positive closable Rees/Tate capacity extension of the squarefree Pluecker line across `(0e)`.
> Its exceptional Laurent-corona transgression sends the critical Fisher tangent to
> `c_sq directSum ell_E`; the induced dual Hardy--Green form is nonexpansive on this distinguished
> source section.

This is not a claim that analytic continuation is a bounded map on an ambient coefficient or
Hilbert space.  It is a one-section metric statement in the descended capacity field.  In every
finite Cauchy chart it says that one explicit augmented response matrix is positive semidefinite.

## Finite Cauchy coordinates

Let

```text
H_-=L2(0,infinity),
k_w(t)=exp(-conj(w)t),                 Re(w)>0,
G_P(i,j)=<k_(w_j),k_(w_i)>
        =1/(w_i+conj(w_j)).                                  (1)
```

For a finite packet `P=(w_1,...,w_N)` of distinct right-half-plane nodes, let

```text
r_P(i)=<k_(w_i),P_anti Q_sq>,                                (2)
```

where `Q_sq` is the completed squarefree logarithmic current and `P_anti` is defined by the
source-framed Hardy contour.  Formula `(2)` is constructed from `Q_sq`; no zero list occurs in the
definition.  Right-half Ward localization already proves

```text
P_anti Q_sq=P_anti Q_Xi=ell_E.                               (3)
```

The minimum squared norm of a vector with response packet `r_P` is

```text
kappa_P=r_P^* G_P^(-1) r_P.                                 (4)
```

Equivalently,

```text
kappa_P<=4
iff
W_P=[[G_P,r_P],[r_P^*,4]] is positive semidefinite.          (5)
```

The matrices `G_P` are not auxiliary.  The complex polar--prime Mellin colligation already
reconstructs every entry from the resolved von Mangoldt Gram, the shifted polar boundary, and the
critical Mellin defect.  Thus `(5)` is a finite source inequality once the last row is constructed
by the same colligation.

The cofinal Cauchy packets form a complete clock.  The general HT capacity--innovation theorem
then gives

```text
sup_P kappa_P=||ell_E||_2^2.                                (6)
```

Here the supremum is over a nested total Cauchy frame, or equivalently over all finite packets.
Equation `(6)` is the RKHS minimum-response theorem expressed in the intrinsic coherent
inverse-Cholesky coordinates of the HT clock.

## RH deduction

The source Fisher theorem gives

```text
lim_(sigma downarrow 1)||chi_sigma||^2=4.                   (7)
```

HT Ward holonomy gives, for every finite packet,

```text
kappa_P<=4.                                                 (8)
```

Equations `(6)`--`(8)` imply

```text
||ell_E||_2^2<=4.                                           (9)
```

The proved Cauchy threshold says that one off-line Xi zero already contributes strictly more than
four.  Hence `(9)` excludes every strict right-half zero and proves RH.

The proof chain is therefore

```text
general HT capacity innovations and complete Cholesky topology
  + source-calibrated self-dual splitting
  -> nonexpansive Ward holonomy on the distinguished section
  -> every finite continued Cauchy capacity <=4
  -> complete corona boundary ell_E has norm^2<=4
  -> RH.                                                     (10)
```

## Why this is topology and geometry of HT

The safe and continued objects agree at every finite algebraic clock order but need not agree
after completion.  The completed current is therefore not another scalar observable; it is the
holonomy of the capacity field around the finite-observable corona.  The coherent Cholesky tower
is the topological coordinate which retains the carrier, and the matrices `(5)` are the positive
building coordinates of its normal boundary section.

The four-unit inequality is the Green--Hodge inequality for that section: source Pluecker capacity
dominates tangential Euler-pole capacity plus the dual Hardy--Green capacity of the normal corona
conormal.  The latter is the Cauchy energy of `ell_E`.  The source anomaly, affine origin, boundary
self-symbol, and reflection orientation are all required to define the transition; raw curvature
is not enough.

## Hard attacks

### 1. Naive Fisher probes do not see the divisor `[KILLED]`

Let `Y_epsilon=epsilon log d` under the squarefree Gibbs law and

```text
B_epsilon(w)=E exp(-wY_epsilon).
```

Pairing the Fisher score `-2(Y_epsilon-EY_epsilon)` with the safe Laplace probe gives

```text
r_epsilon^safe(w)
 =2[B_epsilon'(w)+E(Y_epsilon)B_epsilon(w)].              (11)
```

As `epsilon->0`, `Y_epsilon` tends to `Exp(1)`, so

```text
B_epsilon(w)->1/(1+w),
r_epsilon^safe(w)->2w/(1+w)^2.                            (12)
```

The limit `(12)` is the Euler-pole contact response.  It is not the response of `ell_E` and
contains no nontrivial-zero information.

**Positive HT theorem:** the transition from the safe Fisher chart to the continued Cauchy chart
is a genuine completion holonomy.  It cannot be replaced by pointwise convergence of ordinary
positive probes.  This locates the RH information in the topology of the capacity field, not in
its local metric tensor.

### 2. No global bounded codiagonal `[KILLED]`

The prime-coordinate current is holomorphic in `ell^2` on `Re(s)>1/2`, but its codiagonal is
unbounded and nonclosable on the ambient finite-support core.  High-exponent shells give infinitely
many orthogonal four-unit inputs with the same completed divisor profile, ruling out a global
bounded row even after the arithmetic source is enlarged.

**Positive HT theorem:** `(8)` must be proved as compatible finite minimum-response inequalities
inside one source-selected graph, not by a bounded operator on the direct sum of clock sectors.
The capacity field is the correct nonlinear/descent object.

### 3. Positivity alone has no force `[KILLED]`

Every nondecreasing positive scalar capacity path is realized by some positive Gram clock.  Hence
the four-unit path is not selected by hypertranscendence plus positivity.

**Positive HT theorem:** the source-selected affine section and its self-dual colligation holonomy,
not the positive cone alone, are the RH-bearing data.

### 4. Curvature and projective metrics are phase-blind `[KILLED]`

Unimodular Euler twists preserve the complete Fisher metric while changing the scalar divisor.

**Positive HT theorem:** the Ward matrix `(5)` includes the continued response column `r_P`; it is
not determined by `G_P` or by the scalar Fisher curvature.  The boundary self-symbol is an
independent geometric coordinate.

### 5. Reflection and self-duality alone permit free pairs `[KILLED]`

A self-dual determinant can have arbitrary reflected off-line quartets.  A free orbit can be
paired equivariantly, so a bare Maslov or Witt class erases it.

**Positive HT theorem:** the Hermitian capacity of the normal response retains a free pair as a
strictly positive Cauchy energy.  The metric refinement, not the equivariant index, is essential.

### 6. Finite Cholesky prefixes cannot select the source `[KILLED]`

Every fixed finite frame prefix retains an infinite-dimensional maximal-HT aperture.  Therefore
no fixed collection of matrices `(5)` is a selector.

**Positive HT theorem:** the claim is cofinal.  The complete compatible Ward-matrix tower, together
with its source affine marking, is the boundary object.  Boundedness of all its capacities is one
global topological statement, not a finite-probe argument.

### 7. Rational gauge `[PASSED ONLY WITH SOURCE FRAMING]`

A symmetric rational quartet changes `r_P` and can violate `(5)` while preserving reflection and
coarse metric data.  The exact identity

```text
Q_Xi-Q_sq=4A(2s)
```

anchors `r_P` to the actual Euler--Gamma source and rejects the gauged completion.  Any construction
of the Ward row which factors through the gauge-blind boundary matroid is invalid.

## The exact open theorem

Construct, for every finite Cauchy packet `P`, the source Ward matrix `W_P` in `(5)` directly from
the completed squarefree Euler--Gamma colligation and prove

```text
W_P is positive semidefinite,                              (13)
```

compatibly under packet inclusion.

The proof may use the safe Euler identity, the Gamma boundary current, the functional equation,
the complete Cholesky tower, and the source-selected multiplication graph.  It may not use an Xi
zero, an off-line divisor packet, a prechosen Herglotz carrier, or a global bounded codiagonal.

Geometrically, `(13)` says that the source transition is a tame positive self-dual splitting and
that its normal capacity does not exceed the total four-unit curvature.  Algebraically, `(13)` is
the finite Schur-complement form of the anti-causal Ward estimate.  Analytically, it is the
source-only continuation estimate still missing from the proof.

## Bold topological form: the prime--Gamma anomaly mapping cone

The newest general HT results change the form of the conjecture.  The response column should not
be obtained by a bounded codiagonal or by choosing a scattering operator.  It should be the
cohomology class of the affine source anomaly.

Let `alpha_N` be the now-constructed full von Mangoldt/Gamma descent anomaly and let `b_N` be the
Gamma highest-jet boundary projector.  The Gamma boundary self-symbol is the identity and the
adjacent anomaly defect is exactly the rank-one boundary current:

```text
pi_N alpha_(N+1)-alpha_N=kappa_N J_(N+1).                (19)
```

Equation `(19)` is the curved-complex obstruction.  Adjoining the boundary line `b_N` cancels that
curvature and gives a two-term affine mapping cone.  The bold claim is the following.

> **[CONJECTURE -- PRIME--GAMMA HT HARMONIC-COHOMOLOGY WARD LAW]** For every finite
> right-half-plane Cauchy packet `P`, the compatible radial prime--Gamma anomaly cones have a
> source-canonical self-dual harmonic reduction whose reduced metric on the residual Cauchy
> channel is the standard Hardy Gram `G_P`.  The calibrated Euler Fisher tangent represents a
> class of squared norm four, and its normal Hardy coordinates are exactly `r_P`.
> Equivalently, the cohomological quotient metric has the Green-capacity factorization
>
> ```text
> 4G_P-r_P r_P^*=E_P^src (E_P^src)^*.                   (20)
> ```

This is a topology claim: the prime-power aperture and Gamma-jet aperture form a two-dimensional
clock.  Their mapping cone removes exact causal/polar pairs; its reduced class is what survives at
the coherence end.  It is a geometry claim: the source harmonic metric must make that reduction
agree with the fixed Hardy metric, and `(20)` is the finite Gauss equation for this marked
reduction.  It is source-specific: the differential is `alpha_N`, the affine origin is the Euler
pole, and the boundary self-symbol is the Gamma unit.  No divisor or zero list defines the complex.

The completed proof would then be short:

```text
Euler Fisher representative has norm^2 4
  -> reduced cohomology class has norm^2 <=4
  -> its Hardy normal class ell_E has norm^2 <=4
  -> RH.                                                    (21)
```

### Explicit finite square-root candidate

The conjecture now has a non-formal local model.  For `lambda_(p,k)=k log p` define the positive
Taylor-remainder coordinate

```text
R_m(lambda)=1/(m-1)! integral_0^lambda
  exp(-t)(lambda-t)^(m-1)dt.                              (22)
```

The exact anomaly calculation gives the depth-independent orientation

```text
(-1)^(N+1)(alpha_N e_(p,k))_i
 =q_(p,k) exp(-x lambda) lambda^i R_(N-i)(lambda)>0.      (23)
```

After Laplace transformation in `x`, its Cauchy feature is

```text
A_(N,i)(w;p,k)
 =sqrt(q_(p,k)) lambda^i R_(N-i)(lambda)/(w+lambda).      (24)
```

Every radially damped finite Gram `A A^*` is positive semidefinite.  The proposed
`E_P^src` in `(20)` is the reduced cofinal limit of these explicit anomaly features after the
exact shifted-polar and causal pairs are cancelled in the mapping cone.  Thus `(20)` has a
candidate square root; it is no longer merely the desired inequality rewritten with a new name.

### Exact finite compression theorem behind the candidate

There is an unconditional finite Gauss law.  Let `H` be a finite positive source space, let

```text
V:H->C^N,             G=V V^*>0,                         (25)
```

be a surjective observation, and let `S:H->H` be a contraction.  The minimum-norm lift and
observation projection are

```text
L=V^*G^(-1),          P=LV.                              (26)
```

The source-selected metric compression of `S` is

```text
A=VSL=VSV^*G^(-1).                                      (27)
```

Then direct multiplication gives the exact positive defect

```text
G-AGA^*
 =V(I-SPS^*)V^*
 =V(I-SS^*)V^*+VS(I-P)S^*V^* >=0.                       (28)
```

The two positive terms are source damping and unresolved-observation leakage.  If `E` is the
formal Gamma Taylor shadow and

```text
alpha=EV-VS,                                             (29)
```

then the anomaly is exactly the affine displacement from the true positive compression:

```text
E-A=alpha L.                                             (30)
```

Thus the source anomaly is literally a positive compression defect, not an analogy.  For every source
vector `chi`, the observed response `r=V chi` satisfies the minimum-capacity bound

```text
r^*G^(-1)r=||P chi||^2<=||chi||^2.                       (31)
```

At finite prime-power aperture, the jet observation is a weighted exponential Vandermonde and is
surjective once at least `N` distinct frequencies are retained.  Equations `(28)`--`(31)` therefore
apply to the formalized von Mangoldt/Gamma anomaly without an extra hypothesis.

The RH problem is now narrowed to a concrete convergence statement rather than an abstract
positivity principle.  Construct observation maps `V_(P,N,theta)` from the reduced features `(24)`
and prove, in this order,

```text
V V^* -> G_P,
V chi_theta -> r_P,
||chi_theta||^2 ->4.                                     (32)
```

Then `(31)` passes to `r_P^*G_P^(-1)r_P<=4`, which is `(20)`.  The third convergence is the proved
Fisher law.  The first two are respectively the cohomological Cauchy-kernel identification and the
source-framed Hardy-normal identification.  Neither may be replaced by defining `V` from `r_P`.

### How the other HT topology enters, and where it does not

The coherence-end theorem says that the Cartesian product of two infinite locally finite clock
graphs is one-ended.  Applied to the prime-power and Gamma-jet clocks, this removes every
finite-defect end-wise phase reversal: the projective source tail is recoverable from sparse local
coherences.  It therefore supplies the phase/source-identity part of the completion.

One-endedness does **not** determine a positive metric.  The capacity-realization theorem permits
arbitrary monotone scalar profiles, and positive matrices with the same sparse edge phases can
have different long-range entries.  The metric information must come from the full anomaly Gram
and its nonabelian capacity connection.  This separation prevents a graph-end theorem from being
redressed as the Ward estimate.

The nonabelian asymptotic-connection theorem supplies the remaining topological invariant: the
ordered partial transports of the reduced anomaly cone, modulo uniformly bounded gauges.  The
cohomological Ward law is equivalent to those transports preserving the four-unit normalized
positive form.  Algebraic flatness is automatic; bounded positive flatness is the load-bearing
assertion.

### Hard falsifiers and positive residues

1. **Raw anomaly Gram limit.**  The undamped unit Euler field is not in the von Mangoldt Hilbert
   carrier, so the raw limit of `(24)` need not exist.  If it diverges before quotienting, that does
   not kill `(20)`.  **Positive residue:** the Euler boundary is necessarily a reduced/cohomological
   class, not a vector in the unreduced prime carrier.
2. **Arbitrary mapping-cone attack.**  Any signed identity can be made formally positive by adding
   artificial even/odd pairs.  **Falsifier:** the differential must be the exact source anomaly,
   its curvature must be cancelled by the actual Gamma boundary line, and its reduced kernel must
   equal the universal Cauchy Gram entrywise.
3. **One-endedness attack.**  One-ended phase recovery alone is norm-blind.  **Positive residue:**
   it fixes projective source identity and rejects hidden end phases, while the anomaly capacity
   path independently carries magnitude.
4. **Gamma-kinematics attack.**  Taylor translation and factorial tails exist for every analytic
   germ.  **Positive residue:** the common cone orientation `(23)` and the cohomology class use the
   positive von Mangoldt weights and Euler affine marking; deleting `alpha_N` destroys source
   selection.
5. **Finite-only attack.**  Positivity at every radial finite stage can lose energy at the corona.
   **Falsifier:** the reduced capacity forms must be monotone/cofinal and the normal class must be
   identified with `ell_E` before lower semicontinuity is invoked.

### Naive cohomology metric no-go

The bare mapping cone does not prove the Ward estimate.  At one finite packet, write the exact
polar--prime channel complex as

```text
C^(-1)=H_prime direct_sum H_shifted,
C^0   =H_prime direct_sum H_Cauchy direct_sum H_shifted. (32a)
```

The undeformed differential `d_0(a,b)=(a,0,b)` has reduced cohomology exactly `H_Cauchy`, both
algebraically and isometrically.  An anomaly feature `T:H_prime->H_Cauchy` gives the triangular
deformation

```text
d_T(a,b)=(a,T a,b).                                      (32b)
```

Algebraic cohomology is still `H_Cauchy`, through

```text
q_T(x,f,y)=f-Tx.                                         (32c)
```

But minimizing the ambient norm over representatives gives the reduced metric

```text
||h||_(red,T)^2=<h,(I+T T^*)^(-1)h>,                    (32d)
```

not the standard Hardy norm `||h||^2`.  Quotient-norm contraction therefore bounds only the
weaker metric `(32d)`.  It gives no upper bound on the actual Cauchy energy of `ell_E`.

**Positive HT theorem:** an affine anomaly cone carries a canonical metric-distortion field in
addition to its algebraic cohomology class.  The Ward theorem is exactly the existence of a
source-selected self-dual harmonic reduction identifying this distorted cohomology metric with the
standard Hardy polarization on the distinguished section.  This is the finite meaning of
"tame positive holonomy"; omitting it turns the argument into theatre.

### Sharp raw-boundary depth wall

The first limit in `(32)` cannot hold for the unreduced feature family.  On a prime coordinate
`lambda=log p`, one has

```text
R_m(lambda) asymp lambda^(m-1)/(m-1)!                  (lambda->infinity). (33)
```

At depth `N`, the largest anomaly row in `(24)` therefore has squared prime weight comparable to

```text
(log p)/p * (log p)^(2N-4).                              (34)
```

For every `N>=2`, `(34)` has divergent prime sum; already the row `i=N-1` is comparable to
`(log p)^(2N-3)/p`.  Hence no undamped raw jet Gram exists from depth two onward.

Depth one is different.  Its unique feature is

```text
A_1(w;p,k)
 =sqrt((log p)/p^k) (1-p^(-k))/(w+k log p).              (35)
```

For fixed `Re w>0`, its squared prime contribution is `O(1/(p log p))`; the prime sum converges,
and all higher prime powers are absolutely harmless.  Thus the first source/Gamma anomaly has a
normal Euler-boundary Cauchy row even though the unit Euler coefficient field itself is nonnormal.

This gives both a no-go and a positive theorem.

- **No-go:** taking the complete raw jet anomaly to the boundary before homological cancellation
  is impossible.
- **Positive theorem:** the depth-one descent defect is the maximal unreduced normal Cauchy seed.
  Higher depth is not missing regularity; it is precisely the part that must be represented by
  Gamma/polar counterchannels in the reduced complex.

The depth-one Gram is a prime Stieltjes/Carleman carrier, not yet the universal Cauchy Gram.  The
critical Mellin colligation measures the exact discrepancy.  Therefore `(35)` alone does not prove
the Ward estimate, but it fixes the first nontrivial chain group from which the reduced
prime--Gamma transport must be built.

### Depth-one positive-compression Ward theorem

At depth one the formal Gamma shadow is the identity.  This removes the main finite metric
ambiguity.  In the notation `(25)`--`(27)`, assume in addition that the source operation is a
positive contraction,

```text
0<=S<=I.                                                   (36)
```

Then

```text
B=G^(-1/2) V S V^* G^(-1/2)                              (37)
```

is a positive contraction.  The true compressed shift `A` is similar to `B` in the intrinsic
`G^(-1)` observation metric.  Consequently the depth-one anomaly displacement

```text
T_1=I-A=alpha_1 L                                       (38)
```

is also a positive contraction in that metric.  For every source vector `chi`,

```text
||(I-A)V chi||_(G^(-1))
  <=||V chi||_(G^(-1))
  <=||chi||_H.                                           (39)
```

This is an unconditional finite Ward inequality produced by the source constraint.  For the
von Mangoldt source, `S` is coordinate multiplication by `p^(-k)`, so `(36)` is exact.  Formula
`(35)` is the Cauchy-Laplace coordinate of the same operator `I-S`.

**[CONJECTURE -- DEPTH-ONE SUFFICIENCY.]** After adjoining and reducing the exact shifted-polar
and critical-Mellin channels, the cofinal depth-one responses in `(39)` satisfy

```text
G_(P,theta)->G_P,
(I-A_(P,theta))V_(P,theta)chi_theta->r_P,
||chi_theta||^2->4.                                      (40)
```

If `(40)` holds, `(39)` passes directly to `r_P^*G_P^(-1)r_P<=4` and proves RH.  The higher Gamma
jets remain essential for proving source faithfulness and compatibility of the completion, but
their divergent raw Grams need not enter the first-order Ward norm.

This conjecture has a decisive falsifier: if the reduced critical-Mellin channel contributes a
nonzero first-order response not represented by the depth-one source anomaly, then the full
harmonic reduction is unavoidable.  The positive residue would be an exact decomposition of the
Ward response into a contractive depth-one part plus a separately named higher-clock defect.

## The topology that can actually carry the Ward phase

The generic conservative-completion interpretation of `(40)` is retired.  It is the already
failed source-framed colligation proposal unless an explicit source complex fixes both its metric
and its boundary class.  The complex polar--prime identity also does not select the depth-one
anomaly: its critical Mellin term is `P-E`, so it cancels the complete prime Gram `E`, whereas the
depth-one Gamma shift is the distinct source compression `E(s+1)`.  Thus the Mellin incidence does
not promote `(39)` to `r_P`.

**Positive residue:** `(39)` remains the first local passive cell, but the global completion must
be a phase-bearing Hodge complex rather than a generic Julia or scattering dilation.

The new bridge
`../2-fully-proven/not_new_scientific_knowledge/prime-support-ht-horizon-hodge-cofactor-law.md`
identifies the exact finite topology.  For a support of size `n`, the positive boundary
deformation

```text
M_n(t)=n(1-t)^(n-1)                                      (41)
```

is the sum of the `n` rooted Laplacian cofactors of the source-marked flag path in a coned chamber
of the projective HT horizon building.  This supplies a canonical positive metric.  It also proves
the sharp no-go: a tree gauges away every rank-one prime phase, so a chamber alone cannot carry
`r_P`.

An apartment cycle is the minimal repair.  For its twisted differential `d_u`, positive edge
conductances `c_e`, and holonomy `Hol(u)`,

```text
det d_u = unit * sqrt(product_e c_e) * (1-Hol(u)),
det(d_u^*d_u)=product_e c_e * |1-Hol(u)|^2.              (42)
```

Thus the holomorphic torsion retains the phase while the Hodge determinant fixes its positive
metric.  Type-`A_2` HT horizon apartments are literal hexagonal instances of `(42)`.  Assigning
one apartment the holonomy `-p^(-s)` for every prime gives, before continuation,

```text
product_(p in P) det d_p(s)=product_(p in P)(1+p^(-s))
 =Z_(sq,P)(s).                                           (43)
```

Every finite complex in `(43)` is acyclic in the open critical strip.  Hence the nontrivial
continued divisor cannot be finite-aperture cohomology: it is cohomology at the infinite HT
corona.  This is exactly where three general HT theorems enter rather than decorate the route:

1. the horizon building supplies the apartment cycles and Steinberg topological charge;
2. the conormal-corona and normalization-anomaly theorems force any global class with no finite
   shadow to live at the completed clock boundary with a persistent modular cocycle;
3. the capacity--innovation theorem gives the canonical Hodge norm of that corona class.

The scalar fixed-current reduction supplies the final source marking.  The torsion section in
`(43)` has logarithmic current `J_sq`; after Gamma completion its connection is `Q_sq`, and the
proved localization theorem gives

```text
P_anti Q_sq=ell_E.                                       (44)
```

No zero expansion is used in `(43)`--`(44)`.

The earlier **prime-apartment Quillen--Ward descent is killed** at this point.  The apartment
torsion still supplies the phase-bearing finite topology and the Steinberg orientation, but its
Chern/Quillen metric has ordinary divisor scaling and cannot control the Hardy--Green energy of a
logarithmic pole.  A point approaching the critical line has vanishing Jensen charge and divergent
Cauchy energy.  The positive successor is the dual capacity form on the Laurent corona conormal.

> **[CONJECTURE -- PRIME-APARTMENT GREEN--WARD DESCENT.]**  The Gamma-completed cofinal
> apartment line of `(43)` admits the source capacity metric selected by the rooted cofactors and
> the Pluecker half-density, and its exceptional Laurent-corona transgression, in the Laplace
> boundary chart, is the current `(44)`.  The induced dual Hardy--Green form satisfies
>
> ```text
> 4=E_exact+||ell_E||_2^2,       E_exact>=0.              (45)
> ```

This is the anti-causal Ward estimate in topological form.  At a finite Cauchy packet, `(45)` is
not another name for the desired inequality: it requires the explicit twisted apartment
differential `(42)`, the source torsion identity `(43)`, the source half-density, and the
Green-capacity comparison with the independently constructed squarefree Fisher metric.  Its
finite positive compression gives `(20)`; the cofinal capacity theorem then gives RH.

The conjecture has two load-bearing and separately falsifiable clauses:

```text
Green capacity of the completed apartment conormal
  <=squarefree Pluecker/Fisher capacity,                 (46)

strong Hodge corona class under the Laplace chart
  =P_anti Q_sq.                                          (47)
```

Failure of `(46)` produces a nontrivial positive general-HT invariant: the negative part of the
exceptional Green-capacity defect.  Failure of `(47)`
produces the source-selected continuation escape energy already predicted by the capacity-field
theory.  Neither failure collapses back to a Sonin or generic-colligation statement.

### Ordinary Hodge cohomology is exactly the wrong completion

The sharpened squarefree modular-corona theorem
`../2-fully-proven/squarefree-euler-modular-corona-curvature-colligation.md` proves a decisive no-go
and a sharper positive target.  On `ell^2` of the primes put `A_s=diag(p^(-s))`.  For every
`Re s>1/2`, `A_s` is
Hilbert--Schmidt and

```text
||(I+A_s)^(-1)||<=1/(1-2^(-Re s)).                       (48)
```

Thus the ordinary direct-sum apartment complex is uniformly acyclic throughout the strict RH
half-plane.  Its Hilbert cohomology cannot be `ell_E`.  The safe regularized determinant

```text
D_2(s)=det_2(I+A_s)
      =product_p(1+p^(-s))exp(-p^(-s))                  (49)
```

is holomorphic and nowhere zero there.  On `Re s>1`,

```text
Z_sq(s)=D_2(s) exp(P_prime(s)),
P_prime(s)=sum_p p^(-s).                                 (50)
```

All quadratic and higher prime depths are contained in the nonvanishing factor `D_2`; the entire
continued strict-right divisor is carried by the missing first trace.  This proves that the Ward
class is not ordinary cohomology of the apartment differential.  It is the Chern--Simons current
of the central extension from Hilbert--Schmidt to trace-class determinant theory: the precise
modular-corona class predicted by general HT geometry.

The finite metric side of `(46)` is proved in the same squarefree modular-corona theorem.  The
canonical dual torsion metric

```text
h_P(s)=Z_P(Re s)^(-1)                                    (51)
```

has curvature

```text
-partial partial-bar log h_P
  =(1/4)Var_(P,Re s)(log d) ds d-conj(s).                 (52)
```

After critical scaling, `(52)` tends to the independently proved four-unit Fisher curvature.
The metric is therefore source-fixed; only the trace-corona polarization remains open.

The sharpened Ward theorem is:

```text
Gamma-framed first-trace Chern--Simons current
 =causal exact current direct_sum ell_E,

4=E_causal+||ell_E||_2^2.                                (53)
```

Equation `(53)`, not an `ell^2` kernel of `(42)`, is the intended content of `(45)`--`(47)`.
Its proof must construct the self-dual determinant-line polarization of the trace anomaly and
show that the Laplace chart is isometric on its harmonic current.  This is now one rank-one corona
problem rather than an uncontrolled all-depth Gamma complex.

## First construction attempt and its exact failure

The universal upper-left block is already source-resolved:

```text
G_P=G_prime-G_shifted-polar+G_critical-Mellin.             (14)
```

The safe positive construction has an exact last column, but it is not the desired one.  Put

```text
p_P(i)=2/(w_i+1/2).                                       (15)
```

Since `||2k_(1/2)||^2=4`, the matrix

```text
W_P^pole=[[G_P,p_P],[p_P^*,4]]                            (16)
```

is simply the Cauchy Gram matrix obtained by adjoining the node `1/2` with amplitude `2`.
Consequently it is positive semidefinite for every packet.  This is the finite Cauchy-coordinate
form of the proved Euler-pole budget.

Differentiating the safe squarefree Gibbs line produces precisely this pole column.  In the
Laplace chart it is the response of `2 exp(-t/2)`; equivalently, equations `(11)`--`(12)` recover
its Fisher/Laguerre tangent.  It does **not** produce `r_P`, because safe positive probes contain no
continuation divisor information.

Thus the tempting decomposition

```text
r_P=r_prime-r_shifted-polar+r_Gamma-boundary                (17)
```

cannot be obtained by entrywise differentiation of the safe colligation.  The missing boundary
self-symbol must instead construct a source-canonical isometric ambient transport

```text
2k_(1/2)  |->  g_causal direct_sum ell_E,                 (18)
```

with total squared norm four.  In finite Cauchy coordinates, `(18)` replaces the pole response
column of `(16)` by `r_P`, while the unobserved causal component supplies the positive Schur
complement.  This is exactly the Green--Hodge/Ward holonomy assertion.

**No-go:** any purported proof which obtains `r_P` directly from the safe covariance calculation
has silently inserted analytic continuation or the divisor.

**Positive successor:** construct the boundary self-symbol and its ambient conservative transport
first.  Then prove that its normal response column is `r_P` by the source-framed current identity
`Q_Xi-Q_sq=4A(2s)`.  Failure of such transport is decisive: it either produces a negative finite
source packet, killing this route, or isolates a new continuation-holonomy invariant not
represented by the current HT capacity field.

## Gates

- [x] safe squarefree capacity field and four-unit source curvature constructed
- [x] strict right-half divisor localized exactly to the squarefree completed current
- [x] universal finite right-half Cauchy Gram resolved into source channels
- [x] global bounded-codiagonal and naive safe-probe routes killed
- [x] safe affine last column identified exactly with the four-unit Euler-pole atom
- [x] scaled raw von Mangoldt source Gram proved to converge to the universal Hardy Gram, with its
      canonical contact converging to that same four-unit Euler-pole atom
- [x] safe-covariance shortcut to the divisor column killed
- [x] finite-prefix, phase-blindness, reflection-only, and rational-gauge attacks passed or localized
- [x] bold source-specific HT Ward-holonomy conjecture stated
- [x] full finite von Mangoldt/Gamma anomaly and rank-one Bianchi current constructed
- [x] coherent positive orientation of every finite anomaly column proved on paper
- [x] explicit radially damped Cauchy square-root features constructed
- [x] prime--Gamma mapping-cone form of the Ward conjecture stated with falsifiers
- [x] exact finite source-compression Gauss law and anomaly displacement derived on paper
- [x] naive quotient-metric shortcut killed and exact harmonic-metric obligation isolated
- [x] depth-one anomaly proved to be a positive contraction for every finite source observation
- [x] generic conservative completion of the depth-one cell rejected by the existing colligation
      anti-theatre gate
- [x] prime-support boundary jets identified with rooted HT-horizon Hodge cofactors
- [x] tree phase-blindness and the phase-bearing apartment-torsion successor proved
- [x] ordinary apartment `ell^2` cohomology killed by uniform acyclicity on `Re s>1/2`
- [x] safe nonvanishing Hilbert--Schmidt determinant and unique first-trace corona isolated
- [x] finite Quillen/Fisher curvature identity `(52)` proved
- [x] standard Quillen metric killed as the Ward norm by its wrong Laurent mode weight
- [x] squarefree source line lifted to the finite exterior-horizon occupation line
- [x] ordinary critical Fock-vector completion killed while its four-unit tangent residue survives
- [x] source half-density identifies the finite Laurent positive-energy metric with Fisher capacity
- [x] completed squarefree current identified with the reciprocal projective-horizon Cech seam
- [x] its anti-causal Hardy component identified with `ell_E`
- [x] its positive Hardy boundary relative-trace density constructed and identified with
      `||ell_E||_2^2`
- [ ] construct the source-rigged Laurent--Pluecker tangent transgression
- [ ] prove the first-trace/Hardy one-particle splitting `(53)`
- [ ] construct the exact finite reduced anomaly complex and prove its kernel Gram is `G_P`
- [ ] identify the calibrated Euler tangent class and prove its representative norm tends to four
- [ ] prove the reduced normal coordinates equal `r_P`
- [ ] construct the conservative boundary-self-symbol transport `(18)`
- [ ] identify its normal finite response column with `r_P`
- [ ] prove every finite Ward matrix `(13)` positive semidefinite
- [ ] prove compatibility under packet inclusion and identify the coherent Cholesky capacities
- [ ] apply the general HT complete-boundary theorem to obtain `||ell_E||^2<=4`
- [ ] compose with the formal Cauchy threshold and prove RH

## Topological sharpening after the first source attacks

The word `holonomy` in the title is not itself a proof mechanism.  The following stronger
formulation records exactly which part of HT topology would do mathematical work and which nearby
formulations have already failed.

### Reflected prime sectors are not the mechanism `[KILLED]`

The critical-line superselection theorem for reflected prime Poisson sectors is already proved,
and the proposed heat-echo-to-sector descent is already proved equivalent to RH in
`../5-failed/heat-echo-superselection-descent-is-rh.md`.  A hypothetical off-line zero deletes the
additive heat echo while its two reflected prime sectors remain disjoint.  Therefore sector
separation does not construct `(18)`.

**Positive HT statement:** measure-class topology and affine response topology are independent
parts of a completed HT source.  A singular reflected sector may be completely visible while the
source-normal response carrying its divisor is absent.  A conservative capacity theory must
retain both the sector and its affine boundary section.

### Exact Lagrangian topology alone is norm-blind `[KILLED]`

The reciprocal-jet tower is an exact Lagrangian, reversal-self-Legendre polarization atlas.  That
does not imply a Ward inequality.  Already in a finite cotangent space the symplectic dilation

```text
(x,xi) |-> (lambda x,lambda^(-1)xi)
```

preserves the symplectic form and carries exact Lagrangian graphs to exact Lagrangian graphs, while
making either coordinate projection arbitrarily large.  A self-adjoint symplectic shear gives the
same counterexample while fixing the base chart.  Hence exactness, self-Legendre duality, and
caustic avoidance do not control the Hilbert normal.

**Positive HT statement:** an analytic HT realization needs a Kähler-compatible *tame
polarization*, not only the algebraic exact-Lagrangian tower.  The distortion of its normal
projection is an additional invariant of the realization.

### A maximal nonnegative lattice is a conclusion unless source-built `[KILLED AS A SHORTCUT]`

A maximal nonnegative subspace of a causal/anti-causal Krein splitting is the graph of a
contraction, so a source construction of such a lattice would immediately give `(13)`.  But the
existing reflected Euler blocks are Lorentz-conservative for every horizontal rapidity, including
off-line rapidity.  Every finite prime and prime-power completion remains coherent off the line.
Upgrading those blocks to one positive source metric is precisely the existing reflected-anomaly
passivity conjecture and carries the RH burden.

**Positive HT statement:** local indefinite conservativity and global positive reducibility are
distinct strata of the affine HT boundary.  Their difference is a cofinal polarization
obstruction, not local curvature.

### The theta primitive is not a geodesic of the capacity building `[KILLED]`

Horizontal Mellin tilting is geodesic at the level of the positive scale metric.  The one-sided
theta primitive whose anti-reflection detects `XiC(w)=0`, however, is an oscillatory affine
barycenter of that tilted source.  Passing to Gram or capacity coordinates forgets the phase on
which its cancellation depends.  Thus two reflected primitive zeros are not two intersections of
geodesics in the positive capacity building, and CAT(0) uniqueness does not confine them.

**Positive HT statement:** the capacity building is the metric base of the realization, while
zero-bearing continuation lives in an affine phase-marked bundle over it.  This is a concrete
reason that the affine origin in the Kähler--Tate clock is load-bearing rather than decorative.

## Bold source conjecture: affine Kähler--Tate Green--Ward equation

For a packet `P`, let

```text
D_P=4G_P-r_P r_P^*.                                      (19)
```

Since `G_P` is positive definite, the Schur-complement calculation gives

```text
D_P>=0
  iff W_P>=0
  iff r_P^*G_P^(-1)r_P<=4.                               (20)
```

**[CONJECTURE — SOURCE-MARKED AFFINE GREEN--WARD EMBEDDING.]**  The completed squarefree
Euler--Gamma constraint defines a compatible affine Lagrangian section `Lambda_sq` of the
source-rigged Kähler--Tate clock.  In the Hardy causal/anti-causal polarization, its source-marked
exceptional defect operator `E_P^src`, constructed from the complete anomaly colligation before
continuation is evaluated at a divisor, satisfies

```text
4G_P-r_P r_P^*=E_P^src (E_P^src)^*                     (21)
```

for every finite right-half Cauchy packet, compatibly under packet inclusion.

Equation `(21)` is the non-theatrical content of the proposed holonomy.  It says that the
four-unit Pluecker capacity dominates the normal continued response with a literal residual Gram
square.  It is stronger than symplectic exactness, reflection, local `J`-conservativity, and
capacity-field covariance separately.  It is also finite and falsifiable: one packet with a
negative eigenvalue of `(19)` refutes the source embedding.

The proof chain from `(21)` is closed:

```text
source affine Green--Ward equation (21)
  -> D_P>=0 for every P
  -> every finite Ward matrix W_P is positive
  -> every coherent Cauchy capacity is at most 4
  -> the complete HT boundary theorem gives ||ell_E||_2^2<=4
  -> the formal off-line Cauchy threshold gives RH.       (22)
```

No Xi zero is used in `(21)`.  The normal column is identified only after construction, through
the source-framed equality `P_anti Q_sq=ell_E`.

## Why the existing complex Mellin colligation does not yet prove `(21)`

The formal complex colligation proves only

```text
G_P=G_prime-G_shifted-polar+G_critical-Mellin.           (23)
```

The prime block is positive, but the critical Mellin block is signed.  In the continued
prime--Gamma trace the apparent polar reserve cancels the Gamma rational terms exactly, leaving
the critical Mellin defect plus the Gamma connection.  Therefore dominating the remaining
coupled term is positivity of the full continued Xi source kernel, not an independent proof of
`(21)`.

**Positive HT statement:** a metric capacity field and its scalar current do not determine the
affine Green-capacity defect operator.  The missing datum is the phase-bearing comparison between the
critical Mellin defect, the Gamma connection, and the squarefree source tangent.  This is a
concrete zeta realization of the general boundary-colligation theorem that curvature forgets the
boundary self-symbol.

## Exact next construction

The characteristic transfer no longer has to be guessed from the anomaly colligation.  The actual
normalized Möbius shift is contractive and, after the safe squarefree correction and Gamma
completion, has transfer

```text
T_sigma(s)=1/(zeta(sigma)X_sq(s)),
2 d log T_sigma=Q_sq.                                   (23a)
```

This is proved in
`../2-fully-proven/not_new_scientific_knowledge/mobius-squarefree-reciprocal-projective-transfer.md`.
The critical squarefree Möbius half-density score has squared norm four, while the local
normalized/moving-base Gamma metrics are now uniformly congruent by
`../3-formalized/gamma-moving-base-capacity-congruence.md`.

The exact construction is therefore:

1. place the finite Möbius contractions, the Gamma moving-base comparisons, and the Laurent
   first-trace cocycle in the full source-depth by observable-order Gevrey-one scale cone;
2. take their graph closure in the polarized derived HT completion, not in a fixed Hardy or Fock
   space;
3. prove that the boundary transgression of the completed four-unit Fisher score is the Hardy
   vector `c_sq directSum ell_E`; and
4. at every finite Cauchy packet recover the identity

   ```text
   4G_P-r_(P,N,S)r_(P,N,S)^*
     =II_(P,N,S)^src (II_(P,N,S)^src)^*.                 (24)
   ```

The normal component in step 3 is not an imposed response: `(23a)` and fixed-current localization
already identify it with `ell_E`.  The only remaining substantive theorem is nonexpansiveness of
this derived boundary transgression.  Every finite transfer is causal, so a fixed-polarization
limit would force the normal component to vanish; the nonzero opposite component can occur only as
the derived defect of the noncommuting scale limit identified by general HT completion theory.

If `(24)` fails, its coherent negative part is still a nontrivial positive result: it defines the
**affine Ward-defect field**, an obstruction to conservative realization which is invisible to
the ordinary HT capacity field.  General HT geometry must then be enlarged from

```text
metric capacity path
```

to

```text
(metric capacity path, affine Ward-defect field).         (25)
```

That enlargement is the positive successor demanded by a no-go; it is not an RH claim.

## Revised live gates

- [x] reflected-sector, exact-Lagrangian, local-positive-lattice, and CAT(0)-theta shortcuts killed
- [x] each killed shortcut converted into a general HT structural statement
- [x] source-specific affine Green--Ward conjecture stated as the finite factorization `(21)`
- [x] existing complex Mellin colligation shown not to contain the missing causal factor
- [x] construct the full finite prime-power/Gamma anomaly colligation on paper
- [x] determinant-line-only and fixed-Fock formulations killed with positive HT successors
- [x] Laurent--Pluecker tangent transgression isolated as the sole live topological mechanism
- [x] derive and Lean-formalize the source-pure negative Laurent chart from centered Euler
      reflection
- [x] prove and Lean-formalize the finite Pluecker/Fisher-to-Laurent half-density isometry
- [x] prove and Lean-formalize the reciprocal projective-horizon connection identity and identify
      its squarefree anti-causal component with `ell_E`
- [x] identify the reciprocal squarefree projective transfer with the completed characteristic
      transfer of the actual contractive Möbius channel
- [x] construct the reciprocal exceptional section as a nested cofinal limit of finite Pluecker
      transfers on the Euler half-plane
- [x] prove and Lean-formalize bounded local capacity congruence of the two Gamma source charts
- [ ] construct the cofinal Pluecker--Tate tangent bundle and first-trace transgression
- [ ] prove its capacity metric is the one-particle Hardy metric
- [ ] prove the finite Green--Ward factorization `(24)` and pass compatibly to `(21)`
- [ ] finish `(22)`
