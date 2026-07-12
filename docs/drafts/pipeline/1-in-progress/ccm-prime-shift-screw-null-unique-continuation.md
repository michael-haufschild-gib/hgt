# Prime-shift unique continuation for the CCM screw null equation

- **ID:** `ccm-prime-shift-screw-null-unique-continuation`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / DIRECT CCM RH CORE
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOT AN RH PROOF]`
- **Source:** Suzuki's compact screw operator, the exact prime-power atomic kernel, and the CCM
  aperture Morse-index conservation law
- **Statement:** Every compactly supported mean-zero solution of the anchored
  archimedean-plus-prime shift null system is zero. Equivalently, the compact CCM screw operator is
  injective at every aperture, which proves RH.

## 1. Exact null equation

Fix `a>0`. Let `u in L2_0(-a,a)` and extend it by zero to the real line. Suzuki's compact operator
has the truncated-convolution form

```text
(G_a u)(x)=integral_(-a)^a g(x-y)u(y)dy,       |x|<a.    (1)
```

The screw kernel is even. Distributionally,

```text
K=-g''
 =K_infinity
  -sum_(n>=2) Lambda(n)n^(-1/2)
     (delta_(log n)+delta_(-log n)),                     (2)
```

where `K_infinity` is the completed pole--Gamma distribution. Away from the origin its regular
part is

```text
K_infinity(t)
 =exp(|t|/2)-exp(-5|t|/2)/(1-exp(-2|t|)),       t!=0.    (3)
```

If `G_au=0`, differentiating `(1)` twice on the open aperture gives the exact distributional
constraint

```text
(K_infinity*u)(x)
 =sum_(2<=n<exp(2a)) Lambda(n)n^(-1/2)
    (u(x-log n)+u(x+log n)),       |x|<a.                (4)
```

Terms with `log n>=2a` vanish because the zero-extended supports do not overlap. No prime cutoff is
chosen: `(4)` contains precisely every prime power visible to the aperture.

Differentiation loses the affine kernel of the second derivative. Therefore the exact null system
also retains two anchors, for example

```text
(G_a u)(0)=0,
(G_a u)(a/2)=0.                                        (4a)
```

Conversely, `(4)` says that `G_au` has zero second distributional derivative on `(-a,a)`, hence is
affine there. Since the screw kernel is continuous, these point values are defined. The two
conditions `(4a)` kill that affine function. Thus `(4)` plus `(4a)` is
equivalent to `G_au=0`; `(4)` alone is only necessary.

Suzuki--Yoshida and `ccm-aperture-morse-index-conservation-law.md` give

```text
RH
 iff ker G_a={0} for every a>0
 iff the anchored system (4)--(4a) has no nonzero mean-zero
     compactly supported solution.                              (5)
```

Thus `(4)` is the direct CCM core, not an auxiliary sufficient condition.

## 2. Why the equation is structurally different from a flow

The anchored system `(4)`--`(4a)` is one static compatibility constraint among three carriers:

```text
archimedean logarithmic pseudodifferential channel
  + finite faithful prime-shift module
  + hard aperture support boundary.                       (6)
```

The translations commute in the ambient line. Their nontrivial geometry enters only because the
zero extension and the aperture restriction do not commute with them. This is the same boundary
noncommutation forced by the pole-to-divisor capacity theorem.

At aperture `a`, the distinct prime rays have rational rank `pi(exp(2a))`. Prime powers on one ray
are dependent, but two different rays have disjoint shift labels by unique factorization.

## 3. Candidate mechanisms

### A. Log-elliptic support rigidity `[CONJECTURE]`

The Fourier symbol of `K_infinity` grows like `log|xi|`, whereas the right side of `(4)` is a finite
sum of unitary translations. Localize inside `(-a,a)` and seek an iterated logarithmic-elliptic
estimate strong enough to place `u` in a quasi-analytic class. The zero extension would then be
flat across an exterior interval and force `u=0`.

The required estimate must be genuinely quasi-analytic. Membership in every logarithmic Sobolev
space is not enough.

`[PROVED ATTACK]` Pure logarithmic elliptic bootstrapping cannot supply that conclusion. For every
nonzero `v in C_c^infinity(-a,a)` and every integer `k>=0`,

```text
(log(2+|D|))^k v in L2(R).                               (7)
```

Thus

```text
intersection_(k>=0)D((log(2+|D|))^k)                    (8)
```

already contains nonzero compactly supported functions and is not quasi-analytic. Any successful
version of mechanism A must extract super-logarithmic derivative bounds from the coupled prime and
boundary relations, not merely iterate the archimedean symbol.

### B. Boundary-shell prime peeling `[CONJECTURE]`

Order the finitely many visible shift lengths. On a thin interval adjacent to `a`, half of each
translation pair vanishes by support. Compare the equations after translating by two
rationally-independent prime logs. The goal is to peel the outer support shell and iterate inward.

The archimedean term is nonlocal, so the peeling must use a simultaneous cancellation identity or
a boundary value of its Wiener--Hopf factorization; treating it as a local remainder is invalid.

### C. Two-direction periodic-pencil weld `[CONJECTURE]`

If the boundary-shell relations generate an exact nonpure Stanley--Reisner annihilator, the
periodic-pencil theorem forces at least two genuine analytic directions and constructs the optimal
dimension-two HT realization. One direction would carry the Euler shift module and the other the
reflected boundary relation.

This mechanism is conditional on first proving the exact relation complex. The scalar
principalization theorem shows that neither two Hardy polarizations of one variable, arbitrary
componentwise channel multiplicity, constant finite internal monodromy, nor a DA-gauge-flat finite
cocycle satisfies that cost by itself. A nonpure branch must positively carry a second analytic
variable, a non-DA-flat cocycle, an infinite-dimensional action with new differential
transcendence, or a non-additive action.

`[PROVED ROUTE CLASSIFICATION]` There is a complementary one-clock branch. If a CCM realization
does satisfy the exact full Stanley--Reisner matroid hypothesis while remaining scalar/additive and
DA-flat finite-state, its relation ideal is forced to be pure and principal. Its off-line detector
must then reside in the source pointing, aperture support seam, divisor marking, or boundary
compatibility rather than in nonpure prime incidence. The present equation `(4)` is consistent with
that branch: it is one scalar pseudodifferential compatibility constraint. It is not presently
proved to be the full annihilator of a Stanley--Reisner system, so neither branch may import more
than this classification.

### D. Exact finite-interval Wiener--Hopf factorization `[OPEN CORE]`

The untruncated polar part `2cosh(t/2)` is not tempered and therefore has no ordinary real Fourier
multiplier by itself. On the aperture, however, only `|t|<2a` occurs. Its exact truncated
multiplier is

```text
P_a(xi)
 =[2sinh(a)cos(2a xi)+4xi cosh(a)sin(2a xi)]/(xi^2+1/4).

W_a(xi)
 =Re psi(1/4+i xi/2)-log pi
  -2 sum_(2<=n<=exp(2a)) Lambda(n)n^(-1/2)cos(xi log n)
  +P_a(xi).                                             (9)
```

Equation `(4)` is equivalent to a support-separated relation

```text
W_a(D)u=r,
supp u subset [-a,a],
supp r subset (-infinity,-a] union [a,infinity).        (10)
```

This is a finite-interval Wiener--Hopf problem, not a global multiplier equation. The two anchors
`(4a)` remain part of the boundary data and cannot be recovered from `(10)` alone.

`[PROVED CORRECTION]` The prime main term does not force a real characteristic crossing. Put
`X=exp(2a)` and

```text
E(X)=sum_(n<=X)Lambda(n)-X.
```

Then `P_a(0)=8sinh(a)`, and exact partial summation gives

```text
W_a(0)
 =m(0)+2-4/sqrt(X)
  -2E(X)/sqrt(X)-integral_1^X E(t)t^(-3/2)dt.           (11)
```

Thus the polar `4sqrt(X)` term cancels the prime `4sqrt(X)` term exactly. The ordinary prime number
theorem does not determine the sign of `(11)`. The earlier symbol without `P_a` was not the exact
finite-aperture symbol and its claimed cofinal crossings are retracted. The correction and its
rank-two parity signature are proved in `ccm-polar-prime-critical-mellin-defect-law.md`.

For fixed `a`, the corrected prime and polar terms are bounded and decay or oscillate at infinity,
while the Gamma symbol satisfies

```text
W_a(xi)=log|xi|+O_a(1) ->+infinity.                     (12)
```

The real zero set is therefore finite, but may be empty. The route splits exactly: either prove a
zero-free aperture factorization that retains the rank-two polar block, or retain every real
crossing and prove that its finite-interval boundary Evans relation has no nonzero compatible pair.

`[PROVED BRANCH DECISION]` The zero-free alternative is false already in the initial prime-free
regime. Put

```text
m_0=psi(1/4)-log pi<0,
a_0=min((log 2)/2,arsinh(-m_0/8)).                       (12a)
```

For every `0<a<a_0` the prime sum is empty and

```text
W_a(0)=m_0+8sinh(a)<0,
W_a(xi)->+infinity.                                      (12b)
```

Hence `W_a` has a nonzero symmetric real characteristic pair. Suzuki--Yoshida small-aperture
injectivity nevertheless holds, so those ambient characteristic modes are eliminated only by the
nonlocal exterior trace, compact-support seam, mean-zero condition, and affine anchors. Every
successful proof is therefore forced into the boundary Evans branch from the start. The proof is
in `ccm-prime-free-aperture-characteristic-pair-law.md`.

`[PROVED BRIDGE]` Factoring the possibly empty real characteristic set out
by

```text
b_a(xi)=p_a(xi)/(1+xi^2)^L,
W_a=b_a c_a,                                             (13)
```

with `c_a` real-zero-free and invertible, sends every interior solution `u` to
`v=c_a(D)u` satisfying

```text
p_a(D)v=0.                                              (14)
```

Thus `v` is a finite exponential polynomial with one Jordan chain for each real characteristic
crossing; when the set is empty, its interior trace vanishes. Because the inverse multiplier is
nonlocal, the exterior trace of `v` remains part of the boundary data. The remaining theorem is
that the corrected inverse multiplier, exterior trace, two-sided support condition, mean-zero
condition, and two affine anchors admit no nonzero compatible Evans pair. The complete reduction is in
`ccm-characteristic-crossing-interior-mode-reduction-law.md`.

`[PROVED CARRIER LAW]` The exterior trace is irreducibly infinite-dimensional. The multiplier
`c_a` retains the infinite digamma pole lattice, while a finite-rank exterior Hankel map would force
an exponential-polynomial kernel and a rational multiplier by Kronecker's theorem. Hence no raw
Evans determinant involving only the finite real characteristic packet can be complete. The native
object is an infinite-dimensional Fredholm boundary relation with a finite characteristic block.
It may reduce to a finite effective determinant only through an exact Schur complement whose
entries retain the infinite boundary resolvent; see
`ccm-characteristic-evans-boundary-infinite-rank-law.md`.

`[PROVED SCHUR CARRIER LAW]` If the infinite boundary block `D_a` admits a bounded inverse, the
complete Evans kernel is exactly the kernel of the finite characteristic Schur complement

```text
S_a=A_a-B_aD_a^(-1)C_a.
```

Thus a finite determinant is permitted only after the infinite source state has been eliminated
exactly. The all-finite-order transport theorem in `PrimeLogHerglotz.lean` and the rational-packet
independence theorem in `PrimeLogCauchySeamRank.lean` force the prime-coordinate lift of
`D_a^(-1)C_a` to have infinite renormalization rank. The existing all-prime Sonin residual is only
the Hilbert--Schmidt tail of this block; the exponent-one principal Calkin shell and degree-one
relative trace must remain. The proof and carrier statement are in
`ccm-fredholm-schur-resolvent-carrier-law.md`.

`[PROVED FUNCTIONAL-CATEGORY DECISION]` The natural inverse-symbol exterior block is not boundedly
invertible on raw `L2`. Indeed `m_a=1/c_a` tends to zero at high frequency, and any fixed exterior
wave packet modulated to frequency `n` is an approximate null vector for
`1_E m_a(D)1_E`. Therefore the exact reduction must be made on a logarithmic graph space, as a
closed Feshbach relation, or through a relative resolvent before determinant formation. This is
proved in `ccm-exterior-inverse-symbol-graph-norm-law.md`.

The same theorem proves that the exterior block is positive and injective with dense nonclosed
range. Hence an exterior solution, if it exists, is unique. The remaining Evans condition is the
exact range incidence

```text
-1_E m_a(D)1_I v_I in range(1_E m_a(D)1_E)
```

for each finite characteristic trace `v_I`, followed by the two anchors. This is strictly sharper
than asking for an unspecified infinite-dimensional boundary state.

`[PROVED OBSERVABILITY REDUCTION]` Dense-range membership has an exact dual test. For
`D_(a,E)=1_E m_a(D)1_E` and `g_a(f)=-1_E m_a(D)1_I f`, one has

```text
g_a(f) in range D_(a,E)
iff
sup_(h!=0)
 |<f,1_I m_a(D)1_E h>|/||1_E m_a(D)1_E h||<infinity.     (15)
```

The supremum is the norm of the unique exterior datum. Hence the finite characteristic space has a
canonical admissible subspace `F_a^adm`, and every supported solution whose transformed trace lies
in raw `L2` is reconstructed uniquely from it. Because the rational characteristic factor is
nonlocal, the exact residual equation and the three scalar anchors must then be imposed on this
reconstructed subspace. Extending the reduction to every original screw null vector still requires
the local logarithmic-elliptic regularity gate. The proof is in
`ccm-exterior-range-observability-law.md`.

`[PROVED OBSERVABILITY CLOSURE]` The actual logarithmic symbol makes `(15)` automatic for every
interior `L2` forcing. After normalizing the characteristic factor,

```text
c_a(xi)=(1/2)log(1+xi^2)+q_a(xi),
q_a in L_infinity,
inf c_a>0.
```

The cross-boundary kernel of the logarithmic term is dominated by the Carleman kernel
`1/(s+t)`, while the `q_a` block is bounded. The coercive Dirichlet realization `C_(a,I)` therefore
gives, for every characteristic trace `f`, a unique supported state

```text
u_f=C_(a,I)^(-1)f,
v(f)=c_a(D)u_f=f+v_E(f).
```

Thus `F_a^adm=F_a`. The live theorem is injectivity of the exact reconstructed map consisting of
`1_I b_a(D)v(f)`, mean zero, and the two affine anchors. This is proved in
`ccm-log-symbol-dirichlet-exterior-reconstruction-law.md`.

`[PROVED FINITE EVANS REDUCTION]` Put `d_a=2L_a`. The kernel of
`(1+D^2)^(-L_a)` is `exp(-|x|)` times a polynomial of degree `L_a-1`. Since
`p_a(D)f=0` in the interior, both the zero-extension boundary defect of `f` and the contribution of
the reconstructed exterior state land in

```text
R_(L_a)=span{x^j exp(x),x^j exp(-x):0<=j<L_a},
dim R_(L_a)=d_a.
```

Therefore the residual, mean, and two anchors define a finite map `M_a` on the `d_a`-dimensional
characteristic space, and injectivity is equivalent to `det(M_a^*M_a)>0`. The determinant is finite
in size but its entries retain the complete logarithmic Dirichlet reconstruction. The proof is in
`ccm-rational-residual-finite-evans-matrix-law.md`.

`[PROVED GLOBAL REGULARITY CLOSURE]` Every original `L2` screw null vector belongs to this
factorized category. Indeed `v=c_a(D)u` satisfies `p_a(D)v=0` on the aperture, hence is an
exponential polynomial there; outside the aperture, the Carleman-bounded cross block places `v` in
`L2`. Therefore `u` equals the unique logarithmic Dirichlet reconstruction of its characteristic
trace. It follows unconditionally that

```text
ker G_a={0} iff det(M_a^*M_a)>0,
RH iff for every a>0, det(M_a^*M_a)>0.
```

This equivalence is proved in `ccm-screw-null-global-log-regularity-law.md`. The remaining theorem
is the strict cofinal determinant bound, not another regularity or boundary-existence lemma.

`[SOTA COMPARISON]` This determinant is not the conjectural finite spectral-triple determinant of
Connes--Consani--Moscovici. Their 2025 proof obligation is normalized determinant convergence to
`Xi`; Suzuki's 2026 screw paper instead constructs an unconditional deficiency-index
characteristic function with real zeros and leaves a compact-limit identity to `xi/xi'` open. The
map `M_a` here is an exact fixed-aperture kernel detector. None of those primary papers supplies the
remaining strict inequality `det(M_a^*M_a)>0`.

`[PROVED QUANTIZED-CARRIER REFINEMENT]` The Gram determinant is the squared norm of the top exterior
power `P_a=wedge^(d_a)M_a`. Its zeros detect the kernel, but `M_a` is rectangular: `P_a` is a
Pluecker vector, not a scalar determinant-line section, and the square forgets crossing orientation.
Therefore a cofinal proof must first identify the finite Evans complex with the intrinsic Fredholm
determinant line, then transport a canonical prime--Gamma orientation and prove zero spectral flow
from the small-aperture chamber. This requirement is proved in
`ccm-evans-gram-requires-determinant-line-lift.md`.

`[PROVED PARITY SPLIT]` Reflection decomposes the exact map into

```text
M_a^+: even residual + mean + constant-affine anchor,
M_a^-: odd residual + slope anchor.
```

Both characteristic and residual spaces have dimension `L_a` in each parity, and the Gram
determinant factors as the product of the even and odd Gram determinants. Thus the three excess
target channels are canonically graded as two even plus one odd. Identifying them with the actual
Fredholm cokernel remains part of the determinant-line lift. The proof is in
`ccm-parity-split-evans-gram-law.md`.

`[PROVED SUZUKI-LINE BOUNDARY]` Suzuki's deficiency-index characteristic function cannot provide
the missing unshifted orientation for free. It is built from
`T_(a,lambda)=A_a-lambda I>0`, requiring `lambda<lambda_0(a)`. Setting `lambda=0` for every aperture
is already RH; even constructing source-selected `lambda(a)->0` below the floor proves RH by the
negative-spectrum no-evacuation law. Hence the viable lift must be an unshifted indefinite Fredholm
line, or it must directly prove the cofinal floor. The proof is in
`ccm-suzuki-deficiency-line-zero-shift-floor-equivalence.md`.

`[PROVED DERIVATIVE-VARIABLE DOMAIN LAW]` Replacing `W_a` by `W_a-lambda` does not turn the
rectangular screw-variable Evans map into a finite Morse counter automatically. Suzuki's
generalized derivative problem

```text
G_a u=lambda K_a u
```

lives on the completed space `H(S_(a,mu))`, which is explicitly not contained in `L2`. Hence a
realization in that variable must either prove that every nonpositive generalized eigenvector lifts
into the global logarithmic Evans domain, or construct the Evans/Fredholm complex directly on the
Suzuki completion. The forced positive alternative is proved in
`ccm-spectral-parameter-evans-completion-carrier-law.md`.

`[PROVED SQUARE-EVANS ESCAPE]` The original restricted-Weil eigenfunction `v` remains in `L2` and
satisfies

```text
1_I(W_a(D)-lambda)v=0.
```

Factoring the shifted symbol in this variable gives an exact square residual map

```text
N_(a,lambda):F_(a,lambda)->R_(a,lambda),
ker N_(a,lambda) isomorphic to ker(A_a-lambda I).
```

The zero-mean and two affine channels disappear because no derivative inversion is performed.
Hence `det N_(a,lambda)` is a genuine determinant-line section whose nonpositive zeros compute the
fixed-aperture negative spectrum. The proof is in
`ccm-restricted-weil-square-evans-determinant-law.md`.

`[PROVED STRATUM-STABLE EVANS LINE]` A symbol-root birth does not obstruct the square determinant.
Weierstrass continuation retains the pair as nonreal conjugate roots on the zero-free side, so the
finite source and target keep equal constant dimension. The resulting local square determinants
are exact Grushin reductions of `A_a-lambda I` and glue by nowhere-zero transition factors to its
intrinsic Fredholm determinant line. Their zero divisor is the operator spectrum with multiplicity.
This is proved in `ccm-weierstrass-stabilized-square-evans-line-law.md`. The live task is now
aperture-coherent source normalization and the proof that this divisor avoids `lambda<=0`.

`[PROVED SOURCE NORMALIZATION]` In the even sector, the exact frame identity gives

```text
H_a=B_a^*B_a=A_a^++mu_a I>0,
A_a^+-lambda I
 =H_a^(1/2)[I-(mu_a+lambda)H_a^(-1)]H_a^(1/2).
```

Hence the Evans line is canonically normalized to the identity at `lambda=-mu_a`, and the RH
obligation is the sharp source estimate

```text
mu_a||H_a^(-1)||<1.
```

The inverse is compact but lies in no finite Schatten class: its singular values are asymptotic to
`1/log n`. Thus the finite square boundary determinant or intrinsic determinant line is compulsory;
no trace-class or finite-order regularized Fredholm determinant can replace it. This is proved in
`ccm-source-normalized-nonschatten-birman-schwinger-line-law.md`.

The cutoff-dependent level is not needed for cofinal normalization. The explicit continuous bound

```text
bar_mu_a=8a exp(a)-m(0)+1>mu_a
```

places `-bar_mu_a` strictly below the restricted-Weil spectrum for every aperture. Hence the same
source formula normalizes every Evans line, and the exact remaining estimate is

```text
bar_mu_a||(A_a^++bar_mu_a I)^(-1)||<1.
```

`[PROVED COFINAL CHARGE EXHAUSTION]` Every off-line Hardy defect channel reaches a finite screw
aperture. More precisely,

```text
sup_(a>0)kappa(a)
 =sum_(Re rho>1/2)multiplicity(rho)
 =sup_(omega>0)dim K(B_omega).
```

The proof uses the global screw-kernel Krein index and continuous-kernel exhaustion; it is an exact
index transport rather than a comparison of Boolean RH criteria. See
`ccm-aperture-morse-hardymodel-index-exhaustion-law.md`.

## 4. Attacks

1. **Global Fourier division is unavailable.** Equation `(4)` holds only on `(-a,a)`, not on the
   whole line. Dividing by the archimedean symbol would silently discard the aperture seam.
2. **Ambient shift independence is insufficient.** Finite sums of rationally independent
   translations can have compactly supported solutions to inhomogeneous equations. The proof must
   use the support boundary and the exact Gamma channel.
3. **Analytic-kernel rhetoric is insufficient.** An analytic convolution kernel can have finite
   Fourier support and a large truncated nullspace. One needs a verified quasi-analytic or
   Wiener--Hopf condition for the actual `K_infinity`.
4. **Positivity is circular here.** Showing the Fourier symbol of the full left-minus-right side is
   nonnegative is the Weil criterion. The target is injectivity/unique continuation, which is
   weaker at each fixed aperture but cofinally equivalent to RH.
5. **Fixed-prime induction is insufficient.** The visible number of prime rays grows with `a`; any
   estimate whose constants deteriorate without a controlled cofinal law cannot prove `(5)`.
6. **The polar boundary block is compulsory.** It is rank two after aperture compression and has
   opposite even/odd signatures. Omitting it destroys the leading polar--prime cancellation and
   creates spurious characteristic crossings.

## 5. Promotion and kill conditions

Promote the route only after proving one of:

- a Denjoy--Carleman estimate for every solution of `(4)` whose class is quasi-analytic uniformly
  on compact subapertures;
- a boundary-shell theorem that strictly shrinks the essential support of every nonzero solution;
- a Wiener--Hopf factorization whose partial indices vanish from the exact Euler--Gamma source;
- an exact nonpure relation complex plus a two-direction source-selected positivity theorem.

Kill the unique-continuation mechanism if an explicit nonzero compactly supported solution exists
for the actual coefficients at one aperture, or if the strongest regularity consequence of `(4)`
is proved non-quasi-analytic and the boundary-shell equations admit a free datum.

## Gates

- [x] exact compact screw null equation isolated
- [x] two lost affine modes restored by exact source anchors
- [x] finite visible prime-power cutoff derived from support
- [x] direct equivalence to the CCM aperture injectivity core recorded
- [x] three distinct mechanisms generated
- [x] invalid Fourier, analyticity, and fixed-prime shortcuts excluded
- [x] pure logarithmic ellipticity proved non-quasi-analytic
- [x] exact aperture-dependent polar multiplier restored
- [x] polar--prime main-term cancellation and critical Mellin defect proved
- [x] coarse cofinal-crossing argument retracted
- [x] interior null space reduced to the finite real-characteristic packet
- [x] zero-free scalar factorization branch refuted in the initial prime-free aperture
- [x] exterior characteristic trace proved infinite-rank
- [x] raw finite characteristic-only Evans determinant retired
- [x] exact conditional Fredholm Schur-complement carrier law proved
- [x] finite rational/log-order boundary-resolvent surrogates retired
- [x] bounded raw-`L2` boundary inverse refuted
- [x] logarithmic graph-space/Feshbach carrier forced
- [x] exterior matching reduced to a finite-to-infinite dense-range incidence condition
- [x] dense-range incidence converted to an exact boundary-observability inequality
- [x] canonical admissible characteristic subspace isolated
- [x] logarithmic Dirichlet reconstruction proves the full characteristic space admissible
- [x] reconstructed residual reduced to an exact finite exponential-polynomial block
- [x] exact finite Gram determinant retaining the infinite boundary state constructed
- [x] global logarithmic regularity proved for every screw null vector
- [x] exact cofinal Evans determinant criterion proved equivalent to RH
- [x] determinant-line lift from the rectangular Evans Gram isolated as the Morse-charge carrier
- [x] exact even/odd Evans Gram factorization constructed
- [x] shifted positive deficiency-line shortcut separated from the unshifted RH carrier
- [x] spectral-parameter root-count shortcut reduced to the Suzuki-completion carrier
- [x] restricted-Weil eigenfunction square Evans determinant constructed
- [x] identify the cofinal Evans/Morse charge with the complete Hardy model-space defect
- [x] one-clock principal relation branch separated from nonpure periodic-pencil escape
- [x] prove a local logarithmic-elliptic regularity theorem
- [ ] prove or refute quasi-analyticity
- [ ] prove or refute boundary-shell support peeling
- [x] decide the initial aperture in favor of the characteristic-crossing branch
- [x] construct the infinite-dimensional finite-interval characteristic Evans/Fredholm relation
- [x] construct the closed logarithmic Dirichlet reconstruction on the characteristic space
- [x] construct the exact unbounded exterior reconstruction on the characteristic space
- [ ] prove the exact finite Evans Gram determinant is positive for every aperture
- [ ] prove even-sector and odd-sector injectivity for every aperture
- [ ] construct the Evans-to-Fredholm determinant-line lift and prove zero spectral flow
- [ ] lift nonpositive generalized eigenvectors to the logarithmic Evans domain, or build the
      completed Evans complex directly
- [x] glue the square Evans determinant line through characteristic-stratum changes
- [x] select a continuous explicit normalization chamber in aperture
- [x] construct the source normalization separately at every aperture
- [x] remove prime-cutoff jumps from the source normalization
- [ ] prove `ker G_a=0` for every aperture
- [ ] RH
