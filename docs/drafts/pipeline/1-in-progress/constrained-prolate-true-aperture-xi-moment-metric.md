# The true constrained-prolate aperture metric is an arithmetic Xi-square Gram

- **ID:** `constrained-prolate-true-aperture-xi-moment-metric`
- **Stage:** 1-in-progress
- **Type:** THEOREM / NO-GO CLOSURE / TRUE-METRIC PIVOT
- **Scientific status:** `[EXACT FINITE METRIC PROVED]`
  `[METRIC-RIGID SCHUR DIRECTION PROVED FROM THE RECORDED FIXED-MODE REGULARITY INPUT]`
  `[CANDIDATE NEW SOURCE-SPECIFIC KNOWLEDGE] [EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** the CCM summation map, the constrained fixed-mode Hermite ladder, the exact
  Poisson--Muntz fold, the radial leakage Gram law, and the regular Weil--Toeplitz limit.
- **Open consumer:** `constrained-prolate-weil-toeplitz-schur-law.md`.

## Why this card exists

The source `L2` metric used to discover the Weil--Toeplitz Schur correction is not the metric of
the true CCM aperture vector.  The true denominator is

```text
G^E_(ij)(lambda)
 =<R_lambda E(g_(i,lambda)),R_lambda E(g_(j,lambda))>_(L2(d*u)),
E(f)(u)=sqrt(u) sum_(n>=1) f(nu),
I_lambda=[lambda^(-1),lambda].                              (AM1)
```

The map `E` is unbounded on ambient additive `L2`.  Therefore ordinary prolate-to-Hermite
convergence does not imply convergence of `(AM1)`.  This kills the attempted identification of
the aperture metric with the source identity.

The no-go has a non-trivial positive survivor.  The finite metric has an exact arithmetic formula,
its fixed-Hermite target is an explicit `Xi^2` polynomial moment Gram, and its polynomial condition
growth is subordinate to the `lambda^8` adjacent prolate hierarchy.  Consequently the canonical
two-rung Schur **direction** survives in the true generalized eigenproblem even before the full
metric limit is proved.

## Exact source contrasts

Let `e_(j,lambda)=h_(4j,lambda)` and

```text
ell_j(lambda)=integral_R e_(j,lambda).
```

The source-normalized CCM ground contrast is

```text
g_(0,lambda)
 =(ell_1 e_0-ell_0 e_1)/sqrt(ell_0^2+ell_1^2).            (AM2)
```

The exact next zero-integral contrast, orthogonal to `g_(0,lambda)` in source `L2`, is

```text
gHat_(1,lambda)
 =-ell_0 e_0-ell_1 e_1+[(ell_0^2+ell_1^2)/ell_2]e_2,
g_(1,lambda)=gHat_(1,lambda)/||gHat_(1,lambda)||_2.        (AM3)
```

Equation `(AM3)` is the second vector in the Gram--Schmidt ladder of the raw CCM contrasts.  It
removes an ambiguity in the earlier statement of `(WT16)`.

## Exact finite aperture Hilbert metric `[PROVED]`

Let `f,g` be even sources supported in `[-lambda,lambda]`.  Expanding the finite sums in `(AM1)`
gives

```text
G^E_lambda(f,g)
 =sum_(1<=m,n<=floor(lambda^2))
   integral_(lambda^(-1))^(lambda/max(m,n))
     conjugate(f(mu)) g(nu) du.                              (AM4)
```

Write `m=da`, `n=db`, with `(a,b)=1`, and put

```text
H_N=sum_(1<=d<=N)1/d.
```

Then the same finite sum has the primitive-ray decomposition

```text
G^E_lambda(f,g)
 =sum_((a,b)=1)
   integral_(lambda^(-1))^(lambda/max(a,b))
     H_(floor(lambda*x)) conjugate(f(ax)) g(bx) dx.           (AM5)
```

The sum is finite because the interval is empty when `max(a,b)>lambda^2`.  Formula `(AM5)` is the
actual arithmetic Hilbert metric.  One may not replace `H_(floor(lambda*x))` by `log(lambda)`
termwise: the zero-mean cross-ray cancellation is what keeps the global Muntz norm finite.

On the entire source space this is only semidefinite, because the central aperture gauge lies in
`ker(R_lambda E)`.  It becomes a Hilbert metric on the quotient.  On every finite analytic prolate
span it is already strictly positive: for `u in (lambda/2,lambda)`, only the `n=1` summand remains,
so a zero metric vector would vanish on an interval and hence vanish identically.

## Exact Poisson fold `[PROVED]`

Suppose additionally that `f,g` have zero integral and bounded variation.  Poisson summation gives

```text
E(f)(1/u)=E(Fourier(f))(u)-f(0)/(2sqrt(u)).                    (AM6)
```

Splitting the aperture at `1` and applying `u ->1/u` to the lower half yields

```text
G^E_lambda(f,g)
 =integral_1^lambda [
     E(f)(u) conjugate(E(g)(u))
    +(E(Fourier(f))(u)-f(0)/(2sqrt(u)))
      conjugate(E(Fourier(g))(u)-g(0)/(2sqrt(u))) ] d*u.       (AM7)
```

Thus the true metric is a two-channel physical/Fourier Gram, not an unknown abstract denominator.
If `V_f,V_g` are the positive-half variations, the zero-mean Riemann-sum bound gives

```text
|G^E_lambda(f,g)-<E(f),E(g)>_(L2(R_+,d*u))|
 <=V_f V_g/lambda,                                           (AM8)
```

because the only missing part of the global vector is `(0,lambda^(-1))` and
`|E(f)(u)|<=V_f sqrt(u)` there.

## The fixed-Hermite target is a Xi-square moment metric `[PROVED]`

Let `h_(4j)` be the normalized Fourier-fixed Hermite functions and put

```text
a_j=h_(4j)(0),
a_j^2=sqrt(2) binom(4j,2j)/16^j.
```

Let `phi_k` be the normalized Hermite limit of the `k`-th constrained contrast.  For the positive
Mellin transform,

```text
M h_(4j)(s)
 =2^(-3/4) pi^(-s/2) Gamma(s/2) P_j(s),
P_j(1-s)=P_j(s).                                             (AM9)
```

The zero-integral constraint makes the contrast polynomial vanish at both `s=0` and `s=1`.
Therefore, for an explicit polynomial `R_k`,

```text
sum_j c_(kj)P_j(s)=s(s-1)R_k(s(1-s)),

zeta(s) M(phi_k)(s)
 =2^(1/4) xi(s) R_k(s(1-s)).                                 (AM10)
```

On the critical line put

```text
u(t)=1/4+t^2,
M_r=1/(sqrt(2)pi) integral_R u(t)^r |xi(1/2+it)|^2 dt.        (AM11)
```

Every `M_r` is finite.  The candidate fixed-depth aperture metric is the unconditional positive
Gram

```text
Gamma_(k,ell)
 =1/(sqrt(2)pi) integral_R |xi(1/2+it)|^2
     R_k(u(t))R_ell(u(t))dt.                                 (AM12)
```

This does not assume RH.  It uses the completed zeta function as the Mellin multiplier of the
source-built summation map, not its zero divisor.

## First two rows and strict determinant `[PROVED]`

Choose independent orientations so that

```text
R_0(u)=4/sqrt(33),
R_1(u)=sqrt(2/731115)(401-44u).                              (AM13)
```

Equivalently, on the critical line `R_1=sqrt(2/731115)(390-44t^2)`.  Equations
`(AM11)`--`(AM13)` give

```text
Gamma_00=16/33 M_0,

Gamma_01=[4/sqrt(33)]sqrt(2/731115)(401M_0-44M_1),

Gamma_11=2/731115
  (160801M_0-35288M_1+1936M_2).                              (AM14)
```

The determinant collapses exactly to the strict variance

```text
det Gamma_[0,1]
 =512/199395 (M_0 M_2-M_1^2)>0.                              (AM15)
```

Strictness follows because `u(t)` is nonconstant on the support of the positive density
`|xi(1/2+it)|^2dt`.  Hence the true limiting metric target is nondegenerate and generally
non-diagonal.

The ground contrast has an additional exact identification.  In the CCM orientation,

```text
phi_0(x)
 =sqrt(3/11)h_0(x)-sqrt(8/11)h_4(x)
 =[2^(1/4)8pi/sqrt(33)]x^2(3-2pi*x^2)exp(-pi*x^2)
 =-[4*2^(1/4)/sqrt(33)] thetaCuspSeed(x).                    (AM16)
```

The logarithmic integer sum of `thetaCuspSeed` is the formalized `thetaCuspFullSource`, whose
Fourier transform is the formalized `XiC`.  Thus `(AM16)` identifies the precise normalization of
the ground target already present in the Lean theta-cusp corpus.

## Exact missing convergence theorem `[OPEN]`

Equation `(AM12)` is the identified target; it is not yet a proved limit for the actual prolate
vectors.  The missing input is the source-specific zeta-graph convergence

```text
integral_R |zeta(1/2-it)|^2
 |M(g_(k,lambda)-phi_k)(1/2-it)|^2 dt ->0.                    (AM17)
```

Ordinary additive `L2` convergence cannot prove `(AM17)` because `E` is unbounded.  A concrete
sufficient PSWF theorem is weighted-BV convergence on the positive half-line: for one
`alpha>1/2`, including the zero-extension endpoint atom,

```text
B_alpha(g_(k,lambda)-phi_k)->0,

B_alpha(f)
 =integral_0^infinity (1+x)^alpha |f(x)|dx
  +integral_[0,infinity) (1+x)^alpha d|Df|(x).                 (AM18)
```

The sampling estimate

```text
sum_(n>=1)|f(nu)|
 <=u^(-1) integral_u^infinity |f(x)|dx+|Df|([u,infinity))
```

makes the upper folded channel continuous from `B_alpha` to `L2([1,infinity),d*u)`.  The proved
radial leakage law controls the Fourier-exterior remainder, and `(AM8)` removes the shrinking
lower interval.  Thus `(AM18)` implies `(AM17)` and entrywise convergence to `(AM12)` for every
fixed finite family.

The local corpus currently invokes fixed-mode `W^(1,1)` convergence and the bound
`Var(g_(k,lambda)^+)=O(1)`, but has not proved the stronger weighted theorem `(AM18)`.  Therefore
`(WT16)` remains open and no limiting true eigenvalue constant is claimed unconditionally.

There is a sharper minimal rate lemma.  Let `f_lambda` be supported in `[0,lambda]`, let `f` be
Schwartz, and suppose both have zero positive-half integral.  If

```text
Var(f_lambda-f)->0,
lambda ||f_lambda-f||_(L-infinity(0,lambda))->0,               (AM18a)
```

then `||E(f_lambda)-E(f)||_(L2(d*u))->0`.  On `0<u<1`, the zero-mean BV discrepancy contributes at
most `Var(f_lambda-f)^2`.  On `1<=u<=lambda`, the sampled head contributes at most
`lambda^2||f_lambda-f||_infinity^2`.  The omitted Schwartz tail is `o(1)` after choosing any decay
power greater than one.  Hence a fixed-mode PSWF estimate

```text
||g_(k,lambda)-phi_k||_infinity=O(lambda^(-2))                 (AM18b)
```

together with the already invoked `W^(1,1)` convergence would close `(AM17)`.  Neither `(AM18b)`
nor an equivalent uniform Agmon envelope is currently recorded in the live corpus.

## Positive survivor without `(AM17)`: metric-rigid Schur direction `[PROVED FROM THE RECORDED
FIXED-MODE W1,1 AND VARIATION INPUT]`

Full zeta-graph convergence is stronger than what is needed to identify the leading source
direction.  Fix a finite depth `N`.  Local `W^(1,1)` convergence and the sampling inequality imply
convergence of the folded vectors on every compact interval in `(0,infinity)`.  The Hermite Muntz
vectors are analytic and linearly independent, so their Gram on one fixed interval is positive
definite.  The full aperture metric therefore has a fixed lower floor.  The BV global estimate
gives the upper bound

```text
m_N I <=G^E_(lambda,N)<=C_N lambda I.                         (AM19)
```

For the first two regular Weil channels, write `L=log c`, `delta=sqrt(d_1/d_2)=O(lambda^(-4))`.
The numerator has the hierarchy

```text
Q_00~theta_0 D_0 d_1 L,
Q_01~s sqrt(theta_0 theta_1)D_1 sqrt(d_1d_2)L,
Q_11~theta_1 D_0 d_2 L.                                      (AM20)
```

The lower generalized eigenvalue satisfies `epsilon_-=O(d_1L)` by the `e_0` trial vector and the
lower floor in `(AM19)`.  In the second row of

```text
Q_lambda c=epsilon_- G^E_lambda c,
```

the metric correction to `Q_01` has relative size at most

```text
O(lambda*d_1/sqrt(d_1d_2))=O(lambda^(-3)),
```

and the correction to `Q_11` has relative size `O(lambda^(-7))`.  Therefore

```text
y/x
 =-s (D_1/D_0)sqrt(theta_0/theta_1)sqrt(d_1/d_2)
   +o(sqrt(d_1/d_2)).                                        (AM21)
```

This is the canonical `O(lambda^(-4))` Toeplitz/Schur direction in the **true aperture generalized
eigenproblem**.  The true metric can distort a fixed section by a polynomial factor, but the
adjacent prolate hierarchy separates by `lambda^8`; the metric is asymptotically subordinate.

If `(AM17)` is later proved, the eigenvalue constant becomes

```text
epsilon_-/(d_1 log c)
 ->[theta_0/Gamma_00](D_0-D_1^2/D_0)
 =[3/(2M_0)](D_0-D_1^2/D_0)>3/(4M_0).                       (AM22)
```

The upper generalized level then also has the exact limit

```text
epsilon_+/(d_2 log c)
 ->theta_1 D_0 Gamma_00/det(Gamma_[0,1]),                     (AM23)
```

so the true two-rung generalized gap retains the `lambda^8` prolate hierarchy.

The full closed Weil form still additionally requires the intact bilinear graph-defect estimate
`(WT17)`.  Even `(AM17)` and `(WT17)` together control only the fixed trial span, not its orthogonal
complement.

## No-go closure and novelty verdict

- **Killed statement:** the aperture Gram is asymptotically the source identity, or scales with the
  exponentially small prolate leakage.
- **Exact obstruction:** `E` is an unbounded zeta multiplier; its fixed-Hermite image carries the
  order-one `Xi^2` moment metric `(AM12)`.
- **Positive survivor:** the metric is explicit, positive, polynomially conditioned at fixed
  depth, and subordinate to the `lambda^8` prolate ladder.  Hence the Schur direction `(AM21)` is
  already true-metric rigid.
- **Novelty audit:** the Hermite-to-polynomial-`Xi` factorization is already present in CCM
  Proposition 3.6; Hermite Mellin formulas, the zeta multiplier, and positive polynomial moment
  Grams are parent material.  The candidate-new residue is the constrained-prolate aperture
  assembly: the exact arithmetic metric `(AM5)`, its explicit first two source-normalized entries,
  the minimal graph-rate gate `(AM18a)`, and especially the scale-separation theorem
  `(AM19)`--`(AM21)`.  Actual finite-prolate Gram convergence and the spectral constants
  `(AM22)`--`(AM23)` become candidate-new theorems only after `(AM18b)` or an equivalent estimate is
  proved.  External priority remains unverified.

## Lean status

The source-specific finite algebra is formalized in
`GaloisForLFunctions.RHTower.ConstrainedProlateApertureXiMetric`:

- the limiting ground Hermite seed is identified exactly with the existing theta-cusp seed;
- its all-integer logarithmic source is identified with the existing `thetaCuspFullSource`;
- its Fourier transform is therefore the corresponding exact scalar multiple of `XiC`;
- the first two Xi-square metric entries have determinant
  `512/199395*(M_0*M_2-M_1^2)`;
- strict Hankel variance implies strict positive definiteness;
- the aperture-normalized regular Schur coefficient reduces to `(AM22)` and retains the strict
  lower bound `3/(4M_0)`.

No Lean declaration assumes `(AM17)`, `(WT17)`, a true Weil spectral floor, or RH.

## Gates

- [x] define the exact second source contrast
- [x] derive the finite aperture metric `(AM4)` and primitive-ray form `(AM5)`
- [x] derive the exact Poisson fold `(AM7)` and lower-tail error `(AM8)`
- [x] identify the fixed Hermite metric as the Xi-square Gram `(AM12)`
- [x] compute the first two invariant polynomials and strict determinant
- [x] identify the ground contrast with the formal theta-cusp source
- [x] prove the polynomial metric bounds `(AM19)` from the recorded fixed-mode regularity input
- [x] prove true-metric rigidity of the Schur direction `(AM21)` under that same input
- [x] reduce graph convergence to the minimal BV plus sup-rate lemma `(AM18a)`
- [ ] prove the weighted fixed-mode PSWF convergence `(AM18)`
- [ ] conclude the actual aperture metric limit `(AM17)`
- [ ] prove the intact full-Weil bilinear graph defect `(WT17)`
- [ ] control the orthogonal complement / true global floor
