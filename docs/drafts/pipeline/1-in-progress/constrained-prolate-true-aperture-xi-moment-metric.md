# The true constrained-prolate aperture metric has an arithmetic fold and an Xi-square target

- **ID:** `constrained-prolate-true-aperture-xi-moment-metric`
- **Stage:** 1-in-progress
- **Type:** THEOREM / NO-GO CLOSURE / TRUE-METRIC PIVOT
- **Scientific status:** `[EXACT FINITE METRIC, RADICAL, AND MOBIUS FRAME LAW PROVED]`
  `[METRIC-RIGID REGULAR SCHUR DIRECTION PROVED FROM CLASSICAL LOCAL PROLATE CONVERGENCE]`
  `[SOURCE-SPECIFIC ASSEMBLY] [EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
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
convergence does not imply convergence of `(AM1)`.  This kills the attempted **inference** that
the aperture metric converges to the source identity; it does not by itself prove that the two
metrics cannot agree in the particular prolate limit.

The no-go has a non-trivial positive survivor.  Finite Möbius inversion determines the exact
radical and gives a polynomial frame bound for the actual aperture metric.  That bound is already
subordinate to the `lambda^8` adjacent prolate hierarchy.  Consequently the canonical two-rung
Schur **direction** survives in the true-aperture-metric regular generalized pencil even before the
full metric limit is proved.

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

## Exact finite aperture Hilbert metric `[PROVED FOR lambda>1]`

Let `lambda>1`, and let `f,g` be point-evaluable even sources supported in
`[-lambda,lambda]`.  Expanding the finite sums in `(AM1)`
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

Put `S_f(u)=sum_(n>=1)f(nu)=E(f)(u)/sqrt(u)`.  Finite divisor Möbius inversion gives, pointwise for
`0<x<=lambda`,

```text
f(x)=sum_(1<=d<=floor(lambda/x)) mu(d) S_f(dx)
    =sum_(1<=d<=floor(lambda/x)) mu(d)E(f)(dx)/sqrt(dx).       (AM5a)
```

Indeed, after inserting the definition of `S_f`, the coefficient of `f(kx)` is
`sum_(d|k)mu(d)`, hence is one for `k=1` and zero otherwise.  Therefore the radical is exact:

```text
ker(R_lambda E) on sources supported in [0,lambda]
 ={f : f=0 on [lambda^(-1),lambda]}                           (AM5b)
```

up to null sets in an `L2` realization.  For even sources this is precisely the central aperture
gauge supported in `[-lambda^(-1),lambda^(-1)]`.  Thus `(AM1)` is a pre-Hilbert metric on the exact
quotient, isometric to `ran(R_lambda E)`; its Hilbert completion is the closure of that range.  No
closed-range claim is made.  On every finite analytic prolate span it is already strictly positive:
on `(max(lambda^(-1),lambda/2),lambda)`, only the `n=1` summand remains, so a zero metric vector
vanishes on an interval and hence identically.

More importantly, `(AM5a)` yields a quantitative local inverse.  For
`lambda^(-1)<=a<b<=lambda`, Cauchy--Schwarz gives

```text
|f(x)|^2
 <=floor(lambda/x)
   sum_(d<=lambda/x)|E(f)(dx)|^2/(d*x).
```

Integrating over `[a,b]`, setting `u=dx`, and observing that each `u` is hit by at most `u/a`
integers gives

```text
||f||^2_(L2[a,b]) <=(lambda/a) G^E_lambda(f,f).               (AM5c)
```

Conversely, direct Cauchy--Schwarz in the defining sum and a dilation change of variables give

```text
G^E_lambda(f,f) <=lambda^2 ||f||^2_(L2[0,lambda]).             (AM5d)
```

These bounds are statements about point-evaluable representatives, such as the analytic prolate
sources, not arbitrary ambient `L2` representatives.  They are compatible with `(AM5b)`: a global
source coercivity inequality is impossible because the central gauge is invisible.

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
`|xi(1/2+it)|^2dt`.  Hence the fixed-Hermite target is nondegenerate.  Its displayed off-diagonal
entry need not vanish for a generic positive moment sequence; no nonvanishing claim for the
specific Xi moments is used.

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

makes the upper folded channel continuous from `B_alpha` to `L2([1,infinity),d*u)`.  Together with
the zero-mean BV bound on `(0,1)`, it directly gives global `E`-graph convergence; `(AM8)` removes
the shrinking lower interval.  Thus `(AM18)` implies `(AM17)` and entrywise convergence to
`(AM12)` for every fixed finite family.

The local corpus currently invokes fixed-mode `W^(1,1)` convergence and the bound
`Var(g_(k,lambda)^+)=O(1)`, but has not proved the stronger weighted theorem `(AM18)`.  Therefore
`(WT16)` remains open and no limiting true eigenvalue constant is claimed unconditionally.

There is a sharper sufficient rate lemma.  Let `f_lambda` be supported in `[0,lambda]`, let `f` be
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

## Positive survivor without `(AM17)`: Möbius-frame-rigid Schur direction

Full zeta-graph convergence is stronger than what is needed to identify the leading source
direction.  Fix a finite depth `N` and one compact interval `[a,b]` in `(0,infinity)`.  Classical
fixed-mode local `L2` prolate-to-Hermite convergence makes the local source Gram converge to the
Gram of the limiting Hermite contrasts.  Analytic independence makes that limiting Gram positive
definite.  Hence, for some `m_N>0` and all sufficiently large `lambda`, `(AM5c)`--`(AM5d)` give

```text
(a*m_N/lambda) I <=G^E_(lambda,N)<=lambda^2 I.                (AM19)
```

This uses neither `(AM17)` nor global `W^(1,1)`/variation control.  The arithmetic bounds are
unconditional.  Their prolate specialization uses the classical local convergence in the exact
CCM normalization; that analytic parent input is paper-level and is not yet constructed in Lean.

For the first two regular Weil channels, write `L=log c`, `delta=sqrt(d_1/d_2)=O(lambda^(-4))`.
The numerator has the hierarchy

```text
Q_00~theta_0 D_0 d_1 L,
Q_01~s sqrt(theta_0 theta_1)D_1 sqrt(d_1d_2)L,
Q_11~theta_1 D_0 d_2 L.                                      (AM20)
```

The lower generalized eigenvalue satisfies `epsilon_-=O(lambda*d_1L)` by the `e_0` trial vector
and the lower floor in `(AM19)`.  In the second row of

```text
Q_lambda c=epsilon_- G^E_lambda c,
```

the metric correction to `Q_01` has relative size at most

```text
O(lambda^3*d_1/sqrt(d_1d_2))=O(lambda^(-1)),
```

and the correction to `Q_11` has relative size `O(lambda^(-5))`.  Therefore

```text
y/x
 =-s (D_1/D_0)sqrt(theta_0/theta_1)sqrt(d_1/d_2)
   +o(sqrt(d_1/d_2)).                                        (AM21)
```

This is the canonical `O(lambda^(-4))` Toeplitz/Schur direction in the **true-aperture-metric
generalized pencil for the regular two-rung numerator**.  The aperture metric has condition number
at most `O(lambda^3)` on the fixed span, whereas adjacent leakage scales separate by `lambda^8`;
the metric is asymptotically subordinate.  More generally, a leakage ratio `O(lambda^(-beta))`
survives these frame bounds whenever `beta>6`; the CCM exponent `8` clears the sharp threshold of
this argument by two powers.  This is not yet a statement about the full restricted-Weil operator.

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

- **Killed inference:** source `L2` convergence alone does not identify the aperture Gram with the
  source identity.  A global source lower bound is impossible because of the exact central radical
  `(AM5b)`.
- **Exact obstruction:** `E` is an unbounded zeta multiplier and the aperture has an invisible
  central source gauge; its fixed-Hermite image has the order-one `Xi^2` moment target `(AM12)`.
- **Positive survivor:** Möbius inversion classifies the entire radical and gives the local frame
  law `(AM5c)`--`(AM5d)`.  On fixed prolate spans, classical local convergence turns this into the
  polynomial conditioning `(AM19)`, subordinate to the `lambda^8` ladder.  Hence the regular
  two-rung Schur direction `(AM21)` is true-metric rigid without zeta-graph convergence.
- **Novelty audit:** the Hermite-to-polynomial-`Xi` factorization is already present in CCM
  Proposition 3.6; Hermite Mellin formulas, the zeta multiplier, positive polynomial moment Grams,
  the elementary arithmetic fold `(AM5)`, finite divisor Möbius inversion, and the sufficient
  graph-rate lemma `(AM18a)` are parent or bridge material.  No prior corpus card was found with the
  exact local frame law `(AM5c)`--`(AM5d)`, the radical equality `(AM5b)`, or their `beta>6`
  true-metric stability consequence, but these are a source-specific assembly of classical tools;
  external novelty is therefore **unverified**, not claimed.  Actual finite-prolate Gram convergence
  and the spectral constants
  `(AM22)`--`(AM23)` become candidate-new theorems only after `(AM18b)` or an equivalent estimate is
  proved.  External priority remains unverified.

## Lean status

The source-specific finite algebra is being formalized in
`GaloisForLFunctions.RHTower.ConstrainedProlateApertureXiMetric`:

- finite ray summation and its exact Möbius reconstruction, the algebraic engine of `(AM5a)`;
- the corresponding finite ray energy coercivity at the base source value;
- the limiting ground Hermite seed is identified exactly with the existing theta-cusp seed;
- its all-integer logarithmic source is identified with the existing `thetaCuspFullSource`;
- its Fourier transform is therefore the corresponding exact scalar multiple of `XiC`;
- the first two Xi-square metric entries have determinant
  `512/199395*(M_0*M_2-M_1^2)`;
- a strict symbolic Hankel-variance hypothesis makes the two-by-two determinant positive;
- the fixed-Hermite-target-normalized regular Schur coefficient reduces to `(AM22)` and retains
  the strict lower bound `3/(4M_0)`.

No Lean declaration assumes `(AM17)`, `(WT17)`, a true Weil spectral floor, or RH.

## Gates

- [x] define the exact second source contrast
- [x] derive the finite aperture metric `(AM4)` and primitive-ray form `(AM5)`
- [x] prove exact Möbius recovery, radical classification, and local frame bounds `(AM5a)`--`(AM5d)`
- [x] derive the exact Poisson fold `(AM7)` and lower-tail error `(AM8)`
- [x] identify the fixed Hermite metric as the Xi-square Gram `(AM12)`
- [x] compute the first two invariant polynomials and strict determinant
- [x] identify the ground contrast with the formal theta-cusp source
- [x] derive the polynomial metric bounds `(AM19)` from the Möbius frame law and classical local
      fixed-mode convergence
- [x] derive true-metric rigidity of the regular two-rung Schur direction `(AM21)` without `(AM17)`
- [x] reduce graph convergence to the sufficient BV plus sup-rate lemma `(AM18a)`
- [ ] prove the weighted fixed-mode PSWF convergence `(AM18)`
- [ ] conclude the actual aperture metric limit `(AM17)`
- [ ] formalize the analytic integral lift of the finite Möbius frame law and the normalized local
      prolate-to-Hermite mass floor
- [ ] prove the intact full-Weil bilinear graph defect `(WT17)`
- [ ] control the orthogonal complement / true global floor
