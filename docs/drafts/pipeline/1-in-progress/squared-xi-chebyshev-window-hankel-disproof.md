# Squared-Xi Chebyshev-window Hankel disproof criterion

- **ID:** `squared-xi-chebyshev-window-hankel-disproof`
- **Stage:** 1-in-progress
- **Type:** THEOREM / RH-FALSE source reduction
- **Scientific status:** `[BRIDGE] [PAPER PROOF COMPLETE BELOW]
  [TARGET POSITIVITY AND RH-FALSE ENDPOINT FORMALIZED] [NO RH DISPROOF WITNESS YET]`
- **Parents:** `squared-xi-radial-jet-reverse-bessel-source-alignment.md`;
  `squared-xi-radial-jet-chebyshev-window.md`;
  `seam-log-hankel-rh-equivalence.md`;
  `prime-arch-central-moment-germ.md`
- **Statement:** At every real absolute-Euler point `s=1/2+w>1`, the normalized squared-Xi
  radial jets form the complete shifted Hankel moment tower of the Möbius-translated reciprocal
  Xi divisor.  Each matrix entry is one completed Chebyshev window.  A single strictly negative
  finite quadratic value in these source entries proves `not RH`.

## 1. Translated reciprocal divisor

For a multiplicity copy `q` of the Xi divisor, put

```text
lambda_q = -(rho_q-1/2)^(-2),
tau_y(lambda)=lambda/(1+y*lambda),       y>=0.             (1)
```

The corpus proves `Re(lambda_q)>0` unconditionally.  Hence

```text
|1+y*lambda_q|^2
  =(1+y*Re(lambda_q))^2+y^2*Im(lambda_q)^2 >= 1,           (2)
```

so the denominator in `(1)` never vanishes and

```text
|tau_y(lambda_q)| <= |lambda_q|.                           (3)
```

The translated family is therefore absolutely summable.  It remains conjugation symmetric,
has no accumulation point except zero, and has infinite support because `tau_y` is injective.

Define its shifted moments

```text
T_n(y)=sum_q tau_y(lambda_q)^(n+1),       n>=0.             (4)
```

For `y<41/2`, the formal height bound `|lambda_q|<2/41` also gives the absolutely convergent
negative-binomial source transport

```text
T_n(y)=sum_(r>=0) (-1)^r binom(n+r,r) y^r T_(n+r)(0).      (5)
```

In particular `(5)` holds throughout the only scalar window left by the protected-sector
theorems, `1/4<y<8`.

## 2. Exact radial-jet identity

Let `Phi` be the unique entire function satisfying

```text
Phi(w^2)=xi(1/2+w),
```

which exists because the centered completed function is even.  Write

```text
L(s)=xi'(s)/xi(s),
F(w)=L(1/2+w)/w,
D=(1/(2w))*d/dw=d/dy,
y=w^2.
```

The multiplicity-exact reciprocal-resolvent identity gives

```text
F(w)=sum_q lambda_q/(1+w^2*lambda_q).                      (6)
```

Absolute local convergence permits differentiation, hence

```text
(-1)^n D^n F(w)/n! = T_n(w^2).                            (7)
```

For the reverse-Bessel radial polynomial from the parent card,

```text
Q_n(w)=sum_(j=0)^n (-1)^j b_(n,j) w^j L^(j)(1/2+w),
b_(n,j)=(2n-j)!/(2^(n-j)(n-j)!j!),
```

the already proved radial recurrence is

```text
Q_n(w)=(-1)^n 2^n w^(2n+1) D^n F(w).                      (8)
```

Combining `(7)` and `(8)` gives the exact normalized source identity

```text
T_n(w^2)=Q_n(w)/(2^n n! w^(2n+1)).                        (9)
```

No zero location is assumed in `(6)`--`(9)`.

## 3. RH-complete Hankel hierarchy at every absolute-Euler base point

For `N>=1`, define

```text
H_N(w)_(i,j)=T_(i+j)(w^2)
 =Q_(i+j)(w)/(2^(i+j)(i+j)!w^(2(i+j)+1)),  0<=i,j<N.      (10)
```

If RH holds, every `lambda_q` is positive real, hence every translated atom
`tau_(w^2)(lambda_q)` is positive real.  For a nonzero real vector `c` and
`p_c(X)=sum_i c_i X^i`,

```text
c^T H_N(w)c
 =sum_q tau_(w^2)(lambda_q)*p_c(tau_(w^2)(lambda_q))^2
 >0.                                                       (11)
```

Strictness follows from the infinite transformed support: a nonzero polynomial cannot vanish on
every atom.  Thus RH implies that every `H_N(w)` is positive definite.

Conversely, all-order positive semidefiniteness isolates every transformed atom by the same
countable-compact polynomial approximation used in the central seam-log criterion.  It forces
every `tau_(w^2)(lambda_q)` to be positive real.  Since

```text
Im(tau_y(lambda))=Im(lambda)/|1+y*lambda|^2,               (12)
```

all `lambda_q` are real; their unconditional positive real part makes them positive.  This is RH.
Consequently, at any one fixed `w>1/2`, the full hierarchy `(10)` is RH-equivalent.

For the RH-false direction, only the easy half is needed:

```text
exists N c, c!=0 and c^T H_N(w)c<0   ==>   not RH.         (13)
```

## 4. Completed Chebyshev-window source matrix

Put `s=1/2+w`, `a=s-1`, and

```text
B_n(z)=sum_(j=0)^n b_(n,j)z^j,
f_(n,s)(x)=x^(-s)B_n(w log x),
d_n(w)=2^n n!w^(2n+1).
```

The parent Chebyshev-window theorem gives

```text
Q_n(w)=C_n(s)+integral_[1,infinity) f_(n,s)(x)d(x-psi(x)). (14)
```

Therefore `(10)` is the source-built matrix identity

```text
H_N(w)_(i,j)
 =C_(i+j)(s)/d_(i+j)(w)
  +integral_[1,infinity)
     f_(i+j,s)(x)/d_(i+j)(w) d(x-psi(x)).                 (15)
```

Equivalently, for a real vector `c`, define

```text
A_(c,s)=sum_(i,j)c_i*c_j*C_(i+j)(s)/d_(i+j)(w),
K_(c,s)(x)=sum_(i,j)c_i*c_j*f_(i+j,s)(x)/d_(i+j)(w).
```

Then

```text
c^T H_N(w)c
 =A_(c,s)+integral_[1,infinity)K_(c,s)(x)d(x-psi(x)).      (16)
```

This is a source reduction, not a restatement through zeros: `C_n`, `B_n`, and `psi` are the
completed Gamma, finite reverse-Bessel, and prime-counting data.  Unlike a scalar alternating
derivative, the full family `(16)` is architecturally complete for RH.

## 5. Exact quadratic-band kernel

The reverse-Bessel polynomial has the positive integral representation

```text
B_n(wt)=1/n! * integral_0^infinity
  exp(-u) u^n (w*t+u/2)^n du.                             (17)
```

With

```text
r_(w,t)(u)=u*(w*t+u/2)/(2*w^2),
P_c(r)=sum_(i,j)c_i*c_j*r^(i+j)/((i+j)!)^2,
```

the source kernel in `(16)` becomes

```text
K_(c,s)(exp(t))
 =exp(-s*t)/w * integral_0^infinity exp(-u)P_c(r_(w,t)(u))du.  (18)
```

Thus a Hankel combination is not merely a signed sum of nearby prime windows.  It is an exact
finite polynomial filter averaged against one exponential auxiliary variable.  If
`C_c(z)=sum_i c_i z^i`, then the coefficient of `r^n` in `P_c` is the coefficient of `z^n` in
`C_c(z)^2`, divided by `(n!)^2`.

For the first nonconstant probe `N=2`, take `c=(1,-alpha)` with `alpha>0`.  Then

```text
P_c(r)=1-2*alpha*r+alpha^2*r^2/4.                         (19)
```

Using `integral exp(-u)u^k du=k!`, equation `(18)` is

```text
K_(c,s)(exp(t))=exp(-s*t)/w * Pbar_(alpha,w)(t),

Pbar_(alpha,w)(t)
 =1-alpha*(w*t+1)/w^2
   +alpha^2*(w^2*t^2+3*w*t+3)/(8*w^4).                   (20)
```

Its discriminant is

```text
Delta=alpha^2*w^2*(32*w^4-16*alpha*w^2-3*alpha^2).       (21)
```

Hence, whenever

```text
0<alpha/w^2<4*(sqrt(10)-2)/3,                             (22)
```

the normalized source kernel is strictly negative on the explicit logarithmic band

```text
t_- < t < t_+,
t_+-t_-=sqrt(32*w^4-16*alpha*w^2-3*alpha^2)/(alpha*w),
t_++t_-=(8*w^2-3*alpha)/(alpha*w).                        (23)
```

This identifies a real source mechanism: coefficient polarization creates a movable negative
band even though each scalar reverse-Bessel window is positive.  It does not yet give the sign of
the completed discrepancy `(16)`.  At `N=2`, optimizing over `alpha` is exactly the first Hankel
minor test `T_0*T_2-T_1^2`; the corpus still treats the corresponding central source minor as an
open theta-cusp inequality.  Therefore `(20)` is a diagnostic and a template for higher-rank
filters, not a claimed disproof.

## Binomial high-rank audit: hyper-Bessel hard edge and its collapse

The most economical all-rank family is

```text
C_(m,R)(z)=(1-z/R)^m,
c_i=(-1)^i*binom(m,i)*R^(-i).                            (24)
```

Because `C_(m,R)(z)^2=(1-z/R)^(2m)`, its filter in `(18)` is exactly

```text
P_(m,R)(r)
 =sum_(n=0)^(2m) (-1)^n binom(2m,n)(r/R)^n/(n!)^2
 ={}_1F_2(-2m;1,1;r/R).                                 (25)
```

Fix `R_0>0` and take the hard-edge scaling `R_m=2mR_0`.  Then, uniformly for `r` in every compact
subset of the complex plane,

```text
P_(m,R_m)(r) -> {}_0F_2(;1,1;-r/R_0)
 =sum_(n>=0)(-1)^n(r/R_0)^n/(n!)^3.                     (26)
```

Indeed

```text
binom(2m,n)/(2m)^n <= 1/n!,
binom(2m,n)/(2m)^n -> 1/n!
```

for every fixed `n`; the compact majorant is `sum M^n/(n!)^3`.  This is the direct dominated-series
proof of `(26)`.  Van Assche's Mehler--Heine theorem identifies the same generalized-Bessel hard
edge, and its positive-zero theorem applies at the parameters `(1,1)`; see
`https://arxiv.org/abs/1408.6140`.  Thus the auxiliary polynomial filters really do acquire
cofinal oscillatory bands.  This is not a numerical observation.

The completed quadratic, however, has a different and decisive limit.  Writing
`tau_q=tau_(w^2)(lambda_q)`, equations `(10)`--`(11)` give

```text
V_m
 :=sum_q tau_q*C_(m,R_m)(tau_q)^2
 =sum_q tau_q*(1-tau_q/(2mR_0))^(2m)
 ->sum_q tau_q*exp(-tau_q/R_0).                          (27)
```

The interchange is unconditional: `(3)` gives `sum_q|tau_q|<infinity` and the summands are bounded
by `|tau_q|*exp(|tau_q|/R_0)`, with the transformed atoms uniformly bounded.  Hence the
rank-proportional hyper-Bessel scaling collapses to one Laplace probe of the same unknown
translated divisor.  Negative bands in `(26)` are exactly balanced by the completed source
integral unless the value in `(27)` is independently proved negative.  They do not by themselves
supply such a proof.

The fixed-scale family `R_m=R` has a complementary exact interpretation.  For
`rho=1/2+a+i*gamma`,

```text
1/tau_(w^2)(lambda_rho)
 =w^2+1/lambda_rho,
Re(1/tau_(w^2)(lambda_rho))=w^2+gamma^2-a^2.             (28)
```

Consequently

```text
|1-tau/R|^2
 =1+|tau|^2/R^2*(1-2R*Re(1/tau)).                       (29)
```

So `(24)` is only a radial-energy threshold at `Re(1/tau)=1/(2R)`: it suppresses or amplifies an
atom according to `w^2+gamma^2-a^2`, not according to whether `a` vanishes.  Any lower-energy
critical-line atoms remain dominant unless they are separately deflated.  Choosing their roots
from the Xi divisor would make the construction target-fed; proving their source-side deflation is
the original open problem.

**Anti-theatre verdict.**  Both natural binomial scalings are now exhausted.  The hard-edge
scaling produces a rigorous oscillatory kernel but collapses to the unresolved Laplace value
`(27)`; the fixed scaling is a radial-energy selector, not an off-line selector.  A viable
high-rank family must instead cancel explicit polar/Gamma source modes while retaining a strict
one-sided Chebyshev discrepancy, and that cancellation has to be proved after completion.

## Open source core

`[CONJECTURE]` There exist an exact real `w>1/2`, an integer `N>=2`, and a nonzero rational vector
`c` such that the completed Chebyshev-window value `(16)` is strictly negative.

The next task is not another moment-coordinate recoding.  It is to construct `c` so that the
nearby exponential windows in `K_(c,s)` cancel the protected polar/Gamma modes while retaining a
one-sided Chebyshev discrepancy.  The exact polynomial-filter form `(18)` makes high-rank,
source-fixed rational families the live lane; stopping at the first `2 x 2` band would only rename
the already open first-minor problem.  A proof of the conjecture, followed by `(13)`, is an
unconditional proof that RH is false.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/XiShiftedReciprocalHankelDisproof.lean` defines the translated
atoms, their multiplicity-exact moments, and the finite real Hankel quadratic.  It proves
unconditionally:

```text
summable_xiShiftedReciprocalSquare_pow
xiShiftedReciprocalHankelQuadratic_nonneg_of_riemannHypothesis
not_riemannHypothesis_of_xiShiftedReciprocalHankelQuadratic_neg
```

The module is wired into the `RHTower` umbrella.  Its touched-file check and exact target build
pass.  The public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  The full
formal lint still reports unrelated concurrently unwired RHTower and HTGeometry modules, but does
not report this module.

## Gates

- [x] translated reciprocal family is absolutely summable
- [x] exact transformed-moment formula `(7)`
- [x] exact radial normalization `(9)`
- [x] RH implies strict positivity of every finite source Hankel block
- [x] all-order converse at a fixed absolute-Euler base point
- [x] exact completed Chebyshev-window quadratic identity `(16)`
- [x] exact polynomial-filter representation `(18)` and first movable negative band `(20)`
- [x] formalize the translated reciprocal moments and RH-implied Hankel positivity
- [ ] formalize the analytic radial/source identity `(9)`
- [ ] prove one strict negative source quadratic value
- [x] formalize `strict negative quadratic -> not RiemannHypothesis`
