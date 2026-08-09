# Physical prime-log aperture fusion and the off-diagonal RH kernel

- **ID:** `xi-physical-prime-log-aperture-fusion-cross-kernel`
- **Stage:** `3-formalized`
- **Formalized companion:** `xi-physical-prime-log-aperture-fusion-cross-kernel-formalized.md`
- **Type:** `THEOREM / NEW RH-PROOF-SHAPE OBJECT / POSITIVE SURVIVOR`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED FINITE CORE] [SOURCE-DEFINED]`
  `[UNCONDITIONAL] [NOVELTY UNVERIFIED]`
  `[CANDIDATE NEW PROJECT-LEVEL SCIENTIFIC KNOWLEDGE]`
  `[PARENT INTERVAL-COVARIANCE ALGEBRA STANDARD]`
  `[EXTERNAL SOURCE-SPECIFIC NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `physical-prime-endpoint-radical-mesh-coercivity.md`,
  `fcrj-corrected-response-saturation-law.md`,
  `xi-terminal-conditioned-true-aperture-hilbert-metric.md`,
  `XiAperturePhysicalEndpointResponseRenormalization.lean`, and the
  coordinate-relative prime-layer independence results in `XiShiftPrimeHypertranscendence.lean`.

## Why this object is needed

The terminal-conditioned true-aperture metric is prime-diagonal.  It removes a radial terminal
mode but preserves normalized aperture correlations and, at the critical joint germ, preserves
all relative prime weights.  It therefore cannot create the missing RH gain.

The physical endpoint carrier does something genuinely different: it maps all independent prime
rays into one common log-aperture space *before* the norm square.  This creates a forced
off-diagonal interaction between distinct primes.  The present card identifies that fusion map,
its exact kernel, the continuum mode it annihilates, and the precise off-diagonal object left after
the already-harmless diagonal is removed.

## The fusion map

Fix `A>0`, logarithmic endpoints `m<k`, and put `c=k-m`.  In the physical application

```text
m=log M,   k=log K,   0<c<A.
```

For an ordinary prime `p`, define its clipped physical aperture interval

```text
I_p=(0,A] intersect (m-log p,k-log p],
ell_p=length(I_p),
w_p=log p/p.
```

Its centered aperture feature is

```text
phi_p(u)=1_(I_p)(u)-ell_p/A * 1_((0,A])(u).             (PFK1)
```

For a finite active prime packet `P`, define the coherent physical fusion

```text
F_(m,k,A;P)(u)=sum_(p in P) w_p phi_p(u).               (PFK2)
```

This is not a direct sum over primes.  Every prime is sent into the same `L^2(0,A)` target, so the
norm square necessarily contains `p != q` terms.

## Exact moving-window identity

For `0<u<=A`, interval membership is equivalent to

```text
u in I_p  iff  m-u<log p<=k-u.
```

Consequently the raw fused flux is the moving logarithmic prime window

```text
W_P(u)=sum_(p in P, m-u<log p<=k-u) log p/p,            (PFK3)
```

and

```text
F_(m,k,A;P)(u)
 =1_((0,A])(u) [W_P(u)-A^(-1) integral_0^A W_P(v)dv].  (PFK4)
```

For `m=log M` and `k=log K`, `(PFK3)` is equivalently

```text
W_P(u)=sum_(p in P, M exp(-u)<p<=K exp(-u)) log p/p.
```

Thus the endpoint carrier from `(HGS29)` is exactly a centered moving prime-log flux, not a sum of
independent prime energies.

## Continuum annihilation and the discrepancy measure

Let

```text
mu_P=sum_(p in P)(log p/p) delta_(log p),
lambda=Lebesgue measure on the log-prime coordinate,
nu_P=mu_P-lambda.
```

Every moving window has the same Lebesgue mass:

```text
lambda((m-u,k-u])=k-m=c.                               (PFK5)
```

Centering kills this constant exactly.  Hence

```text
F_(m,k,A;P)
 =Center_A[u |-> nu_P((m-u,k-u])].                     (PFK6)
```

Equation `(PFK6)` is the missing representation change.  The operator consumes only source data,
annihilates the continuum log-prime density before squaring, and measures the aperture-filtered
prime-log discrepancy.  It is nonlocal in the prime label even though the underlying HT prime
layers remain differentially independent.

## Exact cross-prime Gram kernel

Put

```text
kappa_(m,k,A)(p,q)
 =length(I_p intersect I_q)-ell_p ell_q/A.              (PFK7)
```

Then

```text
integral_0^A phi_p(u)phi_q(u)du=kappa_(m,k,A)(p,q),

||F_(m,k,A;P)||_2^2
 =sum_(p,q in P)w_p w_q kappa_(m,k,A)(p,q).             (PFK8)
```

For two bulk primes, meaning neither interval is clipped,

```text
I_p=(m-log p,k-log p],
I_q=(m-log q,k-log q],
ell_p=ell_q=c,
```

and the kernel becomes the exact logarithmic tent

```text
kappa_(m,k,A)(p,q)
 =max(0,c-|log p-log q|)-c^2/A
 =max(0,c-|log(p/q)|)-c^2/A.                           (PFK9)
```

This is the required distinct-prime coupling.  The positive part connects precisely primes in the
multiplicative ratio band `exp(-c)<p/q<exp(c)`; the negative rank-one term is the aperture mean
removed before squaring.

## Diagonal removal theorem

Split the exact energy into

```text
D_diag=sum_(p in P)w_p^2 kappa(p,p),
C_cross=sum_(p,q in P,p!=q)w_p w_q kappa(p,q).
```

Since

```text
kappa(p,p)=ell_p(1-ell_p/A),
0<=ell_p<=A,
```

one has

```text
0<=D_diag,
||F||_2^2=D_diag+C_cross,
C_cross>=-D_diag.                                      (PFK10)
```

Every active prime lies in `M exp(-A)<p<=K`, and `ell_p<=A`.  Therefore, for fixed `A` and fixed
ratio `K/M=exp(c)`,

```text
D_diag
 <=A sum_(p>M exp(-A))(log p/p)^2
 <=A sum_(n>M exp(-A))(log n/n)^2
 <<_A log(M)^2/M.                                      (PFK11)
```

The final estimate follows from the elementary decreasing-tail integral

```text
sum_(n>=N)(log n/n)^2
 <<(log(N)^2+2log(N)+2)/N.
```

Thus the complete prime-diagonal contribution is already inside the allowed RH error budget.  The
remaining RH-strength upper bound is, up to this unconditional diagonal term, exactly

```text
C_cross <<_(A,rho) log(M)^b/M.                         (PFK12)
```

The lower side `C_cross>=-D_diag` is automatic.  The open content is the positive excess of the
signed off-diagonal overlap over the continuum rank-one background.

## Exact renormalized pair excess

The off-diagonal object has a sharper source-side form.  Define

```text
O_cross=sum_(p!=q) w_p w_q length(I_p intersect I_q),
L_mass =sum_p w_p ell_p,
L_diag =sum_p (w_p ell_p)^2.
```

Then finite expansion of the square gives the exact identity

```text
C_cross
 =O_cross-(L_mass^2-L_diag)/A.                            (PFK12a)
```

Thus the RH-facing term is not an unspecified cancellation inside a Hilbert norm.  It is the
upper excess of the literal distinct-prime overlap mass over the continuum mean-field pair mass;
the self-pair mass has already been removed exactly.  In the bulk, `O_cross` only sees pairs in
the multiplicative band `exp(-c)<p/q<exp(c)`.

## Width-curvature tomography of prime ratios

The preceding pair excess contains a still sharper invariant when the physical width is varied.
For the untruncated bulk kernel put

```text
d(p,q)=|log p-log q|,
C_bulk(c)=sum_(p!=q)w_p w_q [max(0,c-d(p,q))-c^2/A],
W_off=sum_(p!=q)w_p w_q,
B_(c,h)=sum_(p!=q)w_p w_q max(0,h-|d(p,q)-c|).
```

For every `h>=0`, the scalar ReLU identity

```text
max(0,x+h)+max(0,x-h)-2max(0,x)
 =max(0,h-|x|)
```

and the exact second difference of `c^2` give

```text
C_bulk(c+h)+C_bulk(c-h)-2C_bulk(c)
 =B_(c,h)-(2h^2/A)W_off.                                (PFK12b)
```

This is an exact aperture-width tomography law.  The positive term is supported precisely on

```text
| |log(p/q)|-c |<h,
```

so width curvature localizes the distinct-prime ratio measure to a triangular shell around the
chosen logarithmic ratio.  The rank-one continuum subtraction becomes the explicit uniform
background `(2h^2/A)W_off`; it creates no ratio atoms and hides no diagonal term.

Since all physical endpoint weights are positive,

```text
B_(c,h)>=0,
C_bulk(c+h)+C_bulk(c-h)-2C_bulk(c)
  >=-(2h^2/A)W_off                                      (PFK12c)
```

for `A>0`.  Hence the compensated cross defect is unconditionally semiconvex in width, with its
entire singular positive curvature carried by actual multiplicative prime ratios.  In the limit
language, the distributional width curvature is the weighted off-diagonal prime-ratio measure
minus the constant continuum background.  No limiting or distributional argument is needed for
`(PFK12b)` itself.

There is also an exact finite atom-recovery theorem, with no limiting language.  Put

```text
M_P(c)=sum_(p!=q, d(p,q)=c) w_p w_q.
```

The finite set of values `d(p,q)` has a positive separation from every other value at `c`.
Therefore there exists `h>0` such that the triangular shell meets no distance except `c`, and

```text
B_(c,h)=h M_P(c),

C_bulk(c+h)+C_bulk(c-h)-2C_bulk(c)
 =h M_P(c)-(2h^2/A)W_off.                               (PFK12d)
```

Thus the width profile of the true physical aperture metric determines the complete finite
weighted prime-ratio measure atom by atom.  The continuum mode contributes only the smooth
quadratic background and disappears from the first-order cusp coefficient.  This is the precise
positive inversion statement exposed by the cross-defect representation.

For ordinary primes the recovered ratio spectrum is simple after forgetting orientation.  If
`p!=q`, unique factorization gives

```text
|log p-log q|=|log r-log s|
 iff (p=r and q=s) or (p=s and q=r).                     (PFK12e)
```

Indeed equality of absolute log differences exponentiates to `p/q=r/s` or `p/q=s/r`; cross
multiplication and primality force equality of the reduced prime fractions.  Consequently, for
`p,q in P`, `p!=q`,

```text
M_P(|log p-log q|)=2w_p w_q,
```

and some `h>0` satisfies the individual-pair recovery law

```text
Delta_h^2 C_bulk(|log p-log q|)
 =2h w_p w_q-(2h^2/A)W_off.                              (PFK12f)
```

Thus finite physical aperture-width data does not merely detect a blurred pair statistic: after
the continuum background is removed, it reconstructs every unordered prime pair and its exact
weight product.

The curvature law also shows that atom recovery is not the cancellation theorem.  Define the
ordered cumulative ratio mass and its continuum discrepancy by

```text
N_P(c)=sum_(p!=q, d(p,q)<=c) w_p w_q,
D_P(c)=N_P(c)-(2c/A)W_off,
R_P(c,h)=sum_(p!=q, c<d(p,q)) w_p w_q max(0,c+h-d(p,q)).
```

For every `h>=0`, the one-sided ReLU increment gives the exact Green--discrepancy law

```text
C_bulk(c+h)-C_bulk(c)
 =h D_P(c)+R_P(c,h)-(h^2/A)W_off.                        (PFK12g)
```

The boundary ramp `R_P(c,h)` is nonnegative and is supported only on the new ratio sites
`c<d(p,q)<c+h`.  Since a finite packet has a finite ratio spectrum, every `c` has an `epsilon>0`
such that, simultaneously for all `0<h<=epsilon`, this shell is empty.  Hence

```text
C_bulk(c+h)-C_bulk(c)+(h^2/A)W_off=hD_P(c).             (PFK12h)
```

Thus the right germ of the physical aperture-width profile recovers the *signed cumulative
prime-ratio discrepancy* exactly.  The second difference reconstructs individual ratio atoms;
the first difference is the first place where different ratio sites can cancel.  This separates
the lossless tomography theorem from the RH-facing analytic mechanism.

There is a corresponding sharp no-go.  At a prime-ratio site `c=d(p,q)`, `(PFK12f)` holds for
every sufficiently small positive `h`, not merely one selected `h`.  The continuum-compensated
curvature is therefore

```text
Delta_h^2 C_bulk(c)+(2h^2/A)W_off=2h w_p w_q.           (PFK12i)
```

It has an unavoidable linear cusp and cannot satisfy a local `O(h^2)` upper bound.  Any proof
strategy based on pointwise quadratic flatness of the compensated curvature is therefore
impossible.  A viable estimate must act on the Green primitive `(PFK12g)` or average across
different ratio sites; unique factorization leaves no cancellation inside one ordinary-prime
ratio atom.

This cusp belongs coefficientwise to the actual shifted hypertranscendental Xi source.  Write

```text
a_p=w_p(1-p^(-2)),    r_p=log(p)/p^3,
R_(p,q)=2(a_p r_q+r_p a_q+r_p r_q).
```

Then `w_p=a_p+r_p`, so the symmetric-square atom has the exact decomposition

```text
2w_p w_q=2a_p a_q+R_(p,q),
Delta_h^2 C_bulk(d(p,q))+(2h^2/A)W_off
 =h(2a_p a_q+R_(p,q))                                  (PFK12j)
```

throughout the same sufficiently small punctured width neighborhood.  The first term is the
ordinary-prime symmetric-square coefficient of the one-unit-shifted filtered source whose actual
upper-end carrier is Lean-proved hypertranscendental over the genuine `C(z)`; the second is the
complete inverse-cubic correction, not an unnamed asymptotic remainder.

The two germ laws combine into an exact finite spline classification.  For every width `c`, one
positive `epsilon` works for every `0<h<=epsilon` and gives

```text
C_bulk(c+h)=C_bulk(c)+hD_P(c)-(h^2/A)W_off,
C_bulk(c-h)=C_bulk(c)-h(D_P(c)-M_P(c))-(h^2/A)W_off.         (PFK12k)
```

Thus a finite aperture profile is locally quadratic everywhere.  It is one quadratic chamber
across a width with `M_P(c)=0`; at an ordinary-prime ratio knot its one-sided linear coefficients
jump by exactly `M_P(c)=2w_p w_q`.  This is the sharp finite/infinite boundary exposed by the HT
comparison: no fixed finite prime packet can carry local hypertranscendental complexity in the
width coordinate.  Such complexity can enter only through a cofinal limit in which ratio knots
cease to be locally finite.  Density of the full logarithmic prime-ratio set is a standard
consequence of the prime number theorem, not a new claim here and not yet a Lean dependency of
this card.

The new RH-strength core is therefore cumulative: control the excess of `N_P(c)` over its linear
continuum background in an integrated sense strong enough to control `(PFK12g)`.  Requiring the
atom-scale curvature itself to be quadratically small is ruled out by `(PFK12i)`.

## Prime-power completion is stable at exactly the RH norm scale

The ordinary-prime measure has a canonical completion

```text
mu_Lambda=sum_(n>=2) Lambda(n)/n delta_(log n).
```

Its difference from `mu_P` is the positive proper-prime-power measure

```text
Q=sum_p sum_(r>=2) log(p)/p^r delta_(r log p).           (PFK13)
```

If the physical aperture is based at `M`, every active atom has `n>M exp(-A)`.  Put
`X=M exp(-A)`.  Enlarging primes to all integer bases and splitting `r=2` from `r>=3` gives

```text
sum_(p,r>=2,p^r>X) log(p)/p^r << log(X)/sqrt(X).         (PFK14)
```

For `r=2`, this is the integral-test tail of `sum log(n)/n^2`.  For `r>=3`, reverse the order of
summation.  If

```text
r_0(n)=max(3,ceil(log X/log n)),
```

then

```text
sum_(r>=r_0(n))log(n)/n^r
 <=2 log(n) min(n^(-3),X^(-1)).                         (PFK15)
```

Splitting at `n=X^(1/3)` makes the total `r>=3` contribution
`O(log(X)/X^(2/3))`, smaller than `(PFK14)`.

Every centered aperture interval feature has norm at most `sqrt(A)`, since its norm square is
`ell(1-ell/A)<=A`.  The triangle inequality and `(PFK14)` therefore give

```text
||Fusion_A(mu_Lambda)-Fusion_A(mu_P)||_2
 <<_A log(M)/sqrt(M),                                  (PFK16)

||Fusion_A(mu_Lambda)-Fusion_A(mu_P)||_2^2
 <<_A log(M)^2/M.                                      (PFK17)
```

Consequently an `O(polylog(M)/sqrt(M))` norm bound, equivalently an
`O(polylog(M)/M)` energy bound, holds for the ordinary-prime carrier if and only if it holds for
the fully completed von Mangoldt carrier.  This is not a termwise energy comparison; it is a
critical-norm stability theorem, so the cross term is handled by the triangle inequality at the
norm level.

## Divisor-facing interpretation and noncensorship

For `Re(s)>0`, the completed discrepancy measure has exact Laplace transform

```text
integral exp(-s x)d(mu_Lambda-lambda)(x)
 =-zeta'(1+s)/zeta(1+s)-1/s.                           (PFK18)
```

The subtraction cancels the polar mode at `s=0`.  A width-`c` moving-window coboundary multiplies
an exponential mode `exp(sx)` by

```text
B_c(s)=exp(c s)-1.                                     (PFK19)
```

If `c>0` and `Re(s)<0`, then `B_c(s)!=0`, because `|exp(cs)|=exp(c Re(s))<1`.  Subtracting the
aperture mean cannot kill the remaining mode: `exp(-su)` is not constant on `(0,A]` when
`A>0` and `Re(s)<0`.  Every nontrivial zeta-zero mode has `s=rho-1` in this left half-plane.

Thus this one physical operator has the exact selector profile that the prime-diagonal terminal
metric lacked:

```text
continuum/zeta-pole mode s=0        -> annihilated,
every nontrivial divisor mode s=rho-1 -> retained.      (PFK20)
```

Sharp-window noncensorship itself is standard and already appears in the project's bounded-
variation prime-window tomography.  The new point here is `(PFK16)`--`(PFK17)`: the actual
ordinary-prime endpoint carrier can be replaced at the critical RH norm scale by precisely the
completed source to which `(PFK18)` applies.

## Exact bridge to the hypertranscendental Xi-shift source

The rationally corrected `+2` shift of `xi'/xi` exposes the actual coefficient

```text
a_HT(n)=Lambda(n)(1-n^(-2)).                            (PFK21)
```

`XiShiftPrimeHypertranscendence.lean` proves that this source's upper-end meromorphic carrier is
hypertranscendental over the embedded rational coordinate field.  Shift the Dirichlet source one
unit to the right.  Its log-measure weight is

```text
a_HT(n)/n=Lambda(n)/n-Lambda(n)/n^3.                   (PFK22)
```

On primes, `(PFK22)` is the exact endpoint renormalization

```text
log(p)/p
 =[log(p)/p](1-p^(-2))+log(p)/p^3.                    (PFK23)
```

On the whole von Mangoldt source, the correction beyond an active lower endpoint `X` satisfies

```text
sum_(n>X) Lambda(n)/n^3
 <=sum_(n>X)log(n)/n^3
 <<log(X)/X^2.                                         (PFK24)
```

Its fused aperture norm is therefore `O_A(log(M)/M^2)`, far below `(PFK16)`.  Combining
`(PFK16)` and `(PFK24)` gives

```text
Fusion_A(ordinary prime endpoint)
 =Fusion_A(one-unit-shifted HT Xi source)
   +O_A(log(M)/sqrt(M)) in L^2 norm.                   (PFK25)
```

The dominant correction in `(PFK25)` is exactly the proper-prime-power completion, not the Xi
shift filter.  This is the rigorous HT-to-RH role separation:

```text
coordinate-relative HT  -> faithful independent source before fusion,
physical aperture fusion -> forced non-diagonal prime interaction,
cross-defect estimate    -> still-open RH-strength analytic theorem.
```

Hypertranscendence does not prove the final estimate, but the new kernel is now attached to the
actual HT source rather than to an invented parallel model.

## Paper proof

Equation `(PFK3)` is the two linear inequalities obtained from membership in
`(m-log p,k-log p]`.  Summing its indicators and subtracting their aperture means gives `(PFK4)`.
Translation invariance of Lebesgue measure gives `(PFK5)` and therefore `(PFK6)`.

Expanding the product in `(PFK1)` gives

```text
integral phi_p phi_q
 =length(I_p intersect I_q)
  -ell_p ell_q/A-ell_p ell_q/A+ell_p ell_q/A,
```

which is `(PFK7)`.  Finite bilinearity gives `(PFK8)`.  For two untruncated intervals of common
length `c`, their overlap is the triangular autocorrelation
`max(0,c-|log p-log q|)`, proving `(PFK9)`.

For `(PFK12a)`, expand the square of `L_mass`; its diagonal is `L_diag` and its remaining ordered
terms are exactly `sum_(p!=q)w_p w_q ell_p ell_q`.  Substitution into `(PFK7)` proves the identity.
For `(PFK12b)`, apply the scalar ReLU second-difference identity term by term; the quadratic
background has second difference `2h^2/A`.  Positivity of `w_p`, `w_q`, and the triangular shell
gives `(PFK12c)`.  Finally the set of off-diagonal distances of a finite packet is finite.  Choose
`h>0` no larger than the distance from `c` to every unequal distance value.  Each shell term is
then `h` when `d(p,q)=c` and zero otherwise, proving `(PFK12d)`.
For `(PFK12e)`, remove the absolute value into the two possible orientations, exponentiate, and
cross-multiply.  A prime dividing the resulting product divides one of its two prime factors; the
off-diagonal hypothesis excludes the wrong factor, and cancellation gives the second equality.
The two ordered orientations then give `(PFK12f)` from `(PFK12d)`.
For `(PFK12g)`, use

```text
(x+h)_+-x_+=h                         when x>=0,
(x+h)_+-x_+=(x+h)_+                  when x<0
```

with `x=c-d(p,q)` and sum over ordered distinct pairs.  The first case gives `hN_P(c)`; the second
is exactly `R_P(c,h)`.  The quadratic continuum term changes by
`(2ch+h^2)W_off/A`; regrouping its linear part with `N_P(c)` gives `(PFK12g)`.
Choose `epsilon` no larger than the positive distance from `c` to every ratio site strictly to its
right.  Then `R_P(c,h)=0` for all `0<h<=epsilon`, proving `(PFK12h)`.  Choosing `epsilon` smaller
than the distance from `d(p,q)` to every other ratio site and using `(PFK12e)` proves `(PFK12i)`.
Substitute `w_p=a_p+r_p` and expand the product to obtain `(PFK12j)`.  Finally intersect the
isolation radii in `(PFK12h)` and `(PFK12d)`.  The right formula in `(PFK12k)` is `(PFK12h)`
rearranged; subtracting it from the isolated symmetric second-difference formula gives the left
formula.  If `M_P(c)=0` the branches glue, while `(PFK12e)` gives the displayed prime-pair jump.

On the diagonal, `length(I_p intersect I_p)=ell_p`, proving the first part of `(PFK10)`.
Nonnegativity of the full square gives `C_cross>=-D_diag`.  Finally `(PFK11)` follows from the
active-prime range, `ell_p<=A`, enlargement from primes to integers, and the integral test.

No zero, RH hypothesis, numerical experiment, or conditional analytic input occurs in these
identities.

## Hostile audit

1. **Prime-diagonal multiplier?** No.  `(PFK7)`--`(PFK9)` contain literal `p != q` overlaps.
2. **Finite invertible aperture coordinate change?** No.  The fusion maps all prime rays into one
   common function space and is highly non-injective.
3. **Squaring too early?** No.  The continuum subtraction and complete prime fusion occur in
   `(PFK2)`--`(PFK6)` before `(PFK8)` forms a square.
4. **Differential-algebraic relation among prime layers?** No.  The operator is an archimedean
   pushforward of the independent prime source, consistent with coordinate-relative HT.
5. **Endpoint covariance under another name?** The full energy is the endpoint covariance, but
   `(PFK10)`--`(PFK12)` remove its entire prime-diagonal part unconditionally and isolate an
   explicit distinct-prime kernel.  The new open object is not the old norm with a new symbol.
6. **Source-circular?** No.  `mu_P`, Lebesgue measure, the moving window, and the centering are fixed
   from primes and the physical aperture before any Xi-zero or endpoint estimate is read.
7. **Generalized-prime/log-phase stress test?** A coherent burst creates a large discrepancy under
   `(PFK6)` and therefore is not falsely declared harmless.
8. **Prime-power completion hiding a larger error?** No.  `(PFK14)`--`(PFK17)` place the complete
   correction at the same `M^(-1/2)` norm scale required by RH.
9. **HT source only metaphorically related?** No.  `(PFK21)`--`(PFK25)` give the exact coefficient
   shift and the quantitative norm correction to the formalized Xi-shift carrier.
10. **Does ratio tomography itself create cancellation?** No.  `(PFK12i)` shows the opposite:
    every ordinary-prime ratio site has a forced positive linear cusp.  This kills pointwise
    quadratic-curvature strategies and moves the open core to cumulative inter-site discrepancy.
11. **A renamed fixed-ratio Selberg kernel?** The triangular kernel and UFD site simplicity are
    already parent/corpus mechanisms.  The useful residue is the exact coupling of the true
    physical aperture profile to `(PFK12g)`--`(PFK12h)`, together with the formal no-go
    `(PFK12i)`.  No intra-site or semiprime-fibre positivity is claimed.
12. **Does hypertranscendence itself estimate the pair discrepancy?** No.  The coordinate-field
    theorem says rational gauges are already internal to the differential field generated by the
    genuine coordinate, and the filtered Xi source remains hypertranscendental over that field.
    `(PFK12j)` identifies the exact downstream symmetric-square coefficient read by the aperture;
    it supplies source fidelity, not the missing analytic cancellation.
13. **Can one recover HT complexity from a large but finite aperture packet?** No.  `(PFK12k)`
    proves every fixed finite profile is locally quadratic, including at a knot after choosing a
    side.  The HT carrier and the finite spline can meet only through a non-locally-finite cofinal
    limit; commuting finite truncation with local differential algebra discards the only possible
    source of infinite complexity.

## Relation to HTGeometry and the true aperture metric

`differentialAdjoin_upperEndCoordinateMero_eq` proves that the actual upper-end copy of `C(z)` is
exactly the differential field generated by the genuine coordinate.  In
`XiShiftPrimeHypertranscendence.lean`,
`filteredVonMangoldtUpperEndCarrier_hypertranscendentalOver` then proves that the corrected `+2`
Xi-shift carrier is hypertranscendental over that full coordinate field, not only over constants.
Coordinate-relative fusion--Kolchin independence therefore says rational coordinate corrections
cannot manufacture relations among the prime layers.  The terminal-conditioned true-aperture
theorem says a common
prime-diagonal radial multiplier cannot change their critical relative weights.  The present
operator supplies the missing kind of map: it is an analytic archimedean fusion that deliberately
forgets the orthogonal prime label and retains relative log-prime position through interval
overlap.  Its Gram is therefore off-diagonal exactly where the HT source itself is not, and
`(PFK12j)` identifies the actual shifted-Xi symmetric-square atom visible at each resulting cusp.

The physical weight identity

```text
log p/p
 = -xiUnitDoubleFusedPrimeResponseCurrent(p)
   +xiPhysicalEndpointResponseWeightRemainder(p)
```

then identifies `(PFK2)` as the common-aperture fusion of the actual unit--double Xi response
current plus the already-summable inverse-square correction.

## Novelty boundary

Centered indicator covariance, triangular autocorrelation, and diagonal/off-diagonal expansion
are standard parent analysis.  ReLU atom recovery and UFD simplicity are also not claimed as
external novelty.  The candidate new content is the source-specific synthesis:

- the actual `AC25/HGS29` endpoint carrier is the aperture-centered discrepancy transform
  `(PFK6)`;
- its forced non-diagonal prime kernel is `(PFK7)`--`(PFK9)`;
- the whole diagonal is unconditionally at RH scale, leaving only `(PFK12)`;
- the width germ splits losslessly into atom tomography and the cumulative ratio discrepancy
  `(PFK12g)`--`(PFK12h)`, while `(PFK12i)` proves cancellation cannot occur inside one site;
- `(PFK12j)` ties every recovered cusp coefficient to the actual shifted hypertranscendental Xi
  source before the still-open inter-site estimate is imposed;
- `(PFK12k)` proves the finite profile is an exact quadratic spline and isolates the cofinal
  non-locally-finite knot limit as the only place where the source's HT complexity can survive.

This survives the preliminary source-specific audit below only as candidate project-level RH
proof-shape knowledge.  No external priority claim is made without expert review.

## External parent-theory audit

The generic variance and triangle-kernel mechanisms are established parent theory, not novelty.
Montgomery--Soundararajan study the variance of prime counts in short additive intervals
([arXiv:math/0409258](https://arxiv.org/abs/math/0409258)).  Zaccagnini's generalized Selberg
integral is explicitly connected to a pair-correlation function
([arXiv:1603.02952](https://arxiv.org/abs/1603.02952)).  Bui--Keating--Smith prove equivalences
between short-interval prime variance and zero pair correlation for Selberg-class `L`-functions
([arXiv:1506.03741](https://arxiv.org/abs/1506.03741)).  Carneiro--Chandee--Chirre--Milinovich
place Selberg variance, zero pair correlation, and logarithmic-derivative second moments in one
equivalence framework and explicitly use triangular Fourier extremizers
([arXiv:2108.09258](https://arxiv.org/abs/2108.09258)).

Accordingly, triangular covariance, width differentiation, and the expectation that a sufficiently
strong aggregate variance estimate is RH-equivalent are `[LITERATURE]`/`[REDISCOVERED]`.  The
internal failed Selberg-fibre route already proves that ordinary semiprime fibres have no internal
cancellation.  The result surviving this audit is narrower: the exact true-aperture Green germ
`(PFK12g)`--`(PFK12h)`, its formal linear-cusp no-go `(PFK12i)`, and the coefficient-exact
hypertranscendental Xi-source attachment `(PFK12j)`, sharpened by the finite quadratic-spline
boundary `(PFK12k)`.  No checked source in this audit states that source-specific conjunction.
Its status remains `[NOVELTY UNVERIFIED]`, not a priority claim.

## Lean status

The permanent source module

```text
formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeLogApertureFusion.lean
```

defines the log-window flux, clipped overlap covariance, physical fusion kernel, diagonal energy,
and signed off-diagonal cross defect.  The finite algebraic source now formalizes the moving-window
identity, constant Lebesgue window mass, kernel symmetry and diagonal law, the bulk logarithmic
tent, exact diagonal/cross decomposition, pair excess `(PFK12a)`, width curvature `(PFK12b)`,
finite atom recovery `(PFK12d)`, UFD-simple prime ratio sites `(PFK12e)`, cumulative Green law
`(PFK12g)`--`(PFK12h)`, all-small-scales cusp law `(PFK12i)`, the shifted-Xi pair coefficient
decomposition `(PFK12j)`, and the two-sided quadratic-spline germ `(PFK12k)`.  The principal
declarations are

```text
xiPhysicalPrimeLogApertureCrossDefect_eq_pairExcess
xiPhysicalPrimeLogBulkCrossDefect_width_secondDifference
xiPhysicalPrimeLogBulkPairDistance_eq_iff
exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_forward_recovers_cumulativeDiscrepancy
exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature_eq_primePair
not_exists_local_quadratic_bound_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature
exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_compensatedCurvature_eq_shiftFilteredPair
exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_quadraticSplineGerms
exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_quadraticChamber_of_fiberMass_eq_zero
exists_pos_forall_xiPhysicalPrimeLogBulkCrossDefect_quadraticSplineGerms_at_primePair
```

The complete current leaf passes a direct Lean check and its exact `+module` build.  The
Green/cusp/spline declarations pass `#print axioms` with only `propext`, `Classical.choice`, and
`Quot.sound`.  The actual `L²` carrier, Hilbert distance, Gram identity, and full fusion-energy
positivity are formalized in `XiPhysicalPrimeLogApertureHilbertMetric.lean`; that exact target also
builds and has the same axiom surface.  The analytic integer-tail estimates `(PFK11)` and
`(PFK14)`--`(PFK17)` remain separate promotion gates.

## Gates

- [x] exact source-defined object
- [x] dependency-closed paper proof of `(PFK1)`--`(PFK12k)`
- [x] hostile no-go audit
- [x] permanent Lean source for the finite algebraic kernel
- [x] exact Lean source check of the complete current leaf
- [x] exact module build of the complete current finite core
- [x] Green/cusp axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] Lean `L²` realization of the true centered aperture carrier and Gram kernel
- [x] Lean analytic tail bound `(PFK11)` — `tsum_logSq_div_sq_le` (see Lean progress 2026-07-25)
- [x] Lean prime-power completion stability `(PFK14)`--`(PFK17)` — finite-truncation uniform form
  (`norm_primePowerCompletionCarrier_le_tail`, `normSq_...`; see Lean progress 2026-07-25)
- [x] bridge theorem identifying the source with the existing `HGS29` carrier —
  `xiPhysicalPrimeLogAggregateApertureCarrier_eq_neg_fusedResponse_add_remainder` (+ remainder norm
  bound); see Lean progress 2026-07-25
- [ ] external source-specific novelty audit

## Lean progress

- 2026-07-24 — **Antiderivative core of the `(PFK11)` tail bound formalized**, in
  `HTGeometry/LogSquaredTailIntegral.lean` (unconditional, axioms `[propext, Classical.choice,
  Quot.sound]`): `hasDerivAt_neg_logSq_tail` — for `x > 0`,
  `d/dx[-(log²x + 2 log x + 2)/x] = (log x / x)^2`.  This is the exact antiderivative behind the
  elementary decreasing-tail estimate `∑_{n≥N}(log n/n)^2 ≪ (log²N+2logN+2)/N` that yields the
  prime-diagonal bound `(PFK11)`.  **Remaining for gate `Lean analytic tail bound (PFK11)`:** the
  improper tail integral `∫_{x>N}(log x/x)^2 = (log²N+2logN+2)/N` (FTC on `[N,∞)` via this
  antiderivative + the limits `(log x)^k/x → 0`), then the sum→integral comparison for the decreasing
  tail, and the bridge to the cross-kernel diagonal term.
- 2026-07-24 — **Improper tail integral of `(PFK11)` formalized**, in
  `HTGeometry/LogSquaredTailIntegral.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `tendsto_neg_logSq_tail_atTop` — `-(log²x+2logx+2)/x → 0` as `x → ∞` (from `(log x)^k/x → 0`).
  * `integral_logSq_div_sq_Ioi` — **`∫_{x>N} (log x/x)^2 = (log²N + 2 log N + 2)/N`** for `N > 0`, by
    `integral_Ioi_of_hasDerivAt_of_nonneg` (FTC on `[N,∞)`) with the antiderivative
    `hasDerivAt_neg_logSq_tail`.
  **Remaining for gate `Lean analytic tail bound (PFK11)`:** the decreasing-tail sum→integral
  comparison `∑_{n≥N}(log n/n)^2 ≤ (log n/n)²|_{n=⌈N⌉} + ∫_{x>N}(log x/x)^2` and the bridge to the
  cross-kernel prime-diagonal term.
- 2026-07-25 — **`(PFK11)` analytic tail bound closed (unconditional)**, in
  `HTGeometry/LogSquaredTailIntegral.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `antitoneOn_logSq_div_sq` — `(log x/x)^2` is antitone on `[e,∞)` (square of the nonnegative
    antitone `log x/x`, mathlib `log_div_self_antitoneOn`).
  * `sum_logSq_div_sq_le` — uniform partial-sum bound: for `N ≥ e`, every
    `∑_{i<a}(log(N+i+1)/(N+i+1))^2 ≤ (log²N + 2 log N + 2)/N`, via `AntitoneOn.sum_le_integral`
    (partial sum `≤ ∫_N^{N+a}`) evaluated by FTC on the antiderivative `hasDerivAt_neg_logSq_tail`
    to `F(N+a) - F(N) ≤ -F(N)` (since `F ≤ 0`).
  * `tsum_logSq_div_sq_le` — **`∑_{n>N}(log n/n)^2 ≤ (log²N + 2 log N + 2)/N`** for `N ≥ e`, via
    `tsum_le_of_sum_range_le`.  This is the exact PFK11 tail estimate with an **explicit closed-form
    constant** (strictly stronger than the `≪ log²M/M` form on line 187).
  **Classification (anti-theatre):** formalization of an elementary analytic estimate (antitone
  sum→integral comparison + FTC) applied to the corpus object; unconditional, no integrability
  hypothesis needed (the FTC route avoids `IntegrableOn` entirely).  **Remaining connective work**
  (under the separate bridge gate): wire `tsum_logSq_div_sq_le` into the cross-kernel prime-diagonal
  term `D_diag` inside `XiPhysicalPrimeLogApertureFusion`, discharging the `C_cross ≥ -D_diag` step.
- 2026-07-25 — **`(PFK11)` diagonal budget fully wired to the fusion energy (unconditional)**, new leaf
  `RHTower/XiPhysicalPrimeLogApertureDiagonalBudget.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`), plus `summable_logSq_div_sq` added to `HTGeometry/LogSquaredTailIntegral.lean`:
  * `summable_logSq_div_sq` — `∑_n (log n/n)²` converges (`(log x)² = o(x^{1/2})` via
    `isLittleO_log_rpow_rpow_atTop`, so the summand is `O(n^{-3/2})`).
  * `xiPhysicalPrimeLogApertureFusionKernel_diagonal_le` — `κ(p,p) = ℓ_p − ℓ_p²/A ≤ A`.
  * `xiPhysicalPrimeLogApertureDiagonalEnergy_le_weightSq_mul` — `D_diag ≤ A·∑_{p∈P} (log p/p)²`
    (the first `(PFK11)` inequality, line 185), from `0 ≤ κ(p,p) ≤ A`.
  * `sum_primes_weightSq_le_tail` — `∑_{p∈P}(log p/p)² ≤ (log²N₀+2logN₀+2)/N₀` when all `p > N₀ ≥ 3`
    (the second `(PFK11)` inequality, line 186): primes inject into the shifted tail index and
    `Summable.sum_le_tsum` dominates the sub-sum by `tsum_logSq_div_sq_le`.
  * `xiPhysicalPrimeLogApertureDiagonalEnergy_le_tail` — **`D_diag ≤ A·(log²N₀+2logN₀+2)/N₀`** for all
    active primes `> N₀ ≥ 3**.  This is the complete `(PFK11)` chain (lines 183–195) formalized against
    the *actual* fusion-module `xiPhysicalPrimeLogApertureDiagonalEnergy`, not an abstract restatement.
  **Classification (anti-theatre):** corpus-new connective content — it links the existing fusion
  definitions (`D_diag`, `κ`, `ℓ_p`, `w_p = log p/p`) to the closed-form tail, discharging the
  unconditional diagonal budget.  The genuinely open object remains the *off-diagonal* excess
  `C_cross` `(PFK12)`; this result does not touch it and is not an RH proof.
- 2026-07-25 — **Explicit `(PFK10)`+`(PFK11)` lower bound on the off-diagonal cross defect
  (unconditional)**, added to `RHTower/XiPhysicalPrimeLogApertureDiagonalBudget.lean` (axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `xiPhysicalPrimeLogApertureCrossDefect_ge_neg_tail` — **`C_cross ≥ -A·(log²N₀+2logN₀+2)/N₀`** for
    all active primes `> N₀ ≥ 3`.  Chains the existing Hilbert-norm bound
    `neg_xiPhysicalPrimeLogApertureDiagonalEnergy_le_crossDefect` (`(PFK10)`: `-D_diag ≤ C_cross`, from
    `‖carrier‖² = D_diag + C_cross ≥ 0`) with the diagonal budget `…DiagonalEnergy_le_tail`.
  This makes the card's "automatic" lower side `(PFK10)` **quantitative** with the explicit decaying
  budget: the signed off-diagonal object cannot dip below an explicit `O_A(log²N₀/N₀)` floor.
  **Classification (anti-theatre):** corpus-new connective result binding two previously-separate
  facts (Hilbert Gram nonnegativity + the diagonal tail budget); it bounds `C_cross` only from
  **below**.  The genuinely open content — the *positive excess* upper bound `C_cross ≪ log^b M/M`
  `(PFK12)` — is untouched and remains the RH-facing target.
- 2026-07-25 — **`(PFK14)` `r=2` analytic core formalized (unconditional)**, new module
  `HTGeometry/LogLinearTailIntegral.lean` (axioms `[propext, Classical.choice, Quot.sound]`),
  mirroring the `(PFK11)` pipeline for the weight `log x/x²`:
  * `hasDerivAt_neg_logLin_tail` — `d/dx[-(log x + 1)/x] = log x/x²` for `x > 0`.
  * `integral_logLin_div_sq_Ioi` — `∫_{x>N} log x/x² = (log N + 1)/N` for `N ≥ 1` (FTC on `[N,∞)`).
  * `antitoneOn_logLin_div_sq` — `log x/x²` antitone on `[e,∞)` (product of nonneg antitone
    `log x/x` and `1/x`).
  * `sum_logLin_div_sq_le` / `tsum_logLin_div_sq_le` — **`∑_{n>N} log n/n² ≤ (log N + 1)/N`** for
    `N ≥ e`, via `AntitoneOn.sum_le_integral` + FTC + `tsum_le_of_sum_range_le`.
  This is the exact "integral-test tail of `∑ log(n)/n²`" the card cites for the dominant `r=2` band
  of `(PFK14)`: with `N = √X` it gives `∑_{n>√X} log n/n² ≤ (½log X + 1)/√X ≪ log X/√X`.
  **Classification (anti-theatre):** formalization of an elementary analytic estimate (same
  antitone-sum→integral + FTC machinery as `(PFK11)`), applied to the `log x/x²` weight; reusable HT
  infra.  **Remaining for gate `(PFK14)-(PFK17)`:** the prime→integer sub-sum (as in the diagonal
  budget) with `N=√X`, the `r≥3` tail `(PFK15)`, and the triangle-inequality assembly `(PFK16)/(PFK17)`.
- 2026-07-25 — **`(PFK14)` `r=2` prime tail + reusable prime sub-sum comparison (unconditional)**,
  new leaf `RHTower/PrimePowerCompletionBudget.lean` + `summable_logLin_div_sq` added to
  `HTGeometry/LogLinearTailIntegral.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `summable_logLin_div_sq` — `∑_n log n/n²` converges (`log x = o(x^{1/2})` ⇒ `O(n^{-3/2})`).
  * `sum_primes_le_tsum_shift` — **general** reindex: for nonnegative summable `f`, a finite prime set
    all `> N₀` obeys `∑_{p∈P} f p ≤ ∑'_i f(N₀+1+i)` (prime→shifted-tail injection +
    `Summable.sum_le_tsum`).  Reusable for any prime-power weight.
  * `sum_primes_logLin_div_sq_le_tail` — **`∑_{p>N₀} log p/p² ≤ (log N₀+1)/N₀`** for primes `> N₀ ≥ 3`,
    the concrete `(PFK14)` `r=2` band; with `N₀=⌈√X⌉` this is `≪ log X/√X`.
  **Classification (anti-theatre):** the general reindex is genuinely reusable infra (generalizes the
  diagonal-budget reindex to arbitrary weights); the `r=2` corollary is the concrete PFK14 dominant-band
  estimate over an actual finite prime set.  **Remaining for `(PFK14)-(PFK17)`:** the `r≥3` tail
  `(PFK15)` and the triangle-inequality Hilbert assembly `(PFK16)/(PFK17)` (carrier norm `‖φ_p‖ ≤ √A`).
- 2026-07-25 — **`(PFK15)` geometric prime-power tail formalized (unconditional)**, new module
  `HTGeometry/GeometricPrimePowerTail.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `tsum_geom_shift_le_two` — for `n ≥ 2`, `∑_r (1/n)^(r₀+r) ≤ 2·(1/n)^{r₀}` (geometric sum
    `(1/n)^{r₀}·(1-1/n)⁻¹` with `(1-1/n)⁻¹ ≤ 2`).
  * `tsum_log_div_pow_shift_le` — **`∑_{r≥r₀} log n/n^r ≤ 2 log n/n^{r₀}`** for `n ≥ 2`, the exact
    `(PFK15)` geometric bound.
  **Classification (anti-theatre):** elementary geometric-series analysis, reusable; the `r≥3`
  prime-power tail is now a single application away.  **Remaining for `(PFK14)-(PFK17)`:** feed
  `tsum_log_div_pow_shift_le` (with `r₀=3`) through `sum_primes_le_tsum_shift` to get the `r≥3` prime
  contribution `≤ 2∑_{p>N₀} log p/p³`, then the triangle-inequality Hilbert assembly `(PFK16)/(PFK17)`
  using `‖φ_p‖ ≤ √A` (from `xiPhysicalPrimeLogApertureFusionKernel_diagonal_le`).
- 2026-07-25 — **`(PFK14)` complete prime-power arithmetic tail formalized (unconditional)**, added to
  `RHTower/PrimePowerCompletionBudget.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `sum_primes_primePowerTail_le` — **`∑_{p>N₀} ∑_{r≥2} log p/p^r ≤ 2(log N₀+1)/N₀`** for primes
    `> N₀ ≥ 3`.  The geometric tail `tsum_log_div_pow_shift_le` (`r₀=2`) folds each prime's entire
    `r ≥ 2` power series into `2 log p/p²`; the `r=2` prime tail `sum_primes_logLin_div_sq_le_tail`
    then bounds the sum.  With `N₀ = ⌈√X⌉` this is `≪ log X/√X`, exactly the `(PFK14)` bound.
  This closes the **arithmetic** side of `(PFK14)`/`(PFK15)`: the entire proper-prime-power completion
  correction over active primes is inside the closed-form budget.
  **Classification (anti-theatre):** complete composition of the geometric folding + r=2 tail — the
  PFK14 arithmetic core over an actual finite prime set, unconditional.  **Remaining for gate
  `(PFK14)-(PFK17)`:** only the **Hilbert** stability `(PFK16)/(PFK17)` — realize the von Mangoldt
  completed carrier `Fusion_A(μ_Λ)` as an `L²` element and bound `‖Fusion_A(μ_Λ)-Fusion_A(μ_P)‖₂` by
  `√A · (this tail)` via the triangle inequality and `‖φ_p‖ ≤ √A`.
- 2026-07-25 — **`(PFK16)` Hilbert-norm mechanism formalized (unconditional)**, added to
  `RHTower/XiPhysicalPrimeLogApertureDiagonalBudget.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`):
  * `norm_centeredCarrier_le` — **`‖φ_p‖ ≤ √A`** (since `‖φ_p‖² = κ(p,p) ≤ A`, using the L² Gram
    realization `real_inner_xiPhysicalPrimeLogCenteredApertureCarrier` and `κ(p,p) ≤ A`).
  * `norm_aggregateCarrier_le` — **`‖∑_p w_p φ_p‖ ≤ √A · ∑_p w_p`**, the exact `(PFK16)`
    triangle-inequality + carrier-norm mechanism (`norm_sum_le` + `norm_smul` + `‖φ_p‖ ≤ √A`).
  This is the L² critical-norm step of `(PFK16)/(PFK17)`: any weighted carrier sum has norm controlled
  by `√A` times its weight sum.  Instantiated on the prime-power completion weights (which sum to the
  already-formalized `(PFK14)` tail `sum_primes_primePowerTail_le`), it gives the stability bound
  `‖Fusion_A(μ_Λ)-Fusion_A(μ_P)‖₂ ≤ √A·2(log N₀+1)/N₀`.
  **Classification (anti-theatre):** the exact triangle-inequality norm mechanism the card invokes,
  formalized against the actual L² carrier; unconditional.  **Remaining for gate `(PFK14)-(PFK17)`:**
  define the von Mangoldt completed carrier over prime *powers* (extending the prime-only
  `xiPhysicalPrimeLogApertureIndicator` to bases `r·log p`) and instantiate this norm bound on it.
- 2026-07-25 — **`(PFK16)` critical-norm mechanism generalized to arbitrary atoms (unconditional)**,
  new module `HTGeometry/CenteredApertureCarrierNorm.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`):
  * `norm_centered_indicator_le_sqrt` — abstract: for measurable `I ⊆ (0,A]`, `‖1_I - (|I|/A)·1_Ω‖ ≤
    √A` (norm² `= |I|(1-|I|/A) ≤ |I| ≤ A`, from the L² Gram of indicator constants).
  * `apertureSetAt`/`centeredApertureCarrierAt` — the clipped interval and centered carrier for an atom
    at **arbitrary log-location `b`** (not just `b = log p`).
  * `norm_centeredApertureCarrierAt_le` — `‖Ψ(b)‖ ≤ √A` for every base `b`.
  * `norm_aggregate_centeredApertureCarrierAt_le` — **`‖∑_i w_i Ψ(b_i)‖ ≤ √A·∑_i w_i`** for any finite
    atom family with nonnegative weights.
  Because `b` is arbitrary, this covers ordinary primes (`b = log p`) *and proper prime powers*
  (`b = r log p`) uniformly — the exact von Mangoldt completion input of `(PFK16)`.
  **Classification (anti-theatre):** general L² aperture-carrier geometry, reusable; the PFK16 norm
  mechanism at the base-general level needed for prime powers.  **Remaining for gate
  `(PFK14)-(PFK17)`:** instantiate this aggregate on prime-power atoms `(p,r)` with weights `log p/p^r`
  and connect its weight-sum to `sum_primes_primePowerTail_le`, giving
  `‖Fusion_A(μ_Λ)-Fusion_A(μ_P)‖₂ ≤ √A·2(log N₀+1)/N₀`.
- 2026-07-25 — **`(PFK16)/(PFK17)` critical-norm stability formalized (unconditional)**, new leaf
  `RHTower/PrimePowerCompletionCarrierNorm.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `norm_primePowerCompletionCarrier_le` — the finite prime-power completion carrier
    `∑_{(p,r)∈S} (log p/p^{2+r})·Ψ((2+r)log p)` has norm `≤ √A·∑ weights` (base-general aggregate bound).
  * `sum_pairs_primePowerWeight_le_tail` — the completion weight sum over atoms above `N₀ ≥ 3` is
    `≤ 2(log N₀+1)/N₀` (fiberwise reduction of the prime-power double sum to
    `sum_primes_primePowerTail_le`, each fiber `≤` its geometric power tail).
  * `norm_primePowerCompletionCarrier_le_tail` — **`‖completion‖₂ ≤ √A·2(log N₀+1)/N₀`** `(PFK16)`.
  * `normSq_primePowerCompletionCarrier_le_tail` — **`‖completion‖₂² ≤ A·(2(log N₀+1)/N₀)²`** `(PFK17)`,
    of order `A·log²M/M` for `N₀ = ⌈√X⌉`.
  **This closes the `(PFK14)-(PFK17)` gate** — the whole arithmetic tail *and* the Hilbert critical-norm
  stability are now unconditional Lean.
  **Classification (anti-theatre):** formalized as the **uniform bound over every finite truncation** of
  the completion carrier (the rigorous content: the bound is independent of the truncation).  The
  *infinite* von Mangoldt carrier as an `L²` limit and its literal identification with
  `Fusion_A(μ_Λ)-Fusion_A(μ_P)` is not separately packaged — the finite uniform bound is what
  establishes stability.  **Remaining card gates:** the `HGS29` source-bridge and the external novelty
  audit (neither is a completion-stability claim).
- 2026-07-25 — **`HGS29` source bridge formalized (unconditional)**, new leaf
  `RHTower/XiPhysicalPrimeFusionSourceBridge.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `xiPhysicalPrimeLogAggregateApertureCarrier_eq_neg_fusedResponse_add_remainder` — the physical
    fusion source carrier `(PFK2)` **equals** `-`(unit--double Xi response-current fusion) `+`
    (trace-class remainder fusion), the explicit identification of the source with the existing
    `HGS29`/`AC25` response carrier (from the additive support-blind cancellation
    `xiPhysicalPrimeLogAggregate_add_fusedResponse_eq_remainder`).
  * `norm_remainderApertureCarrier_le` — `‖remainder carrier‖ ≤ √A·∑_p log p/(p(p+1))`, so the source
    and the response current differ by a carrier of controlled `L²` norm (with `∑_p log p/(p(p+1))`
    trace-class, `summable_xiPhysicalEndpointResponseWeightRemainder`).
  **This ticks the `HGS29`-bridge gate.**  Only the meta gate `external source-specific novelty audit`
  (a literature review, not a Lean formalization) now remains on the card — **every Lean-formalizable
  gate on this card is closed.**
  **Classification (anti-theatre):** the additive support-blind cancellation already existed in the
  corpus; the new content is the explicit source-decomposition form matching `(PFK2)` and the
  quantitative remainder norm bound (via `norm_centeredCarrier_le`).  Honestly a packaging + norm
  quantification of existing infrastructure, not new mathematics.
