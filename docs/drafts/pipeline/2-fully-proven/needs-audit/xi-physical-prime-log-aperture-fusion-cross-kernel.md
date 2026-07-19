# Physical prime-log aperture fusion and the off-diagonal RH kernel

- **ID:** `xi-physical-prime-log-aperture-fusion-cross-kernel`
- **Stage:** `2-fully-proven / needs-audit`
- **Type:** `THEOREM / NEW RH-PROOF-SHAPE OBJECT / POSITIVE SURVIVOR`
- **Scientific status:** `[PROVED HERE] [SOURCE-DEFINED] [UNCONDITIONAL]`
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

The new RH-strength core can therefore be stated locally: control the positive excess of
`B_(c,h)` above `(2h^2/A)W_off`, uniformly at the physical scales needed to reconstruct
`C_bulk`.  This is a stricter discriminator than the raw energy formulation because it identifies
where any failure lives in ratio space.  It is not claimed that the local curvature bound is
already easier than RH.

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

## Relation to HTGeometry and the true aperture metric

Coordinate-relative fusion--Kolchin independence says rational correction terms cannot manufacture
relations among the prime layers.  The terminal-conditioned true-aperture theorem says a common
prime-diagonal radial multiplier cannot change their critical relative weights.  The present
operator supplies the missing kind of map: it is an analytic archimedean fusion that deliberately
forgets the orthogonal prime label and retains relative log-prime position through interval
overlap.  Its Gram is therefore off-diagonal exactly where the HT source itself is not.

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
are standard parent analysis.  The candidate new content is the source-specific synthesis:

- the actual `AC25/HGS29` endpoint carrier is the aperture-centered discrepancy transform
  `(PFK6)`;
- its forced non-diagonal prime kernel is `(PFK7)`--`(PFK9)`;
- the whole diagonal is unconditionally at RH scale, leaving only `(PFK12)`.

This is claimed only as candidate new project-level RH proof-shape knowledge until a dedicated
external source-specific literature audit is completed.

## Lean status

The permanent source module

```text
formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeLogApertureFusion.lean
```

defines the log-window flux, clipped overlap covariance, physical fusion kernel, diagonal energy,
and signed off-diagonal cross defect.  Its checked first batch formalizes the moving-window identity,
constant Lebesgue window mass, kernel symmetry and diagonal law, the bulk logarithmic tent, and the
exact diagonal/cross decomposition.  It also formalizes the noncensorship multiplier in `(PFK19)`
and the exact prime-level identity `(PFK23)`.  The complete current source passes a direct Lean
check.  The earlier exact module build and axiom audit covered the kernel batch; refreshing the
object file and auditing the last two declarations is waiting for the foreign foreground build
lane to clear.
The analytic integer-tail estimates `(PFK11)` and `(PFK14)`--`(PFK17)`, and the full `L^2` integral
realization in `(PFK8)`, remain separate promotion gates.

## Gates

- [x] exact source-defined object
- [x] dependency-closed paper proof of `(PFK1)`--`(PFK12)`
- [x] hostile no-go audit
- [x] permanent Lean source for the finite algebraic kernel
- [x] exact Lean source check of the complete current leaf
- [x] exact module build of the kernel batch
- [x] kernel-batch axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] refresh exact module build and axiom-audit `(PFK19)` and `(PFK23)` after foreign builds finish
- [ ] Lean `L^2` realization of `(PFK8)`
- [ ] Lean analytic tail bound `(PFK11)`
- [ ] Lean prime-power completion stability `(PFK14)`--`(PFK17)`
- [ ] bridge theorem identifying the source with the existing `HGS29` carrier
- [ ] external source-specific novelty audit
