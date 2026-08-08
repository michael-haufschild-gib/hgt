# Suzuki coalescing-anchor parity-locking reduction

- **ID:** `suzuki-coalescing-anchor-parity-locking-reduction`
- **Ledger:** `SR-65`
- **Stage:** 2 — dependency-closed paper proof
- **Type:** THEOREM (paper) / SOURCE-RANGE AND PRE-DIVISOR CALIBRATION ADVANCE
- **RH used:** no
- **Computation used:** no
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [LEAN READ-ONLY AUDITED]`
  `[CANDIDATE NEW SUZUKI-SPECIFIC SYNTHESIS] [EXTERNAL PRIORITY UNVERIFIED]`
  `[NOT FULL XI IDENTIFICATION] [NOT RH]`

## 1. Result

Eventual equality of Suzuki's even and odd spectral floors is not itself the remaining
first-defect obstruction.  At a locked aperture, collapse the intrinsic deficiency base from
`+-i` to `+-ic`, `c downarrow 0`.  The ground residues are governed by the first visible even and
odd polynomial moments.  Unless those two moments have adjacent degrees, their parity
polarization approaches its pure endpoint faster than the canonically normalized Xi target does.
For every sufficiently large locked aperture, continuity in the spectral shift then proves that
the finite-source response range contains the Xi first defect.

In the adjacent-degree case the whole obstruction reduces to one explicit coefficient comparison.
If that comparison is unfavorable, this endpoint argument fails sharply; an interior excursion
can still survive.

The same collapsing anchor does not destroy the meromorphic target.  The antipodal two-angle
Cayley quotient, multiplied by the deterministic factor `z^2/c`, converges to a positive scalar
multiple of

```text
z^2 xi(1/2-iz) / xi'(1/2-iz).
```

More is forced by the matched first defect.  Schwarz--Pick converts the exact quadratic defect
`1-kappa_Xi(c)=O(c^2)` into local boundedness of the deterministically blown-up finite source
quotients on both open half-planes.  Thus cofinal normality away from the real axis is automatic
for every exactly first-jet-matched family; the remaining compactness obstruction lives on the
real Clark divisor.  Exact matching is only finite-source target reachability here, not yet source
admission in the superselection sense.

Thus the corrected source frontier is an adjacent-moment resonance or cofinal meromorphic
real-axis tightness and identification, not parity-floor locking alone.

## 2. Locked ground bundle and first visible moments

Fix an aperture `a>0`.  Let `A_a` be Suzuki's self-adjoint restricted-Weil operator, let `J` be
reflection, and assume that the two parity floors coincide:

```text
lambda_a^+ = lambda_a^- = lambda_0.                       (1)
```

Let `P_e` and `P_o` be the spectral projections at `lambda_0` in the even and odd sectors.  Both
are nonzero finite-rank projections.  Even and odd polynomials are dense in their corresponding
`L^2(-a,a)` sectors, so the integers

```text
r = min {2k     : P_e(x^(2k))     != 0},
s = min {2k + 1 : P_o(x^(2k + 1)) != 0}                   (2)
```

exist.  Put

```text
A_r = ||P_e(x^r/r!)||_2^2 > 0,
B_s = ||P_o(x^s/s!)||_2^2 > 0.                            (3)
```

For the movable deficiency base `+-ic`, the parity source residues at the common ground pole are

```text
m_E(c) = ||P_e cosh(cX)||_2^2,
m_O(c) = ||P_o sinh(cX)||_2^2.                            (4)
```

Hilbert-valued Taylor expansion and the definitions of `r,s` give

```text
m_E(c) = A_r c^(2r) (1+O(c^2)),
m_O(c) = B_s c^(2s) (1+O(c^2)).                           (5)
```

Consequently the ground-pole defect angle

```text
kappa_g(c) = (m_E(c)-m_O(c))/(m_E(c)+m_O(c))              (6)
```

has the sharp alternatives, with `d=|r-s|`:

```text
r<s:  kappa_g(c)
        =  1 - 2(B_s/A_r)c^(2d) + O(c^(2d+2)),

s<r:  kappa_g(c)
        = -1 + 2(A_r/B_s)c^(2d) + O(c^(2d+2)).            (7)
```

Because `r` is even and `s` is odd, `d` is odd.  Hence either `d=1` or `d>=3`; no quadratic-gap
case is missing.

## 3. The movable Xi target has a universal quadratic endpoint gap

Write

```text
mathcalL(w) = (xi'/xi)(1/2+w),
L(c) = mathcalL(c),                     c>0,
M_j(y) = sum_q (y+omega_q)^(-(j+1)),
```

in the multiplicity-exact centered squared-zero coordinate used by the existing squared-Xi
moment theory.  Conjugation makes the moments real.  The unconditional centered sector theorem
gives

```text
M_0(0)>0,                 M_1(0)>0.                       (8)
```

Absolute divisor summability gives analytic continuation of these two moment sums to `y=0` and

```text
L(c)=c M_0(c^2),
L'(c)=M_0(c^2)-2c^2 M_1(c^2).                             (9)
```

Normalize the Xi Donoghue function at the movable point `ic` by

```text
m_(Xi,c)(z) = i mathcalL(-iz)/L(c),
Theta_(Xi,c)(z) = (m_(Xi,c)(z)-i)/(m_(Xi,c)(z)+i).        (10)
```

Then `m_(Xi,c)(ic)=i`, and direct Cayley differentiation gives the real first defect

```text
kappa_Xi(c)
 = 2ic Theta_(Xi,c)'(ic)
 = c L'(c)/L(c)
 = 1-2c^2 M_1(c^2)/M_0(c^2).                             (11)
```

Set

```text
tau_0 = M_1(0)/M_0(0) > 0.                               (12)
```

Equations `(8)--(11)` give the exact central expansion

```text
kappa_Xi(c)=1-2 tau_0 c^2+O(c^4).                        (13)
```

This also recovers the corpus theorem `c L'(c)-L(c)<0` for every `c>0` at first order.  No RH
assumption occurs: positivity through the required squared reciprocal moments is already
unconditional.

## 4. Free endpoint

For `lambda -> -infinity`, the scaled resolvent converges strongly to the identity.  Therefore the
finite source defect tends to the free exponential polarization

```text
kappa_free(a,c)
 = (||cosh(cX)||^2-||sinh(cX)||^2)
     /(||cosh(cX)||^2+||sinh(cX)||^2)
 = 2ac/sinh(2ac)
 = 1-(2/3)a^2c^2+O(c^4).                                 (14)
```

In particular, if

```text
a^2 > 3 tau_0,                                           (15)
```

then `kappa_free(a,c)<kappa_Xi(c)` for all sufficiently small `c>0`.

## 5. Coalescing-anchor matching theorem

For fixed `a,c`, let `kappa_(a,c)(lambda)` be Suzuki's defect angle for
`lambda<lambda_0`.  Resolvent continuity makes it continuous, its free limit is `(14)`, and its
ground limit is `(7)`.

### Theorem A — nonadjacent locking has automatic target reachability

Assume `(1)` and `d=|r-s|>=3`.

- If `r<s` and `(15)` holds, then for every sufficiently small `c>0` there is
  `lambda(c)<lambda_0` with

  ```text
  kappa_(a,c)(lambda(c)) = kappa_Xi(c).                   (16+)
  ```

- If `s<r`, multiply the finite source Livsic characteristic by its allowed unimodular phase
  `-1`.  Equivalently, for every sufficiently small `c>0` there is
  `lambda(c)<lambda_0` with

  ```text
  kappa_(a,c)(lambda(c)) = -kappa_Xi(c).                  (16-)
  ```

Indeed, `(7)` approaches the relevant signed pure endpoint with gap `O(c^(2d))=o(c^2)`, whereas
the target remains a distance `2 tau_0 c^2+O(c^4)` from that endpoint.  In the even-leading case
`(14)--(15)` put the free endpoint on the opposite side.  In the odd-leading case the free
endpoint tends to `+1`, already on the opposite side of the target near `-1`.  The intermediate
value theorem proves `(16+)--(16-)`.

Multiplying the finite source Livsic characteristic function by `-1` merely relabels its extension
circle by `pi`.  In oriented notation, put `epsilon_a=1` for `r<s` and `epsilon_a=-1` for `s<r`;
then both conclusions read

```text
epsilon_a kappa_(a,c)(lambda(c)) = kappa_Xi(c).           (16)
```

### Theorem B — exact adjacent-moment wall

Assume `d=1`.  Let

```text
eta_a = B_s/A_r,   if r<s,
eta_a = A_r/B_s,   if s<r.                               (17)
```

Then the source-oriented ground endpoint has expansion

```text
epsilon_a kappa_g(c)=1-2 eta_a c^2+O(c^4),               (18)
```

where `epsilon_a` is the source phase above.  Therefore:

```text
eta_a < tau_0  =>  the ground endpoint lies past Xi for all small c;
eta_a > tau_0  =>  the ground endpoint lies before Xi for all small c;
eta_a = tau_0  =>  fourth order is the first undecided term.                 (19)
```

In the even-leading case, the first line together with `(14)--(15)` gives a matching shift as in
Theorem A.  In the odd-leading case the oriented free endpoint tends to `-1`, so the first line
already gives the opposite endpoint ordering.  The second line proves sharp failure of this
particular endpoint argument, not failure of the finite-shift interior-excursion branch.

### Corollary — corrected cofinal locking obstruction

On any cofinal family of locked apertures satisfying Theorem A, or Theorem B with
`eta_a<tau_0`, choose the usable anchors small enough and additionally require `c_a<1/a`.
Then

```text
a -> infinity,       c_a -> 0,
```

and matching finite-source shifts exist for the appropriately phased movable Xi first defect.

Thus eventual parity-floor locking can obstruct this first-jet construction only through a
cofinal adjacent-moment resonance with `eta_a>=tau_0` (including the fourth-order equality case),
or through failure of the separate interior-excursion branch.  Equality of the two floors by
itself is not the frontier theorem.

## 6. Antipodal blow-up retains the Xi meromorphic target

The Cayley algebra in `(10)` gives the exact identity

```text
(1-Theta_(Xi,c)(z))/(1+Theta_(Xi,c)(z))
  = L(c)/mathcalL(-iz).                                  (20)
```

Since `L(c)/c -> M_0(0)>0`, multiplication by the deterministic source parameter `z^2/c` yields

```text
(z^2/c) (1-Theta_(Xi,c)(z))/(1+Theta_(Xi,c)(z))
  -> M_0(0) z^2 xi(1/2-iz)/xi'(1/2-iz)                   (21)
```

locally in the meromorphic topology.  The positive constant `M_0(0)` does not change zeros,
poles, or the Hermite--Biehler reality question.

For every finite Suzuki system, two antipodal extension-angle characteristics recover its Cayley
function by the same fractional-linear algebra.  Hence `(21)` proves that a coalescing defect base
is compatible with the surviving two-angle target category.  What remains is hard: prove
real-axis normality of the **literal source quotients**, prevent numerator/denominator
cancellation, and identify their meromorphic limit with `(21)` without reading the Xi divisor
backward.

## 7. First-jet saturation forces half-plane normality

The compactness statement needed after `(21)` is singular: the normalization point `ic` moves to
the real boundary and the quotient is divided by `c`.  Ordinary Montel compactness of the
unscaled Schur functions does not imply it.  The matched first jet does.

Let `Theta_c` be any meromorphic inner function on the upper half-plane with

```text
Theta_c(ic)=0,       kappa_c=2ic Theta_c'(ic) in [0,1).  (22)
```

The phase in Theorem A has already been chosen so that `kappa_c=kappa_Xi(c)>0`.  Put

```text
b_c(z)=(z-ic)/(z+ic),
f_c(w)=Theta_c(b_c^(-1)(w)).                              (23)
```

Then `f_c` is Schur, `f_c(0)=0`, and

```text
f_c'(0)=2ic Theta_c'(ic)=kappa_c.                        (24)
```

### Theorem C — quadratic jet saturation gives singular compactness

Suppose `c downarrow 0` and

```text
1-kappa_c <= C c^2.                                      (25)
```

Then

```text
R_c(z)=(1-Theta_c(z))/(c(1+Theta_c(z)))                  (26)
```

is locally bounded, hence a normal family, on the upper half-plane.  Its meromorphic-inner
reflection is locally bounded on the lower half-plane.  The same conclusions hold for `z^2 R_c`.

In particular, every exactly matched family from `(16)` satisfies `(25)` by `(13)`.  Therefore
the deterministically blown antipodal source quotients in `(21)` are automatically normal on
`C\R`; no additional source estimate is needed there.

### Proof

Schwarz's lemma factors

```text
f_c(w)=w g_c(w),                                         (27)
```

where `g_c` is Schur and `g_c(0)=kappa_c`.  For `r=|w|`, Schwarz--Pick gives the Euclidean disk
estimate

```text
|g_c(w)-kappa_c|
 <= r(1-kappa_c^2)/(1-r kappa_c)
 <= 2r(1-kappa_c)/(1-r).                                 (28)
```

Consequently

```text
|1-g_c(w)| <= (1-kappa_c)(1+r)/(1-r).                    (29)
```

Fix a compact set `K` in the upper half-plane.  Uniformly for `z in K`, with `w=b_c(z)`,

```text
|1-w|=2c/|z+ic|=O_K(c),
1-|w|^2=4c Im(z)/|z+ic|^2,
(1+|w|)/(1-|w|)=O_K(c^(-1)).                             (30)
```

Equations `(25)`, `(27)`, `(29)`, and `(30)` yield

```text
|1-f_c(w)|
 <= |1-w|+|w||1-g_c(w)|
 =O_K(c).                                                (31)
```

Thus `f_c(b_c(z))=Theta_c(z)` tends uniformly to `1` on `K`, and for small `c` the denominator
in `(26)` is bounded away from zero.  Division of `(31)` by `c` proves local boundedness of
`R_c`.  Montel proves normality.  Meromorphic innerness gives

```text
conj(R_c(conj z))=-R_c(z),                               (32)
```

so reflection proves the lower-half-plane assertion.  Multiplication by `z^2` is harmless on
compact sets.

### Exact frontier effect

The corpus's fixed-anchor theorem gives normality of `Theta_c`, which would allow its limit to be
the constant `1` after the anchor escapes.  Theorem C resolves the missing boundary layer and
retains the first nonconstant scale.  It does **not** control a neighborhood crossing the real
axis: `(28)` loses one power of `c` because `b_c(K)` approaches the disk boundary, and real poles
of `(26)` may still overcrowd.  The surviving compactness theorem is therefore

```text
local real-axis Clark-count tightness
  => full meromorphic normality of the blown source quotients.             (33)
```

This is exactly the source condition isolated independently by the residual-overcrowding theorem.
The two results now meet: exact first-jet matching supplies all off-axis compactness, while
common-gauge entire-pair normality or a sufficient local Clark-count bound is needed only on the
real axis.

### Theorem D — the real-axis remainder is sharp

No theorem using only innerness, all-angle Hermite--Biehler structure, the moving anchor, and exact
first-jet matching can strengthen Theorem C across the real axis.

Fix a bounded open interval `J` compactly contained in `(0,infinity)` and `x_0 in J`.  Let
`kappa_c in (0,1)` satisfy

```text
1-kappa_c=O(c^2).                                        (34)
```

For every positive integer `N`, set

```text
zeta_c=b_c(x_0),
r_(c,N)=kappa_c^(1/N),
B_(c,N)(w)=conj(zeta_c)
             (r_(c,N)zeta_c-w)/(1-r_(c,N)conj(zeta_c)w),
F_(c,N)(w)=w B_(c,N)(w)^N.                               (35)
```

Then `F_(c,N)` is rational inner and

```text
F_(c,N)(0)=0,       F_(c,N)'(0)=r_(c,N)^N=kappa_c.       (36)
```

Define the upper-half-plane carrier

```text
Theta_(c,N)(z)=F_(c,N)(b_c(z)).                          (37)
```

It obeys exactly the normalization and jet in `(22)`.  Nevertheless the two real Clark levels

```text
Theta_(c,N)(x)=1,       Theta_(c,N)(x)=-1                (38)
```

each have `N-O(1)` solutions in `J` as `c downarrow 0`, with an absolute loss independent of
`N`.  The two level sets strictly interlace.  Choosing `N=N(c)->infinity` supplies points of both
levels converging to `x_0`; the corresponding quotients `(26)` have interlacing zeros and poles converging
to the same real point and are not meromorphically normal in any neighborhood of `x_0`.

### Proof

The normalization in `(35)` gives `B_(c,N)(0)=r_(c,N)`, proving `(36)`.  On the unit circle the
argument derivative of `B_(c,N)` is the Poisson kernel

```text
P_r(t-t_c)=(1-r^2)/(1-2r cos(t-t_c)+r^2),
zeta_c=exp(i t_c).                                       (39)
```

For positive real `x`,

```text
d/dx arg b_c(x)=2c/(x^2+c^2).                            (40)
```

Hence `b_c(J)` contains an arc about `zeta_c` of half-width comparable to `c`.  The Poisson mass
outside that arc is `O((1-r)/c)`.  Moreover

```text
N(1-r_(c,N)) <= -N log r_(c,N)=-log kappa_c=O(c^2).      (41)
```

Therefore the boundary argument of `F_(c,N)` increases across `b_c(J)` by

```text
2 pi N+O(1),                                             (42)
```

uniformly in `N`; the extra factor `w` contributes only the arc length.  Strict positivity of
the boundary argument derivative gives `N-O(1)` crossings of each congruence class `0` and `pi`
modulo `2 pi`, and the crossings alternate.  Repeating the estimate in every fixed neighborhood
of `x_0` proves coalescence there.

If a subsequence of `(26)` converged spherically on such a neighborhood, its continuous
meromorphic limit would take both values `0` and `infinity` at `x_0`, because zeros and poles of
the subsequence approach that point.  This is impossible.  Finally, a rational inner function is
the quotient of a finite Hermite--Biehler pair after clearing its denominator.  Thus the example
already lies inside the abstract all-angle structure used by the finite-aperture theory; only the
literal Suzuki source can exclude it.

### Positive survivor from the no-go

Equation `(41)` identifies the conserved quantity.  First-jet saturation controls the total
radial Blaschke budget `-log kappa_c=O(c^2)`, not the number of factors: that budget can be split
among arbitrarily many zeros of depth `O(c^2/N)`.  Any successful Suzuki theorem through the real
axis must therefore prove a source-specific anti-fragmentation law.  Distinct sufficient closure
forms on each fixed physical interval include:

```text
uniform Clark-level count;
uniform lower radial depth per contributing phase turn;
common-gauge normality of the literal antipodal entire pair.               (43)
```

This is a genuine source demand.  It cannot be obtained from the generic Livsic,
Hermite--Biehler, Schur, or first-jet package.

## 8. Intrinsic coalescing source law

The preceding crossing theorem must not be mislabeled as source admission merely because both
endpoints are computed from finite operators.  Selecting `lambda` by a divisor value would still
be a fitted interface.  The coalescing expansion exposes the source object that exists before any
comparison.

Fix `a>0`, let `lambda<lambda_a`, and put

```text
R_(a,lambda)=(A_a-lambda)^(-1),
E_(a,c)(lambda)=<cosh(cX),R_(a,lambda)cosh(cX)>,
O_(a,c)(lambda)=<sinh(cX),R_(a,lambda)sinh(cX)>.          (44)
```

These are positive because the shift is below the floor.  Define the intrinsic source tangent

```text
q_a(lambda)
 = <X,R_(a,lambda)X>/<1,R_(a,lambda)1>.                  (45)
```

### Theorem E — the coalescing defect is a position-resolvent quotient

Uniformly on every compact shift interval below `lambda_a`,

```text
1-kappa_(a,c)(lambda)=2c^2 q_a(lambda)+O(c^4).           (46)
```

The real-analytic curve `q_a` is produced by the literal restricted-Weil operator and the fixed
polynomial source pair `(1,X)`.  It contains no Xi zero, target jet, or fitted coefficient.

### Proof

The `L^2(-a,a)` Taylor expansions are

```text
cosh(cX)=1+(c^2/2)X^2+O(c^4),
sinh(cX)=cX+(c^3/6)X^3+O(c^5).                           (47)
```

On a compact shift interval the positive resolvents are uniformly bounded.  Therefore

```text
E_(a,c)(lambda)=<1,R_(a,lambda)1>+O(c^2),
O_(a,c)(lambda)=c^2<X,R_(a,lambda)X>+O(c^4).             (48)
```

Since `1-kappa=2O/(E+O)`, equations `(45)` and `(48)` give `(46)` with uniform remainder.

The tangent also has an exact source transport law.  Let `mu_(0,a)` and `mu_(1,a)` be the spectral
measures of `1` and `X`.  Resolvent differentiation gives

```text
q_a'(lambda)
 = {<X,R^2X><1,R1>-<X,RX><1,R^2 1>}/<1,R1>^2

 = 1/<1,R1>^2 int int
     (s-t)/((t-lambda)^2(s-lambda)^2)
     dmu_(1,a)(t)dmu_(0,a)(s).                           (49)
```

Thus its turning points are exact credit--debt balances between the position and constant source
spectra, not arbitrary interpolation nodes.  At the free end, strong resolvent scaling gives

```text
lim_(lambda->-infinity) q_a(lambda)
 = ||X||_2^2/||1||_2^2=a^2/3.                           (50)
```

Equations `(45)`, `(49)`, and `(50)` are the intrinsic coalescing analogue of the fixed-anchor
parity-transport curve in the updated source-superselection paper.

### Theorem F — the comparison constant is pre-divisor theta data

The scalar `tau_0` in `(12)` need not be read from the Xi divisor.  Let

```text
mu_j=thetaCuspNormalizedEvenMoment(j)                    (51)
```

be the normalized raw moments of the positive theta-cusp source.  The read-only formal corpus
proves

```text
M_0(0)=normalizedPrimeArchMoment(0)=mu_1,
M_1(0)=normalizedPrimeArchMoment(1)=mu_1^2/2-mu_2/6.     (52)
```

Consequently

```text
tau_src
 := normalizedPrimeArchMoment(1)/normalizedPrimeArchMoment(0)
  = mu_1/2-mu_2/(6mu_1)
  = tau_0>0.                                             (53)
```

This is a pre-divisor source definition: the theta density, its raw moments, and the continued
prime--Gamma cumulant recurrence are constructed without selecting a zero.  The full function
`kappa_Xi(c)` likewise comes from the theta Fourier--Laplace `XiC` and its logarithmic derivative
before any divisor is enumerated.

Combining `(46)` and `(53)` gives the honest small-anchor interface:

```text
finite restricted-Weil source: q_a(lambda)
global theta/prime--Gamma source: tau_src.               (54)
```

If two source-declared shifts bracket `tau_src` under `q_a`, the intermediate-value crossing in
Theorems A--B is source-to-source calibrated.  This repairs the scalar target-fitting defect, but
it is still not full admission--separation: scalar equality does not prove that the Suzuki
completion retained reflection labels or that its full meromorphic carrier equals Xi.

The exact next source theorem is therefore no longer “find a shift matching a target number.”  It
is to derive, from the restricted-Weil prime--Gamma kernel, a cofinal shift schedule and
anti-fragmentation law for `(45)` whose entire blown carrier converges to the theta-source carrier.

### Corollary F.1 — a transverse source tangent canonically lifts to exact matching

The scalar shift need not be reselected independently at every positive anchor.  Put `t=c^2` and,
for `t>0`, define

```text
Phi_a(t,lambda)
  =(1-kappa_(a,sqrt(t))(lambda))/(2t),
Psi(t)=(1-kappa_Xi(sqrt(t)))/(2t).                       (54a)
```

The even power series of `cosh`, `sinh`, and the theta logarithmic derivative extend these
functions real-analytically across `t=0`, with

```text
Phi_a(0,lambda)=q_a(lambda),       Psi(0)=tau_src.        (54b)
```

Suppose a finite aperture has a pre-divisor tangent match

```text
q_a(lambda_*)=tau_src,      q_a'(lambda_*)!=0.            (54c)
```

Then the analytic implicit-function theorem gives `epsilon>0` and a unique real-analytic branch
`lambda_a(t)` for `|t|<epsilon` such that

```text
lambda_a(0)=lambda_*,
kappa_(a,sqrt(t))(lambda_a(t))=kappa_Xi(sqrt(t))
                                      for 0<t<epsilon.   (54d)
```

Every object in `(54a)--(54c)` is declared before divisor enumeration: `Phi_a` comes from the
finite restricted-Weil resolvent and `Psi` from the global theta/prime--Gamma source.  Thus a
transverse tangent root supplies a canonical exact small-anchor continuation, rather than a new
target-fitted root choice for each `c`.  This still does not prove that such roots exist cofinally,
remain uniformly transverse, preserve reflection labels, or identify the full carrier.

### Theorem F.2 — locked-floor boundary layers give source-calibrated schedules

The tangent chart above describes roots staying a fixed distance below the floor.  Roots may
instead enter the ground pole as `c` collapses.  That singular schedule is also determined by
finite-source data.

Let `P_0` be the common ground projection, `Q=I-P_0`, and let

```text
S_0=Q(A_a-lambda_0)^(-1)Q                              (54e)
```

denote the positive reduced resolvent on `Q L^2(-a,a)`.  Retain the first visible degrees and
residues `r,s,A_r,B_s` from `(2)--(3)`, put `d=|r-s|`, and set `t=c^2`.

**Odd-leading floor.** Suppose `s<r`.  Then `P_0 1=0`, so

```text
C=<1,S_0 1>>0.                                          (54f)
```

For `rho>0`, take

```text
lambda=lambda_0-rho t^(s+1),      widehat(kappa)=-kappa.
```

The oriented defect has the uniform boundary-layer limit

```text
lim_(t->0+) (1-widehat(kappa))/(2t)
  =(rho C+1_(d=1) A_r)/B_s.                             (54g)
```

Consequently the source/theta equation has a unique analytic positive boundary-layer branch
whenever

```text
rho_*=(B_s tau_src-1_(d=1)A_r)/C>0.                    (54h)
```

For every nonadjacent odd-leading floor `d>=3`, `(54h)` is automatic and
`rho_*=B_s tau_src/C`.  For an adjacent floor it is exactly the already sharp condition
`eta_a=A_r/B_s<tau_src`.  Analytic implicit continuation gives

```text
lambda_a(c)=lambda_0-rho_a(c^2)c^(2s+2),
rho_a(0)=rho_*,
-kappa_(a,c)(lambda_a(c))=kappa_Xi(c)                  (54i)
```

for all sufficiently small `c>0`.

**Even-leading floor.** Suppose `r<s`, `r>=2`, and `a^2/3>tau_src`.  Then
`P_0 1=P_0 X=0`; put

```text
C=<1,S_0 1>>0,       D=<X,S_0 X>>0.                    (54j)
```

On the scale `lambda=lambda_0-rho t^r`,

```text
lim_(t->0+) (1-kappa)/(2t)
  =(D rho+1_(d=1)B_s)/(C rho+A_r).                     (54k)
```

This fractional-linear boundary coefficient joins the literal ground coefficient

```text
gamma_0=1_(d=1)B_s/A_r
```

to the reduced-resolvent coefficient `D/C`.  If `tau_src` lies strictly between them, there is a
unique positive `rho_*` and an analytic exact branch on the scale `c^(2r)`.  In the nonadjacent
case `gamma_0=0`.  If instead `D/C<=tau_src`, every finite `rho` gives a coefficient below
`tau_src` when equality holds, or a fixed shift near the floor does so when the inequality is
strict; the free coefficient `a^2/3>tau_src` gives the opposite source-declared endpoint.  The
intermediate value theorem then gives exact matching shifts for all small `c`.  In the nonadjacent
case `r=0<s`, the same fixed-shift bracket applies because `q_a(lambda)->0` at the ground pole.

For an adjacent even-leading floor with `r>=2`, this gives the sharper exhaustive automatic
selection test

```text
min {eta_a,D/C}<tau_src
  => exact pre-divisor matching shifts for all small c.                   (54k')
```

If `tau_src` lies strictly between `eta_a` and `D/C`, the shifts form the analytic boundary branch
above.  If `D/C<tau_src`, the reduced fixed-shift endpoint and the free endpoint give the bracket.
Thus failure of automatic adjacent selection requires both `eta_a>=tau_src` and
`D/C>=tau_src`, with equality cases deferred to higher order, plus failure of any finite-shift dip
below `tau_src`.

Therefore every nonadjacent locked floor at a sufficiently large aperture has a pre-divisor
source-to-source exact matching schedule.  In the adjacent even-leading case, `(54k)` exposes a
joint sharp wall when `r>=2`: automatic selection can fail only when both
`eta_a=B_s/A_r` and `D/C` are at least `tau_src`.  The adjacent case `r=0,s=1` stays in the
fixed-shift tangent chart.

### Proof

For `delta=lambda_0-lambda`, spectral reduction gives

```text
(A_a-lambda)^(-1)=delta^(-1)P_0+S_0+O(delta)             (54l)
```

in operator norm.  If `s<r` and `delta=rho t^(s+1)`, equations `(5)` and `(54l)` give

```text
O_(a,c)=B_s/(rho t)+O(1),
E_(a,c)=C+1_(d=1)A_r/rho+O(t).                           (54m)
```

Since `1+κ=2E/(E+O)`, this proves `(54g)`.  Its derivative with respect to `rho` at `t=0` is
`C/B_s>0`, so `(54h)--(54i)` follow from the analytic implicit-function theorem.

If `r<s`, `r>=2`, and `delta=rho t^r`, the same calculation gives

```text
E_(a,c)=A_r/rho+C+O(t),
O_(a,c)=t(D+1_(d=1)B_s/rho)+O(t^2),                     (54n)
```

which proves `(54k)`.  Its derivative has the constant sign of
`D A_r-1_(d=1)B_s C`, so it is strictly monotone unless its two endpoint coefficients coincide.
The analytic branch and the stated bracketing alternatives follow.  All expansions are uniform
for `rho` in a compact subinterval of `(0,infinity)`.

## 9. Movable-anchor Clark coherence law

The anti-fragmentation term can be written entirely in Suzuki source vectors.  Keep `a,c,lambda`
fixed, put `T=A_a-lambda>0`, and let

```text
T v_z=e^(-izX),
N_c=||v_(ic)||_T^2.                                      (55)
```

For a self-adjoint extension `L_theta`, normalize `g_c=v_(ic)/sqrt(N_c)` and let `nu_(c,theta)` be
its spectral probability.  Rephase the characteristic function so that this extension is the
Clark level in the Cayley transform below.  The movable-anchor Donoghue function then has the exact
spectral formula

```text
m_c(z)=i(1+Theta_c(z))/(1-Theta_c(z))
      =int_R (tz+c^2)/(c(t-z)) dnu_(c,theta)(t).          (56)
```

Indeed the integrand equals `i` at `z=ic`, and the Livsic--Donoghue resolvent identity gives the
same normalized Herglotz function.  Rewriting the kernel gives

```text
(tz+c^2)/(c(t-z))
 =(t^2+c^2)/(c(t-z))-t/c.                               (57)
```

Thus the finite Nevanlinna weight at an extension eigenvalue `x` is

```text
mu_x=(x^2+c^2)p_x/c,
p_x=nu_(c,theta)({x}).                                   (58)
```

### Theorem G — Clark mass is exact source coherence

Let `phi_x=v_x/||v_x||_T` be the normalized extension eigenvector.  Cyclicity of the deficiency
vector gives

```text
p_x
 = |<g_c,phi_x>_T|^2
 = |<v_(ic),v_x>_T|^2/(N_c ||v_x||_T^2)
 =: C_(a,c,lambda)(x)>0.                                 (59)
```

Here `C` is the squared cosine of the `T`-angle between the anchor deficiency vector and the
actual real extension eigenvector.  At the same point, the Cayley residue law and `(58)` give

```text
phi_c'(x)
 =2/mu_x
 =2c/((x^2+c^2)C_(a,c,lambda)(x)).                      (60)
```

Equations `(59)--(60)` generalize the corpus's fixed-anchor `c=1` source-weight law.  Their proof
uses only the spectral theorem, normalization at `ic`, and the already established finite Suzuki
cyclicity; no cofinal or RH premise occurs.

### Exact fragmentation consequence

For either antipodal extension level and any real interval `J`,

```text
sum_(x in spec(L_theta) intersect J) C_(a,c,lambda)(x) <= 1.  (61)
```

Therefore `N` Clark points in `J` force at least one literal source coherence to be at most `1/N`.
Conversely, a uniform positive coherence floor on the points in `J` gives a uniform Clark-count
bound there.  The rational-inner family in Theorem D realizes the failure mode by splitting one
probability into arbitrarily many vanishing coherences.

This is the precise source meaning of real-axis overcrowding:

```text
unbounded local Clark count
  => fragmentation of the anchor probability
  => extension eigenvectors with vanishing T-angle coherence.             (62)
```

The implication is deliberately one-way.  A bounded number of local atoms may also have weights
tending to zero, so a uniform coherence floor is sufficient, not necessary, for count tightness.

The position-commutator identity supplies only part of a possible proof.  For

```text
H_(a,lambda)(x)=||v_x||_T^2=<e^(-ixX),R_(a,lambda)e^(-ixX)>,
```

resolvent differentiation gives the convention-independent identity

```text
|H_(a,lambda)'(x)|
 =|<v_x,[A_a,X]v_x>|.                                   (63)
```

Hence the literal prime--Gamma torque controls variation of the norm in the denominator of
`(59)`.  It does not bound the overlap `|<v_(ic),v_x>_T|` from below.  Cauchy--Schwarz has the wrong
orientation.  A torque-only proof of anti-fragmentation is therefore incomplete; the missing
source theorem must couple torque to overlap, or directly prove local Clark-count tightness.

### Corollary G.1 — boundary-layer overcrowding has a ground Fourier near-zero bottleneck

The exact schedules in Theorem F.2 make the overlap factor asymptotically explicit.  On an
odd-leading boundary branch, put

```text
u_a=P_0(X^s/s!),
G_a(x)=<u_a,P_0 e^(-ixX)>,
H_a^0(x)=||P_0 e^(-ixX)||^2.                             (64)
```

Uniformly on every real compact set on which `H_a^0` is bounded away from zero,

```text
C_(a,c,lambda_a(c))(x)
  -> |G_a(x)|^2/(B_s H_a^0(x)).                          (65)
```

On an even-leading analytic boundary branch, use `u_a=P_0(X^r/r!)`, let
`C_0=<1,S_0 1>`, and let `rho_*` be the branch coefficient.  Then

```text
C_(a,c,lambda_a(c))(x)
  -> |G_a(x)|^2/((A_r+rho_* C_0)H_a^0(x)).               (66)
```

### Proof

Write `delta=lambda_0-lambda_a(c)`.  The numerator in `(59)` is

```text
<v_(ic),v_x>_T=<e^(cX),(A_a-lambda)^(-1)e^(-ixX)>.       (67)
```

For the odd-leading scale `delta~rho_*c^(2s+2)`, its ground term is
`delta^(-1)c^s G_a(x)(1+O(c))`; the anchor norm is
`B_s/(rho_*c^2)(1+O(c^2))`, and the real-vector norm is
`delta^(-1)H_a^0(x)(1+o(1))`.  The powers and `rho_*` cancel in `(59)`, proving `(65)`.

For the even-leading scale `delta~rho_*c^(2r)`, the same numerator is
`delta^(-1)c^r G_a(x)(1+O(c))`, the anchor norm tends to
`A_r/rho_*+C_0`, and the real-vector norm is
`delta^(-1)H_a^0(x)(1+o(1))`.  This proves `(66)`.  Finite-dimensionality of `P_0` makes all
remainders uniform on real compact sets.

### Frontier consequence

The function `G_a` is the Fourier transform of the compactly supported literal ground vector
`u_a`; it is entire and not identically zero.  On every compact interval avoiding its zeros and
the common zeros of `P_0e^(-ixX)`, equations `(65)--(66)` give a positive coherence floor.  By
`(61)`, local Clark count is then uniformly bounded as `c downarrow0`.  For fixed `a`, any
vanishing-coherence sequence with a convergent physical point and nonvanishing `H_a^0` must
approach a zero of `G_a`.

Thus the real-axis obstruction is no longer an unspecified normality estimate.  On locked-floor
branches it is the cofinal quantitative near-zero/sublevel-set problem for the normalized overlap
built from

```text
x |-> <P_0(X^k/k!),e^(-ixX)>,                            (68)
```

with `k=s` on odd-leading floors and `k=r` on even-leading floors.  Exact zero count alone is not
enough across changing apertures: these normalized Fourier overlaps may become arbitrarily small
without vanishing.  Compact support and exponential type give neither a uniform fixed-window zero
bound nor a uniform sublevel estimate as `a` changes.  A successful theorem must use the literal
restricted-Weil ground equation; generic Paley--Wiener theory cannot supply it.

### Corollary G.2 — exact ground-frame angular torque

The forced vanishing at the origin is not a coherence defect.  In either leading orientation let
`k=min{r,s}`, `u_a=P_0(X^k/k!)`, and `w_a(x)=P_0e^(-ixX)`.  Minimality of `k` gives the
Hilbert-valued expansion

```text
w_a(x)=(-ix)^k u_a+O(x^(k+1)).                           (69)
```

Therefore

```text
|<u_a,w_a(x)>|^2/(||u_a||^2||w_a(x)||^2) -> 1
                                                    as x->0.             (70)
```

The only possible loss is projective rotation away from the leading ground direction.  Wherever
`w_a(x)!=0`, define its Fubini--Study speed

```text
Omega_a(x)
 = ||(I-P_(w_a(x)))P_0 X e^(-ixX)||/||w_a(x)||,          (71)
```

where `P_(w)` is orthogonal projection onto the complex line through `w`.  On every interval from
the removable initial point `0` containing no other zero of `w_a`, the standard projective-length
bound gives

```text
arccos(|<u_a,w_a(x)>|/(||u_a|| ||w_a(x)||))
 <= int_[0,x] Omega_a(t) |dt|.                           (72)
```

Consequently, if one cofinal locked family satisfies on a fixed physical interval

```text
sup_x int_[0,x] Omega_a(t)|dt| <= pi/2-epsilon,          (73)
```

then the normalized overlap in `(65)--(66)` is at least `sin(epsilon)^2`.  After multiplication by
the explicit even-leading ground-share factor `A_r/(A_r+rho_*C_0)`, this gives a literal coherence
floor and hence a uniform Clark-count bound through `(61)`, provided that factor also has a cofinal
positive floor.  No extra factor is needed in the odd-leading case.

Equation `(71)` is the missing overlap-sensitive torque.  The earlier scalar position torque
`(63)` controls only norm variation; `(71)` removes the radial component and measures rotation of
the actual ground Fourier line.  The ambient position bound gives only
`Omega_a(x)<=a||e^(-ixX)||/||P_0e^(-ixX)||`, which degenerates exactly when ground observability is
small.  The needed subcritical budget `(73)` must therefore come from the restricted-Weil ground
equation.

### Sharpness — compact support, parity, and exponential sourcing do not bound angular torque

Fix `L>0`, put `a_N=N pi/L`, and in `L^2(-a_N,a_N)` let `P_N` project onto

```text
span {e_n(t)=(2a_N)^(-1/2)exp(i n pi t/a_N):
                                      1<=|n|<=N}.         (74)
```

This space is reflection invariant and contains both parities.  It is orthogonal to `1`, its odd
part sees `X`, and its even part sees `X^2`; hence its first visible degrees are exactly `s=1` and
`r=2`.  It is the common ground space of the bounded reflection-invariant self-adjoint operator

```text
A_N=I-P_N.                                               (75)
```

The projection kernel is a finite symmetric Fourier sum in `x-y`; hence `(75)` is itself a
bounded even truncated-convolution operator, not an arbitrary nonlocal matrix.

At the fixed physical nodes `x_n=-n pi/a_N in [-L,L]`, `1<=|n|<=N`,

```text
P_N e^(-ix_n X)=sqrt(2a_N)e_n.                           (76)
```

Successive node lines are orthogonal.  Therefore either the projective curve
`x |-> [P_Ne^(-ixX)]` meets a zero between two nodes, or its Fubini--Study length across
`[-L,L]` is at least `(2N-1)pi/2`.  In either case no aperture-uniform version of `(73)` follows
from compact support, parity, even convolution structure, finite ground multiplicity, polynomial
visibility, or exponential sourcing.

This countermodel is not Suzuki's restricted-Weil operator and makes no statement about its
literal ground spaces.  Its role is class closure: proving `(73)` now provably requires arithmetic
ground-equation structure beyond every abstract ingredient listed above.

### Corollary G.3 — the ground multiplier cancels; angular torque is a two-port residual invariant

The literal restricted-Weil ground equation identifies where that arithmetic structure must enter.
Choose an orthonormal basis `phi_1,...,phi_d` of `ran(P_0)` and put

```text
F_a(x)=(Fourier(phi_1)(x),...,Fourier(phi_d)(x)).         (77)
```

Up to conjugation of coordinates, `[F_a(x)]` is exactly the projective line
`[P_0e^(-ixX)]`.  Let `p_a(x)` be Suzuki's whole-line prime--Gamma multiplier and set

```text
m_a(x)=p_a(x)-lambda_0,
beta_a(x)=m_a(x)F_a(x).                                  (78)
```

For each ground mode, the compressed eigen-equation says that `beta_(a,j)` is the Fourier transform
of its exterior residual.  The completed-mode theorem gives the exact two-port decomposition

```text
beta_a(x)=e^(iax)B_(a,-)(x)+e^(-iax)B_(a,+)(x),          (79)
```

with vector-valued boundary amplitudes in the two opposite `L^2` Hardy classes.

On every real interval where `m_a` is nonzero, scalar multiplication changes only the radial and
phase component of a vector derivative.  Hence

```text
[beta_a(x)]=[F_a(x)],
||(I-P_(beta_a))beta_a'||/||beta_a||
 =||(I-P_(F_a))F_a'||/||F_a||
 =Omega_a(x).                                            (80)
```

Thus no pointwise size, sign, or monotonicity estimate for the common prime--Gamma multiplier can
control the angular budget `(73)`; it cancels identically in projective geometry.  Arithmetic can
enter only through the return constraint coupling the two Hardy port vectors in `(79)`, together
with control of the low-frequency zeros of `m_a`.  Existing rigged-Wiener inversion controls the
high-frequency carrier but deliberately leaves exactly this low-frequency return kernel open.

The source theorem needed for real-axis closure is therefore sharper than “use the restricted-Weil
multiplier”: prove a cofinal low-frequency **two-port return-coherence bound** for the actual ground
residual vector in `(79)`, strong enough to make its projective length subcritical, or prove that no
such bound can hold.

### Corollary G.4 — conditional port-wedge death/survival classification

Suppose on a real interval that the two Hardy boundary vectors in `(79)` have locally absolutely
continuous representatives.  Write

```text
beta_a(x)=e^(iax)u_a(x)+e^(-iax)v_a(x).                  (81)
```

For vectors in the finite-dimensional ground-coordinate space, the projective speed is

```text
Omega_a(x)=||beta_a(x) wedge beta_a'(x)||/||beta_a(x)||^2. (82)
```

Then direct differentiation gives the exact almost-everywhere identity

```text
beta_a wedge beta_a'
 =-2ia (u_a wedge v_a)+R_a,

R_a
 =e^(2iax)(u_a wedge u_a')
  +e^(-2iax)(v_a wedge v_a')
  +(u_a wedge v_a')+(v_a wedge u_a').                   (83)
```

Within this regularity class, `(83)` classifies the aperture-scale obstruction.  Put
`S_a=||u_a||+||v_a||`.  On any interval where

```text
2a||u_a wedge v_a||-||R_a|| >= delta a S_a^2            (84)
```

for one `delta>0`, equations `(82)--(83)` and `||beta_a||<=S_a` give

```text
Omega_a>=delta a.                                       (85)
```

On every fixed interval of positive length, `(85)` contradicts the subcritical budget `(73)` for
large aperture.  Therefore a Suzuki survivor must defeat `(84)` on every set of fixed positive
length through a mixture of the following source mechanisms:

```text
projective port coalescence: ||u_a wedge v_a||/S_a^2 loses every positive floor;
order-a countertransport:    ||R_a|| comparable to a||u_a wedge v_a||;
singular concentration:      all transverse failure is confined to shrinking sets;
rough-port escape:           local absolute continuity itself fails.                (86)
```

Parity and reality identify the left port with a reflected, parity-signed right port, so `(86)` is
exactly a pre-scalar reflection statement.  It is not implied by scalar multiplier control because
that multiplier has already cancelled in `(80)`.  Excluding the first three mechanisms for the literal
prime--Gamma return relation after proving the displayed port regularity would kill the
boundary-layer Suzuki producer; a quantitatively subcritical combination that proves `(73)` would
supply the missing real-axis compactness input.  Existing exterior-residual theory gives only Hardy
`L^2`, not the local absolute continuity assumed here.  Without a new regularity theorem, `(83)` is
not licensed pointwise and rough-port escape remains open.

The updated admission--separation and source-horizon theorems classify these mechanisms.  Port
coalescence occurring before a label-sensitive reflected source map is not admission: it erases the
distinction before scalarization.  Order-`a` countertransport is necessarily non-uniform in
aperture, while shrinking-set concentration and rough-port escape are singular.  Hence every
source-valid realization of `(86)` must retain reflection labels before coalescence or enter a singular, nonclosable, or
relation-valued category.  This excludes regular label-blind use of `(86)` but does not exclude
Suzuki's literal scalar finite-interval family; proving its source provenance remains a separate
gate.

### Corollary G.5 — actual Suzuki ports are locally `H^1` away from zero frequency

The rough-port alternative can be removed on every real compact interval separated from `0`.
For a completed ground mode, translate either exterior residual half-line to `[0,infinity)` and call
it `h_a(t)`.  The atomic prime translations and the compact polar remainder vanish for large `t`.
The only long-range term is the logarithmic kernel.  Since the ground mode is bounded and supported
in `[-a,a]`, the elementary expansion

```text
1/(t-y)=1/t+y/(t(t-y))
```

gives constants `gamma_(a,+-)` such that

```text
h_a(t)=gamma_(a,+-)/(1+t)+r_(a,+-)(t),
t r_(a,+-)(t) in L^2(0,infinity).                        (87)
```

The boundary collar contributes no obstruction: its worst singularity is logarithmic, so
`t h_a(t)` is square integrable there.  By scalar Plancherel, the Fourier transform of the remainder
has weak derivative in `L^2`.  For the model tail,

```text
t/(1+t)=1-1/(1+t),                                      (88)
```

so its Fourier derivative is the sum of a distribution supported at frequency `0`, a principal
`1/x` term, and an `L^2_loc` function.  Hence on every compact `K subset R\{0}`,

```text
B_(a,+-)|_K in H^1(K) subset AC(K).                     (89)
```

Coordinatewise application proves `(89)` for the vector ports in `(79)`.  Corollary G.4 and the
wedge identity `(83)` are therefore unconditional almost everywhere on every nonzero physical
window.  Port roughness survives only at frequency `0`, where the first-visible ground expansion
`(69)--(70)` separately removes the apparent coherence zero.  The actual nonzero-window survival
mechanisms are now only projective port coalescence, order-`a` countertransport, and shrinking-set
concentration.

## 10. Conjecture loop and failures

1. **Prime-seam shape derivative forces parity splitting — failed.**  The ground form domain is
   `H^log`, not `H_0^1`; boundary values and derivatives need not exist.  A Taylor law at a new
   seam would be theatre without a new regularity theorem.
2. **Eventual parity locking is itself terminal — failed.**  Antipodal angles retain both parity
   residues, while a movable anchor makes their first visible moments measurable.
3. **Arbitrary purity is enough — failed and repaired.**  Source and target both approach a pure
   endpoint as `c downarrow 0`.  Comparing only their limits loses the problem.  Equations
   `(7)` and `(13)` compare the rates and expose the adjacent resonance `(19)`.
4. **Moving the anchor destroys the fixed Xi target — failed.**  Exact identity `(21)` gives a
   canonical meromorphic blow-up with no fitted `z`-dependent gauge.
5. **A separate half-plane normality estimate is still needed — failed.**  Factoring the anchored
   Schur map and using Schwarz--Pick proves Theorem C.  Exact first-jet matching already pays the
   singular `1/c` compactness cost off the real axis.
6. **The same jet estimate should control the real divisor — failed sharply.**  Theorem D splits
   the fixed radial defect budget into arbitrarily many ultrashallow Blaschke factors.  Generic
   all-angle structure permits unlimited Clark overcrowding at one real point.  The positive
   survivor is the menu of sufficient source anti-fragmentation closures `(43)`.
7. **An IVT crossing is automatically source admission — failed and repaired.**  A scalar crossing
   can be target-fitted.  Theorem E extracts the pre-comparison restricted-Weil curve `q_a`, and
   Theorem F reconstructs its comparison constant from the positive theta source.  This makes the
   calibration pre-divisor, but reflection separation and full-carrier identification remain.
8. **A relative position-torque bound should prevent overcrowding — failed as stated.**  Equation
   `(63)` controls the norm of real deficiency vectors, while `(59)` shows that Clark mass also
   needs a lower overlap with the anchor vector.  The missing quantity is source coherence, not
   norm growth alone.
9. **Exponential type alone should impose a local Weyl count — failed as a route-closing
   argument.**  Across changing apertures, global phase growth does not prevent an abstract
   Hermite--Biehler family from evacuating one fixed interval or concentrating arbitrarily many
   shallow turns there.  Theorem D realizes the concentration side.  Any usable density theorem
   must therefore be proved for the literal restricted-Weil resolvent vectors and at the physical
   shrinking-anchor scale; generic Cartwright or Schur growth is insufficient.
10. **Every tangent crossing should be automatically transverse — failed generically.**  In the
    spectral formula `(50)`, take both parity measures at the same one-point spectral location and
    choose their masses with ratio `tau_src`.  Then `q_a(lambda)` is identically `tau_src`, so
    `q_a'=0`.  Abstract positivity and parity cannot supply `(54c)`.  Corollary F.1 moves the live
    task to literal restricted-Weil existence and transversality, without laundering either as a
    generic resolvent fact.
11. **A root entering the locked ground pole is intrinsically target-fitted — failed.**  Reduced
    resolvent expansion proves Theorem F.2.  The singular powers `c^(2s+2)` and `c^(2r)`, their
    leading constants, and the adjacent reduced coefficient `D/C` are all finite-source data.
    Nonadjacent locking therefore has a pre-divisor exact schedule.  The remaining adjacent wall
    is literal source geometry, not freedom to choose a divisor-dependent path.
12. **Boundary-layer source coherence remains opaque — failed.**  Substituting the exact singular
    schedules into `(59)` proves `(65)--(68)`.  A uniform normalized-overlap floor prevents
    fragmentation and bounds local Clark count.  The hard real-axis problem is now a cofinal
    quantitative near-zero estimate for `(68)`, not an arbitrary Clark-measure estimate.  Bare
    zero counting would still be insufficient and is not claimed.
13. **The forced origin zero causes unavoidable overcrowding — failed.**  First-visible-degree
    minimality proves `(69)--(70)`: numerator and vector norm vanish in the same ground direction.
    The source overlap loses mass only by projective rotation.  Equations `(71)--(73)` identify the
    exact angular-torque budget sufficient to prevent it; the ambient position estimate degenerates
    with ground observability and leaves the literal ground-equation estimate open.
14. **Compact support and exponential sourcing should bound the ground rotation — failed
    sharply.**  The Fourier-window ground spaces `(74)--(76)` have exact degrees `(s,r)=(1,2)` but
    traverse `2N` mutually orthogonal projective directions in one fixed interval.  Their angular
    length grows at least `(2N-1)pi/2`.  Any proof of `(73)` must use Suzuki's arithmetic ground
    equation, not support, parity, even convolution, rank, or source analyticity.
15. **Prime--Gamma multiplier control should bound the ground rotation — failed exactly.**  The
    common multiplier cancels from projective speed in `(80)`.  The actual arithmetic variable is
    the low-frequency return relation between the two exterior Hardy ports `(79)`, not multiplier
    growth or sign.  High-frequency Wiener inversion does not touch this kernel.
16. **Two-port reflection is only qualitative — failed conditionally, with a new regularity
    wall.**  For locally absolutely continuous ports, exterior differentiation gives exact wedge
    law `(83)` and classification `(86)`: reflected ports coalesce, derivatives pay order-aperture
    countertransport, or failure concentrates.  Actual corpus ports are only Hardy `L^2`; failure
    of local absolute continuity is a fourth singular escape and must not be silently differentiated.
17. **The rough-port escape persists on target windows — failed.**  The explicit exterior
    logarithmic tail splits as `(87)`.  After subtracting its single `1/(1+t)` mode, the residual has
    an `L^2` first moment, while the model derivative is regular away from frequency zero.  Thus the
    actual Suzuki ports satisfy `(89)`, licensing `(83)` on every nonzero window without an added
    regularity hypothesis.

## 11. Hostile scope audit

- **No RH proof.**  First-jet matching is necessary, not full Clark-measure or Xi identification.
- **No source-provenance laundering.**  Theorems A--B prove finite-source range, not by themselves
  admission.  Theorem E constructs the source-only curve before comparison, and Theorem F gives a
  pre-divisor theta formula for its calibration.  Full label-sensitive separation remains open.
- **No fake uniformity.**  Anchor `c_a` may shrink with aperture.  Equation `(21)` states exactly
  which deterministic blow-up is then required.  Theorem C proves its normality only on compact
  subsets of `C\R`, not through the moving real divisor.
- **No boundary regularity.**  Proof uses bounded spectral projections and `L^2` Taylor series,
  never pointwise values of a Friedrichs-domain eigenfunction.
- **No claim at the joint adjacent wall.**  `eta_a>tau_src` alone is not terminal: an even-leading
  floor is rescued when `D/C<tau_src`.  Even when both coefficients are unfavorable, a finite
  interior excursion remains logically possible.
- **No Lean mutation.**  Existing corpus was read only.  It supplies the unconditional positive
  shifted-moment and radial-gap theorems used to audit `(8)--(13)`.
- **No generic compactness laundering.**  Theorem D proves that even exact jet matching plus a
  finite Hermite--Biehler pair does not control the real boundary.  Any later claim must use a
  property proved for Suzuki's resolvent vectors or characteristic pair.
- **No count/weight equivalence.**  Theorem G proves that overcrowding forces coherence collapse
  and that a coherence floor prevents overcrowding.  It does not claim every vanishing atom
  weight creates extra points.
- **No abstract angular bound.**  The Fourier-window countermodel `(74)--(76)` proves that compact
  support, parity, even convolution, exponential sourcing, and finite ground rank do not control `(73)`.  Only a
  theorem using Suzuki's literal ground equation can advance that wall.
- **No multiplier laundering.**  Corollary G.3 proves that the common literal prime--Gamma
  multiplier cancels from projective speed.  The arithmetic input must constrain the actual
  low-frequency two-port return relation, not merely the multiplier.

## 12. Novelty boundary

Classical parents, not claimed novel:

- changing deficiency points and unimodular normalization of a Livsic characteristic function;
- spectral-projection pole residues;
- Hilbert-valued Taylor expansion;
- Cayley/Donoghue fractional-linear identities;
- the intermediate value theorem;
- Schwarz--Pick, Schwarz factorization, and Montel compactness;
- reduced-resolvent Laurent expansion and the analytic implicit-function theorem;
- Aleksandrov--Clark atomic measures, reproducing-kernel bases, and reciprocal
  phase-derivative weights in model/de Branges spaces;
- Fubini--Study path length as an upper bound for projective angle.

Candidate new content is their exact Suzuki--Xi conjunction: the degree-gap trichotomy
`d=1` versus `d>=3`, the adjacent coefficient wall `eta_a=tau_0`, the resulting correction of
eventual parity locking, the coalescing antipodal blow-up `(21)`, and the implication from its
matched quadratic jet to singular half-plane compactness in Theorem C.  Repository searches found
only fixed-anchor Schur compactness and the separate conditional real-axis overcrowding theorem,
not `(25)--(33)`.  Targeted primary-literature searches found Suzuki's fixed `+-i` construction,
general Livsic base-change theory, and classical boundary Schwarz lemmas, but no coalescing
restricted-Weil parity classification or Suzuki boundary-layer theorem `(19)--(33)`.  Specialist
review is still required before a priority claim.

The source identities in `(52)` are existing formal corpus, not new knowledge.  Candidate-new
content is the coalescing restricted-Weil tangent `(45)--(50)` and its exact assembly with the
pre-divisor theta cumulant `(53)` into the source-to-source interface `(54)`, plus the canonical
analytic lift `(54a)--(54d)` from a transverse tangent root to exact small-anchor matching and the
locked-floor boundary-layer classification `(54e)--(54n)`.

The fixed-anchor Donoghue source weights and prime--Gamma position torque also already exist in
the corpus, and the underlying Clark/reproducing-kernel geometry is classical.  Candidate-new
content in Theorem G is their movable-anchor Suzuki synthesis: the exact
`c`-dependent phase-speed law `(60)`, the identification of cofinal overcrowding with source
probability fragmentation `(61)--(62)`, and the proof that torque-only control misses the overlap
factor.  Candidate-new content in Corollary G.1 is the boundary-layer limit `(65)--(66)` and its
reduction of locked-floor overcrowding to the literal ground Fourier near-zero problem `(68)`.
Candidate-new Suzuki-specific content in Corollary G.2 is the removable origin law `(69)--(70)`
and exact ground-frame angular-torque sufficient condition `(71)--(73)`; the projective metric
inequality itself is classical.  The Fourier-window construction `(74)--(76)` is an elementary
class countermodel; its candidate-new role is proving that this exact Suzuki frontier cannot be
closed from compact support, parity, finite rank, or exponential sourcing alone.

The exterior-residual `L^2` and two-Hardy-port realization `(79)` already exists in the corpus.
Candidate-new content in Corollary G.3 is its exact projective coupling to the ground-frame torque:
the scalar multiplier cancellation `(80)` and resulting relocation of the real-axis source theorem
to low-frequency two-port return coherence.

Exterior-product differentiation is classical algebra.  Candidate-new Suzuki-specific content in
Corollary G.4 is the conditional aperture-leading port-wedge law `(83)` and its use to isolate the
three regular reflection-sensitive mechanisms plus the separate rough-port escape `(86)`.
Candidate-new content in Corollary G.5 is the source-specific upgrade from the corpus's exterior
`L^2` bound to local port `H^1` regularity away from zero, via the exact logarithmic tail split
`(87)--(89)`; Plancherel and the Fourier transform of the half-line model are classical.

The rational-inner construction of Theorem D is not claimed as a new theorem of Schur analysis.
Its scientific role is hostile classification: it proves the off-axis result is sharp and that
Route G's remaining compactness premise cannot follow from any already available abstract carrier
axiom.  Candidate-new content there is only the exact Suzuki frontier correction `(43)`.

Primary comparisons:

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- D. N. Clark, *One dimensional perturbations of restricted shifts*, J. Analyse Math. 25 (1972).
- A. Aleman, R. T. W. Martin, W. T. Ross, *On a theorem of Livsic*, arXiv:1209.4497.
- S. Belyi, K. A. Makarov, E. Tsekanovskii, *Conservative L-systems and the Livsic function*,
  arXiv:1406.2399.

## 13. Exact remaining Route-G statement

After this theorem, every nonadjacent locked ground bundle has a pre-divisor exact matching
schedule.  Cofinal scalar scheduling can fail only through an adjacent joint wall
`eta_a>=tau_src` and `D/C>=tau_src` (where the latter applies to `r>=2`), equality/higher-order
resonance, and failure of every literal finite-shift excursion.  Route G still requires:

1. local real-axis normality of the deterministically blown-up antipodal source quotients, via one
   of the literal source anti-fragmentation laws `(43)`, now concretely reduced to Clark-count
   tightness or a sufficient nonfragmentation bound on the coherences `(59)`; on boundary-layer
   branches Corollary G.1 reduces this further to a cofinal normalized-overlap sublevel estimate
   for `(68)`, with the explicit sufficient angular budget `(73)` and exact two-port residual
   formulation `(79)--(80)`; Corollary G.5 licenses the port-wedge law `(83)` on every nonzero
   target window;
2. no meromorphic cancellation of the labeled zero/pole divisors;
3. cofinal control of the remaining adjacent/resonant shift schedules and source-derived
   identification with `(21)`;
4. the higher-jet/Hermite--Biehler passage forcing the Xi divisor real.

Item 1 is now proved on both open half-planes by Theorem C.  Its exact surviving part is local
normality through the real axis, equivalently source control of Clark-divisor overcrowding.  That
real-axis tightness, noncancellation, and source-derived Xi identification -- not parity-floor
equality or the safe-shift target minor -- are the surviving scientific frontier.
Corollary F.1 closes the local-in-anchor scheduling problem whenever a source tangent root is
simple, and Theorem F.2 closes it for every nonadjacent locked-floor branch.  Cofinal control of the
remaining adjacent/resonant cases remains open.
