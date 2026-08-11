# Suzuki coalescing-anchor parity-locking reduction

- **ID:** `suzuki-coalescing-anchor-parity-locking-reduction`
- **Ledger:** `SR-65`, `SR-66`, `SR-67`, `SR-68`, `SR-69`, `SR-70`, `SR-71`
- **Stage:** 2 — dependency-closed paper proof
- **Type:** THEOREM (paper) / SOURCE-RANGE AND PRE-DIVISOR CALIBRATION ADVANCE
- **RH used:** no in Sections 2--14.7; yes as the hypothesis of the global-limit and target audits
  in Sections 14.8--14.12
- **Computation used:** no
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL CORE + RH-CONDITIONAL GLOBAL-LIMIT AUDIT]`
  `[LEAN READ-ONLY AUDITED]`
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
quotients on both open half-planes.  Section 14 computes their complete first boundary layer.  A
nonadjacent ground-pole branch loses all finite spectral response and converges to the free kernel
`i/z`, not the Xi reciprocal logarithmic derivative.  Only an adjacent ground pair or an interior
resolvent tangent can retain a nontrivial meromorphic limit.

Real-axis Clark tightness is sufficient but not logically necessary.  Normality plus agreement
with the theta/Xi target on any upper-half-plane uniqueness set already gives global half-plane
identification by Vitali, and finite-source positivity then implies RH.  The corrected source
frontier is therefore convergence, on one source-declared imaginary interval, of the explicit
adjacent ground Fourier ratio or interior resolvent Fourier ratio in Section 14.  First-defect
matching, Pick positivity, and nonadjacent scalar scheduling do not supply that convergence.

That interval theorem has an exact spectral meaning.  It is equivalent to weak convergence of
the squared movable Clark probabilities to the normalized inverse-square spectral measure of the
global zeta screw function.  Consequently interval identification forces, rather than assumes,
both zero escape at finite and projective infinity and every limiting local Clark mass.  In
dynamical form the missing theorem is convergence of the normalized cyclic correlations of the
finite self-adjoint extensions to the normalized screw signal.  Suzuki's conjectural convergence
of eigenvalue sets alone does not contain this weight information.

The target probability is nevertheless source-declared.  Suzuki's unconditional prime--Gamma
screw line has, under RH, a unique zero-energy coboundary origin obtained by Cesaro averaging the
line itself; its spectral probability is exactly the inverse-square target.  This removes target
fitting but exposes a new obstruction in Suzuki's own RH-conditional `lambda=0` embedding:
normalized coalescing finite deficiency anchors converge weakly to zero in the global Weil space.
Hence clean local spectral-projection convergence cannot carry the required positive Clark
weights.  Any successful Route-G limit must be singular at the pointed level (projection
rotation/crowding), or must use shifted metrics outside that `lambda=0` embedding.  Exact-node
real defect vectors behave oppositely: they Galerkin-lock to the global Xi eigenvectors.  The
combination yields a quantitative resolution wall: any mass-carrying one-for-one eigenvalue must
lock slower than `sqrt(alpha_a/a^3)`, unless local rank or metric comparison becomes singular.
The metric alternative is itself rigid: amplification is at most
`lambda/(alpha_a-lambda)`.  Evasion requires a positive floor-hugging shift, while proving any
positive admissible shift cofinally already proves RH directly by Weil positivity.

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

Section 14 supersedes the earlier scalar interpretation of Theorem F.2.  Every nonadjacent locked
ground bundle still has a pre-divisor exact **first-defect** schedule, but a nonadjacent
ground-pole boundary schedule has the wrong complete limit: its entire blown quotient is `i/z`.
It therefore contributes no full Xi-identifying branch.  The live branches are exactly:

1. adjacent ground-pole branches whose two first visible ground modes survive through the quotient
   `H_a/G_a`;
2. interior tangent branches whose full source coordinate is the resolvent Fourier ratio
   `H_(a,lambda)/G_(a,lambda)`;
3. equality/higher-order resonances not covered by either first-order chart.

For either of the first two branches, exact first-defect matching already supplies open-half-plane
normality and forces the limiting ratio to be a strict Caratheodory function.  Consequently
real-axis Clark tightness, explicit divisor noncancellation, and a separate higher-jet
Hermite--Biehler passage are **bypassable**, not mandatory: it suffices to prove source-derived
convergence to the theta/Xi reciprocal logarithmic derivative on one imaginary interval.  In Clark
coordinates this is the bounded transform convergence `(107)` below.  On an interior branch it is
equivalently the resolvent-position Ward equation `(112)`.

Thus the exact open core is not generic compactness.  It is to construct cofinally, from Suzuki's
literal restricted-Weil source and without divisor-fitted shifts, an adjacent or interior branch
whose explicit finite-source transform satisfies `(107)` or `(112)` on a nonempty interval.
Section 14.5
proves sharply that first-defect matching plus Pick positivity leaves infinitely many possible
carriers, so no finite-jet substitute closes this core.

## 14. Full-carrier boundary-layer classification and half-plane closure criterion

This section corrects the only remaining overstatement in Theorem F.2.  Its schedules match one
scalar jet.  The following computation decides what the **whole** coalescing quotient does on those
schedules.

### 14.1 Exact full quotient on every first-order chart

For a source-selected shift `lambda(c)<lambda_a`, set

```text
F_c(z)=int_(-a)^a [(A_a-lambda(c))^(-1)e^(cX)](x)e^(izx) dx,
b_c(z)=(z-ic)/(z+ic),
Theta_c(z)=b_c(z)F_c(z)/F_c(-z).                         (90)
```

The last identity is the movable-anchor version of Suzuki's characteristic quotient: reflection
sends the `+ic` deficiency vector to the `-ic` vector.  Multiplication by a constant unimodular
phase only relabels the extension circle.

Consider first a ground-pole boundary branch in Theorem F.2.  Put `k=min(r,s)`,
`epsilon=(-1)^k`, and

```text
u=P_0(X^k/k!),          v=P_0(X^(k+1)/(k+1)!),
G(z)=int u(x)e^(izx) dx,       H(z)=int v(x)e^(izx) dx. (91)
```

Minimality of `r,s` gives

```text
P_0e^(cX)=c^k(u+c v+O(c^2)),
G(-z)=epsilon G(z),             H(-z)=-epsilon H(z).    (92)
```

On the odd-leading scale `lambda_0-lambda(c)=rho(c^2)c^(2s+2)`, and on the even-leading
scale `lambda_0-lambda(c)=rho(c^2)c^(2r)` with `r>=2`, the reduced-resolvent expansion `(54l)`
implies, locally uniformly in `z`,

```text
F_c(z)=(c^k/(lambda_0-lambda(c)))
          (G(z)+cH(z)+o(c)).                             (93)
```

Indeed the bounded reduced term, divided by the ground term, is `O(c^(s+2))` in the odd-leading
case and `O(c^r)=o(c)` in the even-leading case.  Thus no reduced-resolvent contribution has been
silently dropped at first order.

Orient the characteristic by `widehat(Theta)_c=epsilon Theta_c`, so that it tends to `1`.  Away
from the discrete zero set of `G`, equations `(90)--(93)` give

```text
F_c(z)/F_c(-z)
 =epsilon(1+2c H(z)/G(z)+o(c)),

R_c(z):=(1-widehat(Theta)_c(z))/(c(1+widehat(Theta)_c(z)))
 -> i/z-H(z)/G(z).                                      (94)
```

For an interior tangent branch, suppose

```text
lambda(c)=lambda_*+O(c^2),       lambda_*<lambda_a,
G_(a,lambda)(z)=int [(A_a-lambda)^(-1)1](x)e^(izx) dx,
H_(a,lambda)(z)=int [(A_a-lambda)^(-1)X](x)e^(izx) dx.  (95)
```

Reflection makes `G_(a,lambda)` even and `H_(a,lambda)` odd.  Analytic resolvent expansion now
gives directly

```text
R_c(z) -> P_(a,lambda_*)(z)
 :=i/z-H_(a,lambda_*)(z)/G_(a,lambda_*)(z).              (96)
```

Near zero,

```text
H_(a,lambda)(z)/G_(a,lambda)(z)
 =i q_a(lambda)z+O(z^3).                                (97)
```

Thus Theorem E's scalar `q_a(lambda)` is exactly the first regular Taylor coefficient of the full
meromorphic source coordinate `(96)`, not a separate observable.

### Theorem H — full-carrier branch trichotomy

For every exactly first-defect-matched branch covered above:

1. if the ground degrees are nonadjacent, then `v=0` and every ground-pole boundary branch has
   the universal limit

   ```text
   R_c(z) -> i/z;                                        (98)
   ```

2. if the ground degrees are adjacent, the boundary branch has the nontrivial ground two-port
   limit `i/z-H/G`;
3. an interior branch has the nontrivial resolvent two-port limit `(96)`.

In cases 2 and 3 the apparent poles at upper-half-plane zeros of `G` are removable.  More
precisely, the right sides of `(94)` and `(96)` extend to holomorphic functions on the upper half
plane and have strictly positive real part there.  Consequently every upper-half-plane zero of
the denominator `G` is a numerator zero of at least the same order.

#### Proof

Only the removability and positivity remain after `(90)--(97)`.  Exact first-defect matching gives
`1-kappa_c=O(c^2)`, so Theorem C makes `R_c` locally bounded on the upper half plane.  Formula
`(94)` or `(96)` gives convergence off the discrete zero set of `G`.  Every normal subsequential
limit agrees there; the identity theorem makes it unique, so the whole family converges locally
uniformly and the displayed quotient extends across every zero of `G`.

Each finite `R_c` has positive real part because it is a positive multiple of the inverse Cayley
transform of a Schur function.  Its limit has nonnegative real part.  At `z=iy` for sufficiently
small `y>0`, minimality in `(91)` or parity in `(95)` gives `H/G=O(z)`, hence
`R(iy)=1/y+O(y)>0`.  The harmonic minimum principle makes the real part strictly positive
throughout the upper half plane.  A pole of `H/G` there is impossible, proving the zero-sharing
claim.

This Pick/divisibility law is not an added assumption.  It is forced by Suzuki's all-angle reality
together with the exact scalar schedule.

### 14.2 Nonadjacent ground-pole schedules are a full-carrier dead end

The Xi quotient in `(20)` has the blown limit

```text
T_Xi(z)=M_0(0)/mathcalL(-iz),
mathcalL(w)=w M_0(w^2).                                  (99)
```

For `z=iy`, with `y>0` sufficiently small,

```text
T_Xi(iy)
 =M_0(0)/(y M_0(y^2))
 =(1/y)(1+tau_0 y^2+O(y^4)),       tau_0>0.             (100)
```

The free limit `(98)` equals `1/y` on this ray, so `(98)` and `(99)` disagree for every
sufficiently small positive `y`.  Therefore:

> **No nonadjacent ground-pole boundary branch can identify the Xi reciprocal logarithmic
> derivative, even when it matches the Xi first defect exactly for every small anchor.**

This is a no-go only for the boundary branch.  A nonadjacent aperture can still have an interior
tangent branch, which is governed by `(96)`.

The no-go has an exact positive spectral survivor.  Let `nu_c` be the oriented Clark probability
in `(56)`.  Reflection gives `widehat(Theta)_c(-z)=1/widehat(Theta)_c(z)`, so its Donoghue
function is odd and `nu_c` is even.  At `z=iy`, `(56)--(57)` give

```text
m_c(iy)
 =i(y/c) int_R (t^2+c^2)/(t^2+y^2) dnu_c(t),

R_c(iy)
 =1 / [y int_R (t^2+c^2)/(t^2+y^2) dnu_c(t)].           (101)
```

If `R_c(iy)->1/y`, the integral in `(101)` tends to `1`, and

```text
1-int_R (t^2+c^2)/(t^2+y^2) dnu_c(t)
 =(y^2-c^2)int_R 1/(t^2+y^2) dnu_c(t) ->0.              (102)
```

For every fixed `T>0`,

```text
nu_c([-T,T])
 <=(T^2+y^2)int_R 1/(t^2+y^2)dnu_c(t) ->0.              (103)
```

Thus nonadjacent boundary matching forces **complete Clark probability escape to infinity**.  The
free kernel is not a mysterious cancellation; it records loss of every finite spectral response.
The Xi target instead requires

```text
int_R (t^2+c^2)/(t^2+y^2)dnu_c(t)
 -> M_0(y^2)/M_0(0)<1                                   (104)
```

for all sufficiently small `y>0`.  Equations `(103)--(104)` are incompatible.

### 14.3 Half-plane uniqueness bypasses the real Clark divisor

The preceding Clark laws do not make real-axis tightness necessary.  They expose a smaller
source-identification theorem.

### Theorem I — one imaginary interval closes the analytic Route-G endpoint

Let `a_n->infinity`, `c_n->0`, and let `lambda_n` be a source-predeclared sequence of exact
first-defect matches.  Orient the corresponding quotients as above.  Suppose there is a set
`Y subset (0,infinity)` with an accumulation point in `(0,infinity)`, contained in a sufficiently
small interval on which `M_0(y^2)>0`, such that

```text
R_n(iy) -> M_0(0)/(y M_0(y^2))       for every y in Y.  (105)
```

Then `R_n` converges locally uniformly on the upper half plane to `T_Xi`, and the Riemann
Hypothesis holds.

#### Proof

The matched jet and Theorem C make `{R_n}` locally bounded on the upper half plane, uniformly in
the changing apertures.  Vitali's theorem upgrades pointwise convergence on the uniqueness set
`iY` to locally uniform convergence to a holomorphic function `R`.  The identity theorem for
meromorphic functions gives

```text
R(z)=M_0(0)/mathcalL(-iz)                              (106)
```

throughout the upper half plane; any apparent target pole is removable because `R` is holomorphic.
Since every `R_n` has positive real part, `Re R>=0`.  Equation `(105)` makes `R` positive at an
interior point, so `Re R>0` everywhere by the minimum principle.

If `XiC(w)` had a zero with `Re w>0`, then `XiC(w)/XiC'(w)` would extend holomorphically with a
zero there, irrespective of its multiplicity.  Under `w=-iz`, equation `(106)` would make `R`
vanish in the upper half plane, contradicting `Re R>0`.  Hence `XiC` has no right-half-plane zero.
The functional equation reflects every left-half-plane zero to the right, so every zero is on the
critical line.

No real-axis passage occurs in this proof.  Once `(105)` is source-proved, separate Clark-count
tightness, explicit divisor noncancellation, and higher-jet Hermite--Biehler reality are redundant.
They remain possible sufficient routes to `(105)`, not independent obligations.

Combining `(101)` with `(105)` gives the exact source-side statement:

```text
int_R (t^2+c_n^2)/(t^2+y^2)dnu_n(t)
 -> M_0(y^2)/M_0(0)                   for y in Y.        (107)
```

Thus Route G's analytic endpoint is a bounded Stieltjes-transform convergence problem on one
interval, not a global real-divisor counting problem.

### 14.4 Interior source Ward equation

The interior ratio `(96)` admits a pre-divisor differential form.  For fixed `a,lambda`, abbreviate
`R=(A_a-lambda)^(-1)` and define the bounded resolvent-position commutator transform

```text
C_(a,lambda)(z)
 =int [(R X-X R)1](x)e^(izx) dx.                        (108)
```

Differentiating `G_(a,lambda)` under its compact Fourier integral gives the exact identity

```text
C_(a,lambda)(z)=H_(a,lambda)(z)+i G_(a,lambda)'(z),

P_(a,lambda)(z)
 =i d/dz log(z G_(a,lambda)(z))
   -C_(a,lambda)(z)/G_(a,lambda)(z).                    (109)
```

The first line is simply `RX-XR=[R,X]`.  On the operator/form domain, the existing inverse
commutator law identifies it further as the dressed literal source torque

```text
[R,X]=R[X,A_a]R.                                        (110)
```

No Xi quantity occurs in `(108)--(110)`.  Put

```text
g_(a,lambda)(y)=G_(a,lambda)(iy),
c_(a,lambda)(y)=C_(a,lambda)(iy),
T(y)=M_0(0)/(yM_0(y^2)).                                (111)
```

Then interior identification on an imaginary interval is exactly the first-order source Ward
equation

```text
g_(a,lambda)'(y)+(1/y-T(y))g_(a,lambda)(y)
 =c_(a,lambda)(y).                                      (112)
```

For a cofinal family, Route G needs convergence of the residual in `(112)` to zero locally on one
interval, with the source-selected shifts and the nonvanishing forced by Theorem H.  This is
strictly stronger than the scalar equation `q_a(lambda)=tau_src`: the latter is only the coefficient
of `y` at the singular endpoint.

### 14.5 Sharpness: first defect plus Pick positivity does not determine the carrier

The new Pick/divisibility law must not be mistaken for Xi identification.  Let `nu` be any even
probability measure with finite support away from zero and put

```text
J_nu(z)=int_R t^2/(t^2-z^2)dnu(t),
P_nu(z)=i/(z J_nu(z)).                                  (113)
```

For `z` in the upper half plane,

```text
zJ_nu(z)=int_R tz/(t-z)dnu(t)
```

has strictly positive imaginary part.  Hence `P_nu` has strictly positive real part.  If
`m_j=int t^(-2j)dnu(t)`, then

```text
P_nu(z)=i/z-i m_1 z+i(m_1^2-m_2)z^3+O(z^5).            (114)
```

Fix `tau>0`.  The symmetric two-atom probability at `+-tau^(-1/2)` has `m_1=tau` and
`m_2=tau^2`.  The symmetric four-atom probability with half its total mass on
`+-sqrt(2/tau)` and half on `+-sqrt(2/(3tau))` also has `m_1=tau`, but has
`m_2=5tau^2/4`.  Their strict Caratheodory functions therefore have the same singular term and
the same first regular coefficient, but different cubic coefficients.

This is a sharp finite atomic counterfamily.  Exact first-defect matching and all open-half-plane
Pick positivity still leave infinitely many complete carriers.  The interval transform law
`(107)` or Ward law `(112)` is genuinely new source information; it cannot be replaced by any
argument that merely rechecks the first jet.

### 14.6 The interval law is a complete weighted spectral convergence theorem

The transform in `(107)` determines much more than one half-plane function.  Let `nu_n` be the
even movable-anchor Clark probability for the `n`-th source system, and let `mu_n` be its squared
pushforward to the one-point compactification `[0,infinity]`:

```text
mu_n=(t |-> t^2)_* nu_n,
k_(s,c)(u)=(u+c^2)/(u+s),       k_(s,c)(infinity)=1.    (115)
```

For `s>0`, `k_(s,c)` is continuous on this compactification and

```text
sup_(u in [0,infinity]) |k_(s,c)(u)-u/(u+s)| <= c^2/s. (116)
```

Assume the interval law `(107)` on a uniqueness set and retain the actual finite-source
hypotheses of Theorem I.  Theorem I first gives RH.  Hence every centered squared Xi coordinate
`omega_q` is positive real.  Define the canonical probability

```text
mu_Xi
 =1/M_0(0) sum_q omega_q^(-1) delta_(omega_q).          (117)
```

The sum of its masses is one, and for every `s>0`,

```text
int_[0,infinity] u/(u+s) dmu_Xi(u)
 =1/M_0(0) sum_q 1/(omega_q+s)
 =M_0(s)/M_0(0).                                        (118)
```

### Theorem J — Clark--screw spectral rigidity

For an exactly matched cofinal Suzuki source sequence, the following are equivalent:

1. the imaginary-interval transform law `(107)` holds on any set with an interior accumulation
   point;
2. RH holds and

   ```text
   mu_n  -->  mu_Xi                                     (119)
   ```

   weakly on `[0,infinity]`.

Thus `(107)` forces the complete squared Clark probability, not merely its Stieltjes values.
In particular,

```text
lim_(delta downarrow 0) limsup_n mu_n([0,delta])=0,
lim_(T to infinity)     limsup_n mu_n([T,infinity])=0.  (120)
```

If `u_0` is an isolated squared Xi ordinate and `delta` isolates it from the other squared
ordinates, then

```text
mu_n((u_0-delta,u_0+delta))
 -> 1/M_0(0) sum_(q:omega_q=u_0) omega_q^(-1).           (121)
```

#### Proof

The implication `2=>1` follows from weak convergence, continuity of `u/(u+s)`, and the uniform
estimate `(116)`.  For the converse, probability measures on `[0,infinity]` form a compact space.
Take a weakly convergent subsequence `mu_(n_j)->mu`.  Equations `(107)` and `(116)` give

```text
int u/(u+s) dmu(u)=M_0(s)/M_0(0)                        (122)
```

on the squared uniqueness set.  Both sides are holomorphic for `Re s>0` after RH, so the identity
holds for every positive `s`.

The functions

```text
r_s(u)=s/(u+s),        r_s(infinity)=0,                 (123)
```

together with the constants separate the points of `[0,infinity]`.  For distinct `s,t`, the
product `r_s r_t` is a linear combination of `r_s,r_t`; moreover `r_s^2` is the uniform limit as
`t->s` of those products.  Hence the uniform closure of their linear span is a unital separating
subalgebra.  Stone--Weierstrass makes that closure all real continuous functions.  Since
`u/(u+s)=1-r_s(u)`, equations `(118)` and `(122)` imply
`mu=mu_Xi`.  Every convergent subsequence has the same limit, so the whole sequence converges,
proving `(119)`.  Portmanteau and the fact that `mu_Xi` has no mass at `0` or `infinity` give
`(120)`.  Applying weak convergence to an isolating interval whose boundary has zero `mu_Xi`
mass gives `(121)`.

This also recovers the exact source coherence weights: by Theorem G, the left side of `(121)` is
the sum of squared angles between the movable deficiency anchor and all extension modes in the
window.  Suzuki's predicted convergence of extension eigenvalue sets does not control these
sums.  Even a fixed two-point support carries a continuum of probability weights and hence a
continuum of distinct transforms.  The missing theorem is weighted, or **pointed**, spectral
convergence.

There is a source-native dynamical form.  Under RH the even lift of `mu_Xi` to the signed
ordinate line is the normalized inverse-square spectral probability of Suzuki's global screw
function.  If `g_zeta` denotes that screw function and `nu_Xi` the even lift, then, in the
signed-copy convention,

```text
int cos(tx) dnu_Xi(x)
 =1-g_zeta(t)/M_0(0).                                   (124)
```

Consequently `(119)` is equivalent to convergence of the cyclic extension correlations

```text
<g_n, exp(it L_n) g_n>
 -> 1-g_zeta(t)/M_0(0)          for every real t,        (125)
```

where `L_n` is the selected self-adjoint extension and `g_n` is its normalized movable
deficiency vector.  Equation `(125)` is precisely the pointed finite-to-global screw theorem
absent from the published Suzuki heuristic.  It is declared entirely by the restricted-Weil
source, its extension, and its anchor; no target zero may be fitted into the finite systems.

### 14.7 Exact mixed-anchor parity response

The Clark measure is useful for classifying the limit, but it is not necessary for proving it
from the literal operator.  Fix `a,lambda`, write `R=(A_a-lambda)^(-1)`, and put

```text
E_c(y)=<cosh(yX),R cosh(cX)>,
O_c(y)=<sinh(yX),R sinh(cX)>.                            (126)
```

Reflection invariance removes the cross-parity terms and gives the exact finite identities

```text
F_c(iy)=E_c(y)-O_c(y),
F_c(-iy)=E_c(y)+O_c(y).                                 (127)
```

Let `sigma=+1` or `-1` be the orientation in `widehat(Theta)_c=sigma Theta_c`.  Direct insertion
of `b_c(iy)=(y-c)/(y+c)` into `(90)` gives, wherever the displayed denominators are nonzero,

```text
sigma=+1:
 R_c(iy)=(c E_c(y)+y O_c(y))/(c(y E_c(y)+c O_c(y))),

sigma=-1:
 R_c(iy)=(y E_c(y)+c O_c(y))/(c(c E_c(y)+y O_c(y))).    (128)
```

This is an exact two-anchor formula, not an asymptotic expansion.  Relative to the free kernel it
has the sharp rank-one parity gaps

```text
sigma=+1:
 R_c(iy)-1/y
  =(y^2-c^2)O_c(y)/[c y(yE_c(y)+cO_c(y))],

sigma=-1:
 R_c(iy)-1/y
  =(y^2-c^2)E_c(y)/[c y(cE_c(y)+yO_c(y))].              (129)
```

For the Xi target `T(y)=M_0(0)/(yM_0(y^2))`, define

```text
Delta_c^+(y)
 =E_c(y)+y O_c(y)/c-T(y)(yE_c(y)+cO_c(y)),

Delta_c^-(y)
 =y E_c(y)/c+O_c(y)-T(y)(cE_c(y)+yO_c(y)).              (130)
```

Then `(128)` gives exactly

```text
R_c(iy)-T(y)=Delta_c^+(y)/(yE_c(y)+cO_c(y))   (sigma=+1),
R_c(iy)-T(y)=Delta_c^-(y)/(cE_c(y)+yO_c(y))   (sigma=-1). (131)
```

Thus Route G's live theorem can be attacked directly as convergence of one normalized mixed
parity residual, with no real-axis eigenvalue enumeration.  On an interior even-oriented branch,

```text
E_c(y)->g(y)=<cosh(yX),R1>,
O_c(y)/c->o(y)=<sinh(yX),RX>,                            (132)
```

and `(131)` reduces to

```text
g(y)+y o(y)-yT(y)g(y)=0,                                (133)
```

which is the imaginary-axis form of the Ward equation `(112)`.  The new formula identifies the
finite-`c` error that `(112)` had suppressed.  The hard source estimate is now one of the
equivalent statements `(119)`, `(125)`, or normalized residual decay in `(131)`.

### 14.8 The inverse-square target has a source-declared Green origin

Theorem J identifies the needed weights but does not by itself prove that they are source-native.
Suzuki's global screw line removes that concern.  Let `mathfrak S_t` be the unconditional
`L^2(R)`-valued prime--Gamma screw line from his source formula.  Under RH his spectral expansion,
in the orthonormal screw coordinates `e_gamma=F_gamma^sharp`, is

```text
x(t):=pi^(-1/2) mathfrak S_t
    =sum_(gamma in Gamma) sqrt(m_gamma)
       (exp(-i gamma t)-1)/gamma e_gamma.               (134)
```

For `T>0`, make the declaration before using any zero:

```text
Omega_T=-1/T int_0^T x(t)dt.                            (135)
```

This is an unconditional Bochner integral of Suzuki's explicit source line.  Under RH define only
for the proof

```text
Omega=sum_(gamma in Gamma) sqrt(m_gamma)/gamma e_gamma. (136)
```

The reciprocal-square summability of the Xi ordinates makes `Omega` a Hilbert vector.  Integrating
`(134)` coefficientwise gives

```text
Omega_T-Omega
 =-sum_gamma sqrt(m_gamma)
   (1-exp(-i gamma T))/(i T gamma^2)e_gamma,

||Omega_T-Omega||^2
 <=4/T^2 sum_gamma m_gamma/gamma^4.                     (137)
```

### Theorem K — source-Cesaro screw-origin theorem

Under RH, `Omega_T` converges in `L^2(R)` to `Omega` at the explicit rate `(137)`.  If `U_t` is
the diagonal screw evolution, then

```text
x(t)=(U_t-I)Omega.                                      (138)
```

Moreover `Omega` is the unique vector with `(138)`: the difference of two such origins is fixed by
every `U_t`, while the Xi spectrum has no zero ordinate.  Its norm and normalized spectral
probability are

```text
||Omega||^2=M_0(0)=sum_gamma m_gamma/gamma^2,

nu_Omega
 =1/M_0(0) sum_gamma m_gamma/gamma^2 delta_gamma.       (139)
```

Therefore

```text
<Omega,U_t Omega>/||Omega||^2
 =1-g_zeta(t)/M_0(0),                                  (140)
```

in the signed-copy convention.  The right side is exactly the target correlation in `(125)`.
Thus the inverse-square Clark target is not a divisor-fitted probability: it is the unique
zero-energy coboundary origin recovered by Cesaro averaging the unconditional prime--Gamma screw
line.  Divisors enter only in the RH-conditional proof of what that source-declared limit equals.

The source paper already proves `(134)` and the screw-line norm identities.  The new point here is
the finite source declaration `(135)`, the quantitative Green-origin limit `(137)`, uniqueness,
and its identification with the movable Clark target from Theorem J.

### 14.9 Coalescing finite anchors escape the published global embedding

The most natural next conjecture is that Suzuki's finite deficiency anchors themselves converge
to `Omega` inside his RH-conditional global Weil space.  That conjecture is false.

Assume RH and use Suzuki's `lambda=0` spaces.  Let `a_n->infinity`, `c_n downarrow 0`, and let
`j_n : H(A_(a_n))->H(A_infinity)` be the canonical isometric embedding.  Define

```text
A_(a_n) v_n=e^(c_n X),
N_n=||v_n||_(A_(a_n))^2,
g_n=j_n(v_n/sqrt(N_n)).                                 (141)
```

For every `u in C_c^infinity(R)` and all sufficiently large `n`, the literal Riesz identity is

```text
<[u],g_n>_(A_infinity)
 =1/sqrt(N_n) int_R conjugate(u(x))e^(c_n x)dx.         (142)
```

### Theorem L — global weak-escape theorem

Every sequence `(141)` satisfies

```text
N_n->infinity,                 g_n -> 0 weakly
                                in H(A_infinity).        (143)
```

#### Proof

If `N_n` failed to tend to infinity, take a subsequence on which it is bounded above.  Choose a
compact smooth `u` with nonzero integral.  Cauchy--Schwarz in `(142)` bounds `N_n` away from zero
on this subsequence.  After a further subsequence, `N_n->N_* in (0,infinity)` and the unit vectors
`g_n` have a weak limit `g`.  Since `c_n->0`, equation `(142)` gives

```text
<[u],g>=N_*^(-1/2) int_R conjugate(u(x))dx              (144)
```

for every compact smooth `u`.  This is nonzero and translation-invariant.  Compact smooth classes
are dense, so `g` is fixed by the global translation group.  But in Suzuki's spectral model that
group is diagonal on the nonzero Xi ordinates; it has no nonzero fixed vector.  This contradiction
proves `N_n->infinity`.  Equation `(142)` then tends to zero on a dense set, and boundedness of
`g_n` gives weak convergence to zero.

The escape is not repaired by a small spectral shift.  Let `lambda_n->0`, put

```text
T_n=A_(a_n)-lambda_n>0,
T_n v_n=e^(c_n X),
N_n=||v_n||_(T_n)^2,
h_n=j_n(v_n/sqrt(N_n)).                                 (145)
```

Whenever `(h_n)` is bounded in the global Weil norm, the exact comparison identities are

```text
||h_n||_(A_infinity)^2
 =1+lambda_n||v_n/sqrt(N_n)||_2^2,

<[u],h_n>_(A_infinity)
 =1/sqrt(N_n) int conjugate(u)e^(c_n X)
  +lambda_n<u,v_n/sqrt(N_n)>_2.                         (146)
```

The last term tends to zero.  For `lambda_n>=0`, this follows from

```text
|lambda_n<u,v_n/sqrt(N_n)>_2|
 <=sqrt(lambda_n)||u||_2
   sqrt(lambda_n||v_n/sqrt(N_n)||_2^2),
```

and boundedness of the first identity; for `lambda_n<0`, positivity and unit `T_n`-norm give
`|lambda_n| ||v_n/sqrt(N_n)||_2^2<=1`.  Repeating the invariant-vector argument proves

```text
h_n -> 0 weakly in H(A_infinity).                       (147)
```

Hence no vanishing-shift finite anchor can converge strongly to the nonzero Green origin
`Omega`.  For positive shifts, every attempted escape from `(147)` requires the explicit metric
amplification

```text
lambda_n||v_n||_2^2/N_n
 =||h_n||_(A_infinity)^2-1                              (148)
```

to be unbounded.  This is the precise singular shifted-metric alternative; a regular
`lambda_n->0` comparison is dead.

This has a sharp projection consequence.  Let `P_n(J)` be the orthogonal projection onto the
selected finite extension modes in a bounded interval `J`, extended by zero off the embedded
finite space, and let `P_infinity(J)` be the global Xi spectral projection.  If

```text
||P_n(J)-P_infinity(J)||->0,                            (149)
```

then finite rank of `P_infinity(J)` and `(143)` imply

```text
nu_n(J)=||P_n(J)g_n||^2->0.                             (150)
```

For an interval isolating a Xi ordinate, `(150)` contradicts the positive mass forced by
`(121)`.  In particular, strong convergence of local spectral projections together with eventual
equality of their finite ranks is also impossible, because equal-rank strong convergence to a
finite-rank projection upgrades to operator-norm convergence.

The conclusion is not that the scalar Route G is dead.  It is that the clean pointed version of
Suzuki's published `lambda=0` operator heuristic is dead.  A successful source sequence must
exhibit at least one singular feature: local projection rotation or excess local modes preventing
`(149)`, or shifted-metric amplification `(148)` outside bounded global Weil geometry.  This is
exactly the singular/label-sensitive survivor left by the updated modular-superselection and
source-horizon classifications.  Unpointed eigenvalue-set convergence cannot decide between
these alternatives.

### 14.10 Exact Xi-node Galerkin locking and the resolution wall

Weak anchor escape does not mean every finite real defect vector escapes.  At a genuine Xi
ordinate the opposite happens, and the contrast gives a quantitative obstruction.

Continue under RH with `lambda=0`.  Let `H_a` be the embedded finite Weil space,
`P_a : H(A_infinity)->H_a` its orthogonal projection, and let `gamma in Gamma` have multiplicity
`m_gamma`.  The global functional

```text
ell_gamma([u])=widehat u(gamma)                          (151)
```

is continuous.  Indeed Suzuki's global spectral isometry gives

```text
||ell_gamma||^2=1/m_gamma.                              (152)
```

Let `K_gamma` be its global Riesz vector.  For real `x`, let

```text
K_(a,x)=A_a^(-1)e^(-ixX) in H_a.                       (153)
```

This is the real adjoint defect vector used by the finite self-adjoint extensions.  At the exact
node, the Riesz identities on `H_a` give

```text
K_(a,gamma)=P_a K_gamma.                                (154)
```

The spaces increase with dense union, so `P_a K_gamma->K_gamma` strongly.  Put
`epsilon_a(gamma)=||(I-P_a)K_gamma||` and let `alpha_a>0` be the lowest eigenvalue of `A_a`.
Since `|exp(-ixX)-exp(-i gamma X)|<=|x-gamma||X|`, the finite resolvent gives the exact estimate

```text
||K_(a,x)-K_gamma||_(A_infinity)
 <=epsilon_a(gamma)
   +|x-gamma| sqrt(2a^3/(3alpha_a)).                    (155)
```

### Theorem M — critical-node locking and Clark resolution wall

If `a_n->infinity`, `x_n->gamma`, and

```text
|x_n-gamma| sqrt(a_n^3/alpha_(a_n))->0,                (156)
```

then the normalized finite real defect vectors at `x_n` converge strongly to the normalized
global Xi eigenvector `K_gamma/||K_gamma||`.  For the coalescing normalized anchors `g_n` of
Theorem L, their individual Clark coherences therefore satisfy

```text
|<g_n,K_(a_n,x_n)/||K_(a_n,x_n)||>|^2->0.              (157)
```

#### Proof

Equation `(154)` is uniqueness of the Riesz representative on the closed subspace `H_a`.
Increasing density gives `epsilon_a(gamma)->0`.  For
`f=e^(-ixX)-e^(-i gamma X)`, positivity of `A_a>=alpha_a I` gives

```text
||A_a^(-1)f||_(A_a)^2
 =<f,A_a^(-1)f>_2
 <=alpha_a^(-1)||f||_2^2
 <=2a^3|x-gamma|^2/(3alpha_a),
```

which proves `(155)` and the strong normalized limit under `(156)`.  Equation `(157)` follows
from that strong convergence and `g_n->0` weakly.

Let `J` isolate `gamma`.  If the number of selected extension eigenvalues in `J` stays bounded
and every eigenvalue carrying nonvanishing Clark mass obeys `(156)`, summing `(157)` forces
`nu_n(J)->0`, contradicting `(121)`.  Hence the positive inverse-square target mass forces at
least one of the following:

```text
unbounded local rank/crowding;
failure of the resolution scale (156) for a mass-carrying mode;
failure of the regular global metric through (148).    (158)
```

This does not prove that crowding is necessary: a bounded number of sufficiently ill-conditioned,
slowly locking modes can survive.  It does prove that fast accurate eigenvalue approximation is
not helpful to the pointed problem; in the regular embedding it destroys the required weight.

### 14.11 Relative-gap rigidity of the shifted-metric survivor

The metric-amplification alternative in `(148)` is not an unspecified shift effect.  Spectral
calculus pins it to the ground pole.

Assume RH, let `alpha_a=inf spec(A_a)>0`, choose `0<lambda<alpha_a`, and put

```text
delta=alpha_a-lambda,
T=A_a-lambda,
v=T^(-1)e^(cX),
N=||v||_T^2.                                             (159)
```

Since `T>=delta I`,

```text
||v||_2^2=<e^(cX),T^(-2)e^(cX)>
          <=delta^(-1)<e^(cX),T^(-1)e^(cX)>
          =N/delta.
```

Therefore the exact comparison satisfies

```text
1<=||v/sqrt(N)||_(A_a)^2
   =1+lambda||v||_2^2/N
   <=1+lambda/delta=alpha_a/delta.                      (160)
```

### Theorem N — relative-floor metric wall

For any cofinal family with `c_a->0`, `lambda_a->0`, and positive admissible shifts, a bounded
relative ground gap

```text
sup_a lambda_a/(alpha_a-lambda_a)<infinity              (161)
```

makes the normalized anchors bounded in the global Weil norm.  The shifted escape theorem
`(145)--(147)` then makes them converge weakly to zero.  Hence evasion through the metric requires

```text
lambda_a>0 cofinally,
(alpha_a-lambda_a)/lambda_a -> 0                        (162)
```

along a subsequence: the selected shift must hug the positive spectral floor at vanishing relative
distance.  Nonpositive shifts and positive interior shifts with `(161)` cannot provide a regular
global pointed limit.

There is a terminal logical consequence.  If a source argument proves merely that

```text
0<lambda_(a_n)<inf spec(A_(a_n))
```

on any cofinal aperture sequence `a_n->infinity`, then RH already follows.  Every compact smooth
test is supported in one sufficiently large aperture, where

```text
Q_W(u)=<A_(a_n)u,u>_2>=alpha_(a_n)||u||_2^2>0.
```

Weil's criterion completes the implication.  Thus the positive floor-hugging alternative is not
missing post-limit infrastructure: source admission into it is itself a terminal RH proof.  The
only nonterminal scalar survivor which does not first prove positivity is singular rotation or
crowding of the Clark modes in the varying `T_a` geometries.

### 14.12 Defect-base transport reduces the movable target to one hard edge

The preceding weak-escape theorem concerns the vectors after embedding into Suzuki's changing
global Weil geometry.  It must not be read as saying that Clark probabilities at different defect
bases are independent.  They are tied by an exact Radon--Nikodym law before any aperture limit.

Let `S` be one closed simple symmetric operator with deficiency indices `(1,1)`, let `L` be one
self-adjoint extension, and choose nonzero defect vectors

```text
h_z in ker(S^*-z),             z in C\R.
```

Write `E_L` for the spectral resolution of `L` and

```text
nu_z(B)=||E_L(B)h_z||^2/||h_z||^2.                     (163)
```

The choice of scalar normalization of `h_z` is immaterial.  For nonreal `z,w`, the standard
gamma-field identity follows directly from the resolvent equation:

```text
h_z is proportional to
 [I+(z-w)(L-z)^(-1)]h_w.                               (164)
```

Indeed the vector on the right belongs to `ker(S^*-z)`, and that space is one-dimensional.  In
the spectral representation of `L`, the bracket in `(164)` is multiplication by

```text
1+(z-w)/(t-z)=(t-w)/(t-z).                             (165)
```

Consequently the normalized spectral probabilities satisfy the exact base-change law

```text
dnu_z(t)
 = [ |t-w|^2/|t-z|^2 ] dnu_w(t)
   / int_R [ |s-w|^2/|s-z|^2 ] dnu_w(s).               (166)
```

This is classical gamma-field algebra.  Its consequence for Suzuki's coalescing source limit is
the new source-specific reduction.  Take `w=i`, `z=ic`, keep the same parity extension, and pass to
the squared spectral coordinate `u=t^2`.  If `mu_1` and `mu_c` are the corresponding squared Clark
probabilities, then

```text
r_c(u)=(u+1)/(u+c^2),
s_c(u)=1/r_c(u)=(u+c^2)/(u+1),

dmu_c=r_c dmu_1/Z_c,       Z_c=int r_c dmu_1,
dmu_1=s_c dmu_c/Y_c,       Y_c=int s_c dmu_c=1/Z_c.    (167)
```

Both formulas extend to `[0,infinity]`, with `r_c(infinity)=s_c(infinity)=1`.  Although `r_c`
becomes singular at zero, the reciprocal multiplier has the uniform limit

```text
sup_[0,infinity] |s_c(u)-u/(u+1)| <= c^2.              (168)
```

Under RH define, in addition to the movable target `(117)`, the fixed-anchor probability

```text
mu_Xi^(1)
 =1/M_0(1) sum_q 1/(omega_q+1) delta_(omega_q).        (169)
```

Equation `(118)` at `s=1` gives

```text
A_Xi:=int u/(u+1) dmu_Xi(u)=M_0(1)/M_0(0)>0,
B_Xi:=1/A_Xi=M_0(0)/M_0(1),

mu_Xi^(1)=[u/(u+1)]mu_Xi/A_Xi,
mu_Xi=[(u+1)/u]mu_Xi^(1)/B_Xi.                         (170)
```

The apparent target fitting in `(169)` is only proof notation.  Suzuki's global model-space
basis has

```text
F_gamma(z)
 =sqrt(m_gamma/pi) i(1+Theta(z))/(2(z-gamma)).          (171)
```

The factor independent of `gamma` cancels after normalization.  Thus the global reproducing
kernel at `i` has squared spectral probability `(169)`, while its real boundary kernel at `0` has
probability `(117)`.  The vector `Omega` in Theorem K is, up to the fixed model-space scalar, this
zero-anchor kernel.  Hence the source-Cesaro origin and the defect-base limit are the same global
object, not merely two vectors with coincident weights.

#### Theorem O — fixed-anchor/hard-edge equivalence

Let `c_n->0`, and for each finite Suzuki system compare the movable and fixed defect bases for the
same selected self-adjoint parity extension.  Then

```text
mu_(c_n,n) -> mu_Xi                                     (172)
```

weakly on `[0,infinity]` if and only if both

```text
mu_(1,n) -> mu_Xi^(1),                                  (173)

lim_(delta downarrow 0) limsup_(n->infinity)
 int_[0,delta] (u+1)/(u+c_n^2) dmu_(1,n)(u)=0.          (174)
```

When these conditions hold,

```text
Z_(c_n,n)->B_Xi.                                        (175)
```

Condition `(174)` is the complete movable-anchor debt.  In source-operator form it is

```text
lim_(delta downarrow 0) limsup_n
 <g_(1,n), 1_[0,delta](L_n^2)
   (L_n^2+1)(L_n^2+c_n^2)^(-1) g_(1,n)> = 0            (176)
```

Here `g_(1,n)` is the
normalized fixed-anchor defect vector.  Thus the remaining singularity is exactly amplified
zero-energy spectral leakage.  It is not an unspecified exterior port, an independent movable
Clark law, or generic crowding near every Xi ordinate.

#### Proof

Assume `(172)`.  By `(168)`, weak convergence and `(167)` give

```text
Y_(c_n,n)->A_Xi,
mu_(1,n)->[u/(u+1)]mu_Xi/A_Xi=mu_Xi^(1),
Z_(c_n,n)->B_Xi.                                       (177)
```

Moreover the left side of `(174)` equals
`Z_(c_n,n) mu_(c_n,n)([0,delta])`.  Portmanteau, followed by `delta downarrow 0`, makes this vanish
because `mu_Xi({0})=0`.

Conversely assume `(173)--(174)`.  On every interval `[delta,infinity]`, `r_(c_n)` converges
uniformly to `(u+1)/u`.  Weak convergence handles that truncated bounded multiplier, while `(174)`
removes the discarded neighborhood of zero.  Letting `delta downarrow 0` gives both `(175)` and,
for every continuous test `f`,

```text
int f dmu_(c_n,n)
 -> B_Xi^(-1) int f(u)(u+1)/u dmu_Xi^(1)(u)
 =int f dmu_Xi.
```

This is `(172)`.  Equation `(176)` is the spectral theorem applied to `(174)`.

The hard edge is sharp.  Let `rho=mu_Xi^(1)`, choose `u_n->0`, `epsilon_n->0`, and put

```text
q_n=(1-epsilon_n)rho+epsilon_n delta_(u_n),
ell_n=epsilon_n(u_n+1)/(u_n+c_n^2).                    (178)
```

Always `q_n->rho`.  If `ell_n->ell` in `[0,infinity]`, its movable reweighting converges to

```text
[B_Xi mu_Xi+ell delta_0]/(B_Xi+ell),                   (179)
```

with the evident value `delta_0` for `ell=infinity`.  Hence fixed-anchor convergence alone does
not control the movable limit.  But choosing `ell_n->0` realizes the target, so abstract hard-edge
amplification is not a no-go either.  Only the literal restricted-Weil source can decide `(174)`.

This corrects the last sentence of Section 14.11.  Projection rotation and local rank growth may
still be needed to prove the fixed-anchor law `(173)` in Suzuki's changing global embedding, but
they are not separate movable-anchor mechanisms at each Xi node.  Once `(173)` holds, every extra
coalescing obstruction is concentrated at the single real boundary point `u=0` and is measured
exactly by `(174)`.

The hard edge is not an independent source theorem if the defect base itself may be selected from
the finite source, as it may in the movable-anchor construction.  Define the finite impedance

```text
Z_n(c)=int_[0,infinity] (u+1)/(u+c^2) dmu_(1,n)(u),
D_n=Z_n(0).                                             (180)
```

For Suzuki's canonical even extension, zero is not an eigenvalue.  Its spectrum is discrete, so
`D_n<infinity`.  The map `c |-> Z_n(c)` is continuous and strictly decreasing on `[0,1]`, with
`Z_n(0)=D_n` and `Z_n(1)=1`.  The constant

```text
B_Xi=M_0(0)/M_0(1)>1                                   (181)
```

is prime--Gamma/theta declared; no zero location is needed to evaluate it.

#### Theorem P — source-impedance defect-base calibration

Choose `c_n` using only `mu_(1,n)` and `(181)` as follows.

1. If `D_n>B_Xi`, take the unique `c_n in (0,1)` satisfying

   ```text
   Z_n(c_n)=B_Xi.                                       (182)
   ```

2. If `D_n<=B_Xi`, choose `0<c_n<=1/n` so that

   ```text
   D_n-1/n <= Z_n(c_n) <= D_n.                          (183)
   ```

If the fixed-anchor law `(173)` holds, then

```text
c_n->0,
Z_n(c_n)->B_Xi,
mu_(c_n,n)->mu_Xi.                                     (184)
```

Thus fixed-anchor pointed convergence admits a canonical source-measurable coalescing selector
which automatically pays the entire hard-edge debt.  No extra real-axis eigenvalue labels,
Xi-node neighborhoods, or divisor-fitted shifts enter this calibration.

#### Proof

Existence in the first case is the intermediate value theorem and strict monotonicity.  Existence
in the second follows from `Z_n(c)->D_n` as `c downarrow 0`.

Under `(173)`, lower semicontinuity of the extended function `(u+1)/u` and Portmanteau give

```text
liminf_n D_n>=int (u+1)/u dmu_Xi^(1)=B_Xi.             (185)
```

Therefore on the second branch `D_n->B_Xi`, and `(183)` gives `Z_n(c_n)->B_Xi`; on the first
branch this equality is exact.

It remains to prove coalescence.  The second branch already has `c_n<=1/n`.  If a subsequence of
the first branch had `c_n>=epsilon>0`, extract a further subsequence with `c_n->c_*>=epsilon`.
The multipliers `r_(c_n)` then converge uniformly to the bounded continuous `r_(c_*)`, so `(173)`
and `(182)` would give

```text
B_Xi=int r_(c_*) dmu_Xi^(1)
    <int r_0 dmu_Xi^(1)=B_Xi,
```

a contradiction.  Hence `c_n->0`.  Fixed-anchor convergence plus `Z_n(c_n)->B_Xi` is equivalent
to the hard-edge uniform integrability in Theorem O: away from zero the weighted integrals already
converge to `B_Xi`, so no positive mass can remain in the discarded edge.  Theorem O now proves
the last statement of `(184)`.

Theorem P removes coalescing and zero-energy leakage as independent Route-G conjectures.  The
remaining nonterminal theorem is the original fixed-anchor pointed law `(173)` for a
source-selected adjacent or interior shifted family.  Operator convergence without convergence of
the normalized fixed defect vector still does not imply `(173)`; eigenvalue-set convergence is
even weaker.  But once `(173)` is proved, no further movable-anchor spectral theorem is missing.

### 14.13 Conjecture loop and novelty correction

18. **A nonadjacent exact boundary schedule advances the full carrier -- failed.**  Theorem H
    proves universal collapse to `i/z`; `(102)--(103)` identify complete Clark escape.
19. **Real-axis Clark tightness is logically necessary -- failed.**  Theorem I proves that one
    upper-half-plane uniqueness set suffices.  Real-axis estimates are optional providers of that
    identification, not separate endpoints.
20. **Adjacent or interior limits may retain uncancelled upper-half-plane Fourier poles -- failed
    under exact matching.**  Theorem H forces strict Caratheodory extension and numerator
    divisibility at every such zero.
21. **First-defect matching plus the forced Pick law should identify Xi -- failed sharply.**  The
    two- and four-atom family `(113)--(114)` has identical first defect and strict positivity but
    different full carriers.
22. **The remaining source theorem is an unspecified meromorphic convergence problem -- failed.**
    Equations `(107)` and `(112)` give two exact, bounded, interval-local forms: Clark Stieltjes
    convergence and the resolvent-position Ward residual.
23. **The interval law can bypass real spectral information even as an output -- failed.**
    Theorem J proves that it forces complete weak convergence to the canonical inverse-square
    Clark--screw probability and hence both endpoint tightness statements `(120)`.
24. **Suzuki's conjectural convergence of extension spectra is enough -- failed.**  The target
    fixes the local masses `(121)` as well as support.  A fixed support with varying cyclic-vector
    weights gives different transforms, so unpointed strong-resolvent or eigenvalue-set
    convergence misses exactly the needed datum.
25. **A proof of the live source theorem must first control real Clark points -- failed.**  The
    exact mixed-anchor formulas `(126)--(131)` reduce it directly to a normalized parity-resolvent
    residual on one imaginary interval.
26. **Sign of the surviving parity response should close the residual -- failed.**  Equation
    `(129)` fixes only which side of the free kernel is reached.  The atomic Pick counterfamily
    `(113)--(114)` already realizes the correct sign and first coefficient with different full
    transforms.  Magnitude and all weighted spectral data in `(119)` remain essential.
27. **The inverse-square target probability is merely divisor-fitted -- failed.**  Theorem K
    reconstructs its Green origin by Cesaro averaging Suzuki's unconditional prime--Gamma screw
    line and proves the quantitative source-to-spectral identification `(137)--(140)`.
28. **The finite coalescing deficiency anchors should converge strongly to that Green origin in
    Suzuki's global `lambda=0` embedding -- failed.**  Theorem L proves their norms before
    normalization diverge and the normalized anchors converge weakly to zero.
29. **Clean strong-resolvent convergence with one stable local mode per Xi ordinate can still
    transport the Clark weights -- failed.**  Norm convergence of the corresponding finite-rank
    local projections forces every local anchor mass to vanish by `(150)`, contradicting `(121)`.
30. **Weak anchor escape kills every Suzuki scalar limit -- failed.**  It kills only a regular
    pointed operator limit.  Projection rotation, local rank excess/crowding, or a genuinely
    shifted metric can retain the scalar spectral probability.  These singular alternatives are
    now the exhaustive live frontier.
31. **A finite real defect vector at an exact Xi ordinate may also escape -- failed.**  It is
    exactly the Galerkin projection `(154)` of the global Xi evaluation vector and converges
    strongly.
32. **Faster one-for-one eigenvalue convergence should improve the pointed limit -- failed.**
    The resolution estimate `(155)` and weak anchor escape force the corresponding Clark weight
    to zero whenever `(156)` holds.
33. **The target therefore forces local spectral crowding -- failed as a class-complete claim.**
    The sharp survivor `(158)` also permits a bounded number of mass-carrying modes whose locking
    is slower than `sqrt(alpha_a/a^3)`, or singular shifted-metric amplification.
34. **Any vanishing positive shift can create the needed metric singularity -- failed.**  The
    comparison bound `(160)` shows that every bounded relative distance below the floor remains
    globally bounded and weakly escapes.
35. **The metric survivor is a broad new analytic regime -- failed.**  It requires the positive
    floor-hugging law `(162)`.  Proving cofinal admissibility of even one positive shift already
    proves RH directly by Weil positivity.
36. **This eliminates the whole scalar Route G -- failed.**  Clark probabilities live in the
    varying `T_a` metrics and can still converge through sub-resolution projection rotation or
    local rank growth without a nonzero vector limit in the global Weil metric.
37. **The one-sided exterior ports provide an independent movable-anchor datum -- failed.**  The
    two Carleman sheets and their triangle split are corpus-known.  For one fixed extension, the
    entire movable Clark probability is already the base reweighting `(167)` of Suzuki's original
    fixed-anchor probability.
38. **Singular rotation or crowding must be solved independently near every Xi ordinate for the
    movable family -- failed.**  Theorem O reduces the movable target to the fixed-anchor pointed
    law `(173)` plus one zero-energy Lindeberg condition `(174)`.  Any Xi-node complexity belongs
    to the fixed-anchor convergence problem, not a second movable layer.
39. **Fixed-anchor pointed convergence alone closes Route G -- failed sharply.**  The family
    `(178)--(179)` has the correct fixed-anchor limit while an asymptotically invisible mass at zero
    produces any desired residual `delta_0` component after coalescing reweighting.
40. **The hard edge is automatically fatal -- failed as a class-complete claim.**  The same family
    with `ell_n->0` satisfies exact hard-edge tightness.  Whether Suzuki's literal source-selected
    branch does so is the remaining source theorem.
41. **The source-Cesaro origin only happens to share the target weights -- failed.**  Suzuki's
    global basis formula `(171)` identifies it with the real zero-anchor reproducing kernel; the
    fixed and zero-anchor target probabilities obey the same exact base-change law as the finite
    systems.
42. **The hard-edge law is an independent analytic estimate after fixed-anchor convergence --
    failed.**  The impedance selector `(180)--(183)` uses only the finite fixed-anchor probability
    and source constant `B_Xi`; Theorem P makes its hard-edge law automatic.
43. **The calibrated bases might fail to coalesce -- failed.**  Any positive limiting base would
    give `int r_c dmu_Xi^(1)<int r_0 dmu_Xi^(1)=B_Xi`, contradicting the calibrated impedance.
44. **Finite systems with `D_n<=B_Xi` obstruct calibration -- failed.**  Portmanteau forces their
    inverse moments to approach `B_Xi` from below, and the second branch of `(183)` recovers the
    required diagonal limit.
45. **This closes Route G -- failed.**  It closes the entire extra coalescing layer, not Suzuki's
    original source-to-limit problem.  The one remaining nonterminal theorem is fixed-anchor
    pointed convergence `(173)` for a source-selected shifted family; neither eigenvalue-set
    convergence nor generic strong-resolvent language supplies its cyclic vector weights.

Classical parent tools, not claimed new, are reduced-resolvent expansion, Fourier parity,
Schwarz--Pick, Montel--Vitali, the Herglotz representation, and the inverse commutator identity.
The corpus theorem `SuzukiGroundEdgeCayleyUniversality` is the closest internal parent: at a
**fixed** defect base it turns derivative saturation into the ordinary free Cayley map.  It does
not compute the moving-base `c^(-1)` boundary layer, distinguish adjacent from nonadjacent ground
degrees, or imply Clark escape `(103)`.
Candidate-new Suzuki-specific content is their exact conjunction in `(93)--(112)`: the
nonadjacent free-kernel collapse, Clark escape classification, adjacent/interior Pick divisibility,
reduction of full source identification to one imaginary-interval transform or Ward equation,
the Clark--screw weak-limit rigidity `(115)--(125)`, the finite mixed-anchor residual
`(126)--(133)`, the source-Cesaro Green origin `(134)--(140)`, the global weak-escape/singular
metric/projection wall `(141)--(150)`, and the critical-node Galerkin resolution trilemma
`(151)--(158)`, the relative-floor metric wall `(159)--(162)`, and the defect-base/hard-edge
equivalence and source-impedance calibration `(163)--(185)`.
Repository-wide searches found no prior occurrence of the limit `i/z-H/G`, its nonadjacent
specialization, `(101)--(112)`, the canonical inverse-square Clark weak limit, the mixed-anchor
formula `(128)`, or the global weak-escape/projection wall.  The internal corpus does contain the
two classical parents separately:
compactified Donoghue weak convergence and the inverse-square critical-ordinate screw series.  It
does not identify them as the unique movable-anchor target.  Suzuki's global paper contains the
screw-line expansion that is the parent of Theorem K, but not its source-Cesaro origin or its
comparison with coalescing finite anchors.  Targeted primary-literature searches found Suzuki's
fixed-anchor `+-i` construction, its conjecture of extension-operator/eigenvalue convergence,
general Livsic base-change theory, and general Donoghue spectral encoding, but no coalescing
restricted-Weil full-quotient boundary layer, inverse-square Clark-weight theorem, or anchor-escape
projection trilemma.  Gamma-field base change itself is classical and is not claimed new.  The
targeted source and literature audit found no prior reduction of Suzuki's movable inverse-square
limit to his fixed-anchor pointed measure plus the exact hard-edge condition `(174)`, nor the
identification of his screw-Cesaro origin with the zero-anchor model-space kernel or the
source-impedance selector `(180)--(184)` which removes that hard edge once fixed-anchor convergence
is known.  Specialist priority review remains required.
