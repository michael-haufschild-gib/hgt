# Suzuki coalescing-anchor parity-locking reduction

- **ID:** `suzuki-coalescing-anchor-parity-locking-reduction`
- **Ledger:** `SR-65`, `SR-66`, `SR-67`, `SR-68`, `SR-69`, `SR-70`, `SR-71`, `SR-72`, `SR-73`, `SR-74`, `SR-75`, `SR-76`, `SR-77`, `SR-78`, `SR-79`, `SR-80`, `SR-81`, `SR-82`, `SR-83`, `SR-84`, `SR-85`, `SR-86`, `SR-87`, `SR-88`
- **Stage:** 2 — dependency-closed paper proof
- **Type:** THEOREM (paper) / SOURCE-RANGE AND PRE-DIVISOR CALIBRATION ADVANCE
- **RH used:** no in Sections 2--14.7, in the finite spectral-shift identities/selector of
  Sections 14.13--14.14, in the literal normalized-Hankel theorems of Sections 14.15--14.19, and
  in the first-jet part of Theorem AC; yes as the hypothesis of the global-limit and Xi-target
  audits in Sections 14.8--14.14 and in the complete-family consequences of Theorems AC--AE
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

## 13. Exact post-admission Route-G statement

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

Thus the exact post-admission open core is not generic compactness.  It is to construct cofinally,
from Suzuki's
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
 inner(g_(1,n), 1_[0,delta](L_n^2)
   (L_n^2+1)(L_n^2+c_n^2)^(-1) g_(1,n)) = 0            (176)
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

The fixed anchor itself does not converge as a vector in Suzuki's published global embedding.
Theorem L used `c_n->0`, where translation covariance becomes an invariant-functional
contradiction.  The same argument is stronger at every positive limiting exponent.

#### Theorem Q — all bounded exponential anchors weakly escape

Assume RH and use Suzuki's `lambda=0` nested Weil spaces.  Let `a_n->infinity`, let
`c_n->c_*` for any `c_*>=0`, and put

```text
A_(a_n)v_n=e^(c_n X),
N_n=||v_n||_(A_(a_n))^2,
g_n=j_n(v_n/sqrt(N_n)).                                (186)
```

Then

```text
N_n->infinity,
g_n weakly ->0 in H(A_infinity).                       (187)
```

In particular `(187)` holds for Suzuki's original fixed deficiency base `c_n=1`.  Therefore the
fixed-anchor pointed law `(173)`, if true, is necessarily singular in the global embedding too.

#### Proof

For a compact test `u`, eventually supported in every aperture under consideration,

```text
<[u],j_n v_n>_(A_infinity)
 =int_R conjugate(u(x))e^(c_n x)dx.                    (188)
```

If `N_n` were bounded on a subsequence, weak compactness would produce a global Riesz vector for
the nonzero functional

```text
ell_(c_*)(u)=int_R conjugate(u(x))e^(c_* x)dx.          (189)
```

For physical translation `tau_t u(x)=u(x-t)`, direct change of variables gives

```text
ell_(c_*)(tau_t u)=e^(c_* t)ell_(c_*)(u).               (190)
```

Translations are unitary in `H(A_infinity)`.  If `c_*>0`, the norm of a nonzero bounded
functional cannot be multiplied by `e^(c_*t)` for arbitrary real `t`; this contradicts `(190)`.
If `c_*=0`, its Riesz vector would be fixed by every translation, hence would give the forbidden
zero eigenvalue of Suzuki's global translation generator.  Thus `N_n->infinity`.  Dividing `(188)`
by `sqrt(N_n)` proves convergence to zero against the dense compact-test core, and boundedness of
`g_n` upgrades it to weak convergence.

Theorem Q changes the interpretation of Theorem P.  Impedance calibration proves that a movable
Clark probability contains no more information than the fixed probability, but it cannot turn the
finite defect vectors into the global kernels in norm or weak topology.  If `(173)` holds, its
positive mass must be carried by local projection rotation, rank excess, or another noncompact
pointed mechanism already at base `i`.  Coalescing then transports that singular probability
without adding a second singular layer.

There is nevertheless a direct source declaration of the fixed-anchor target.  Let the
unconditional source screw line `x(t)=pi^(-1/2)mathfrak S_t` be as in Theorem K and define, for
finite `T`,

```text
Psi_T=-int_0^T e^(-t)x(t)dt.                            (191)
```

This is a source-native Bochner integral: Suzuki proves continuity and locally uniform `L^2`
bounds for the line.  No zero is used in `(191)`.

#### Theorem R — Laplace screw-origin theorem

Under RH, the vectors `(191)` converge exponentially in Suzuki's screw-line Hilbert space to

```text
Psi_i=sum_gamma sqrt(m_gamma)/(gamma-i) e_gamma,        (192)

||Psi_T-Psi_i||^2<=4e^(-2T)M_0(0),
||Psi_i||^2=M_0(1).                                    (193)
```

The squared spectral probability of `Psi_i` is exactly `mu_Xi^(1)`.  Its correlation is

```text
<Psi_i,U_t Psi_i>/||Psi_i||^2
 =1/M_0(1) sum_gamma m_gamma e^(-i gamma t)/(gamma^2+1). (194)
```

Thus Suzuki's original fixed-anchor target is source-declared by exponential averaging of the
same unconditional prime--Gamma line whose Cesaro average declares the zero-anchor target.  The
impedance constant has the source-norm form

```text
B_Xi=||Omega||^2/||Psi_i||^2.                           (195)
```

#### Proof

Insert the RH-conditional expansion `(134)` into `(191)`.  For each ordinate,

```text
-int_0^infinity e^(-t)(e^(-i gamma t)-1)/gamma dt
 =1/(gamma-i).                                         (196)
```

The omitted tail has modulus at most `2e^(-T)/|gamma|`.  Orthogonality and reciprocal-square
summability give `(193)`.  Equations `(192)`, `(139)`, and the diagonal action of `U_t` give
`(194)--(195)`.

The exact fixed-anchor endpoint can now be stated without reference to moving atoms.  For `s>0`
put

```text
k_s^(1)(u)=(u+1)/(u+s),        k_s^(1)(infinity)=1.     (197)
```

Equation `(169)` gives

```text
int k_s^(1) dmu_Xi^(1)=M_0(s)/M_0(1).                  (198)
```

#### Theorem S — fixed-anchor screw rigidity

For a source-selected finite Suzuki family, the fixed-anchor law `(173)` is equivalent to

```text
<g_(1,n),(L_n^2+1)(L_n^2+s)^(-1)g_(1,n)>
 ->M_0(s)/M_0(1)                                       (199)
```

on any set of positive `s` with an interior accumulation point.  Equivalently, the cyclic
correlations converge to `(194)` for every real time.

#### Proof

Weak convergence implies `(199)` because `(197)` is continuous on `[0,infinity]`.  Conversely,
compactness gives a weakly convergent subsequence.  Since

```text
k_s^(1)(u)-1=(1-s)/(u+s),                               (200)
```

the identities on a uniqueness set determine all Stieltjes transforms by holomorphic
continuation.  Constants together with `1/(u+s)` form a separating algebra after uniform closure,
exactly as in Theorem J.  Stone--Weierstrass identifies the subsequential limit with
`mu_Xi^(1)`.  Uniqueness removes extraction.  The correlation statement is the spectral theorem.

Equation `(199)` is the actual remaining analytic Route-G statement after first-defect source
admission.  It is bounded, fixed-base,
source-operator local, and its target vector is the finite source declaration `(191)`.  Theorem Q
proves it cannot follow from regular convergence of `g_(1,n)`; source arithmetic must instead
control the singular cyclic spectral measures.

### 14.13 Compactified two-extension spectral shift: singular weights become gap occupancy

Theorem S still presents the fixed law through the moving cyclic vector.  For Suzuki's canonical
parity pair there is an equivalent invariant which contains no cyclic vector and remains meaningful
under the spectral pollution forced by Theorem Q.

First note the exact target identity.  With `XiC(z)=xi(1/2-iz)` and the convention of Section 3,

```text
m_(Xi,1)(z)
 =i mathcalL(-iz)/M_0(1)
 =-XiC'(z)/(M_0(1)XiC(z)).                              (201)
```

Thus the target is a normalized logarithmic derivative.  At a simple pole `x` of the finite even
pencil, write `mu_x` for its Nevanlinna mass.  Since

```text
m_n=-i W_(n,1)/W_(n,-1),
mu_x=i W_(n,1)(x)/W_(n,-1)'(x),
```

the entire derivative-companion defect

```text
J_n(z)=W_(n,-1)'(z)-i M_0(1)W_(n,1)(z)                 (202)
```

satisfies

```text
J_n(x)/W_(n,-1)'(x)=1-M_0(1)mu_x.
```

Consequently `(202)` is not a formal pencil identity: at the even eigenvalues it is exactly the
missing flat-Jacobian law `mu_x -> 1/M_0(1)`.  The free clock has constant masses for a different
reason and with the wrong cofinal scale, so it does not prove `(202)`.

There is, however, a second exact description.  Let the positive eigenvalues of the canonical even
and odd extensions be respectively

```text
0<p_(n,1)<q_(n,1)<p_(n,2)<q_(n,2)<... .                (203)
```

The odd extension has in addition its forced eigenvalue at zero.  Put

```text
x(t)=1/(1+t^2),
E_n=union_(k>=1) (x(q_(n,k)),x(p_(n,k))),
sigma_n=1_(E_n)(x) dx.                                  (204)
```

Strict interlacing makes the intervals in `(204)` disjoint, so `sigma_n` is a subprobability
measure dominated by Lebesgue measure on the fixed compact interval `[0,1]`.  The classical
canonical product for a normalized odd meromorphic Herglotz function gives

```text
H_n(s):=m_n(i sqrt(s))/(i sqrt(s))
 =product_(k>=1)
   [1+(s-1)x(q_(n,k))]/[1+(s-1)x(p_(n,k))],             (205)
```

where the constant is fixed by `m_n(i)=i`.  Taking the real logarithm for `s>0` and integrating
each factor across its interlacing interval yields the exact linearization

```text
log H_n(s)
 =(1-s) integral_[0,1] 1/[1+(s-1)x] dsigma_n(x).        (206)
```

No limiting argument occurs in `(206)`.  A pole--zero pollution pair contributes only the length
of its compactified gap.  Arbitrarily many pairs may therefore cancel while a nonzero singular
limit survives.  This is precisely the mechanism that one-extension eigenvalue convergence and
the regular pointed-vector picture both miss.

#### Theorem T — fixed-anchor law is compactified spectral-shift convergence

Under RH, let `sigma_Xi` be the measure obtained from the normalized target `(201)` by `(203)--(204)`:
its pole locations are the distinct positive Xi ordinates and its zero locations are the positive
zeros of the meromorphic logarithmic derivative between consecutive poles.  Equivalently it is
the unique finite measure on `[0,1]` satisfying

```text
integral_[0,1] 1/[1+(s-1)x] dsigma_Xi(x)
 = log(M_0(s)/M_0(1))/(1-s),       s>0, s!=1.           (207)
```

For any source-selected finite Suzuki sequence, the following are equivalent:

1. the fixed-anchor transform law `(199)` holds on a positive uniqueness set;
2. the paired-extension occupancy measures satisfy

   ```text
   sigma_n --> sigma_Xi                                  (208)
   ```

   weakly on `[0,1]`.

Indeed, evenness of the fixed Clark probability and the Donoghue identity give

```text
H_n(s)
 =integral_[0,infinity] (u+1)/(u+s) dmu_(1,n)(u).       (209)
```

Thus `(199)`, `(206)`, and `(207)` identify the transforms.  Weak convergence in `(208)` implies
the transform limit because the kernel in `(206)` is continuous.  Conversely the measures
`sigma_n<=dx` are compact.  Every weak subsequential limit has the transform in `(207)` on the
given uniqueness set; holomorphic continuation in `s` and uniqueness of the Stieltjes transform
identify it with `sigma_Xi`.  Hence every subsequence has the same limit.

The measure in `(204)` is the compactified Krein spectral-shift occupancy of the two rank-one
self-adjoint extensions.  Spectral-shift theory and exponential Herglotz representations are
classical.  The new Suzuki-specific point is that the singular fixed-anchor Clark law is exactly
this **two-extension eigenvalue-only** invariant.  One extension remains insufficient; the
opposite extension records its missing Jacobians through the pole--zero gaps.

#### Theorem U — smoothing-trace hierarchy and first source selector

For `j>=0`, let `f_j(t)=(1+t^2)^(-(j+1))`, and denote the canonical even and odd extensions by
`L_n^-` and `L_n^+`.  Their finite-aperture spectra make both `f_j(L_n^-)` and `f_j(L_n^+)` trace
class.  Directly from `(203)--(204)`,

```text
Tr(f_j(L_n^-)-f_j(L_n^+))
 =2(j+1) integral_[0,1] x^j dsigma_n(x)-1.              (210)
```

The `-1` is the forced odd eigenvalue at zero.  Expanding `(206)` at `s=1` gives the target moments

```text
c_j^Xi
 :=integral_[0,1] x^j dsigma_Xi(x)
 =(-1)^(j+1)/(j+1)!
   [d^(j+1)/ds^(j+1) log M_0(s)]_(s=1).                 (211)
```

Since polynomials are dense on `[0,1]`, `(199)` is therefore equivalent to the countable,
source-declared trace hierarchy

```text
Tr(f_j(L_n^-)-f_j(L_n^+)) -> 2(j+1)c_j^Xi-1
for every j>=0.                                         (212)
```

This is not a regular strong-resolvent consequence.  Strong convergence of moving rank-one
resolvent differences does not by itself control their traces; rank-one projections onto a weakly
escaping orthonormal sequence are the elementary model of the missing implication.  Theorem Q
therefore does not kill `(208)--(212)`, but it proves that their limit must be singular.

The zeroth occupancy moment is already the anchored defect:

```text
sigma_n([0,1])=(1-kappa_n)/2,       kappa_n=m_n'(i),
c_0^Xi=(1-kappa_Xi)/2 in (0,4/85).                      (213)
```

The scalar defect and its endpoint transport are not new here: they are the content of the existing
`suzuki-parity-resolvent-transport-budget` route (`SR-55` and its interior refinements).  What is
new in the present reduction is the identification of that known defect as the **zeroth moment** of
the two-extension occupancy and its placement inside the full trace hierarchy `(210)--(212)`.
At fixed anchor `i`, the far-negative endpoint is

```text
kappa_free(a)=2a/sinh(2a),                              (214)
```

while a source-visible simple even ground state gives `kappa_(a,lambda)->1` as `lambda` rises to
the spectral floor.  Here source-visible means that its inner product with the even anchor
`cosh(X)` is nonzero.  The corpus theorem `77/85<kappa_Xi<1` is unconditional.  Hence, for every
sufficiently large aperture with source-visible simple even ground state, continuity in `lambda`
gives at least one admissible shift satisfying

```text
kappa_(a,lambda_a^*)=kappa_Xi.                          (215)
```

Taking, for example, the least crossing makes `(215)` source-measurable from the finite resolvent
and the theta-declared scalar; it uses no Xi zero location.  This crossing is an application of the
already-known defect transport, not a separate novelty claim.  A source-visible simple odd ground
state approaches `-1`, so the same endpoint argument genuinely fails there; an interior overshoot
or cofinal source-visible even-ground theorem would be required.

Equation `(215)` matches only `j=0` in `(212)`.  The sharp finite-atomic counterfamily of Section
14.5 proves that no first-moment argument can supply the rest.  The exact nonterminal Route-G
theorem is now:

> construct a source-selected cofinal family and prove compactified spectral-shift convergence
> `(208)`, equivalently all smoothing-trace laws `(212)`; or prove that Suzuki's literal paired
> extensions cannot have the source-declared limit `(207)`.

This formulation survives both weak anchor escape and eigenvalue overcrowding.  It is strictly
stronger than one-extension spectral convergence and strictly less pointwise than matching every
polluted eigenvalue: only the total compactified pole--zero gap occupancy matters.

### 14.14 Low-energy extinction and the regular phase-mixing no-go

The occupancy formulation yields a quantitative obstruction which is invisible in the pointed
probability alone.  The unconditional zero-height estimate used in the Xi first-defect theorem is

```text
gamma^2>81/4
```

for every real centered Xi ordinate under RH.  Every positive zero of the target logarithmic
derivative lies between two consecutive positive poles, so it obeys the same lower bound.  Hence

```text
supp(sigma_Xi) subset [0,4/85),                         (216)
```

because `x(t)=(1+t^2)^(-1)`.  In particular

```text
0<=c_j^Xi< (4/85)^(j+1),
-1<2(j+1)c_j^Xi-1
   <-1+2(j+1)(4/85)^(j+1).                              (217)
```

The first inequality uses `c_0^Xi<4/85` and `x^j<=(4/85)^j` on the support.  Thus `(208)` forces
the positive low-energy extinction law

```text
lim_n sigma_n([4/85+epsilon,1])=0
for every epsilon>0.                                    (218)
```

There is no cancellation hidden in `(218)`: it is the sum of the compactified lengths of all
even-pole/odd-zero gaps meeting that low-energy window.  Any source theorem giving a uniform
positive lower bound for one such window would retire Route G.

The opposite regular regime is already class-completely dead.  Let `phi_n` be the increasing
boundary phase of `Theta_n`, normalized by `phi_n(0)=pi`, and for `0<x<1` put

```text
t(x)=sqrt(x^(-1)-1),
vartheta_n(x)=phi_n(t(x)).                              (219)
```

The phase runs from the central odd zero through alternating even poles and positive odd zeros.
Consequently, away from the discrete endpoints,

```text
d sigma_n/dx
 =1_{sin(vartheta_n(x))>0}.                             (220)
```

This is an exact phase form of `(204)`.  The periodic square wave in `(220)` has mean `1/2` and a
bounded periodic primitive after subtracting that mean.

#### Theorem V — regular high-frequency phase mixing is a dead end

Assume that on every compact interval `I subset (0,1)`, `vartheta_n` is `C^1`, has no stationary
point, and its signed inverse speed obeys

```text
||1/vartheta_n'||_(L^infinity(I))
 +Var_I(1/vartheta_n') ->0.                             (221)
```

Then

```text
sigma_n --> (1/2)dx                                    (222)
```

weakly on `[0,1]`.  Therefore no sequence satisfying `(221)` can obey the Xi law `(208)`.

To prove the theorem, write `S(y)=1_{sin y>0}-1/2` and choose a bounded periodic primitive `P` of
`S`.  For a `C^1` test function `h` supported in `I`, integration by parts gives

```text
integral_I h(x)S(vartheta_n(x))dx
 =boundary[h P(vartheta_n)/vartheta_n']
  -integral_I P(vartheta_n)d(h/vartheta_n').
```

The right side tends to zero by `(221)`.  Approximation extends this to continuous compactly
supported tests.  Exhausting `(0,1)` and using `0<=sigma_n<=dx` handles the two endpoints, proving
`(222)`.  But `(216)` gives

```text
sigma_Xi((4/85,1])=0,
(1/2)dx((4/85,1])=81/170,
```

so the two limits are different by a fixed amount.

Condition `(221)` is the precise regular-clock hypothesis: phase frequency diverges while inverse
phase speed becomes locally flat.  Free-clock homogenization is its model.  Theorem V proves that
smoothly distorted clocks are just as dead.  A successful Suzuki branch must violate `(221)` on
some fixed compact subinterval of `(4/85,1)`: either its phase does not become high-frequency
there, or its inverse speed develops nonvanishing bounded-variation concentration locked to the
alternating extension parity.  Combined with Theorem Q, this is the exact singular survivor:

```text
weak vector escape
 + spectral overcrowding
 + alternating phase-speed boundary layers
 -> possible nonfree paired occupancy.                 (223)
```

The periodic averaging lemma is classical and is not claimed new.  Candidate-new content is the
Suzuki/Xi support wall `(216)--(218)`, the exact parity square wave `(220)`, and the resulting proof
that every regular high-clock realization of the fixed-anchor route converges to the wrong
half-Lebesgue spectral-shift state.

### 14.15 The actual first obstruction: a negative normalized Hankel edge

The occupancy problem occurs only after a cofinal shifted family has passed the first Xi defect.
The updated source-superselection paper correctly places this earlier obstruction at the literal
even/odd restricted-Weil resolvents.  The following theorem removes one of its two apparent
sources: the common Toeplitz channel can carry only exponentially vanishing parity bias.  Any
cofinal admission must instead be nonperturbative in the arithmetic Hankel carrier.

Use the half-interval parity decomposition from
`ccm-finite-prime-parity-hankel-carrier`.  For `lambda` below the full restricted-Weil floor, write

```text
q_e=C_(a,lambda)+H_a,       q_o=C_(a,lambda)-H_a,
C_(a,lambda)=T_a-lambda I.                              (224)
```

Both forms in `(224)` are coercive.  Their average `C_(a,lambda)` is therefore coercive too, and
`|H_a(f,f)|<=C_(a,lambda)(f,f)`.  Let

```text
K_(a,lambda)
 =C_(a,lambda)^(-1/2) H_a C_(a,lambda)^(-1/2)           (225)
```

be the corresponding self-adjoint form contraction.  Define its even-favouring negative radius

```text
r_(a,lambda)=max{0,-inf spec K_(a,lambda)} in [0,1].    (226)
```

Before inserting `H_a`, let

```text
E_0=<cosh,C^(-1)cosh>,       O_0=<sinh,C^(-1)sinh>,
kappa_0=(E_0-O_0)/(E_0+O_0).                            (227)
```

The literal responses after inserting the Hankel carrier are

```text
E=<cosh,(C+H_a)^(-1)cosh>,
O=<sinh,(C-H_a)^(-1)sinh>,
kappa=(E-O)/(E+O).                                      (228)
```

The harmless common factor from the unitary full-interval parity lifts cancels in `(227)--(228)`.
The bounded Carleman-plus-finite-reflection realization of `H_a` also shows that the two closed
forms in `(224)` have the same half-interval form domain; no identification of different Friedrichs
domains is being assumed.

#### Theorem W — Toeplitz `sech` wall and Hankel rapidity budget

For every aperture and every admissible shift,

```text
|kappa_0|<=sech(a).                                     (229)
```

Moreover,

```text
kappa
 <=[kappa_0+r_(a,lambda)]/[1+kappa_0 r_(a,lambda)].     (230)
```

Equivalently, with `artanh(1)=infinity`,

```text
artanh(kappa)<=artanh(kappa_0)+artanh(r_(a,lambda)).    (231)
```

Consequently, whenever `sech(a)<kappa_Xi` and a literal shift reaches the first Xi wall,

```text
kappa_(a,lambda)>=kappa_Xi,
```

its normalized Hankel carrier necessarily satisfies

```text
r_(a,lambda)
 >=[kappa_Xi-sech(a)]/[1-kappa_Xi sech(a)].             (232)
```

Both inequalities are strict when `kappa_(a,lambda)>kappa_Xi`.

For every cofinal admitted family this gives the unconditional asymptotic wall

```text
liminf r_(a,lambda_a)>=kappa_Xi>77/85.                  (233)
```

Thus neither the common convolution channel nor a small Hankel perturbation can admit Route G.
The actual first source theorem must create a negative spectral edge of the normalized literal
prime--Gamma Hankel form at least `77/85` of the way to loss of even coercivity.

#### Proof

Let `J_a f(x)=f(a-x)` on `L^2(0,a)`.  Since `T_a` has difference kernel `K(x-y)` and that kernel is
even, midpoint reflection commutes with `C=C_(a,lambda)` and hence with `C^(-1)`.  Put

```text
u(x)=exp(x),       v(x)=exp(-x).
```

The exact source relation is

```text
u=exp(a) J_a v.                                         (234)
```

Set

```text
A=<u,C^(-1)u>,   B=<v,C^(-1)v>,   D=<u,C^(-1)v>.
```

Commutation and `(234)` give `A=exp(2a)B`, while Cauchy--Schwarz gives
`|D|<=exp(a)B`.  Since `cosh=(u+v)/2` and `sinh=(u-v)/2`, direct expansion yields

```text
E_0-O_0=D,       E_0+O_0=(A+B)/2.
```

Therefore

```text
chi_(a,lambda):=D/[exp(a)B] in [-1,1],
kappa_0=sech(a) chi_(a,lambda),
|kappa_0|<=sech(a).                                     (235)
```

which proves `(229)`.  Notice that this is uniform in the shift and uses the literal exponential
sources; it is not a large-negative-shift approximation.  The scalar `chi_(a,lambda)` is the exact
common-Toeplitz midpoint-reflection fidelity, so the exponential decay is structural.

For `(230)`, first suppose `inf spec K=-1`.  Then `r=1` and the bound is immediate.  Otherwise put
`m=inf spec K>-1`.  Quadratic-form functional calculus applied to `(225)` gives

```text
E<=E_0/(1+m),       O>=O_0/(1-m).                       (236)
```

If `m>=0`, `(236)` gives `E/O<=E_0/O_0`, so `(230)` holds with `r=0`.  If `m<0`, put `r=-m` and
obtain

```text
E/O <=(E_0/O_0)(1+r)/(1-r).                            (237)
```

The Cayley identities

```text
E_0/O_0=(1+kappa_0)/(1-kappa_0),
E/O=(1+kappa)/(1-kappa)
```

turn `(237)` into `(230)`; `(231)` is the hyperbolic addition formula.  If
`kappa>=kappa_Xi`, rearrangement gives

```text
r>=(kappa_Xi-kappa_0)/(1-kappa_Xi kappa_0).
```

The right side decreases with `kappa_0`, so `(229)` proves `(232)`; strict source passage makes
both displayed comparisons strict.  Letting `a` tend to infinity and using the unconditional
`kappa_Xi>77/85` proves `(233)`.

The operator inequality is sharp at the abstract level: equality in `(237)` occurs when both
source directions lie in the bottom spectral subspace of `K` and the midpoint Cauchy--Schwarz
bound is saturated.  No such alignment is assumed for Suzuki; proving or excluding it is part of
the remaining source problem.

The edge has a completely explicit arithmetic witness.  Recall

```text
H_a=H_(a,infinity)-P_a,                                 (238)
```

where `P_a` is the finite von-Mangoldt reflection form `(9)` of
`ccm-finite-prime-parity-hankel-carrier` and `H_(a,infinity)` is its archimedean Hankel part.
If the right side of `(232)` is `b`, the spectral definition of `(226)` gives, for every
`epsilon>0`, a half-interval form vector `f` such that

```text
P_a(f,f)-H_(a,infinity)(f,f)
 >(b-epsilon)[T_a(f,f)-lambda||f||_2^2].                (239)
```

For the same vector, `q_e=C+H_a` and `q_o=C-H_a` give

```text
q_o(f)/q_e(f)>(1+b-epsilon)/(1-b+epsilon).              (240)
```

At the exact bound in `(232)`, the limiting right side of `(240)` is

```text
R_Xi [1-sech(a)]/[1+sech(a)]
 > (81/4)[1-sech(a)]/[1+sech(a)].                       (241)
```

Thus admission forces an actual prime-power autocorrelation surplus, measured against the common
Toeplitz energy, and a same-profile odd/even form ratio approaching the full Xi cost.  These are
not merely abstract parity labels.  Equations `(239)--(241)` are necessary, not
sufficient: its near-edge vector must also align with the exponential source, and higher fixed
anchor laws remain after first-jet admission.

The parity decomposition `(224)`, form contraction `(225)`, and spectral-calculus estimate are
classical operator theory.  Candidate-new content is the exact Suzuki source conjunction: midpoint
reversal plus the two exponential parity sources gives the uniform `sech(a)` wall `(229)`, and the
Xi defect converts it into the sharp negative normalized-Hankel edge and prime-correlation budget
`(232)--(241)`.  Repository and targeted primary-literature searches found the separate
Toeplitz--Hankel and Birman--Schwinger parents, but no restricted-Weil `sech` wall, hyperbolic
parity budget, or `77/85` negative-edge and same-profile `81/4` consequence.  Specialist priority
review remains required.

This relocates the true first frontier to a falsifiable source theorem:

> either prove a cofinal lower bound
> `inf spec K_(a,lambda)>-77/85+eta` uniformly over all admissible shifts, which kills Route G at
> its first jet, or construct source-aligned near-edge vectors satisfying `(239)` and then prove
> the paired occupancy hierarchy.  Strong indefiniteness of `H_a` alone decides neither side,
> because `(225)` normalizes it by the full Toeplitz energy.

### 14.16 The source-alignment slack law

Theorem W leaves an apparent loophole: perhaps the normalized Hankel carrier has the required
negative edge but the exponential source never sees it.  That is possible when the edge overshoots
the minimum budget.  It is impossible near the minimum budget.  The exact excess over the sharp
edge threshold pays for every source-alignment defect.

Assume `sech(a)<kappa_Xi`, `kappa>=kappa_Xi`, and `r=r_(a,lambda)<1`.  Admission and Theorem W force
`r>0`, so `inf spec K=-r`.  Put

```text
rho_0=E_0/O_0,                  R_Xi=(1+kappa_Xi)/(1-kappa_Xi),
q=R_Xi/rho_0>1,
r_*=(q-1)/(q+1)
   =(kappa_Xi-kappa_0)/(1-kappa_Xi kappa_0).            (242)
```

The number `r_*` is the exact edge strength required by the actual common-channel fidelity
`kappa_0`; replacing `kappa_0` by `sech(a)` gives the coarser wall `(232)`.  Define the unit
common-channel source vectors

```text
x_e=C^(-1/2)cosh/sqrt(E_0),
x_o=C^(-1/2)sinh/sqrt(O_0),                             (243)
```

and let `mu_e,mu_o` be their probability spectral measures for `K`.  Functional calculus gives

```text
A_e:=E/E_0=int 1/(1+t) dmu_e(t),
A_o:=O/O_0=int 1/(1-t) dmu_o(t).                       (244)
```

Define nonnegative bottom-edge deficits

```text
Delta_e=1/(1-r)-A_e
       =int (t+r)/[(1-r)(1+t)] dmu_e(t),

Delta_o=A_o-1/(1+r)
       =int (t+r)/[(1-t)(1+r)] dmu_o(t).               (245)
```

#### Theorem X — exact Hankel-edge/source-alignment dichotomy

Every matching shift above satisfies the sharp slack law

```text
Delta_e+q Delta_o
 <=S:=1/(1-r)-q/(1+r)
     =(1+q)(r-r_*)/(1-r^2).                            (246)
```

If `kappa>kappa_Xi`, inequality `(246)` is strict.  In particular, for every `delta>0`,

```text
mu_e([-r+delta,1]) <=2(1-r)S/delta,
mu_o([-r+delta,1]) <=(1+r)^2 S/(q delta).              (247)
```

The same law directly controls the normalized-Hankel Rayleigh defects:

```text
0<=<x_e,(K+r)x_e><=2(1-r)Delta_e<=2(1-r)S,
0<=<x_o,(K+r)x_o><=(1+r)^2Delta_o<=(1+r)^2S/q.         (248)
```

Equivalently, with the unit common-form Riesz profiles

```text
f_e=C^(-1)cosh/sqrt(E_0),       f_o=C^(-1)sinh/sqrt(O_0),
C(f_e,f_e)=C(f_o,f_o)=1,                               (249)
```

the literal finite-prime surplus obeys

```text
P_a(f_e,f_e)-H_(a,infinity)(f_e,f_e)
 >=r-2(1-r)S,

P_a(f_o,f_o)-H_(a,infinity)(f_o,f_o)
 >=r-(1+r)^2S/q.                                       (250)
```

At exact target matching, `kappa=kappa_Xi`, if the edge merely equals its sharp minimum
`r=r_*`, then `S=0`, both measures in `(245)` are supported on the singleton `{-r}`, and

```text
Kx_e=-r x_e,                 Kx_o=-r x_o.              (251)
```

The two vectors are linearly independent, because `C^(-1/2)` is injective and `cosh,sinh` are
linearly independent.  Thus exact saturation forces bottom-edge multiplicity at least two.  A
simple normalized-Hankel bottom edge cannot attain the sharp Xi response; it must overshoot
`r_*`.  This statement concerns the bottom edge of `K`, not simplicity of a restricted-Weil
ground state, and the existing ground-residue results do not supply it.

#### Proof

From `(244)` and `E/O>=R_Xi`,

```text
A_e/A_o>=(R_Xi/rho_0)=q.                               (252)
```

Substitute `A_e=1/(1-r)-Delta_e` and
`A_o=1/(1+r)+Delta_o`.  Rearranging `(252)` is exactly the first expression in `(246)`.
The second follows from the definition of `r_*`.  Strict source passage makes `(252)` and hence
`(246)` strict.

On `[-r+delta,1]`, the first integrand in `(245)` is at least
`delta/[2(1-r)]`, while the second is at least `delta/(1+r)^2`; Markov's elementary integral
bound proves `(247)`.  The pointwise identities

```text
t+r <=2(1-r) (t+r)/[(1-r)(1+t)],
t+r <=(1+r)^2 (t+r)/[(1-t)(1+r)]
```

prove `(248)`.  For `(250)`, note that `x_e=C^(1/2)f_e`, `x_o=C^(1/2)f_o`, and

```text
<x,Kx>=H_a(f,f)=H_(a,infinity)(f,f)-P_a(f,f).
```

Finally, `r=r_*` makes the right side of `(246)` zero.  Both nonnegative deficits vanish, and
their integrands vanish only at `t=-r`.  This proves `(251)` and the multiplicity statement.

For a cofinal matching family, `|kappa_0|<=sech(a)` gives `rho_0->1` and `r_*->kappa_Xi`.  Hence
there are only three surviving first-gate regimes:

```text
maximal edge collapse r=1 along a subsequence;
nonvanishing edge overshoot limsup(r-r_*)>0;
near-minimal edge with both source laws concentrating at -r.     (253)
```

The last regime forces the source-profile prime surplus in `(250)` to converge to at least
`kappa_Xi>77/85`.  This is stronger than the arbitrary near-edge witness `(239)`: it uses the
literal common-channel exponential Riesz profiles.  It still does not close Suzuki.  Regimes one
and two remain possible, and even regime three supplies only first-jet admission, not the paired
occupancy hierarchy.

The probability spectral calculus and slack rearrangement are elementary and are not claimed new.
Candidate-new content is their exact Suzuki/Xi specialization: minimum negative edge strength,
source-alignment deficit, arithmetic prime surplus, and bottom-edge multiplicity are one identity
`(246)`.  Repository and targeted primary-literature searches found the ground-residue
polarization and parity-transport parents, plus generic Toeplitz--Hankel spectral theory, but no
restricted-Weil alignment-slack or sharp-edge degeneracy theorem.  Specialist priority review
remains required.

### 14.17 Maximal normalized edge is the ground-pole branch

The first regime in `(253)` is not an additional mysterious Hankel mechanism.  It is the relative
form signature of an even parity floor.  This also exposes why a uniform edge ceiling over every
admissible shift is only a sufficient no-go and may be much too strong: a source-invisible even
ground mode still drives the abstract edge to `-1` without admitting the exponential source.

Let `A_e,A_o` be the half-interval even and odd restricted-Weil operators, with common closed form
domain and floors

```text
alpha_e=inf spec A_e,          alpha_o=inf spec A_o.
```

For `lambda<min(alpha_e,alpha_o)`, write

```text
q_(e,lambda)=q_e-lambda||.||_2^2=C_lambda+H_a,
q_(o,lambda)=q_o-lambda||.||_2^2=C_lambda-H_a,          (254)
```

and form `K_lambda` as in `(225)`.  Put `m_lambda=inf spec K_lambda`.

#### Theorem Y — exact relative-edge/parity-floor correspondence

For every such shift,

```text
sup_(f!=0) q_(o,lambda)(f)/q_(e,lambda)(f)
 =[1-m_lambda]/[1+m_lambda],                            (255)
```

with both sides interpreted as `infinity` when `m_lambda=-1`.  In particular, whenever
`m_lambda<0`, the left side is `(1+r_lambda)/(1-r_lambda)`.

Suppose `phi_e` is an `L^2`-unit even ground vector and put

```text
eta_e=q_(o,alpha_e)(phi_e)>=0.
```

Then for every `lambda<min(alpha_e,alpha_o)`,

```text
[1+r_lambda]/[1-r_lambda]
 >=1+eta_e/(alpha_e-lambda),

r_lambda>=eta_e/[2(alpha_e-lambda)+eta_e]              (256)
```

whenever `eta_e>0`.  If the even floor is strict, `alpha_e<alpha_o`, then

```text
eta_e>=alpha_o-alpha_e,
r_lambda
 >=(alpha_o-alpha_e)/[2(alpha_e-lambda)+alpha_o-alpha_e]
 ->1                         as lambda->alpha_e-.       (257)
```

At a tied floor `alpha_e=alpha_o=alpha`, the same conclusion holds for every
`phi_e in ker(A_e-alpha)` not belonging to `ker(A_o-alpha)`.  Therefore avoiding edge collapse
from the even bottom space requires the rigid incidence

```text
ker(A_e-alpha) subset ker(A_o-alpha).                   (258)
```

This condition is necessary only for avoiding that pole-driven collapse, not sufficient for a
uniform edge bound: other relative near-kernel sequences can still send `m_lambda` to `-1`.

#### Proof

For `y=C_lambda^(1/2)f`, the two shifted forms are

```text
q_(e,lambda)(f)=<y,(I+K_lambda)y>,
q_(o,lambda)(f)=<y,(I-K_lambda)y>.
```

Since `C_lambda` is coercive, `C_lambda^(-1/2)` maps the whole Hilbert space into its form domain.
The supremum over `f` is therefore the spectral supremum of
`(I-K_lambda)(I+K_lambda)^(-1)`.  Its scalar symbol `(1-t)/(1+t)` is decreasing, which proves
`(255)`.

Let `d=alpha_e-lambda`.  The ground equation gives

```text
q_(e,lambda)(phi_e)=d,
q_(o,lambda)(phi_e)=eta_e+d,
q_(o,lambda)(phi_e)/q_(e,lambda)(phi_e)=1+eta_e/d.      (259)
```

Insert `(259)` into `(255)` and solve for `r_lambda`; this is `(256)`.  If
`alpha_e<alpha_o`, the odd variational floor gives
`q_(o,alpha_e)(phi_e)>=alpha_o-alpha_e`, proving `(257)`.  At a tied floor,
nonnegativity of `q_(o,alpha)` gives `eta_e=0` exactly when `phi_e` belongs to its form kernel,
which proves `(258)`.

If additionally `<cosh,phi_e>!=0` and the even floor is strict, the even resolvent has a visible
pole while the odd resolvent remains bounded, so `kappa(lambda)->1`.  Thus strict source-visible
even ground is simultaneously

```text
ground-reflection-cone admission
 = visible maximal normalized-Hankel edge.              (260)
```

If the overlap vanishes, `(257)` still forces the edge but the defect response need not see it.
This is the exact reason raw edge collapse does not by itself prove admission.  At a mixed tied
floor, the already-proved ground-residue polarization law replaces the pure-even conclusion.

Generalized Rayleigh quotients and pole limits are classical and are not claimed new.  The advance
is the exact Suzuki frontier identification `(255)--(260)`: maximal normalized-Hankel edge is the
old bottom-cone branch, source invisibility separates operator edge from admission, and the
uniform all-shift edge ceiling is not the complete no-go.  The actual negative closure must rule
out the source-visible ground residue cone and the finite-shift source response, not merely one
operator norm.

### 14.18 The prime-seam localization penalty

The literal first-prime seam proves infinite positive and negative index of `H_a` by reflected
narrow bumps.  Theorem W shows that inertia is not the required quantity.  The following theorem
proves more: those exact bump packets become asymptotically invisible after normalization by the
common Toeplitz form.  Repeating the strong-indefiniteness construction at finer resolution drives
the relative Hankel spectrum toward zero, not toward the required `-77/85` edge.

Fix `a`, an admissible `lambda`, and a visible prime seam

```text
L=log p<2a,                  w_p=log(p)/sqrt(p)>0.
```

Choose finitely many disjoint intervals `I_(j,eta)` of common length `eta` and their seam
reflections

```text
R_L I_(j,eta)={L-x:x in I_(j,eta)}                     (261)
```

inside `(0,a)`.  Keep their centers fixed as `eta downarrow 0`, choose them so all these intervals
remain mutually disjoint, and exclude every other visible prime-power sum seam from their pairwise
sum neighborhoods.  There is then a fixed `d>0` such that each component has an adjacent
left/right buffer of length `d` disjoint from the whole packet.  Let `V_eta` be the finite packet
space generated by bumps in the intervals and their reflected copies.

#### Theorem Z — microlocal prime seams have zero normalized-Hankel strength

There are finite constants `B_(a,lambda)` and `M_a`, independent of `eta`, such that every
`f in V_eta` satisfies

```text
C_(a,lambda)(f,f)
 >=[log(1+2d/eta)-B_(a,lambda)]||f||_2^2,              (262)

|H_a(f,f)|
 <=[w_p+2m M_a eta]||f||_2^2,                         (263)
```

where `m` is the fixed number of reflected interval pairs.  Consequently, once the denominator is
positive,

```text
sup_(0!=f in V_eta) |H_a(f,f)|/C_(a,lambda)(f,f)
 <=[w_p+2m M_a eta]/[log(1+2d/eta)-B_(a,lambda)]
 ->0.                                                   (264)
```

In particular, the reflected-even directions on which the `p`-atom makes `H_a` negative and the
reflected-odd directions on which it makes `H_a` positive both have relative Hankel Rayleigh
quotient tending to zero.  The arbitrary finite-dimensional signed packets used to prove
`ind_+(H_a)=ind_-(H_a)=infinity` therefore accumulate at the center of the relative contraction,
not at either coercivity edge.

#### Proof

The exact finite-part decomposition of the restricted Weil form contains the positive common
Toeplitz term

```text
J(f)=1/4 int_(0,a) int_(0,a)
          |f(x)-f(y)|^2/|x-y| dx dy.                   (265)
```

After this singular term is removed, the regular difference kernel is bounded on the fixed compact
half interval.  The finite prime translation block is a nonnegative sum of jump forms minus a
finite scalar potential, and the shift contributes another scalar term.  Hence all remaining
common-form terms are bounded below by
`-B_(a,lambda)||f||_2^2` for one finite constant independent of `eta`.

Let `I=(b,b+eta)` be one packet component and write `s=x-b`.  Since `f` vanishes on its two adjacent
buffers, the two orientations of the cross pairs in `(265)` give

```text
J(f; I and its buffers)
 >=1/2 int_I |f(x)|^2
      [log(1+d/s)+log(1+d/(eta-s))] dx.
```

The bracket is symmetric, diverges at both endpoints, and has minimum
`2log(1+2d/eta)` at `s=eta/2`.  Summing over disjoint components proves `(262)`.

On `V_eta`, the selected prime atom is exactly the bounded reflection `-w_p R_L`, with norm `w_p`.
All other atomic Hankel terms vanish by the sum-seam exclusion.  The remaining Hankel kernel is
bounded in absolute value by `M_a` on the packet product.  Since the union of the `2m` intervals
has measure `2m eta`, Cauchy--Schwarz gives

```text
|H_(a,infinity)(f,f)|
 <=M_a||f||_1^2<=2m M_a eta||f||_2^2.                 (266)
```

Equations `(263)--(264)` follow.  The sign statements use the exact swap identities

```text
<-w_p R_L(u,+R_Lu),(u,+R_Lu)><0,
<-w_p R_L(u,-R_Lu),(u,-R_Lu)>0,                        (267)
```

and the regular error in `(266)`.

The logarithmic localization estimate for the finite-part Cauchy form and the reflection action of
a delta Hankel seam are classical separately.  Candidate-new content is their exact Suzuki
conjunction `(262)--(264)`: the prime-seam packets responsible for cofinal two-sided infinite
inertia are quantitatively incapable of approaching the Xi-required normalized edge.  Targeted
search found Yafaev's strong-singularity Hankel parent and general logarithmic-fractional form
theory, but no comparison with Suzuki's common restricted-Weil Toeplitz energy or this relative
edge conclusion.  Specialist priority review remains required.

The surviving source mechanism is therefore not “more localized seam bumps.”  It must use a
delocalized profile whose common Cauchy energy stays comparable to the coherent sum of many prime
reflections, or the ground-pole mechanism of Theorem Y.  Establishing or excluding that global
multi-seam coherence is now the literal arithmetic hard problem.

### 14.19 Prime-reflection rigidity and the nonuniform PNT wall

Theorem Z kills isolated narrow seam packets but does not quantify a delocalized packet meeting
many prime reflections.  There is an exact square identity for that problem.  It yields genuine
log-ratio translation rigidity only when the negative-edge budget leaves little unused prime
mass.  A second theorem then proves why the prime number theorem cannot supply that small reserve
uniformly: on every fixed endpoint window the centered prime--archimedean Hankel operators converge
strongly to zero but stay a fixed positive distance from zero in operator norm.

Extend `f in L^2(0,a)` by zero to the real line and define

```text
(R_t f)(x)=f(t-x),              (tau_h f)(x)=f(x+h).
```

For the visible prime powers put

```text
w_n=Lambda(n)/sqrt(n),
W_a=sum_(2<=n<e^(2a)) w_n,
D_a(f)=sum_(2<=n<e^(2a)) w_n||f-R_(log n)f||_2^2.       (268)
```

#### Theorem AA — prime-reflection Dirichlet budget and log-ratio rigidity

For every half-interval form vector,

```text
D_a(f)=2W_a||f||_2^2-2P_a(f,f).                         (269)
```

Consequently any normalized negative-edge witness

```text
P_a(f,f)-H_(a,infinity)(f,f)>=b C_(a,lambda)(f,f)
```

obeys the exact reserve bound

```text
D_a(f)
 <=2[W_a||f||_2^2-H_(a,infinity)(f,f)
                     -b C_(a,lambda)(f,f)].             (270)
```

Two prime reflections generate a log-ratio translation.  For every visible `m,n`,

```text
R_(log m)R_(log n)=tau_(log n-log m),
||f-tau_(log n-log m)f||_2^2
 <=2[||f-R_(log n)f||_2^2+||f-R_(log m)f||_2^2].       (271)
```

Hence

```text
sum_(m,n) w_m w_n
  ||f-tau_(log n-log m)f||_2^2
 <=4W_aD_a(f).                                          (272)
```

If `pi_a(n)=w_n/W_a`, then for every `epsilon>0`,

```text
(pi_a tensor pi_a){(m,n):
  ||f-tau_(log n-log m)f||_2>epsilon||f||_2}
 <=4D_a(f)/(epsilon^2 W_a||f||_2^2).                    (273)
```

Thus near-invariance under a positive proportion of prime reflections is not an extra heuristic:
it forces near-invariance under the corresponding weighted family of logarithmic prime ratios.
But `(270)` also records the missing hypothesis.  A large negative normalized Hankel edge alone
does not make `D_a/(W_a||f||^2)` small; the prime-mass reserve on the right can remain macroscopic.

#### Proof

Each `R_t` is a self-adjoint unitary on `L^2(R)`, and the zero-extension form of `(9)` is

```text
P_a(f,f)=sum_n w_n<f,R_(log n)f>.
```

Expanding the squares proves `(269)`, and insertion of the assumed edge inequality proves `(270)`.
The reflection product is direct substitution.  The triangle inequality followed by
`(u+v)^2<=2u^2+2v^2` proves `(271)`.  Summing first in `m` and then in `n` proves `(272)`;
weighted Markov proves `(273)`.

The square identity and the fact that two reflections compose to a translation are classical.
Candidate-new content is their exact Suzuki placement: `(270)` turns the Xi-required normalized
prime surplus into a finite reserve for the physical reflection Dirichlet energy, while
`(272)--(273)` identifies logarithmic prime-ratio rigidity as the precise global coherence forced
when that reserve is small.  Internal search found prime autocorrelation and a different
divisor-horizontal reflection energy, but no physical reflection-square or log-ratio translation
budget for Suzuki's half-interval carrier.

The fixed-profile endpoint asymptotic gives a hostile test of whether the reserve can be controlled
by the prime number theorem.  Fix `L>0`, take `a>L`, put

```text
u_(a,n)=2a-log n,
mu_(a,L)=e^(-a) sum_(0<=u_(a,n)<=2L) w_n delta_(u_(a,n)). (274)
```

The prime number theorem gives the already-known weak limit

```text
mu_(a,L) -> nu_L,          dnu_L(u)=e^(-u/2)1_[0,2L]du. (275)
```

On `L^2(0,L)`, with `g` extended by zero, define the rescaled physical boundary compressions

```text
(B_(a,L)g)(x)=int g(u-x)dmu_(a,L)(u),
(A_(a,L)g)(x)=e^(-a)int_0^L K_reg(2a-x-y)g(y)dy,
(B_(infinity,L)g)(x)=e^(-x/2)int_0^L e^(-y/2)g(y)dy.   (276)
```

Here `B_(a,L)` is exactly the endpoint-window compression of `e^(-a)P_a`, `A_(a,L)` is that of
`e^(-a)H_(a,infinity)`, and `B_(infinity,L)` is the rank-one Laplace limit common to both.

#### Theorem AB — PNT cancellation is strong but never uniform

As `a->infinity`,

```text
B_(a,L) -> B_(infinity,L) strongly,
A_(a,L) -> B_(infinity,L) in operator norm,
Z_(a,L):=B_(a,L)-A_(a,L) ->0 strongly.                  (277)
```

Nevertheless, if

```text
M_(a,L)(x)=mu_(a,L)((x,x+L)),
```

then for every `a`

```text
||Z_(a,L)|| >= ||M_(a,L)||_(L^2(0,L))/sqrt(L),          (278)
```

and therefore

```text
liminf_(a->infinity)||Z_(a,L)||
 >=2(1-e^(-L/2))sqrt((1-e^(-L))/L)>0.                  (279)
```

Thus leading prime--Laplace cancellation holds for every fixed boundary profile but fails
maximally as a uniform operator statement.  The centered prime discrepancy has high-frequency
almost-periodic revivals at every finite aperture.

#### Proof

Weak convergence `(275)`, compact support, and bounded total masses imply pointwise convergence of
the Fourier transforms with a uniform bound.  Plancherel and dominated convergence therefore give
strong convergence of the full-line convolution operators, hence of their reflected interval
compressions `B_(a,L)`.  The explicit regular kernel gives, uniformly for `0<=u<=2L`,

```text
e^(-a)K_reg(2a-u)
 =e^(-u/2)-e^(-6a+5u/2)/(1-e^(-4a+2u)),                (280)
```

so the second convergence in `(277)` holds even in Hilbert--Schmidt norm.

Fix `a`.  The measure `mu_(a,L)` has finitely many atoms `u_1,...,u_N`.  Simultaneous Dirichlet
approximation supplies `xi_k->infinity` with `exp(i xi_k u_j)->1` for every `j`.  For

```text
g_k(y)=L^(-1/2)exp(i xi_k y)1_(0,L)(y),
```

one has in `L^2(0,L)`

```text
B_(a,L)g_k
 -L^(-1/2)exp(-i xi_k x)M_(a,L)(x) ->0.
```

The integral-kernel operator `A_(a,L)` is compact, while `g_k` converges weakly to zero, so
`A_(a,L)g_k->0`.  This proves `(278)`.  From `(275)`, for almost every `x`,

```text
M_(a,L)(x)->int_x^(x+L)e^(-u/2)du
             =2(1-e^(-L/2))e^(-x/2).
```

Uniform boundedness of the total masses gives `L^2` convergence by dominated convergence.  Taking
the norm proves `(279)`.

Strong-not-norm convergence of atomic convolution operators to an absolutely continuous limit is
a classical Fourier phenomenon, and the PNT boundary measure `(275)` is corpus-known.  Candidate-
new content is the exact Suzuki conclusion `(277)--(279)`: the physical prime and archimedean
endpoint Hankel compressions have the same rank-one Laplace strong limit, yet their centered
difference stays uniformly nonzero in operator norm.  Targeted search found general
multiplicative-Hankel and Helson operator theory, but no von-Mangoldt endpoint-window theorem or
this Suzuki prime--archimedean topology split.  Specialist priority review remains required.

This does **not** construct the normalized edge required by Theorem W.  The revival vectors in the
proof can have large common finite-part Cauchy energy; Theorem Z already shows the analogous
localization penalty.  The literal interior problem is now more precise: compare the centered
strongly-null-but-nonnorm-null family `Z_(a,L)` with the rescaled common form, rather than compare
prime and archimedean masses separately.  Fixed-profile PNT asymptotics and unweighted operator
norm both use the wrong topology for deciding `77/85`.

### 14.20 Macroscopically safe negative shifts are source-blind

The operator-norm recurrence in Theorem AB is not automatically visible to Suzuki's two
exponential sources.  At a negative shift of the same `e^a` scale as the endpoint prime mass,
strong prime--archimedean cancellation is enough to identify both source resolvents whenever the
shift stays a fixed `e^a` distance below both parity floors.  Hence a macroscopic negative-shift
survivor must itself be singular: it must hug at least one parity floor at that scale.

Let `A_(e,a)=T_a+H_a` and `A_(o,a)=T_a-H_a`, and let `U_a` be the boundary-coordinate unitary

```text
(U_af)(z)=f(a-z),              0<z<a.
```

Normalize the literal half-interval sources by

```text
s_(e,a)=e^(-a)U_a(cosh),       s_(o,a)=e^(-a)U_a(sinh).
```

After extension by zero to `L^2(0,infinity)`,

```text
s_(e,a),s_(o,a) -> s,          s(z)=e^(-z)/2,
||s||_2^2=1/8.                                           (281)
```

#### Theorem AC — macroscopic safe-shift source blindness

Let `a_j->infinity` and let `lambda_j` lie below both parity floors.  Assume

```text
-e^(-a_j)lambda_j -> c in (0,infinity)                  (282)
```

and that for some `delta>0` both shifted parity forms obey

```text
A_(e,a_j)-lambda_j I >=delta e^(a_j)I,
A_(o,a_j)-lambda_j I >=delta e^(a_j)I.                  (283)
```

Then the literal responses satisfy

```text
e^(-a_j)E_(a_j,lambda_j) ->1/(8c),
e^(-a_j)O_(a_j,lambda_j) ->1/(8c),
kappa_(a_j,lambda_j) ->0.                               (284)
```

In particular no such family reaches the positive Xi wall.  Therefore every Xi-admitted family
with `(282)` must, after passage to a subsequence, satisfy the macroscopic floor-hugging law

```text
min{alpha_(e,a_j)-lambda_j,alpha_(o,a_j)-lambda_j}
   =o(e^(a_j)).                                         (285)
```

For a **full Xi-identifying Route-G family**, even that singular alternative is impossible.  The
imaginary-interval target implies RH by Theorem I, so Weil positivity gives
`alpha_(e,a),alpha_(o,a)>=0` at every aperture.  If the negative part of the shift were not
submacroscopic, a subsequence would satisfy `(282)` and `(283)`, contradicting `(284)`.  Hence every
successful complete Suzuki family necessarily obeys

```text
max(0,-lambda_a)=o(e^a).                                  (285a)
```

Thus macroscopic negative shifts can appear at the isolated first-jet level only by forcing a
macroscopic negative Weil floor, a condition incompatible with the RH conclusion of the complete
carrier.  They are class-completely dead as a Route-G closure mechanism.

#### Proof

On every compact boundary test `g in C_c^infinity(0,infinity)`, Theorem AB and the full PNT
boundary measure give

```text
e^(-a)U_aH_aU_a^*g ->0 in L^2(0,infinity).              (286)
```

The common difference channel sees only translations of length at most `a`, hence prime cutoff
`n<e^a` and polar growth `e^(a/2)`.  Its exact kernel decomposition therefore gives

```text
e^(-a)U_aT_aU_a^*g ->0 in L^2(0,infinity).              (287)
```

Equation `(286)` is the centered endpoint cancellation, not separate convergence of its two
`e^a`-sized terms.  Equation `(287)` is easier by a full exponential factor: the common channel
has only the half-aperture prime mass `O(e^(a/2))` on a fixed boundary test.

Put

```text
B_(sigma,j)=e^(-a_j)U_(a_j)(A_(sigma,a_j)-lambda_j I)U_(a_j)^*,
x_(sigma,j)=B_(sigma,j)^(-1)s_(sigma,a_j),
```

for `sigma=e,o`.  Coercivity `(283)` gives `||x_(sigma,j)||<=delta^(-1)||s_(sigma,j)||`.
Take a weakly convergent subsequence.  For every compact smooth `g`, self-adjointness, `(282)`,
and `(286)--(287)` give

```text
<x_(sigma,j),B_(sigma,j)g>=<s_(sigma,j),g>
   -> c<x_sigma,g>=<s,g>.
```

Thus every weak cluster point is `x_sigma=c^(-1)s`; uniqueness removes the subsequence.  Finally,

```text
e^(-a_j)E_(a_j,lambda_j)=<s_(e,a_j),x_(e,j)>,
e^(-a_j)O_(a_j,lambda_j)=<s_(o,a_j),x_(o,j)>.
```

Strong convergence of the sources and weak convergence of the solutions prove `(284)`.  If
`(285)` failed, a subsequence would satisfy `(283)`, contradicting `kappa_Xi>0`.

Fixed-aperture far-negative resolvent expansion and the free projective boundary are already in
the corpus.  They do not address the coupled scale `-lambda asymp e^a` where endpoint prime mass
also grows.  Candidate-new content is the cofinal source theorem `(281)--(285)`: strong
prime--archimedean cancellation plus a uniform macroscopic parity margin forces equality of the
two literal exponential responses and turns every surviving macroscopic negative shift into a
floor-hugging singularity.  Internal search found no such coupled aperture/shift theorem.

This closes the regular `-lambda asymp e^a` chart, not Suzuki.  The remaining negative-shift
possibilities at the first admission gate are submacroscopic shifts `-lambda=o(e^a)`, or
macroscopic shifts satisfying `(285)`.  For the complete Xi-identifying route, `(285a)` removes the
latter.  The live negative-shift scale is therefore strictly submacroscopic; it must still be
compared with Theorem Y's source-visible ground residue and Theorem X's edge-alignment alternatives.

### 14.21 Complete Xi identification forbids negative-shift recession at every scale

The submacroscopic region left by Theorem AC is still much too large.  For a complete Route-G
family it collapses to a bounded window.  This conclusion does not use another PNT asymptotic.  It
uses the zero-side Gram representation which is available after the putative complete family has
already implied RH, together with the exact exponential sources.

Put

```text
N_e(a)=||cosh||_L2(0,a)^2=sinh(2a)/4+a/2,
N_o(a)=||sinh||_L2(0,a)^2=sinh(2a)/4-a/2.              (288)
```

Thus

```text
(N_e(a)-N_o(a))/(N_e(a)+N_o(a))=2a/sinh(2a)->0.       (289)
```

Use the unitary parity lifts `U_+`,`U_-` from Section 14.15.  Under RH the restricted Weil form is
the zero-side Gram form

```text
<phi,A_(e,a)phi>=sum_gamma m_gamma |widehat(U_+phi)(gamma)|^2,
<phi,A_(o,a)phi>=sum_gamma m_gamma |widehat(U_-phi)(gamma)|^2. (290)
```

For the literal sources, elementary integration of the two exponentials gives, uniformly in every
real zero ordinate `gamma`,

```text
|widehat(U_+ cosh)(gamma)|^2,
|widehat(U_- sinh)(gamma)|^2
   <=2 cosh(a)^2/(1+gamma^2).                          (291)
```

With the convention of `(193)`, `M_0(1)=sum_gamma m_gamma/(1+gamma^2)<infinity`.  Hence the two
source Rayleigh means satisfy

```text
m_e(a):=<cosh,A_(e,a)cosh>/N_e(a) <=M_a,
m_o(a):=<sinh,A_(o,a)sinh>/N_o(a) <=M_a,
M_a:=2 cosh(a)^2 M_0(1)/N_o(a) ->4M_0(1).             (292)
```

#### Theorem AD — all-scale negative-recession obstruction

Let `a_j->infinity` and suppose a complete Suzuki family at shifts `lambda_j` identifies the Xi
target.  Then its negative parts `r_j=max(0,-lambda_j)` are bounded.  More precisely, along the
indices with `lambda_j<0`, put

```text
R_j=E_(a_j,lambda_j)/O_(a_j,lambda_j)
   =(1+kappa_(a_j,lambda_j))/(1-kappa_(a_j,lambda_j)),
R_Xi=(1+kappa_Xi)/(1-kappa_Xi).
```

Then

```text
limsup_j r_j <=4M_0(1)/(R_Xi-1)<16M_0(1)/77.          (293)
```

In particular every complete Xi-identifying Suzuki family obeys the strict all-scale recession
law

```text
sup_(j sufficiently large) max(0,-lambda_j)<infinity. (294)
```

#### Proof

Complete half-plane identification implies RH by Theorem I.  Therefore both parity operators in
`(290)` are nonnegative.  For a nonnegative self-adjoint operator `A`, a nonzero source `h` with
spectral mean `m=<h,Ah>/||h||^2`, and `r>0`, Jensen's inequality for the convex function
`x|->1/(x+r)` gives the exact sandwich

```text
||h||^2/(r+m) <= <h,(A+rI)^(-1)h> <= ||h||^2/r.       (295)
```

Apply the upper bound to the even response and the lower bound to the odd response.  Equations
`(288)` and `(292)` yield

```text
R_j<=N_e(a_j)/N_o(a_j) [1+M_(a_j)/r_j].               (296)
```

Whenever `R_jN_o(a_j)/N_e(a_j)>1`, rearrangement gives

```text
r_j<=M_(a_j)/[R_jN_o(a_j)/N_e(a_j)-1].                (297)
```

Target identification gives `R_j->R_Xi`; equations `(288)--(289)` give
`N_o/N_e->1`, and `(292)` gives `M_a->4M_0(1)`.  Taking the upper limit in `(297)` proves the first
inequality in `(293)`.  The unconditional target bound `kappa_Xi>77/85` gives
`R_Xi>81/4`, and hence the strict second inequality.  If the negative parts were unbounded, their
unbounded subsequence would contradict `(293)`.  This proves `(294)`.

The same argument without rearrangement shows the mechanism transparently.  If `r_j->infinity`,
both inequalities in `(295)` become asymptotic equalities uniformly because of `(292)`.  Thus

```text
E_(a_j,-r_j)~N_e(a_j)/r_j,
O_(a_j,-r_j)~N_o(a_j)/r_j,
kappa_(a_j,-r_j)->0,                                  (298)
```

regardless of how slowly `r_j` diverges relative to `e^(a_j)`.

Fixed-aperture Neumann collapse, the dyadic negative-shift scalar-jump obstruction, and the
existence of a bounded-below admissible schedule exactly under RH are already in the corpus.  None
proves `(293)`: they respectively keep the aperture fixed, use two far-negative shifts in a
different scalar quotient, or classify existence rather than the scale of every complete
Xi-producing family.  Generic spectral Jensen bounds are classical.  Candidate-new content is the
uniform literal-source Rayleigh law `(291)--(292)` and its all-scale Suzuki recession consequence
`(293)--(294)`.

This still does **not** kill Suzuki.  It collapses all negative complete-family schedules to a
fixed absolute window.  Bounded negative shifts, the zero shift, and positive floor-hugging shifts
remain possible; proving a cofinal positive admissible shift is already RH-strength.  The earliest
unconditional source problem is now unambiguously the finite-shift normalized-Hankel admission
problem, not any negative-shift escape chart.

### 14.22 Every negative shift bounded away from zero is asymptotically free

The bounded window left by Theorem AD still contains an apparent continuum of negative shifts.
The zero-side Gram geometry removes all of it except the singular endpoint `lambda->0`.  Unlike the
first-moment Jensen argument, the next theorem uses the full expanding-interval exponential Gram
matrix and therefore sees every fixed positive resolvent mass.

Under RH let

```text
S_a:D(S_a) subset L2(-a,a)->ell2(Gamma),
(S_af)_gamma=sqrt(m_gamma) widehat f(gamma),
A_a=S_a^*S_a.                                           (299)
```

Here `Gamma` is the set of distinct real Xi ordinates and `m_gamma` their multiplicities.  Smooth
compactly supported functions form a dense domain, and `(299)` is exactly the zero-side restricted
Weil form.  Put

```text
h_(e,a)=U_+(cosh)/sqrt(N_e(a)),
h_(o,a)=U_-(sinh)/sqrt(N_o(a)),
u_(sigma,a)=S_a h_(sigma,a).                            (300)
```

#### Theorem AE — expanding-frame annihilation of fixed negative shifts

Let `a_j->infinity` and `r_j>0` with `inf_j r_j>0`.  Then, for `sigma=e,o`,

```text
r_j <h_(sigma,a_j),(A_(sigma,a_j)+r_j I)^(-1)
       h_(sigma,a_j)> ->1.                              (301)
```

Consequently

```text
r_j E_(a_j,-r_j)/N_e(a_j)->1,
r_j O_(a_j,-r_j)/N_o(a_j)->1,
kappa_(a_j,-r_j)->0.                                   (302)
```

Thus every complete Xi-identifying Route-G family necessarily satisfies the sharp negative-end
law

```text
max(0,-lambda_j)->0.                                   (303)
```

#### Proof

We give the expanding-frame estimate because this is where a false uniform-frame argument would
otherwise enter.  For a closed densely defined `S` and `A=S^*S`, the push-through identity gives

```text
1-r<h,(A+rI)^(-1)h>
 =<Sh,(SS^*+rI)^(-1)Sh>                                (304)
```

for every unit `h in D(S)`.  It is enough to prove that the right side tends to zero for the two
vectors in `(300)`.

Fix a finite symmetric set `Gamma_T={gamma:|gamma|<=T}` and let `P_T` be its coordinate
projection.  For a finitely supported vector `c`,

```text
S_a^*c(x)=sum_gamma sqrt(m_gamma)c_gamma e^(-i gamma x),
<e^(-i gamma x),e^(-i eta x)>_L2(-a,a)
 =2sin(a(eta-gamma))/(eta-gamma).                       (305)
```

Distinctness of the finitely many low frequencies gives a constant `D_T<infinity` such that

```text
||S_a^*P_Tc||^2 >=(2a-D_T)||P_Tc||^2.                  (306)
```

The low--high coupling is bounded independently of aperture.  Indeed `(305)`, the
Riemann--von Mangoldt bound, and reciprocal-square summability give

```text
|<S_a^*P_Tc,S_a^*(1-P_T)c>|
 <=C_T||P_Tc||||(1-P_T)c||,                            (307)

C_T^2
 <=4 sum_(gamma in Gamma_T) m_gamma
       sum_(|eta|>T) m_eta/(eta-gamma)^2 <infinity.
```

No separation estimate between high zeros is used.  Keeping the resolvent mass on the high block
and applying Young's inequality to `(307)`, uniformly for `r>=r_0>0`, yields for all sufficiently
large `a`

```text
||S_a^*c||^2+r||c||^2
 >=k_(a,T)||P_Tc||^2+(r/2)||(1-P_T)c||^2,
k_(a,T)>=2a-D_T-2C_T^2/r_0 ->infinity.                 (308)
```

The variational formula for the inverse of the positive form in `(308)` therefore gives

```text
<u,(S_aS_a^*+rI)^(-1)u>
 <=||P_Tu||^2/k_(a,T)+2||(1-P_T)u||^2/r.               (309)
```

The source estimate `(291)` and the exact norms `(288)` imply a constant `C` independent of all
large `a` such that

```text
|(u_(sigma,a))_gamma|^2<=C m_gamma/(1+gamma^2).        (310)
```

For fixed `T`, the first term of `(309)` tends to zero as `a->infinity`.  The second is at most

```text
(2C/r_0) sum_(|gamma|>T) m_gamma/(1+gamma^2),          (311)
```

which tends to zero as `T->infinity`.  Equations `(304)` and `(309)--(311)` prove `(301)`.
The unitary parity decomposition identifies the two full-interval responses with `E/N_e` and
`O/N_o`; then `(289)` proves `(302)`.

If `(303)` failed, some subsequence of negative shifts would have `r_j>=r_0>0`, and `(302)` would
contradict convergence to `kappa_Xi>77/85`.  This proves `(303)`.

The argument is robust to multiplicity because `(299)` uses one distinct ordinate coordinate with
weight `sqrt(m_gamma)`.  It also avoids the false claim that the full zero exponential system has
a uniform lower frame bound: only one fixed finite block receives the growing `2a` diagonal, while
the moving high block is controlled by the literal source's summable tail.

Generic push-through identities, finite exponential Gram asymptotics, and the zero-counting tail
bound are classical.  The corpus contains fixed-aperture far-negative collapse, weak escape at
`lambda=0`, and RH equivalence for vanishing admissible shifts, but no expanding-aperture theorem
for every mass `r>=r_0`.  Candidate-new content is their exact synthesis in `(299)--(303)`, which
removes the entire negative finite-shift window from complete Suzuki families.

This still does **not** kill Suzuki.  The singular interface `lambda->0^-` is precisely where the
high-zero block in `(308)` loses its coercive `r/2` term, so the proof fails for a structural
reason, not a loose estimate.  Zero shift, vanishing negative shifts, and positive floor-hugging
remain the only complete-family scales.  The source-normalized Hankel/pointed-occupancy theorem at
that zero-mass interface is now the unique negative-side frontier.

### 14.23 The zero-mass survivor has inverse-aperture width

The loss of a fixed high-block mass at `r->0` is quantitative.  Classical local zero counting still
allows a cutoff whose cross-block Gram coupling grows only polylogarithmically.  Combining that
cutoff with the exact source tail shows that most vanishing shifts are free as well.

Let

```text
delta(T)=sum_(|gamma|>T) m_gamma/(1+gamma^2).           (312)
```

Riemann--von Mangoldt counting and partial summation give

```text
delta(T)=O(log(T)/T).                                  (313)
```

For every sufficiently large `T`, the unit-window bound
`sum_(t<|gamma|<=t+1)m_gamma=O(log(t+2))` permits a symmetric cutoff `b_T in [T,T+1]` whose distance
from every ordinate is at least `c/log T`.  Let `P_T` now project onto `|gamma|<b_T`.  Splitting
both sides of each boundary into the near unit window, unit distance shells, and the far tail gives

```text
C_T^2
 :=4 sum_(|gamma|<b_T) m_gamma
       sum_(|eta|>b_T) m_eta/(eta-gamma)^2
 =O((log T)^4).                                        (314)
```

For clarity, the near-boundary contribution is `O((log T)^4)` because each unit window contains
`O(log T)` ordinates with multiplicity and the chosen gap is `Omega(1/log T)`.  For unit shells at
distances `j,k>=1`, the contribution is
`O((log T)^2 sum_(j,k<=2T)(j+k)^(-2))=O((log T)^3)`; ordinates beyond `2T` contribute
`O(N(T)delta(2T))=O((log T)^2)`.  Opposite signs are farther apart.  This proves `(314)` without a
zero-spacing hypothesis.

#### Theorem AF — quantitative vanishing-shift boundary layer

Let `a_j->infinity`, `r_j->0+`, and assume

```text
a_j r_j/(1+|log r_j|)^4 ->infinity.                    (315)
```

Then the free-response conclusions `(301)--(302)` still hold.  Consequently every complete
Xi-identifying family satisfies, on its negative-shift indices,

```text
r_j=max(0,-lambda_j)=O((1+log a_j)^4/a_j).             (316)
```

#### Proof

In `(308)--(311)` choose `T_j=r_j^(-2)` and the cutoffs above.  Equations `(313)` and `(310)` give

```text
||(1-P_(T_j))u_(sigma,a_j)||^2/r_j
 =O(delta(T_j)/r_j)
 =O(r_j|log r_j|)->0.                                  (317)
```

The cross penalty in the low-block coercivity is, by `(314)`,

```text
C_(T_j)^2/r_j=O((1+|log r_j|)^4/r_j)=o(a_j)            (318)
```

under `(315)`.  Thus `k_(a_j,T_j)->infinity` in `(308)`.  The low source norms remain uniformly
bounded by `(292)`, so `(309)` tends to zero.  Equations `(304)` and `(289)` prove the free
response.

If the quotient `a_jr_j/(1+|log r_j|)^4` were unbounded along a complete target family, a
subsequence would satisfy `(315),` contradicting `kappa->kappa_Xi`.  It is therefore bounded.
When `r_j<=1/a_j`, `(316)` is immediate; when `r_j>1/a_j`, one has
`|log r_j|<log a_j`, and the same boundedness gives `(316)`.

The exponent four is not claimed sharp.  It records the strongest bound obtained from local
Riemann--von Mangoldt counting alone, without pair-correlation, simplicity, or a minimum zero gap.
Generic nonharmonic Fourier estimates are classical.  Candidate-new content is the literal Suzuki
source/resolvent synthesis `(315)--(316)`, which turns the qualitative zero-mass survivor into an
explicit inverse-aperture polylogarithmic boundary layer.

This does **not** cross zero.  At `r=O((log a)^4/a)` the mass term can be of the same order as the
worst low--high cancellation capacity allowed by classical zero counting.  Improving `(316)` to
`o(1/a)` or reaching `r=0` requires new information about clustered zero-exponential combinations
as seen by the specific boundary source, or a direct prime-side normalized-Hankel estimate.  That
is the hard frontier; repeating PNT leading terms or assuming zero spacing would be theatre.

### 14.24 The exact positive survivor is a mesoscopic odd hard-edge annulus

Theorems AE--AF do more than constrain the shift.  They identify the spectral geometry which must
survive inside the boundary layer.  Let `mu_(e,a)` and `mu_(o,a)` be the probability spectral laws
of the nonnegative parity operators at the unit sources `h_(e,a),h_(o,a)` from `(300)`.  For `r>0`
put

```text
x_(sigma,a)(r)
 =int_[0,infinity] r/(t+r) dmu_(sigma,a)(t)
 =r <h_(sigma,a),(A_(sigma,a)+rI)^(-1)h_(sigma,a)>.    (319)
```

Theorem AE at every fixed `r>0` gives `x_(sigma,a)(r)->1`.  Stieltjes uniqueness, or the elementary
bound `1-x(r)>=epsilon/(epsilon+r)mu([epsilon,infinity))`, therefore gives

```text
mu_(e,a),mu_(o,a) weakly ->delta_0.                    (320)
```

#### Theorem AG — target-forced mesoscopic odd mass

Let `a_j->infinity`, let `lambda_j=-r_j<0`, and suppose the complete Suzuki quotients identify the
Xi target.  Then

```text
limsup_j x_(o,a_j)(r_j) <=1/R_Xi<4/81,                (321)

limsup_j mu_(o,a_j)([0,r_j])<8/81.                    (322)
```

Consequently, for every fixed `epsilon>0`,

```text
liminf_j mu_(o,a_j)((r_j,epsilon))>73/81.              (323)
```

The outer edge may itself shrink.  If `epsilon_j->0+` and

```text
a_j epsilon_j/(1+|log epsilon_j|)^4 ->infinity,
```

then

```text
mu_(o,a_j)([epsilon_j,infinity))->0,
liminf_j mu_(o,a_j)((r_j,epsilon_j))>73/81.            (323a)
```

In particular one may take `epsilon_j=a_j^(-1/2)`.  The surviving packet is therefore confined to
the explicit shrinking annulus `(r_j,a_j^(-1/2))`, not merely to an unspecified neighborhood of
zero.

More generally, for every fixed `L>=0`,

```text
limsup_j mu_(o,a_j)([0,Lr_j])
 <=(L+1)/R_Xi<4(L+1)/81.                              (324)
```

Thus a successful negative Suzuki family requires a literal odd-source spectral layer which
collapses to zero in absolute energy by `(320)`, remains above its own resolvent mass scale by
`(322)--(324)`, and carries more than `73/81` of the total probability in every fixed hard-edge
window `(r_j,epsilon)`.

#### Proof

Equation `(319)` and the parity responses give

```text
E_(a,-r)/O_(a,-r)
 =[N_e(a)/N_o(a)] x_(e,a)(r)/x_(o,a)(r).               (325)
```

Since `0<=x_e<=1`, target convergence, `(289)`, and `(325)` imply the first inequality in `(321)`.
The strict constant uses `R_Xi>81/4`.

On `[0,Lr]` the Stieltjes multiplier obeys `r/(t+r)>=1/(L+1)`.  Equation `(324)` follows from
`(321)`; `L=1` gives `(322)`.  Finally `(320)` makes
`mu_(o,a_j)([epsilon,infinity))->0` for every fixed `epsilon` which is not an atom of `delta_0`,
and subtracting this tail and `[0,r_j]` from total mass proves `(323)`.  To prove `(323a)`, apply
Theorem AF's estimate with the independent probe mass `epsilon_j` in place of the selected shift.
It gives `x_(o,a_j)(epsilon_j)->1`; since
`1-x_o(epsilon)>=mu_o([epsilon,infinity))/2`, the moving upper tail vanishes.  Subtract `(322)`
again.

The constants are target-sharp at the information level used: they come only from
`R_Xi>81/4`, the fact that the even Stieltjes factor is at most one, and the threshold value
`r/(r+r)=1/2`.  Improving them requires absolute information about the even response, not another
inequality on the odd channel.

Weak convergence to a hard edge and elementary Stieltjes band bounds are classical.  Candidate-new
content is the Suzuki conjunction `(320)--(324)`: the complete target forces a quantitatively
macroscopic odd spectral packet into a vanishing interval strictly above the moving shift scale.
This is the strongest positive survivor exposed by the negative-shift no-go.  It replaces the
phrase “singular zero-mass behavior” by one falsifiable source theorem.

### 14.25 The complete parity-transport cost condenses at the zero-mass edge

The annulus in Theorem AG is a one-channel statement.  It is not by itself a no-go: a moving
Stieltjes scale can always sit below a collapsing atom.  The updated source-superselection paper
already identifies the correct coupled invariant at finite shifts as the integrated even--odd
resolvent hazard.  The negative zero-mass reduction above supplies new information about that
invariant: its entire Xi cost must be paid inside a shrinking shift interval.

For `sigma=e,o`, write

```text
g_(sigma,a)(s)=int_[0,infinity] 1/(t+s) dmu_(sigma,a)(t)
              =x_(sigma,a)(s)/s,

v_(sigma,a)(s)
 = [int_[0,infinity] s t/(t+s)^2 dmu_(sigma,a)(t)]
      /x_(sigma,a)(s) in [0,1].                         (326)
```

Thus `v_sigma` is the posterior hardness of the source spectrum after Stieltjes tilting at scale
`s`.  Put

```text
F_a(s)=[N_e(a)/N_o(a)] x_(e,a)(s)/x_(o,a)(s)
      =E_(a,-s)/O_(a,-s).
```

Differentiation under the spectral integral gives the exact logarithmic flow

```text
d/d(log s) log F_a(s)=v_(e,a)(s)-v_(o,a)(s).           (327)
```

#### Theorem AH — zero-edge parity-transport condensation and capacity slack

Let `a_j->infinity`, let `lambda_j=-r_j<0`, and suppose the complete Suzuki quotients identify the
Xi target.  Let `epsilon_j->0+` be any independent free probe satisfying

```text
a_j epsilon_j/(1+|log epsilon_j|)^4 ->infinity.        (328)
```

Then `r_j<epsilon_j` eventually and

```text
int_(r_j)^(epsilon_j)
 [v_(o,a_j)(s)-v_(e,a_j)(s)] ds/s
 ->log R_Xi>log(81/4).                                  (329)
```

More precisely, the exact capacity-slack identity is

```text
log(epsilon_j/r_j)-log[F_(a_j)(r_j)/F_(a_j)(epsilon_j)]
 =int_(r_j)^(epsilon_j)
    [(1-v_(o,a_j)(s))+v_(e,a_j)(s)] ds/s >=0.          (330)
```

Consequently every such free probe obeys

```text
liminf_j epsilon_j/r_j >=R_Xi>81/4,
limsup_j r_j/epsilon_j <=1/R_Xi<4/81.                  (331)
```

At asymptotic equality in `(331)`, the nonnegative slack in `(330)` vanishes: in logarithmic
mean across the whole transition layer, the odd posterior spectrum lies above the running scale
and the even posterior spectrum lies below it.  Thus minimal-width transport requires almost
perfect paired parity separation, not merely the odd packet from Theorem AG.

The same law has the additive shift form used in the source-superselection paper.  Put

```text
mathfrak h_a(-s)
 = [int (t+s)^(-2)dmu_(e,a)(t)]/g_(e,a)(s)
   -[int (u+s)^(-2)dmu_(o,a)(u)]/g_(o,a)(s)
 =[v_(o,a)(s)-v_(e,a)(s)]/s.                           (332)
```

If `mathcal C_a(s)` and `mathcal D_a(s)` are respectively the positive and negative Jordan masses
of

```text
(u-t)/[(t+s)^2(u+s)^2]
  dmu_(e,a)(t)dmu_(o,a)(u),
```

then

```text
mathfrak h_a(-s)
 =[mathcal C_a(s)-mathcal D_a(s)]/[g_(e,a)(s)g_(o,a)(s)]. (333)
```

Equations `(329)` and `(333)` prove that the complete credit-minus-debt cost `log R_Xi` is paid
inside the vanishing additive interval `(-epsilon_j,-r_j)`.  In particular

```text
sup_(r_j<s<epsilon_j) max(0,mathfrak h_(a_j)(-s))
 >=[log R_Xi+o(1)]/(epsilon_j-r_j).                    (334)
```

Taking `epsilon_j=a_j^(-1/2)` forces a hazard peak of order at least `sqrt(a_j)`.  Taking any
`epsilon_j=L_j(1+log a_j)^4/a_j` with `L_j->infinity` forces a peak at least
`(log R_Xi+o(1))a_j/[L_j(1+log a_j)^4]`.  A successful negative branch therefore cannot be a
bounded finite-shift excursion squeezed toward zero: its literal source-pointed parity transport
must become singular at essentially the inverse-aperture scale.

#### Proof

The derivative of `x_sigma` is

```text
x_sigma'(s)=int t/(t+s)^2 dmu_sigma(t),
```

so `(326)` gives `d log x_sigma/d log s=v_sigma`.  The aperture norms in `F_a` do not depend on
`s`; subtraction proves `(327)`.  Integration from `r_j` to `epsilon_j` gives

```text
int_(r_j)^(epsilon_j)(v_o-v_e)ds/s
 =log[F_(a_j)(r_j)/F_(a_j)(epsilon_j)].                (335)
```

Target identification gives `F_(a_j)(r_j)->R_Xi`.  Theorem AF applied to the independent probe
`epsilon_j` gives `x_e(epsilon_j),x_o(epsilon_j)->1`, while `(289)` gives `N_e/N_o->1`; hence
`F_(a_j)(epsilon_j)->1`.  This proves `(329)`.  Subtract `(335)` from
`log(epsilon_j/r_j)=int ds/s` and use `0<=v_e,v_o<=1` to obtain `(330)--(331)`.

For `(332)`, differentiate `g_sigma`; for `(333)`, put the two fractions over the common product
denominator and use Fubini.  The numerator is `u-t`, so its Jordan split has the stated
credit--debt orientation.  Integration is again `(335)`.  The supremum bound `(334)` follows by
comparing the integral of the positive part with interval length.

The differential hazard identity and its product-measure Jordan split are already present in the
updated source-superselection paper and are not claimed again.  Candidate-new content is their
joint localization by Theorems AF--AG: every complete negative family condenses the full
`log R_Xi` cost at the zero-mass edge, the exact capacity slack `(330)`, and the forced
inverse-aperture hazard blow-up `(334)`.

The capacity law is sharp at the information level used.  For any `R>2`, `r_j->0`, and
`r_j/epsilon_j->0`, the abstract one-dimensional laws

```text
mu_(e,j)=delta_0,
mu_(o,j)=delta_((R-1)r_j)                               (336)
```

satisfy `F_j(r_j)=R`, converge weakly to `delta_0`, put all odd mass in
`(r_j,epsilon_j)`, and have `F_j(epsilon_j)->1`.  Hence neither weak hard-edge collapse, the odd
annulus, nor generic Stieltjes transport can retire Suzuki.  The remaining theorem must use the
literal prime--Gamma coupling between the two parity laws.

### 14.26 Exact paired source energy does not close the condensed layer

The zero-side source formula contains one further literal coupling which the abstract model
`(336)` omits.  Write `A=sinh(a)`, `B=cosh(a)`.  Direct integration gives

```text
widehat(U_+ cosh)(gamma)
 =sqrt(2)[A cos(gamma a)+gamma B sin(gamma a)]/(1+gamma^2),

widehat(U_- sinh)(gamma)
 =i sqrt(2)[B sin(gamma a)-gamma A cos(gamma a)]/(1+gamma^2). (337)
```

The cross terms cancel after squaring and adding.  If

```text
Q_e(a)=<cosh,A_(e,a)cosh>,
Q_o(a)=<sinh,A_(o,a)sinh>,
```

then the exact paired Rayleigh budget is

```text
Q_e(a)+Q_o(a)
 =2sinh(a)^2 M_0(1)
  +2 sum_gamma m_gamma sin(gamma a)^2/(1+gamma^2).      (338)
```

In particular

```text
2sinh(a)^2M_0(1)<=Q_e(a)+Q_o(a)<=2cosh(a)^2M_0(1),
m_e(a)+m_o(a)->4M_0(1).                                (339)
```

#### Theorem AI — target scale versus literal odd Rayleigh energy

Under the hypotheses of Theorem AH,

```text
liminf_j m_o(a_j)/r_j >=R_Xi-1>77/4.                  (340)
```

#### Proof

Equations `(337)--(338)` follow from the two elementary antiderivatives and

```text
[A cos theta+gamma B sin theta]^2
 +[B sin theta-gamma A cos theta]^2
 =(1+gamma^2)[A^2+sin(theta)^2].
```

The bounds in `(339)` use `0<=sin^2<=1`; `(288)` and `N_e/N_o->1` give the limit.  Jensen's lower
resolvent bound gives

```text
x_(o,a_j)(r_j)>=r_j/[r_j+m_o(a_j)].
```

Equation `(321)` gives `limsup x_o<=1/R_Xi`; rearrangement proves `(340)`.

This exact paired energy is genuine literal-source information, but it still does not close the
layer.  A probability law may place vanishing mass at an energy tending to infinity and thereby
carry any prescribed first moment while leaving every Stieltjes factor at scales `O(r_j)`
unchanged.  Thus `(338)--(340)` eliminate countermodels with vanishing total Rayleigh energy but
do not eliminate `(336)` after an asymptotically invisible high-energy correction.  Any successful
no-go needs a source-specific uniform-integrability or relative-Hankel theorem, not another finite
moment identity.

The Fourier algebra and Jensen inequality are classical.  Candidate-new content is the exact
literal parity sum `(338)`, its asymptotic conservation law `(339)`, and its placement against the
condensed Suzuki scale in `(340)`.  This is a proved constraint and a proved failure of the
first-moment closure attempt, not a claim that Route G is dead.

### 14.27 Conjecture loop and novelty correction

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
    original source-to-limit problem.  After first-defect source admission, the remaining analytic
    theorem is fixed-anchor pointed convergence `(173)` for the selected shifted family; neither
    eigenvalue-set convergence nor generic strong-resolvent language supplies its cyclic vector
    weights.  Section 14.15 isolates the still-earlier admission wall.
46. **Suzuki's original fixed defect anchor should converge strongly to the global kernel at `i`
    -- failed.**  Theorem Q proves its norm diverges before normalization and its normalized vector
    converges weakly to zero in the global Weil embedding.
47. **Impedance calibration restores a regular vector limit -- failed.**  It calibrates normalized
    spectral probabilities only.  Every bounded exponential base, including the calibrated bases
    and base `i`, obeys the same weak-escape mechanism.
48. **Fixed-anchor weak escape kills its scalar probability -- failed.**  As in Theorems L--M,
    varying projections can retain mass through rank excess or sub-resolution rotation.  Theorem Q
    forces singularity but does not exclude it.
49. **Suzuki's clean one-to-one extension-eigenvalue convergence supplies the missing fixed law --
    failed.**  Stable finite-rank local projections paired with the weakly escaping fixed anchor
    have zero limiting mass.  Any successful fixed-anchor form of the conjecture must include
    spectral pollution/rank growth or projection rotation, not merely support convergence.
50. **The fixed-anchor probability target is still divisor-fitted -- failed.**  The finite Laplace
    averages `(191)` source-declare its global vector; under RH they converge at the exponential
    rate `(193)` and have exactly the probability `(169)`.
51. **The remaining fixed law is an unbounded boundary-moment problem -- failed.**  Theorem S
    reduces it to the bounded resolvent observable `(199)` on one positive uniqueness set.
52. **This bounded transform follows from abstract strong-resolvent convergence -- failed.**  Its
    cyclic vectors weakly escape by Theorem Q.  Strong-resolvent convergence tests fixed vectors,
    not this moving pointed state; singular source control remains essential.
53. **Finite restriction of the screw metric gives an exact boundary-free correlation window --
    failed.**  The fixed deficiency vector has full interval support.  Only compactly supported
    test vectors enjoy a pre-return translation window, and Theorem Q excludes a regular limit of
    the cyclic anchor.
54. **The odd pencil is automatically the derivative companion of the even pencil -- failed.**
    Equation `(202)` is equivalent pole by pole to flat Nevanlinna weights.  That is the missing
    Jacobian theorem, not an algebraic consequence of the pencil definitions.
55. **The fixed law is intrinsically cyclic-vector data -- failed.**  Equations `(203)--(209)`
    replace it exactly by the compactified spectral-shift occupancy of the two canonical
    extensions, using only their interlacing eigenvalues.
56. **One canonical extension spectrum should determine that occupancy -- failed.**  With a fixed
    pole sequence, every choice of one zero in each pole gap produces a different normalized
    meromorphic Herglotz function.  The opposite extension is the missing datum.
57. **Spectral overcrowding makes every eigenvalue-only invariant useless -- failed.**  In `(206)`
    a polluted pole--zero pair contributes only its compactified gap length.  Arbitrarily many
    nearly cancelling pairs can disappear while a nonzero occupancy limit survives.
58. **Weak anchor escape kills the paired spectral-shift invariant -- failed.**  A weakly escaping
    rank-one channel can retain trace and spectral-shift mass.  The escape proves singularity, not
    vanishing of `(208)`.
59. **Strong resolvent convergence of the two extensions supplies `(208)` -- failed.**  Strong
    convergence does not control traces of moving rank-one resolvent differences; trace-norm or
    the exact hierarchy `(212)` is new source information.
60. **Even the first fixed-anchor occupancy moment has no source-selected schedule -- failed on
    every sufficiently large source-visible simple-even-ground aperture.**  The endpoint crossing
    `(214)--(215)` matches it without divisor fitting.  Source-visible simple odd ground remains a
    real parity obstruction.
61. **Matching that first occupancy moment closes the fixed law -- failed sharply.**  It is only
    `j=0` in `(212)`; Section 14.5 already supplies carriers with the same first moment and
    different higher moments.
62. **High-frequency overcrowding automatically kills the occupancy route -- failed without a
    regularity hypothesis.**  Phase cells can have extremely unequal compactified lengths.
    Theorem V kills exactly the locally flat inverse-speed regime; alternating phase-speed boundary
    layers remain possible.
63. **A smoothly distorted high clock could realize Xi occupancy -- failed class-completely.**
    Condition `(221)` forces the universal half-Lebesgue limit `(222)`, which has mass `81/170`
    above the unconditional Xi support wall while the target has none.
64. **The target hierarchy has no finite-window falsifier -- failed.**  Equations `(216)--(218)`
    force every low-energy paired gap length above `x=4/85` to vanish.  Any uniform positive source
    lower bound there retires Route G without identifying individual Xi zeros.
65. **Paired occupancy is the first unresolved Suzuki obstruction -- failed.**  It becomes relevant
    only after a cofinal shift passes the first Xi defect.  The literal bottom-cone/interior-
    excursion admission theorem remains earlier and unproved.
66. **The common Toeplitz channel might create the required cofinal parity bias -- failed.**
    Midpoint reflection and the exact exponential sources force its defect below `sech(a)` for
    every shift, equation `(229)`.
67. **A perturbative arithmetic Hankel correction can bridge the remaining defect -- failed.**
    The hyperbolic budget `(230)--(233)` forces the even-favouring negative normalized Hankel edge
    past `77/85-o(1)` on every admitted cofinal family.
68. **Strong indefiniteness of the raw Hankel carrier proves this edge -- failed.**  Infinite
    positive and negative index does not control the Rayleigh quotient after normalization by the
    common Toeplitz form.  The hard source quantity is `(225)`, not inertia of `H_a` alone.
69. **An arbitrary strong Hankel edge closes first-jet admission -- failed.**  Edge strength alone
    need not align with the exponential source vectors.  Equation `(239)` supplies an arbitrary
    near-edge arithmetic witness; Theorem X identifies the additional alignment forced only when
    an admitted edge is near its sharp minimum.
70. **No class-complete first-jet falsifier remains -- failed conditionally.**  Any uniform bound
    `inf spec K_(a,lambda)>-77/85+eta` over all cofinal admissible shifts kills Route G before the
    spectral-shift layer.  Proving or refuting this literal normalized-Hankel bound is now the
    earliest exact source problem.
71. **An admitted edge can approach its sharp threshold while both exponential sources avoid it --
    failed.**  The exact nonnegative slack decomposition `(246)` forces both source spectral laws
    to concentrate at the bottom edge whenever `r-r_*->0`; `(250)` turns this into a literal
    source-profile prime-correlation surplus.
72. **A simple normalized-Hankel bottom edge can attain the sharp Xi response -- failed.**  At
    target equality and `r=r_*`, both independent common-channel source vectors are bottom
    eigenvectors by `(251)`.  Exact saturation therefore requires bottom multiplicity at least two.
73. **This alignment law closes Suzuki -- failed.**  A maximal edge, a nonvanishing edge overshoot,
    or a near-minimal aligned edge all remain logically possible.  Even successful first-jet
    admission leaves the singular paired-occupancy hierarchy unproved.
74. **Maximal normalized-Hankel edge is a new independent admission mechanism -- failed.**
    Equations `(255)--(260)` identify it with the existing even ground-pole branch.  Source
    visibility, not the abstract edge, decides whether that pole admits the defect response.
75. **A uniform edge ceiling over every admissible shift is the exact Suzuki no-go -- failed as an
    equivalence.**  It is sufficient, but any strict even floor violates it near the floor even
    when the even ground is source-invisible.  Exact negative closure must exclude the visible
    ground-residue cone and every finite-shift source excursion.
76. **A tied parity floor automatically avoids maximal negative edge -- failed.**  Any even ground
    vector outside the odd ground kernel forces `r_lambda->1`.  Avoiding this pole contribution
    requires the kernel-incidence rigidity `(258)`, and that condition still does not control other
    relative near-kernel sequences.
77. **The first-prime seam's infinite negative index can be amplified by narrower bumps into the
    required edge -- failed.**  The prime reflection weight stays bounded while the common
    finite-part Cauchy energy grows as `log(1/eta)`.  The normalized quotient tends to zero by
    `(264)`.
78. **Arbitrarily large raw packet index implies many large relative eigenvalues -- failed.**  For
    every fixed packet dimension, the full signed packet compression of the relative Hankel form
    tends to zero as resolution increases.  Letting dimension and resolution co-vary is a different
    global multi-seam problem and is not supplied by inertia.
79. **One isolated prime seam can supply the cofinal `77/85` mechanism -- failed for the literal
    microlocal construction.**  A viable interior source must maintain common Cauchy energy
    comparable to a coherent all-prime reflection sum; it cannot be assembled from asymptotically
    isolated delta-Hankel packets.
80. **Delocalized multi-seam coherence has no exact positive structure -- failed.**  The
    reflection-square identity `(269)` makes unused prime mass an exact Dirichlet reserve, and
    `(271)--(273)` turn a small reserve into weighted approximate invariance under the logarithmic
    prime-ratio translations.  What remains open is proving that a Suzuki edge witness must have a
    small reserve.
81. **The fixed-profile PNT boundary cancellation is uniform on the endpoint profile space --
    failed sharply.**  The prime and archimedean boundary Hankel operators have the same rank-one
    Laplace strong limit, but their centered difference has the positive operator-norm lower bound
    `(279)` at every cofinal scale.  Finite atomic prime measures retain arbitrarily high-frequency
    simultaneous phase revivals.
82. **Those phase revivals construct the normalized `77/85` edge -- failed as an inference.**
    Operator norm in `L^2` ignores the common finite-part Cauchy energy.  The revival frequencies
    may be charged at a large logarithmic scale, exactly as localized seam packets are charged in
    Theorem Z.  The missing estimate is relative to `C_(a,lambda)`, not absolute norm of the
    centered prime--archimedean operator.
83. **Leading PNT asymptotics decide whether Suzuki is dead -- failed class-completely.**  Fixed
    profiles see strong cancellation, while aperture-dependent oscillatory profiles see nonuniform
    atomic recurrence.  Neither topology is the normalized form topology.  A genuine no-go must
    control the centered critical Mellin discrepancy against the common logarithmic form, uniformly
    on the source-visible finite-shift branch.
84. **A regular negative shift of endpoint-mass scale can convert the nonuniform prime recurrence
    into source admission -- failed.**  If `-lambda asymp e^a` and both parity coercivity margins
    remain comparable to `e^a`, Theorem AC shows the rescaled even and odd resolvent responses have
    the same limit `1/(8c)`.  Their defect tends to zero, not to `kappa_Xi`.
85. **This kills every macroscopic negative shift -- failed.**  It kills only the uniformly safe
    first-jet chart.  Any merely admitted `-lambda asymp e^a` family can hug a negative parity
    floor within `o(e^a)`, so rotating near-floor modes can defeat the weak source limit.
86. **That singular macroshift remains viable for the complete Route G -- failed.**  Full target
    identification implies RH and hence nonnegative parity floors.  It restores a uniform
    `e^a` coercivity margin and contradicts Theorem AC.  Every complete Suzuki family must satisfy
    the strict recession law `(285a)`; only submacroscopic negative shifts remain open.
87. **Submacroscopic negative recession remains a live complete-family mechanism -- failed
    class-completely.**  Under the RH conclusion forced by complete identification, the literal
    exponential sources have uniformly bounded parity Rayleigh means.  Spectral Jensen then makes
    every diverging negative shift asymptotically free at the first jet, however slowly it diverges
    relative to aperture.  Theorem AD gives the quantitative ceiling `(293)`.
88. **Theorem AD kills the remaining Suzuki family -- failed.**  It forces the negative part into
    a fixed absolute window, not to zero.  Bounded negative and zero shifts still face the genuine
    finite-shift normalized-Hankel/source-visibility problem, while positive admissibility is
    already RH-strength.  No shift asymptotic replaces that finite-window theorem.
89. **A fixed negative shift can retain singular pointed Xi mass -- failed class-completely.**
    The zero-side expanding Gram matrix gives every fixed finite ordinate block energy `2a`, while
    the literal boundary sources have a uniform reciprocal-square high-zero tail.  Theorem AE
    proves that every `-lambda>=r_0>0` family has free first defect, without any uniform frame bound
    on the full zero system.
90. **The expanding-frame proof extends through zero mass -- failed sharply.**  Its high-coordinate
    coercivity is exactly `r||(1-P_T)c||^2`.  When `r->0`, high zero clusters can cancel the finite
    block at vanishing price, and the argument supplies no bound.  This is the same singular
    pointed mechanism left by weak anchor escape, not a technical omission.  Complete negative
    schedules are forced to `lambda->0^-`, but that interface remains open.
91. **Any vanishing negative shift remains viable -- failed.**  Local Riemann--von Mangoldt
    counting supplies spectral cutoffs with reciprocal-square cross capacity `O(log^4 T)`, while
    the literal source tail is `O(log T/T)`.  Theorem AF kills every scale satisfying
    `ar/log^4(1/r)->infinity` and forces successful complete negative schedules into
    `r=O(log^4(a)/a)`.
92. **Classical zero counting closes the inverse-aperture boundary layer -- failed.**  At the
    remaining scale the vanishing resolvent mass and the worst low--high cluster cancellation have
    the same permitted order.  A further theorem needs source-sensitive cluster control or the
    prime-side relative Hankel bound; neither simplicity nor a guessed minimum zero gap is legal.
93. **The residual zero-mass singularity has no quantitative shape -- failed.**  Fixed-mass
    expanding-frame annihilation first forces both normalized source spectral laws weakly to
    `delta_0`.  Target ratio then forces less than `8/81` of the odd law below `r_a` and more than
    `73/81` into the shrinking annulus `(r_a,a^(-1/2))`.  Theorem AG is the exact mesoscopic
    hard-edge survivor.
94. **Weak hard-edge collapse itself kills the target -- failed.**  Weak convergence sees only the
    fixed scale `epsilon`; it is compatible with a macroscopic packet whose energy tends to zero
    while its ratio to `r_a` stays above one.  Closing Suzuki now means ruling out this literal
    source packet or proving it and then solving the paired occupancy hierarchy.
95. **The mesoscopic odd packet is already evidence that Suzuki is dead -- failed sharply.**  The
    one-atom laws `(336)` satisfy the target ratio, weak hard-edge collapse, the moving annulus,
    and free response at every outer probe with `r/epsilon->0`.  The packet is a necessary positive
    survivor, not a contradiction.  A no-go must use literal even--odd source coupling.
96. **The updated finite-shift parity-transport budget remains spread over a macroscopic shift
    interval -- failed for every complete negative family.**  Theorem AH condenses its entire
    cost `log R_Xi>log(81/4)` into `(-epsilon_a,-r_a)` for every free probe `epsilon_a->0`.
    Consequently its positive hazard is unbounded and reaches the inverse-aperture scale modulo
    the zero-counting polylogarithm.
97. **A shrinking interval can pay the Xi transport cost without a scale-capacity law -- failed.**
    The exact nonnegative slack `(330)` forces `epsilon_a/r_a>=R_Xi-o(1)`.  Near equality, odd
    posterior hardness and even posterior softness both saturate in logarithmic mean.  This is a
    paired spectral-separation obligation, not merely an odd mass bound.
98. **The literal paired Fourier energy excludes the sharp Stieltjes countermodel -- failed.**
    Equation `(338)` gives the exact source conservation `m_e+m_o->4M_0(1)` and target matching
    forces `m_o/r>=R_Xi-1`.  A vanishing high-energy mass can carry that finite first moment while
    remaining invisible at the condensed scale.  Closure therefore requires uniform
    integrability or the relative prime--Gamma Hankel estimate; finitely many source moments are
    structurally insufficient.

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
equivalence, source-impedance calibration, all-anchor weak-escape law, and fixed-source Laplace
rigidity `(163)--(200)`, together with the compactified two-extension spectral-shift and
smoothing-trace reduction `(201)--(215)`, the low-energy support/regular phase-mixing wall
`(216)--(223)`, and the source-specific Toeplitz `sech`/normalized-Hankel rapidity,
source-alignment, localization, reflection-rigidity, nonuniform-PNT, and negative-shift recession
walls `(224)--(325)`.
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
is known.  The unitary-character obstruction behind Theorem Q is elementary; the candidate-new
part is its application to every fixed and coalescing Suzuki defect base and the resulting proof
that even the original fixed-anchor pointed law must be singular.  Targeted searches also found
Suzuki's screw-line and model-space expansions but not the Laplace declaration `(191)--(196)` or
its identification with the exact fixed-anchor rigidity law `(199)`.  Meromorphic-Herglotz
canonical products, exponential Herglotz representations, and Krein spectral-shift functions are
classical; they are not claimed new.  The targeted literature search found no Suzuki-specific
identification of the singular fixed-anchor law with compactified even/odd gap occupancy, no theta
log-moment trace hierarchy `(210)--(212)`.  The scalar defect transport and endpoint crossing
`(213)--(215)` already belong to `SR-55` and the parity-resolvent transport card; the new point is
only their placement as moment zero of the paired hierarchy.  The targeted search also found no
Suzuki restricted-Weil midpoint-reversal `sech` bound, normalized-Hankel hyperbolic budget,
prime-correlation consequence `(229)--(241)`, exact edge/source-alignment slack and sharp-edge
multiplicity law `(242)--(251)`, or the Suzuki relative-edge/parity-floor correspondence
`(255)--(260)`.  Yafaev's singular-Hankel analysis contains the isolated delta-reflection parent,
but the search found no Suzuki common-Toeplitz logarithmic localization penalty or normalized
prime-seam collapse `(262)--(267)`.  The physical prime-reflection square and log-ratio translation
budget are classical in their components, but the corpus and targeted search found no
Suzuki-specific reserve law `(268)--(273)`.  Likewise the PNT boundary Laplace limit is known;
candidate-new content is the strong-versus-operator-norm split for the centered physical
prime--archimedean compression `(274)--(280)`.  Fixed-aperture far-negative projective collapse is
corpus-known; the coupled `-lambda asymp e^a` source-blindness and forced floor-hugging law
`(281)--(287)` was not found internally or in the targeted Suzuki source audit.
Primary parent comparisons are Reiffenstein, *Higher-order interlacing for matrix-valued
meromorphic Herglotz functions*, arXiv:2108.10746, Theorem 2.3 for the scalar product law;
Poltoratski, *The Krein spectral shift and rank one perturbations of spectra*,
arXiv:math/9601206; and Yafaev, *Perturbation determinants, the spectral shift function, trace
identities, and all that*, arXiv:math/0701301.
Specialist priority review remains required.
