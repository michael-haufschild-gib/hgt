# Suzuki prime-to-clock-atom velocity transference

- **ID:** `suzuki-prime-clock-atom-velocity-transference`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / RESTRICTED-WEIL PRIME STEPS / DONOGHUE DIVISOR MOTION
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED]`
  `[NOT AN RH PROOF]`
- **Parents:**
  - `suzuki-arithmetic-tangent-inverse-moment-holography.md`
  - `suzuki-high-clock-prime-tangent-tomography.md`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), equations (2.2), (2.11), and Theorem 1.5.
- **New conclusion:** each von-Mangoldt step has an exact first-order action on every pole of
  Suzuki's free Donoghue clock. The hyperbolic defect geometry cancels and leaves the critical
  explicit-formula coefficient `Lambda(m)/sqrt(m)`.

## 1. Setup

Fix `a>0`. Put

```text
F_0(z)=integral_(-a)^a e^x e^(izx) dx,
x_(a,k)=((k+1/2)pi)/a,                         k in Z.    (1)
```

For the far-negative source chart `epsilon=(-lambda)^(-1)`, the parent theorem proves

```text
F_epsilon(z)=F_0(z)-epsilon H_a(z)+o(epsilon),
h_a(z)=H_a(z)/F_0(z),
Delta_a(z)=h_a(-z)-h_a(z),                              (2)
```

locally uniformly away from the displayed denominators. The free Donoghue poles are the points
`x_(a,k)`. If `x_(a,k)(epsilon)` denotes their simple continuation, then

```text
dot x_(a,k)=-Delta_a(x_(a,k))/(2 i a tanh(a)).            (3)
```

Equation `(3)` is linear in the first source response `H_a`. We may therefore decompose the pole
velocity according to Suzuki's finite-part, scalar, prime-step, and smooth archimedean pieces.

For `m>=2`, write

```text
L_m=log(m),
M_a={m: 2<=m<=e^(2a)}.                                  (4)
```

The equality endpoint `L_m=2a` may be included because its translated intervals are empty and all
formulas below vanish there.

## 2. Theorem A: exact prime-step clock velocity

The contribution of the `m`th prime step in Suzuki's distribution kernel to the `k`th free-clock
pole velocity is

```text
dot x_(a,k)^(m)
  = Lambda(m)/(a sqrt(m)) sin(x_(a,k) log(m)).             (5)
```

Consequently the complete arithmetic part of the support velocity is

```text
V_a^prime(k)
  = sum_(m in M_a) Lambda(m)/(a sqrt(m))
      sin((k+1/2)pi log(m)/a).                            (6)
```

Equivalently, in physical spectral coordinate,

```text
a V_a^prime(k)=P_a(x_(a,k)),
P_a(t)=sum_(m in M_a) Lambda(m)/sqrt(m) sin(t log(m)).    (7)
```

Thus the prime part of Suzuki's first Donoghue-divisor motion is exactly the truncated critical
von-Mangoldt sine transform sampled on the half-integer clock.

### Proof

Suzuki's equation (2.11), applied to the zero extension of `e^x`, gives the `m`th prime component

```text
(A_a e)^prime_m(x)
 =-Lambda(m)/sqrt(m) e^x
   [m^(-1) 1_(-a+L_m,a)(x)+m 1_(-a,a-L_m)(x)].           (8)
```

Let `H_m` be its Fourier transform and `h_m=H_m/F_0`. For arbitrary `z` with `F_0(z)!=0`, set

```text
s=1+iz,
Q_z=e^(2as).
```

Direct endpoint integration gives

```text
integral_(-a+L_m)^a e^(sx) dx / F_0(z)
   =(Q_z-e^(sL_m))/(Q_z-1),

integral_(-a)^(a-L_m) e^(sx) dx / F_0(z)
   =(Q_z e^(-sL_m)-1)/(Q_z-1).                           (9)
```

No division by `s` remains: the common primitive factor cancels against `F_0`.

Now set `z=x_(a,k)`, `Q=e^(2a)`, and

```text
y=e^(izL_m).
```

Then

```text
e^(2iaz)=-1,
Q_z=-Q,
e^(sL_m)=m y.                                            (10)
```

Substitution of `(9)--(10)` into `(8)` yields

```text
h_m(z)
 =-Lambda(m)/(sqrt(m)(Q+1))
   [Q/m+m+y+Q y^(-1)].                                   (11)
```

Replacing `z` by `-z` exchanges `y` and `y^(-1)`. Hence

```text
Delta_m(z)
 =h_m(-z)-h_m(z)
 =-Lambda(m)/(sqrt(m)(Q+1))
    [(Q-1)(y-y^(-1))]
 =-2i Lambda(m)/sqrt(m) tanh(a) sin(zL_m).                (12)
```

Insert `(12)` into the pole-velocity formula `(3)`. The factor `tanh(a)` and both signs cancel:

```text
dot x_(a,k)^(m)
 =Lambda(m)/(a sqrt(m)) sin(x_(a,k)L_m),                  (13)
```

which is `(5)`. The source prime sum is finite for fixed `a`, so linear superposition proves `(6)`;
substitution of `(1)` proves `(7)`.

If `L_m=2a`, `(13)` contains `sin((2k+1)pi)=0`, agreeing with the empty intervals in `(8)`.

## 3. Theorem B: exact recovery from divisor velocities

Put

```text
theta_m=pi log(m)/a,
q_m=e^(i theta_m),
r_m=e^(i theta_m/2).                                     (14)
```

Fix `m in M_a`. Assume the finite phase packet is nonresonant at `m`:

```text
q_j!=q_m       for j in M_a, j!=m,
q_j^(-1)!=q_m  for every j in M_a.                        (15)
```

Then

```text
lim_(N->infinity) (1/N) sum_(k=0)^(N-1)
  V_a^prime(k) q_m^(-k)
 =Lambda(m) r_m/(2 i a sqrt(m)),                          (16)
```

and therefore

```text
Lambda(m)
 =2 i a sqrt(m) r_m^(-1)
   lim_(N->infinity) (1/N) sum_(k=0)^(N-1)
     V_a^prime(k) q_m^(-k).                               (17)
```

### Proof

The half-shifted sine has exact exponential decomposition

```text
sin((k+1/2)theta_j)
 =(r_j q_j^k-r_j^(-1)q_j^(-k))/(2i).                     (18)
```

After demodulation by `q_m^(-k)`, Cesaro means of every nontrivial unit geometric phase vanish.
Conditions `(15)` leave only the positive `j=m` term, giving `(16)`. The factors in `(17)` are
nonzero for `a>0` and `m>=2`, so `(17)` follows.

The same countable resonance classification as in the parent high-clock theorem applies:

```text
a=(log j-log m)/(2 ell),       j!=m, ell in Z\{0},
a=log(jm)/(2 ell),             ell in Z_(>0).              (19)
```

Hence one dense cofinal set of apertures is simultaneously nonresonant for every finite prime
packet. Along any cofinal schedule in this complement, each fixed `Lambda(m)` is eventually
recoverable directly from the arithmetic clock-atom velocities.

## 4. What changed

The previous tomography theorem recovered primes from Fourier samples of the source tangent before
passing to spectral data. Equations `(5)--(17)` close the missing first-order transference arrow:

```text
Suzuki prime step
  -> anti-reflected projective source response
  -> motion of concrete Donoghue poles
  -> exact recovery of Lambda(m).                         (20)
```

The weight in the earlier high-clock source packet was
`Lambda(m)(sqrt(m)+m^(-3/2))`. After the projective clock quotient and pole normalization, the
geometry converts it to the critical explicit-formula weight `Lambda(m)/sqrt(m)`. This is the
structural delta: the divisor tangent sees the natural critical prime amplitude with no residual
hyperbolic aperture factor.

The physical-coordinate form `(7)` also removes an apparent phase-collapse artifact. Although
`theta_m->0` at fixed clock index as `a->infinity`, the actual spectral coordinate
`x_(a,k)=(k+1/2)pi/a` retains the stable frequency `log(m)`. Arithmetic is not escaping because its
frequency disappears; the clock grid is becoming dense in the physical spectral line.

## 5. Exact remaining frontier

This theorem is first-order at the far-negative boundary. It does not show that an admissible
finite shift with a non-infinitesimal deformation retains `(7)`, nor that its spectral probability
is tight as `a->infinity`. The growing polynomials `P_a` are critical Dirichlet sine sums; no
ordinary cofinal function limit is asserted.

The next open producer is now narrower:

```text
integrate the exact prime divisor-velocity field along one intrinsic admissible shift path,
prove the resulting Donoghue probabilities remain tight and infinitely atomic,
and identify their support limit with the Xi/de Branges divisor.               (21)
```

Any proposed intermediate shift selector can now be tested against `(5)`: if its normalized
divisor motion kills every critical prime sine mode, it has erased the entire von-Mangoldt source.

## 6. Hostile audit

1. **Two negative signs retained.** Suzuki's prime kernel in `(8)` is negative. Resolvent
   differentiation makes `F_epsilon=F_0-epsilon H`; the quotient law `(3)` contributes the second
   sign. Formula `(5)` is positive with the displayed sine orientation.
2. **Reflected pair retained.** Both translated intervals and their unequal `m^(-1),m` factors are
   necessary for `(11)`. Dropping either destroys the `tanh(a)` cancellation.
3. **Endpoint cutoff exact.** The equality case `log(m)=2a` vanishes both geometrically and in
   `(5)`.
4. **No arbitrary gauge.** The calculation occurs in `Delta=h(-z)-h(z)`, so projectively invisible
   common source scaling has already canceled.
5. **No hidden RH shift.** Differentiation is at `epsilon=0`, corresponding to
   `lambda=-infinity`; no use of `lambda=0` or positivity of the unshifted Weil form occurs.
6. **Classical parent separated.** Simple-root perturbation and Bohr recovery are classical.
   Candidate source-specific novelty is the exact Suzuki prime-step evaluation, cancellation, and
   critical-weight divisor law `(5)--(7)`.
7. **No total-velocity confusion.** `V_a^prime` is the canonical arithmetic summand of the total
   source derivative. The finite-part and archimedean summands are not claimed to vanish; they are
   separated by Suzuki's exact kernel decomposition.
8. **No nonlinear/cofinal overclaim.** First-order faithfulness does not prove tightness or Xi
   divisor convergence.

## 7. Internal and external audit

Internal search found the general pole response `(3)` and source high-clock tomography, but no
insertion of Suzuki's prime steps into the pole law and no formula `(5)`. Related failed routes
warn that infinite-time Bohr recovery is not finite-window compactness; this theorem makes no such
claim.

Targeted searches through 2026-07-21 found Suzuki's source paper but no follow-up deriving primewise
eigenvalue velocities, Donoghue atom motion, or the critical sine law `(5)--(7)`. Generic
eigenvalue perturbation, Livsic--Donoghue theory, and finite trigonometric Bohr uniqueness are
classical. Priority remains `[NOVELTY UNVERIFIED]` pending specialist review.

## 8. Formalization target

Formalize the exact dependency-closed algebra and finite recovery theorem in

```text
formal/GaloisForLFunctions/RHTower/SuzukiPrimeClockAtomVelocity.lean
```

The target declarations are:

```text
suzukiPrimeClockReflectedRatio_sub
suzukiPrimeClockGeometry_cancel
suzukiPrimeClockAtomVelocity
suzukiPrimeClockAtomVelocity_eq_physicalPrimeSine
tendsto_suzukiPrimeClockAtomVelocity_bohrCoefficient
tendsto_suzukiPrimeClockAtomVelocity_normalized_bohrCoefficient.
```

The actual unbounded source operator and implicit pole continuation remain paper-level until that
source layer exists in Lean. The module must formalize the exact reflected-step quotient and
half-shifted velocity recovery, not an assumed atom-motion wrapper.

## 9. Gates

- [x] 0 -> 1: exact source claim and hostile attack isolated
- [x] 1 -> 2: quotient calculation, velocity law, Bohr recovery, and audits complete
- [x] 2 -> 3: exact Lean theorem, build, lint, and axiom audits complete
- [ ] 3 -> 4: specialist novelty review/publication treatment
