# Suzuki Weil Position-Torque Recurrence

- **ID:** suzuki-weil-position-torque-recurrence
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper)
- **Source:** Suzuki 2026 restricted Weil operator, distribution kernel (2.10)--(2.11)
- **Statement:** The free even--odd position commutator of Suzuki's complete restricted Weil
  source changes strict sign in both directions at arbitrarily large apertures.
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL] [NOVELTY-BOUNDARY-AUDITED]`
  `[SOURCE-DOMAIN PROMOTION PROVED]`

## Goal

Expose and determine the first source term that can orient Suzuki's even/odd deficiency channels.
The relevant observable must be obtained from the restricted Weil kernel, not fitted from the Xi
target.

For aperture length `L=2a`, let `X` denote multiplication by position, and let

```text
e(x)=cosh(x),    o(x)=sinh(x),    -a<x<a.
```

The source observable is the form commutator

```text
T(L) = Q_W^a(Xe,o)-Q_W^a(e,Xo).
```

It is the bare position torque that enters the inverse-commutator identity

```text
[T_a^(-1),X] = T_a^(-1)[X,T_a]T_a^(-1)
              = T_a^(-1)[X,A_a]T_a^(-1).
```

The theorem below proves that `T(L)` is not eventually one-signed. This is a source fact. It
neither assumes nor proves convergence of Suzuki's two-angle Livsic quotient.

## Gates

- [x] 0 -> 1 in-progress: literal source observable, exact kernel calculation, hostile alternatives
- [x] 1 -> 2 fully-proven: dependency-closed transform and Landau proof
- [x] 2 -> 3 formalized: exact finite source, archimedean cancellation, tent transform,
      Xi-curvature continuation, exponential order, the Landau lemma, and the actual cofinal sign
      theorem (19)--(20) are all Lean-proved unconditionally
- [ ] 3 -> 4 publication-ready: standalone operator theorem, source-domain promotion, specialist
      novelty review

## Competing hypotheses

- **C1 (proved):** complete position torque changes sign cofinally in both directions.
- **C2:** positive Mangoldt atoms dominate after a finite aperture, making the torque eventually
  nonnegative.
- **C3:** the exponentially growing archimedean term dominates after a finite aperture, making the
  torque eventually nonpositive.
- **C4:** a one-sign tail is compatible with the completed transform because its convergence
  abscissa is a real singularity.
- **C5:** the differentiated completed shift is only a target-side rewriting and does not come from
  Suzuki's literal finite-aperture kernel.

The source calculation kills C5. The missing-real-boundary argument kills C2--C4.

## The exact source observable

Write Suzuki's distribution kernel on `(-a,a)` as

```text
K(t)=-g''(t)
    =-(1/2) Pf(1/|t|) -(2A+1) delta_0
     -sum_(n>=2) Lambda(n)/sqrt(n) [delta_(log n)+delta_(-log n)]
     -r''(t).                                                   (1)
```

For `t>0`, Suzuki's smooth remainder satisfies

```text
r''(t)=-2 cosh(t/2)+exp(t/2)/(2 sinh t)-1/(2t).                 (2)
```

The form commutator multiplies the convolution kernel by its lag:

```text
T(L)=double_integral e(x)o(y)(x-y)K(x-y) dx dy.                (3)
```

Thus the scalar term `(2A+1) delta_0` disappears identically. Define the positive-lag
correlation

```text
C_L(h)=integral_(h-a)^a cosh(x)sinh(x-h) dx.
```

Direct antiderivation gives

```text
C_L(h)=-(L-h)sinh(h)/2,               0<=h<=L.                 (4)
```

Reflection changes the negative-lag correlation to `-C_L(h)`. Applying (4) separately to the
principal-value, prime, and smooth terms of (1) gives

```text
T(L)
 = integral_0^L (1/2+t r''(t))(L-t)sinh(t) dt
   +sum_(2<=n<=exp L) Lambda(n)/sqrt(n) log(n)
      (L-log n)sinh(log n).                                    (5)
```

The principal value is legitimate as a form pairing: multiplication by `t` changes
`Pf(1/|t|)` into the locally integrable odd sign kernel. Formula (5) therefore has no remaining
distributional ambiguity. The prime sum is finite at each aperture.

Using (2), the principal-value `1/2` cancels the singular `-1/(2t)` part exactly:

```text
(1/2+t r''(t))sinh(t)
  =t [exp(-t/2)/2-sinh(3t/2)].                                 (6)
```

Consequently

```text
T(L)=A(L)+P(L),                                                 (7)

A(L)=integral_0^L t(L-t)[exp(-t/2)/2-sinh(3t/2)]dt,             (8)

P(L)=sum_(2<=n<=exp L) Lambda(n)/sqrt(n) log(n)
       (L-log n)sinh(log n).                                   (9)
```

Every summand in `P(L)` is nonnegative. More explicitly,

```text
P(L)=(1/2) sum_(2<=n<=exp L) Lambda(n)log(n)(L-log n)
                 [sqrt(n)-n^(-3/2)].                           (10)
```

The archimedean term also has the closed form

```text
A(L)=-(2L/9-8/27)exp(3L/2)
     +(2L+8)exp(-L/2)
     +(2L/9+8/27)exp(-3L/2)
     +2L-232/27.                                               (11)
```

Formula (11) follows from

```text
integral_0^L t(L-t)exp(kt)dt
  =[exp(kL)(kL-2)+kL+2]/k^3,        k != 0.                    (12)
```

Equations (5)--(10), rather than the completed Xi identity below, establish that `T` is a literal
Suzuki source observable.

## Exact promotion from Suzuki's deficiency vectors

The torque is not merely a formal commutator attached after the fact. It is the first
operator-sensitive coefficient of Suzuki's actual deficiency response.

Fix `rho<lambda_a`, put

```text
B=(A_a-rho I)^(-1),          s=rho-lambda,
mu=-lambda=s-rho,
F_s=mu(A_a-lambda I)^(-1).
```

In the bounded coordinate `B`,

```text
F_s=((s-rho)x/(1+sx))(B).                                  (P1)
```

The usual strong limit is `F_s f -> f`. On the operator domain, equivalently on `range(B)`,
there is an exact first-order upgrade:

```text
mu(F_s-I)Bf
 =-(I+rho B)F_s f
 ->-(I+rho B)f.                                            (P2)
```

This is not an asymptotic resolvent series. The equality in (P2) is the scalar identity

```text
(s-rho)[(s-rho)x/(1+sx)-1]x
 =-(1+rho x)(s-rho)x/(1+sx)
```

transported through continuous functional calculus. It therefore remains valid when zero is a
spectral accumulation point of `B`.

The source vectors

```text
c(x)=cosh x,       o(x)=sinh x
```

belong to `Dom(A_a)`. Here is a dependency-closed verification. Their zero extensions have
Fourier transforms `O(1/|z|)` by one integration by parts. Suzuki's Gamma multiplier in (2.6)
is `O(log(2+|z|))` by (2.8), so its product with either Fourier transform lies in `L2(R)`.
At fixed aperture the prime-translation sum is finite and bounded on `L2`, while convolution with
the `C^2` remainder is bounded. Hence the distributional expressions (2.10)--(2.11) applied to
`c,o` lie in `L2(-a,a)`. By the defining Riesz characterization of `Dom(A_a)`, both functions
belong to that domain.

Choose `c_0,o_0` with `Bc_0=c`, `Bo_0=o`. Multiplication by `x` is bounded and self-adjoint on
`L2(-a,a)`. Taking real pairings in (P2), and using

```text
Re<c,Xo>=Re<o,Xc>,
```

gives

```text
mu {Re<F_s c,Xo>-Re<F_s o,Xc>}
 -> Re<A_a o,Xc>-Re<A_a c,Xo>
  = Q_W^a(Xc,o)-Q_W^a(c,Xo)
  = T(2a).                                                  (P3)
```

Since `(A_a-lambda I)^(-1)=F_s/mu`, (P3) is equivalently

```text
mu^2 {Re<(A_a-lambda I)^(-1)c,Xo>
       -Re<(A_a-lambda I)^(-1)o,Xc>} -> T(2a).              (P4)
```

Equations (P3)--(P4) are the promised source-domain promotion. They prove that `T` is exactly the
large-negative-shift coefficient of the even--odd Suzuki deficiency commutator, not a target-side
Xi observable.

The bounded-resolvent content of (P2)--(P4) is formalized unconditionally in
`SuzukiResolventPositionTorquePromotion.lean`:

- `suzukiShiftedResolventScale_firstOrder_on_range`;
- `suzukiShiftedResolventScale_positionTorque_limit`.

The second theorem expresses operator-domain membership as range membership for `B`, so it does
not postulate an unbounded operator in Lean. The remaining formalization gap is construction of
Suzuki's concrete restricted-Weil operator and the Fourier-multiplier proof that `c,o` lie in its
domain.

## Exact completed transform

Let

```text
D(s)=sum_(n>=2) Lambda(n)log(n)n^(-s)=(zeta'/zeta)'(s),
                                                               Re(s)>1.
```

For `Re(s)>3/2`, absolute convergence permits Fubini. One aperture tent has transform

```text
integral_(h)^infinity (L-h)exp(-sL)dL=exp(-sh)/s^2.             (13)
```

Equations (8)--(10) and (13) give

```text
integral_0^infinity T(L)exp(-sL)dL
 =1/(2s^2) [
      D(s-1/2)-D(s+3/2)
      +1/(s+1/2)^2-1/(s-3/2)^2+1/(s+3/2)^2
   ].                                                          (14)
```

Absolute exchange in the prime term follows from

```text
sum Lambda(n)log(n)(n^(1/2)+n^(-3/2))n^(-sigma)<infinity,
                                                               sigma>3/2.
```

No prime-number theorem is used.

For the completed Riemann function `xi`, the Gamma recurrence and Euler product give, on
`Re(u)>1`,

```text
(xi'/xi)(u+2)-(xi'/xi)(u)
 =sum Lambda(n)(1-n^(-2))n^(-u)
  +1/(u+2)+1/(u+1)-1/(u-1).                                  (15)
```

Differentiate (15), reverse sides, and put `u=s-1/2`. Then (14) becomes

```text
F(s):=integral_0^infinity T(L)exp(-sL)dL
  =[(xi'/xi)'(s-1/2)-(xi'/xi)'(s+3/2)]/(2s^2),                 (16)
```

initially for `Re(s)>3/2`. The right side supplies the meromorphic continuation of the
source transform.

## Exponential order and regularity

The prime sum is locally finite, and a new summand vanishes at its birth point
`L=log n`; hence `P` and `T` are continuous.

For `L>=1`, use `Lambda(n)<=log n`, `n<=exp L`, and (10):

```text
0<=P(L)<= (1/2)L^3 exp(3L/2).                                 (17)
```

The integrand in (8) similarly gives

```text
|A(L)|<=L^3 exp(3L/2).                                        (18)
```

The constants in (17)--(18) are inessential. They prove convergence of the Laplace integral for
every real part strictly greater than `3/2`, so every one-sign tail has finite convergence
abscissa at most `3/2`.

## Landau lemma used

Let `f` be a nonzero, nonnegative, locally integrable function on `[0,infinity)`, and suppose its
Laplace transform has finite convergence abscissa `sigma_c`. Then the transform cannot extend
holomorphically through the real point `sigma_c`.

For completeness, choose `a>sigma_c`. Differentiation under the convergent integral gives

```text
(-1)^k F^(k)(a)=integral_0^infinity t^k f(t)exp(-at)dt>=0.
```

If `F` were holomorphic in a disk centered at `a` of radius larger than `a-sigma_c`, choose
`r` strictly between those two numbers. Absolute convergence of its Taylor series and Tonelli
would give

```text
sum_(k>=0) r^k/k! integral t^k f(t)exp(-at)dt
 =integral f(t)exp(-(a-r)t)dt<infinity,
```

although `a-r<sigma_c`. This contradicts the definition of the abscissa. This is the exact
Taylor--Tonelli form of Landau's theorem; no Tauberian asymptotic is used.

## Cofinal two-sided recurrence theorem [PROVED HERE]

For every `L0>=0`, there exist `L_minus,L_plus>L0` such that

```text
T(L_minus)<0<T(L_plus).                                       (19)
```

Equivalently, the positive Mangoldt torque crosses its exact archimedean baseline cofinally in
both directions:

```text
P(L_minus)<-A(L_minus),    P(L_plus)>-A(L_plus).               (20)
```

### Proof

Assume first that `T` is eventually nonnegative. Choose `H` after its last negative value and put

```text
f_H(u)=T(H+u),                 u>=0.
```

Its Laplace transform is

```text
F_H(s)=exp(sH)[F(s)-integral_0^H T(L)exp(-sL)dL].              (21)
```

The subtracted head is entire, so (21) has the same nonremovable poles as (16). If the tail were
identically zero, (21) would be zero on a right half-plane and hence could not have those poles.
Thus the tail is a nonzero nonnegative carrier.

Choose any nontrivial zero `rho` of `xi`; then `0<Re(rho)<1` and `Im(rho)!=0`. At

```text
p=rho+1/2
```

the first curvature term in (16) has a genuine double pole. Indeed, if `rho` has multiplicity
`m>0`, then

```text
(xi'/xi)'(z)=-m/(z-rho)^2+holomorphic.
```

The second curvature term is regular there because its argument is `rho+2`, which lies in
`Re(z)>2`; the Euler product excludes a zero. Also `p!=0`, so division by `2s^2` cannot cancel
the pole.

Let `sigma_c` be the convergence abscissa of the nonnegative tail. Bounds (17)--(18) give

```text
sigma_c<=3/2.                                                 (22)
```

The pole at `p` gives

```text
sigma_c>=Re(p)=Re(rho)+1/2>1/2.                               (23)
```

Otherwise the absolutely convergent tail transform would be holomorphic in a half-plane
containing `p`, contradicting uniqueness of meromorphic continuation from `Re(s)>3/2`.

The completed Xi function has no real zeros. One dependency-closed proof is: the Euler product
handles real `s>1`; on `0<s<1`, the alternating eta series is positive while
`1-2^(1-s)<0`, so `zeta(s)!=0`; the functional equation handles `s<0`; and the completed endpoint
values at `0,1` are nonzero. Therefore both Xi arguments in (16) are nonzero when

```text
s=sigma_c in (1/2,3/2].
```

The factor `s^2` is nonzero as well. Hence (16), and then (21), is holomorphic through the real
point `sigma_c`. This contradicts the Landau lemma. Thus `T` is not eventually nonnegative.

Apply the same proof to `-T`. Its one-sign tail transform is the negative of (21), with identical
abscissa, genuine double pole, and real-boundary regularity. Therefore `T` is not eventually
nonpositive. These two negations are exactly (19), and (7) gives (20). QED.

## What is new, and what is classical

Classical inputs:

- Suzuki's distribution formula for `-g''`;
- the Euler product, Gamma recurrence, and real zero-freeness of completed Xi;
- existence of nontrivial zeta zeros;
- Landau's nonnegative-Laplace boundary theorem;
- the general fact that explicit-formula remainder terms often oscillate.

New content claimed here:

1. multiplication by position converts Suzuki's literal restricted Weil kernel into the exact
   logarithmically differentiated Mangoldt torque (5);
2. the principal-value singularity and Suzuki's Gamma remainder cancel to the elementary kernel
   (6);
3. the finite-aperture torque has the exact completed curvature transform (16);
4. this specific source commutator, and hence the exact arithmetic crossing (20), has both strict
   signs cofinally.

The analytic sign-change method is not claimed as new number-theoretic technology. The scientific
advance is identification and determination of a previously uncomputed source observable inside
Suzuki's operator.

## Novelty audit

- [Suzuki 2026](https://arxiv.org/abs/2606.09096), (2.10)--(2.11), supplies the kernel but does not
  commute it with position, derive the logarithmically weighted source, or study its aperture
  transform.
- [Kim--Hong--Kim--Choi--Jang--Kim 2026](https://arxiv.org/abs/2607.24830) computes Suzuki's
  spectrum, prime symbol, and trace moments. Full-text searches find no position commutator,
  torque, tent transform, Xi log-curvature difference, or `Lambda(n)log n` source. The paper
  explicitly classifies its arithmetic results as numerical realizations of classical identities.
- Internal `suzuki-screw-cesaro-curvature-recurrence.md` applies a related Landau mechanism to the
  centered primitive of Suzuki's screw function. It does not use the restricted operator
  commutator, the positive prime torque, or the shifted Xi curvature in (16).
- Internal `suzuki-arithmetic-tangent-inverse-moment-holography.md` extracts first tangent data;
  it does not contain the position-weighted second source.
- General Riesz-mean and prime-number-theorem oscillation literature makes broad analytic priority
  implausible. Priority is therefore restricted to the Suzuki source identification and its exact
  operator/arithmetic consequences. Specialist review remains required.

## Relation to the updated modular-superselection paper

The theorem lies outside the conjunctive no-go class of
`riemann-source-modular-superselection/main-universal.tex`. It uses a literal source-defined
pre-scalar commutator and retains even/odd orientation. It assumes neither unit response on
orthogonal exponent shells nor finite-Rees reflected sewing nor post-fusion invariant
scalarization.

It also respects that paper's admission warning: (16) is accepted only after (1)--(10) derive the
carrier from Suzuki's source. Starting from (16) alone would be target-side theatre.

## Consequence for Route G

The theorem kills two simplistic second-jet strategies:

- eventual positivity of the free-profile arithmetic correction;
- eventual negativity forced by the archimedean sector.

It also provides cofinally many apertures of either source orientation. This is positive
infrastructure for an aperture-dependent two-angle selector, not a proof that such a selector
converges.

The source-domain promotion problem is now solved by (P1)--(P4). Combining it with (19) gives a
new deficiency-level consequence. There are cofinal aperture sequences `a_n^-`, `a_n^+` and
admissible shifts `lambda_n^± -> -infinity`, chosen sufficiently negative at each aperture, for
which the actual scaled deficiency anomaly

```text
(-lambda_n^±)^2 {
 Re<(A_(a_n^±)-lambda_n^±)^(-1)c,Xo>
-Re<(A_(a_n^±)-lambda_n^±)^(-1)o,Xc>
}
```

is respectively strictly negative and strictly positive. Positive scaling means the unscaled
anomaly has the same sign. This is a diagonal consequence of fixed-aperture convergence (P4);
no uniformity in aperture is asserted or needed.

This does not rescue the far-negative family: its first Xi defect collapses to zero. The next hard
source theorem is therefore the **transition-scale classification problem**:

```text
classify every joint aperture/shift scale that keeps
kappa_(a,lambda) in the strict Xi cone (77/85,1),
and decide whether its second parity curvature can converge
to the fixed negative Xi calibration while the two-angle
meromorphic carrier remains source-admitted.
```

This is the live Suzuki problem. It is stronger than choosing the anomaly's sign: one must prove
simultaneous first-jet calibration, second-jet normalization, full-frequency Herglotz orientation,
and meromorphic two-angle Xi/de Branges identification. Route G therefore remains open.

## Lean status

Formalized unconditionally:

- `SuzukiSecondDefectParityCommutator.lean`: parity curvature, tilt velocity, inverse commutator,
  and exact source balance;
- `SuzukiSecondDefectCompactParitySource.lean`: actual compact Fourier endpoint and derivative
  parity identities;
- `SuzukiWeilPrimeCommutatorTorque.lean`: finite prime translation torque, exact lag correlation,
  positive visible atoms;
- `SuzukiWeilPositionTorqueCurvature.lean`: smooth remainder, principal-value/Gamma cancellation,
  exact archimedean closed form, complete finite-aperture source, tent transform, differentiated
  completed shift, and exact source-to-Xi curvature continuation;
- `SuzukiResolventPositionTorquePromotion.lean`: first-order strong resolvent expansion on the
  operator domain and exact promotion of the real deficiency commutator to position torque.

Also formalized (2026-08-16), closing the 2 -> 3 gate:

- `SuzukiTorqueTentSeries.lean`, `SuzukiTorqueTentLaplace.lean`, `SuzukiTorquePrimeSeries.lean`,
  `SuzukiTorquePrimeLaplace.lean`, `SuzukiTorqueArchLaplace.lean`, `SuzukiTorqueTotalTransform.lean`,
  `SuzukiTorqueEulerTransform.lean`: the tent transform, absolute convergence of the prime tent
  series, and the complete transform (14)--(16);
- `SuzukiTorquePrimeOrder.lean`, `SuzukiTorqueArchOrder.lean`: continuity and the exponential-order
  bounds (17)--(18) for the full moving-cutoff torque;
- `LaplaceAbscissaExists.lean`, `ComplexLaplaceHolomorphy.lean`, `RealJetsOfHolomorphic.lean`,
  `LandauSingularAtAbscissa.lean`: the Landau lemma in its exact Taylor--Tonelli form;
- `RiemannXiRealAxisNonvanishing.lean`, `SuzukiTorqueContinuationAnalytic.lean`,
  `SuzukiTorqueContinuationPole.lean`: real-axis regularity of the continuation, and its exact
  order `-2` above every strip zero of `xi`;
- `HeadLaplaceEntire.lean`, `TailMeasureLaplace.lean`, `SuzukiTorqueTailCarrier.lean`,
  `SuzukiTailTransform.lean`, `ConvexDiffCountableConnected.lean`, `OneSignTailImpossible.lean`,
  `SuzukiTorqueCofinalSign.lean`: the one-sign-tail obstruction and the actual cofinal sign
  theorem (19), together with its baseline form (20).

Deferred to the 3 -> 4 gate, as listed there:

- construction of Suzuki's concrete restricted-Weil operator and its `cosh/sinh` domain instance
  (the promotion theorems (P1)--(P4) are Lean-stated in the bounded-resolvent coordinate `B`, so no
  unbounded operator is postulated);
- the joint transition-scale classification, which is the card's live open problem, not a claim.

No formal theorem assumes RH.

## Log

- 2026-08-01 — literal position commutator and finite Mangoldt torque derived.
- 2026-08-01 — exact principal-value/Gamma cancellation and Xi-curvature transform Lean-proved.
- 2026-08-01 — cofinal two-sided recurrence paper proof closed; novelty restricted to Suzuki
  source identification and consequence.
- 2026-08-01 — exact source-domain resolvent promotion and cofinal two-sign deficiency-anomaly
  consequence proved; transition-scale classification isolated as live core.
- 2026-08-16 — cofinal sign theorem (19)--(20) formalized unconditionally in Lean 4; card promoted
  to stage 3.  See `suzuki-weil-position-torque-recurrence-formalized.md`.

## Two-jet closure audit

The successor card `suzuki-two-jet-shifted-hankel-gate.md` determines exactly how much this
position torque can contribute to the transition-scale problem. With parity energies `E,O` and
tilts `alpha,beta`, the anchored Schur numerator is

```text
O(E+alpha)-E beta
  = EO + E(alpha-beta) + alpha(O-E).
```

The torque computed here is `alpha-beta`; it controls only the middle term. Off the exactly
balanced locus `E=O`, every real Schur numerator occurs at fixed torque. Thus no strengthening of
the torque sign recurrence alone can close Suzuki's second-jet gate. A new source theorem must
control the local tilt-asymmetry `alpha(O-E)` or force exact balance with the sharp threshold
`alpha-beta >= -E`.

At the Xi target the full slack, not the torque term alone, is exactly

```text
16 (Re M_0(1) Re M_2(1)-Re M_1(1)^2) / Re M_0(1)^2.
```

This converts the vague transition-scale “second curvature” requirement into the safe-shift first
Hankel-minor gate while preserving the conclusion here: cofinal torque sign change is real source
information, but insufficient by itself.
