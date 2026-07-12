# Prime--Gamma rectangular boundary tomography

- **ID:** `prime-gamma-rectangular-boundary-tomography`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / exact CCM source--divisor incidence
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent theories:** Guinand--Weil explicit formula, Connes's trace formula, the corrected
  finite-aperture polar--prime symbol, and cutoff-free rectangular divisor tomography
- **Statement:** One ordinary Dirichlet series whose coefficients are written explicitly from the
  Gamma multiplier, a finite von Mangoldt moving-tent sum, and a rank-one polar boundary square
  has weighted simple-pole divisor equal to the complete off-critical Xi divisor.

## Source coefficient

Fix `L>0`.  For `a>=L`, put

```text
v_(a,L)(x)=1_[a-L,a](x)+1_[-a,-a+L](x).                    (1)
```

With the Fourier convention

```text
hat(v)(t)=integral_R v(x)exp(-i*t*x)dx,
```

one has

```text
hat(v_(a,L))(t)
 =4*sin(L*t/2)*cos((a-L/2)*t)/t,                            (2)
```

with removable value `2L` at `t=0`.  Its positive-lag autocorrelation is

```text
C_(a,L)(h)
 =2*(L-h)_+ +(L-|h-(2a-L)|)_+,       h>=0.                 (3)
```

The first tent comes from the two self-overlaps.  The moving tent is the left-to-right boundary
overlap.  Formula `(3)` is valid also at `a=L`; the possible endpoint intersections have measure
zero.

Let

```text
m_infinity(t)=Re psi(1/4+i*t/2)-log(pi),                    (4)
```

and define the completely source-side scalar

```text
b_L(a)
 =1/(2*pi) integral_R m_infinity(t)|hat(v_(a,L))(t)|^2dt
  -2 sum_(k>=2) Lambda(k)/sqrt(k)*C_(a,L)(log k)
  +32*(sinh(a/2)-sinh((a-L)/2))^2.                          (5)
```

The prime sum in `(5)` is finite: `(3)` vanishes for `h>2a`.  The final term is the exact even
polar energy

```text
2|inner(v_(a,L),cosh(. /2))|^2,                             (6)
```

while the odd polar channel vanishes by evenness.  The Gamma integral converges absolutely because
`m_infinity(t)=O(log(2+|t|))` and `hat(v_(a,L))(t)=O_L(1/|t|)`.

At the arithmetic aperture

```text
a_N=(1/2)log N,       N>=exp(2L),                            (7)
```

the autocorrelation becomes

```text
C_(a_N,L)(log k)
 =2*(L-log k)_+
  +(L-|log(k/N)+L|)_+.                                      (8)
```

Thus every coefficient uses one fixed small-prime tent and one moving prime window

```text
N*exp(-2L)<=k<=N.                                           (9)
```

No zero, zero ordinate, divisor enumeration, or prime cutoff choice occurs in `(4)`--`(9)`.

## Stronger prime--polar core

The archimedean term is not needed to carry the transverse pole divisor.  Define the moving
von Mangoldt tent

```text
T_L(N)
 =sum_(k>=2) Lambda(k)/sqrt(k)
   *(L-|log(k/N)+L|)_+                                      (10)
```

and the explicit even polar coefficient

```text
P_L(N)
 =32*(sinh(log(N)/4)-sinh(log(N)/4-L/2))^2.                 (11)
```

Put `c=exp(-L/2)`, `alpha=1-c`, and `beta=c^(-1)-1`.  Then

```text
P_L(N)=8*alpha^2*N^(1/2)+16*alpha*beta+8*beta^2*N^(-1/2),  (12)
```

so its ordinary Dirichlet series is

```text
8*alpha^2*zeta(s-1/2)
 +16*alpha*beta*zeta(s)
 +8*beta^2*zeta(s+1/2).                                    (13)
```

Define the prime--polar coefficient

```text
p_L(N)=P_L(N)-2*T_L(N).                                    (14)
```

For the continuous tent Mellin factor,

```text
I_L(s)
 =integral_1^exp(2L) (L-|log u-L|)*u^(-s)du
 =((1-exp(-L*(s-1)))/(s-1))^2,                             (15)
```

with removable value `L^2` at `s=1`.  At a shifted zero `s=rho+1/2`,

```text
I_L(rho+1/2)=A_L(rho-1/2)^2.                               (16)
```

For `Re s>3/2`, interchange of the two positive-index sums gives

```text
sum_(N>=1) T_L(N)N^(-s)
 =I_L(s)*(-zeta'(s-1/2)/zeta(s-1/2))+H_L(s),               (17)
```

where `H_L` is the multiplicative Riemann-sum error.  The bounded-variation estimate

```text
|k^(-s) sum_N g_s(N/k)-k^(1-s) integral_0^infinity g_s(u)du|
 <=C_K*k^(-Re s)                                           (18)
```

holds uniformly for `s` in every compact subset `K` of `Re s>1/2`, with

```text
g_s(u)=(L-|log u-L|)_+*u^(-s).
```

Since

```text
sum_k Lambda(k)k^(-Re s-1/2)<infinity       (Re s>1/2),    (19)
```

the error `H_L` is holomorphic on `Re s>1/2`.

`[CONJECTURE: PAPER PROOF OPEN]` Equations `(12)`--`(19)` give a meromorphic continuation

```text
Pcal_L(s)=sum_(N>=1)p_L(N)N^(-s)                            (20)
```

to `Re s>1`.  The pole of `-zeta'/zeta(s-1/2)` at `s=3/2` has residue `1`, while

```text
I_L(3/2)=4*(1-exp(-L/2))^2=4*alpha^2.                       (21)
```

Thus the residue `-2*I_L(3/2)=-8*alpha^2` from the prime tent cancels exactly the
`+8*alpha^2` residue of the polar zeta term in `(13)`.

The remaining poles in `Re s>1` are exactly

```text
s=rho+1/2,
zeta(rho)=0,
Re rho>1/2.                                                 (22)
```

At a zero of analytic multiplicity `m(rho)`, `-zeta'/zeta` has residue `-m(rho)`, hence

```text
Res_(s=rho+1/2) Pcal_L(s)
 =2*m(rho)*A_L(rho-1/2)^2.                                 (23)
```

Because `A_L(w)` is nonzero for `Re w>0`, the prime--polar series alone recovers the complete
right off-critical divisor with multiplicity, and

```text
RH iff Pcal_L is holomorphic on Re s>1.                     (24)
```

This is stronger than the proposed exact source identity below.  It constructs a source-defined
tomographic series directly, without first identifying its coefficients with a zero sum.  Once
formalized, comparison with the cutoff-free Weil continuation will give the quotient law

```text
Pcal_L-Mcal_L is holomorphic on Re s>1:                      (25)
```

the prime--polar and divisor observables represent the same multiplicity-weighted polar class
modulo holomorphic functions.

For example, fixing `L=(1/2)log 2` once and for all makes `(10)` a single dyadic moving window
`N/2<=k<=N`.  Hence one fixed dyadic von Mangoldt statistic plus the elementary polar correction
already carries the entire off-critical divisor.

## Candidate source identity

Let

```text
q_L(N)=xiWeilPolarization(F_(a_N,L),F_(a_N,L)),              (26)
```

where `F_(a,L)` is the bilateral Laplace transform of `(1)`.

`[CONJECTURE: FORMAL GATE OPEN]` The Guinand--Weil formula extends to the triangular
autocorrelation of `(1)` and gives the exact identity

```text
b_L(a_N)=q_L(N)                                              (27)
```

for every `N>=exp(2L)`.

The paper proof should use smooth even approximation of `v_(a,L)` in `L2`, convergence of the
autorrelations in the compactly supported bounded-variation class, absolute convergence of the
Gamma multiplier integral, and finite stabilization of the prime sum away from tent endpoints.
At an endpoint `log k`, the continuous tent value fixes the limiting convention.  No unproved
distributional sign may be imported: the polar kernel must retain the corrected `(+,-)` rank-two
orientation from `ccm-polar-prime-critical-mellin-defect-law.md`.

## Candidate completed-source theorem

Define the complete source coefficient sequence by `(5)`--`(8)`, with its finitely many small
indices included directly, and set

```text
B_L(s)=sum_(N>=1)b_L(a_N)N^(-s)                              (28)
```

on its initial half-plane.

`[CONJECTURE]` For every `L>0`, `B_L` has a canonical meromorphic continuation to `Re s>1` whose
simple poles are exactly

```text
s=rho+1/2,
xi(rho)=0,
Re rho>1/2.                                                  (29)
```

If `rho` has analytic multiplicity `m(rho)`, then

```text
Res_(s=rho+1/2) B_L(s)
 =2*m(rho)*A_L(rho-1/2)^2.                                  (30)
```

Consequently the normalized weighted pole divisor of the prime--Gamma series `(12)` is exactly
the complete off-critical Xi divisor, and

```text
RH iff B_L is holomorphic on Re s>1.                         (31)
```

Once `(27)` is proved, `(28)`--`(31)` follow from the already proved cutoff-free observable
divisor-tomography theorem.  The only new mathematical gate is therefore the exact source identity,
not another divisor-side continuation argument.

## Positive CCM law

The required source carrier has now been reduced to a concrete incidence rather than a no-go:

```text
fixed Gamma logarithmic multiplier
  + fixed small-prime tent
  + cofinal moving von Mangoldt tent
  + even polar boundary square
  = multiplicity-exact transverse divisor observable.       (32)
```

The moving tent in `(9)` continuously pays for new primes.  The archimedean factor supplies the
fixed completion, while the polar square cancels the critical square-root main mass with the
correct orientation.  A successful semilocal or operator realization must reproduce `(16)` before
attempting a lower floor; finite spectra or finite positivity alone do not identify these
coefficients.

## Attacks

1. **Parent-theory attack.**  Equality `(27)` is a specialization of the Guinand--Weil explicit
   formula.  It is a bridge by itself.  The prime--polar theorem `(20)`--`(24)` does not use that
   identity; its candidate new content is one fixed moving prime window, exact polar cancellation,
   ordinary integer Dirichlet compression, and multiplicity-exact pole tomography.  This
   conjunction must pass a primary-literature audit.
2. **Normalization attack.**  A missing factor `2`, the opposite sign for the polar multiplier, or
   a Fourier-normalization mismatch invalidates `(11)`.  The source formula must be checked against
   the physical rank-two kernel and Parseval, not copied from the disputed printed sign.
3. **Endpoint attack.**  Prime powers can lie at tent breakpoints.  The approximation theorem must
   recover the continuous triangular value, not an arbitrary half-atom convention.
4. **Regularity attack.**  The rectangle itself is discontinuous, but its autocorrelation is
   continuous, compactly supported, and piecewise linear.  The proof must work at that exact
   regularity or provide a limit theorem strong enough to preserve all three source channels.
5. **Source-purity attack.**  Defining `b_L` through `q_L`, Xi zeros, or a target-fed Cauchy packet
   is forbidden.  The left side of `(11)` must remain exactly `(4)`--`(9)`.
6. **Significance attack.**  Even if correct, `(11)`--`(15)` do not prove RH.  They close the
   prime--archimedean realization of the detector; the cofinal lower floor remains the RH-bearing
   theorem.

## Lean program

1. Formalize the interval autocorrelation and prove `(3)` without a measure-zero endpoint gap.
2. Prove the explicit Fourier transform `(2)` and absolute Gamma-integrability.
3. Formalize the even polar feature and its exact value `(6)`.
4. Define the finite von Mangoldt tent functional and prove the support localization `(8)`--`(9)`.
5. Prove the compact-uniform Riemann-sum estimate `(18)` and the holomorphy of `H_L`.
6. Construct the prime--polar continuation `(20)`, prove the pole cancellation `(21)`, and compute
   every zero residue `(23)`.
7. Build a concrete Guinand--Weil theorem for the continuous piecewise-linear autocorrelation.
   No `Prop` interface, abstract explicit-formula hypothesis, project axiom, or target-defined source
   is permitted.
8. Prove `(27)` for the actual rectangular polarization.
9. Prove the holomorphic quotient law `(25)` and audit axioms.

## Gates

- [x] exact source coefficient isolated
- [x] prime support and moving-window geometry derived
- [x] polar orientation retained
- [x] stronger Gamma-free prime--polar carrier isolated
- [x] exact pole-cancellation constant derived
- [x] parent-theory and source-purity attacks stated
- [ ] interval autocorrelation and Fourier transform formalized
- [ ] Gamma integral convergence formalized
- [ ] compact-uniform moving-tent Riemann-sum theorem formalized
- [ ] prime--polar divisor tomography formalized
- [ ] exact piecewise-linear Guinand--Weil source identity formalized
- [ ] source-built Dirichlet tomography capstone formalized
- [ ] primary-literature novelty audit
- [ ] standalone paper integration
