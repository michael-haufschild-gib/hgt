# Theta Wigner--Eisenstein orientation current

- **ID:** `theta-wigner-eisenstein-orientation-current`
- **Stage:** 1-in-progress
- **Type:** THEOREM PACKAGE / DIRECT HILBERT--POLYA SOURCE COORDINATE
- **Scientific status:** `[PAPER DERIVATION COMPLETE] [LEAN PARTIAL] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Claim:** The Hermitian diagonal of the critical Xi Bezoutian is a positive radial moment of the
  Wigner distribution of Hedenmalm's theta source.  The Wigner distribution has an exact
  divisor-character/Bessel expansion carrying the full prime-log module.  Consequently the
  missing orientation is a mixed center-frequency theorem; no fiberwise-positive factorization
  can supply it.

## 1. General Wigner current

Let `k : R -> R` be even and superexponentially decreasing, and put

```text
X(w)=integral_R k(x) exp(w x) dx.
```

For `y,b in R`, define the Wigner distribution

```text
W_k(y,b)=integral_R k(y+t)k(y-t)exp(2 i b t)dt.            (1)
```

It is real and even in both variables.  If `w=a+i b` with `a>0`, then the Hermitian diagonal of
the logarithmic-derivative Bezoutian satisfies

```text
B_X(w,w)
 =(X'(w)conj(X(w))+X(w)conj(X'(w)))/(2a)
 =a^(-1) integral_0^infinity
      r sinh(a r) W_k(r/2,b)dr.                           (2)
```

### Proof of (2)

Expand the numerator as the absolutely convergent double integral

```text
integral_R integral_R
  (x+t)k(x)k(t)exp(w x+conj(w)t)dxdt.                     (3)
```

Use `r=x+t`, `q=x-t`, whose Jacobian is `1/2`.  The inner `q`-transform is

```text
integral_R k((r+q)/2)k((r-q)/2)exp(i b q)dq
 =2 W_k(r/2,b).                                          (4)
```

Thus `(3)` equals

```text
integral_R r exp(a r)W_k(r/2,b)dr.                        (5)
```

Evenness of `k` makes `W_k` even in its first variable.  Pairing `r` with `-r` turns `(5)` into

```text
2 integral_0^infinity r sinh(a r)W_k(r/2,b)dr.
```

Division by `2a` proves `(2)`.

## 2. Exact RH orientation statement

Take the correctly normalized Hedenmalm source

```text
k(x)=2 VarTheta_00(i exp(2x)),
X(w)=xi(1/2+w).                                          (6)
```

The scalar Hermitian-diagonal orientation gate and `(2)` give

```text
RH
 iff integral_0^infinity
       r sinh(a r) W_k(r/2,b)dr >= 0
     for every 0<a<1/2 and every b in R.                  (7)
```

The right side is not an unpointed moment condition.  The frequency `b` retains the complete
horizontal phase, and the full critical-width family `0<a<1/2` retains the transverse divisor
rather than a finite prefix.  Full matrix positivity may be tested on the Euler half-plane
`a>1/2`, but the scalar-diagonal equivalence in `(7)` uses the critical half-strip; these two
statements must not be conflated.

## 3. Fiberwise positivity is impossible

For fixed `y`, the function

```text
t |-> k(y+t)k(y-t)
```

has Fourier transform `W_k(y,b)`.  Requiring it to be nonnegative for every `(y,b)` is precisely
nonnegativity of the pure-state Wigner distribution of `k`, up to harmless rescaling conventions.
Hudson's theorem then forces

```text
k(x)=C exp(-alpha x^2+beta x),  Re alpha>0.                (8)
```

Evenness and positivity reduce `(8)` to a centered Gaussian.  Hedenmalm's theta source is not
Gaussian: its positive-tail logarithm has a double-exponential leading term, whereas the logarithm
of `(8)` is quadratic.  Therefore `W_k` has a negative region.

The positive implementation law is consequently:

> A successful theta/Hilbert--Polya factorization must mix center slices before reading
> orientation.  It cannot make the tail kernel positive by proving each difference-frequency
> fiber positive separately.

This is a direct application of Hudson's classical rigidity theorem, hence a bridge rather than
new science.

## 4. Divisor-character/Bessel expansion

Write the theta source as its absolutely convergent atom sum

```text
k(x)=sum_(n>=1) k_n(x),
k_n(x)=exp(x/2) P(n exp x) exp(-pi n^2 exp(2x)),
P(u)=4pi^2 u^4-6pi u^2.                                  (9)
```

For an ordered pair `(n,m)`, put

```text
c=2pi n m exp(2y),
v=t+(1/2)log(n/m).                                       (10)
```

Then

```text
n^2 exp(2y+2t)+m^2 exp(2y-2t)=2nm exp(2y)cosh(2v),       (11)

P(n exp(y+t))P(m exp(y-t))
 =c^4-6c^3 cosh(2v)+9c^2.                                (12)
```

Using

```text
K_nu(c)=(1/2)integral_R exp(-c cosh u)exp(nu u)du,
```

the ordered-pair Wigner contribution is

```text
W_(n,m)(y,b)
 =exp(y)(m/n)^(i b) Kcal_b(c),                            (13)

Kcal_b(c)
 =(c^4+9c^2)K_(i b)(c)+6c^3 partial_c K_(i b)(c).        (14)
```

Grouping by `r=nm` gives the exact arithmetic expansion

```text
W_k(y,b)
 =exp(y) sum_(r>=1) tau_b(r) Kcal_b(2pi r exp(2y)),       (15)

tau_b(r)
 =sum_(nm=r)(m/n)^(i b)
 =r^(i b) sigma_(-2 i b)(r)
 =r^(-i b) sigma_(2 i b)(r).                             (16)
```

The last equality follows by the divisor involution and also shows `tau_b(r)` is real.  Its Euler
factor at `p^j` is

```text
tau_b(p^j)=sum_(ell=0)^j exp(i b(j-2ell)log p).            (17)
```

Hence `(15)` retains every prime-log character and packages it in the standard divisor
coefficient occurring in the Fourier expansion of the real-analytic Eisenstein series.  The
archimedean channel is the Bessel differential kernel `Kcal_b`; the arithmetic channel is
`tau_b`.

Substitution into `(7)` gives the explicit source orientation current

```text
O(a,b)
 =sum_(r>=1) tau_b(r)
    integral_0^infinity
      u sinh(2a u) exp(u)
      Kcal_b(2pi r exp(2u))du,                            (18)

RH iff O(a,b)>=0 for every 0<a<1/2 and b in R,            (19)
```

up to the positive factor `4/a` produced by `r=2u`.  Formula `(18)` records only the sign-relevant
normalization; `(15)`--`(16)` are the primary exact coordinates.

### Ordered-pair Mellin signature `[PROVED ON PAPER; ALGEBRAIC CORE IN LEAN]`

Before grouping by `r=nm`, the same atoms admit a second exact description which determines the
ambient signature.  For `w=a+i b` with `a>1/2`, put

```text
X_n(w)=integral_R k_n(x)exp(w x)dx.
```

The substitution `t=n exp(x)` gives

```text
X_n(w)=A(w)n^(-w-1/2),                                   (18o)

A(w)=integral_0^infinity
       t^(w-1/2)P(t)exp(-pi t^2)dt
    =(w^2-1/4)/2 * pi^(-w/2-1/4)
       Gamma(w/2+1/4).                                   (18p)
```

The last equality follows from the elementary Gaussian Mellin integral and one Gamma recurrence.
In the half-plane `a>1/2`, the sum of `(18o)` is absolutely convergent and `A(w)!=0`.

Expand the Hermitian diagonal `(2)` before summing the ordered pairs.  If

```text
C(a,b)=Re(A'(w)conj(A(w)))/a,
d(a,b)=|A(w)|^2/(2a)>0,
```

then its `(n,m)` entry is

```text
K_(n,m)(a,b)
 =(nm)^(-a-1/2) exp(i b(log m-log n))
    * (C(a,b)-d(a,b)log(nm)).                              (18q)
```

Thus the oscillatory phase is only a diagonal unitary congruence.  For any two distinct positive
integers `n_1,n_2`, the corresponding Hermitian principal determinant is exactly

```text
det K_{n_1,n_2}
 =-d(a,b)^2 (n_1 n_2)^(-2a-1)
    * (log n_1-log n_2)^2 < 0.                            (18r)
```

Indeed the phase cancels from `K_12 K_21`, and the remaining identity is

```text
(C-2du)(C-2dv)-(C-d(u+v))^2=-d^2(u-v)^2.                 (18s)
```

Consequently every two distinct theta atoms span a Krein plane: the ordered-pair kernel has one
positive and one negative direction.  This does **not** contradict possible positivity of the
actual scalar current, which evaluates the kernel only on the distinguished all-one source
section.  It proves the sharper positive implementation law:

> A successful theta/Hilbert--Polya construction must orient the distinguished cofinal all-prime
> section after archimedean completion.  It cannot obtain RH by making the ambient theta-atom
> coefficient kernel positive, by assigning a positive Gram vector to every ordered pair, or by
> extending the desired sign to arbitrary coefficient perturbations.

The restriction `a>1/2` in this signature calculation is essential: it is the region where the
Dirichlet atom expansion is absolutely convergent.  The RH-equivalent scalar gate `(7)` lies in
`0<a<1/2`, where the termwise Dirichlet expansion has crossed its convergence boundary.  The
Wigner--Eisenstein current `(15)` is the completed carrier through that crossing.  Therefore
orientation, if true, must be created by the cofinal source-selected completion rather than being
present in the uncompleted pair kernel.

### Exact Eisenstein differential realization

Put `Y=exp(2y)` and `D_Y=Y partial_Y`.  In the standard completed normalization, the nonconstant
Fourier expansion at spectral parameter `s=1/2+i b` is

```text
E*(x+iY,1/2+i b)_nonconstant
 =4 sqrt(Y) sum_(r>=1)
    tau_b(r) K_(i b)(2pi rY)cos(2pi r x).                (18a)
```

For `b=0`, the completed Eisenstein series itself has the familiar central meromorphic singularity,
but its polar part lies entirely in the constant term.  All identities below are first read for
`b!=0`; after applying the constant-term-annihilating differential factor they extend to `b=0` by
the resulting removable continuation.  No product `0*infinity` is being used.

For one Fourier mode `F_r(Y)=sqrt(Y)K_(i b)(2pi rY)`, the horizontal operator

```text
A=-Y^2 partial_x^2
```

multiplies by `(2pi rY)^2`, while

```text
((D_Y+5/2)^2+b^2)F_r
 =sqrt(Y)((D_c+3)^2+b^2)K_(i b)(c),
c=2pi rY.                                                (18b)
```

The Bessel equation gives

```text
((D_c+3)^2+b^2)K_(i b)(c)
 =(c^2+9)K_(i b)(c)+6c partial_c K_(i b)(c).             (18c)
```

Consequently the Wigner current is exactly

```text
W_k(y,b)
 =1/4 [A ((D_Y+5/2)^2+b^2)
       E*(x+iY,1/2+i b)]_(x=0,Y=exp(2y)).                (18d)
```

The horizontal operator does not commute with `D_Y`; rather,

```text
A Q(D_Y)=Q(D_Y-2)A.                                      (18e)
```

The weight-zero Laplace eigenvalue equation gives, on the Eisenstein eigenspace,

```text
A=(D_Y-1/2)^2+b^2.                                       (18f)
```

Combining the commutation shift with `(18f)` turns `(18d)` into the purely vertical fourth-order
identity

```text
W_k(y,b)
 =1/4 [P_b(D_Y)E*(iY,1/2+i b)]_(Y=exp(2y)),              (18g)

P_b(D)=((D-1/2)^2+b^2)((D+1/2)^2+b^2).                  (18h)
```

The first factor in `(18h)` annihilates both constant terms `Y^(1/2+i b)` and
`Y^(1/2-i b)`.  The full polynomial is even in `D`, exactly as required by modular inversion
`Y -> 1/Y` and evenness of the Wigner current in `y`.  Thus the archimedean differential operator
removes the Eisenstein constant term exactly, while the surviving nonconstant modes are precisely
the all-prime divisor characters `tau_b(r)`.  This is the promised source--completion incidence,
not a later spectral decoration.

### Sharp archimedean coercivity `[PROVED IN LEAN]`

On logarithmic Fourier frequency `tau`, `(18h)` has symbol

```text
p_b(tau)
 =|((i tau-1/2)^2+b^2)|^2
 =(b^2+1/4-tau^2)^2+tau^2.                               (18i)
```

Its exact lower edge is

```text
m(b)= (b^2+1/4)^2,  |b|<=1/2,
      b^2,            |b|>1/2,                           (18j)
```

and

```text
0<m(b)<=p_b(tau)                                         (18k)
```

for every real `b,tau`.  Equality occurs at `tau=0` in the first regime and at
`tau=+-sqrt(b^2-1/4)` in the second.  Thus the archimedean differential current has no negative or
null frequency.  The unresolved orientation cannot be blamed on that operator: it lies in the
mixed arithmetic/radial pairing after the coercive image has been formed.

The sharp minimizer also rules out a high-height bulk-domination proof.  For `|b|>1/2`, the
low-energy channel moves along

```text
tau^2=b^2-1/4,                                            (18k')
```

and the floor is only `b^2`, not quartic in `b`.  Hence the arithmetic current can remain resonant
with the archimedean operator at arbitrarily high spectral height.  A successful estimate must
control the divisor characters on this moving characteristic shell; it cannot discard them by a
large-`|b|` Gamma comparison.

The elementary completion polynomial has a different, equally exact radial law.  If

```text
q_b(a)=|((a+i b)^2-1/4)|^2,
```

then

```text
q_b'(a)=4a(a^2+b^2-1/4).                                  (18l)
```

Hence its radial contribution is positive outside the radius-`1/2` central disk and negative
inside it.  This sign turnover is fully formalized.  It also prevents a false inference from
coercivity of `(18h)` to orientation of `(7)`: operator energy is positive, but its critical-strip
radial readout still crosses an exact boundary chamber.

### Boundary-energy attack and exact residual

Let `E_b(t)=E*(i exp(t),1/2+i b)` and subtract its two Eisenstein constant modes, writing the
decaying nonconstant part as `N_b(t)`.  With

```text
g_a(t)=t sinh(a t),
P_b(lambda)=((lambda-1/2)^2+b^2)((lambda+1/2)^2+b^2),
```

the diagonal current is

```text
B_X(a+i b,a+i b)
 =(4a)^(-1) integral_0^infinity g_a(t)P_b(D)N_b(t)dt.     (18m)
```

Since `N_b` decays at the cusp, four integrations by parts are legitimate.  The values

```text
g_a(0)=g_a'(0)=g_a'''(0)=0,
g_a''(0)=2a
```

give the exact Green identity

```text
B_X(a+i b,a+i b)
 =-N_b'(0)/2
  +P_b(a)/(4a) integral_0^infinity t sinh(a t)N_b(t)dt
  +(a^2+b^2-1/4) integral_0^infinity cosh(a t)N_b(t)dt.  (18n)
```

Here `P_b'(a)=4a(a^2+b^2-1/4)` was used.  Formula `(18n)` attacks the apparent positive operator
directly: coercivity of `P_b(D)` turns the orientation into a **cross energy**, not a squared norm.
The cusp boundary jet and the two nonconstant Eisenstein periods remain coupled, and neither
period has a source-independent sign.

Therefore the positive carrier obligation is sharper than `P_b(D)>=0`:

> a successful construction must align the source-selected radial Green vector with the
> divisor-character Eisenstein current, including the cusp boundary jet.  Bulk coercivity alone
> cannot choose the orientation chamber.

This retires the naive positive-elliptic-operator proof while leaving `(18n)` as a concrete
boundary-energy target.

## 5. Why this is a live source architecture

The moment module uniquely reconstructs `k` and `X`; it does not orient the Bezoutian.  Equations
`(15)`--`(16)` identify the complementary object that orientation must use:

```text
pointed theta source
  + all-prime divisor-character coefficient tau_b
  + archimedean Bessel differential kernel
  + cofinal radial moment in a
  -> Hermitian orientation.                              (20)
```

This carrier is not finite-dimensional, not ordinate-only, and not a Gamma-only phase package.
Each new prime appears explicitly in `(17)`.  Hudson rigidity shows that the sign cannot be moved
inside the `y`-fibers; it must arise from the complete radial/arithmetic coupling in `(18)`.

## 6. Open proof obligations

- [x] derive the general Wigner--Bezoutian diagonal identity `(2)` on paper;
- [x] derive the atom-pair Bessel kernel `(13)`--`(14)` on paper;
- [x] group ordered pairs into the divisor character `(16)` on paper;
- [x] identify the Wigner current with the completed Eisenstein differential current
      `(18d)`--`(18h)` on paper;
- [x] prove and formalize the sharp positive symbol floor `(18i)`--`(18k)`;
- [x] derive the ordered-atom Mellin factorization `(18o)`--`(18q)` and the exact two-point
      Krein determinant `(18r)` on paper;
- [x] formalize the affine-logarithmic determinant and its weighted strict negativity in Lean;
- [x] identify the fiberwise-positive producer as impossible by Hudson rigidity;
- [x] formalize the center-mixed theta density, its exact Fubini phase identity, and its
      unconditional strict positivity, evenness, continuity, and integrability;
- [ ] complete a primary-source audit for the precise theta-product/Eisenstein parent identity;
- [ ] formalize `(2)` and `(13)`--`(16)` in Lean without assuming RH or positivity;
- [ ] formalize the analytic Mellin integral `(18o)`--`(18p)` and its differentiation/summation
      interchange in the absolute-convergence half-plane;
- [ ] formalize the removable `b=0` specialization after annihilation of the Eisenstein polar
      constant term;
- [ ] determine the exact raising-operator relation between `Kcal_b` and the weight-zero
      Eisenstein series, including normalization conventions in `(18a)`;
- [ ] prove a non-target-fed lower bound for the mixed current `(18)`, or retire it as another
      exact RH coordinate.

## References under audit

- R. L. Hudson, *When is the Wigner quasi-probability density non-negative?*, Reports on
  Mathematical Physics 6 (1974), 249--252.
- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494.
- Classical Fourier expansion of the real-analytic Eisenstein series and the integral
  representation of the modified Bessel function `K_nu`.
