# Theta Wigner--Eisenstein orientation current

- **ID:** `theta-wigner-eisenstein-orientation-current`
- **Stage:** 1-in-progress
- **Type:** THEOREM PACKAGE / DIRECT HILBERT--POLYA SOURCE COORDINATE
- **Scientific status:** `[PAPER DERIVATION COMPLETE] [LEAN OPEN] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
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
     for every a>1/2 and every b in R.                    (7)
```

The right side is not an unpointed moment condition.  The frequency `b` retains the complete
horizontal phase, and the cofinal family `a>1/2` retains the global divisor rather than a finite
prefix.

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
      u sinh(2a u) exp(2u)
      Kcal_b(2pi r exp(4u))du,                            (18)

RH iff O(a,b)>=0 for every a>1/2 and b in R,              (19)
```

up to the positive constant produced by `r=2u`.  Formula `(18)` is to be normalized carefully in
the formal proof; `(15)`--`(16)` are the primary exact coordinates.

### Exact Eisenstein differential realization

Put `Y=exp(2y)` and `D_Y=Y partial_Y`.  In the standard completed normalization, the nonconstant
Fourier expansion at spectral parameter `s=1/2+i b` is

```text
E*(x+iY,1/2+i b)_nonconstant
 =4 sqrt(Y) sum_(r>=1)
    tau_b(r) K_(i b)(2pi rY)cos(2pi r x).                (18a)
```

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

The weight-zero Laplace eigenvalue equation replaces `A` by

```text
A=(D_Y-1/2)^2+b^2                                       (18e)
```

on this Eisenstein eigenspace.  Hence `(18d)` is the purely vertical fourth-order identity

```text
W_k(y,b)
 =1/4 [P_b(D_Y)E*(iY,1/2+i b)]_(Y=exp(2y)),              (18f)

P_b(D)=((D-1/2)^2+b^2)((D+5/2)^2+b^2).                  (18g)
```

The first factor in `(18g)` annihilates both constant terms `Y^(1/2+i b)` and
`Y^(1/2-i b)`.  Thus the archimedean differential operator removes the Eisenstein constant term
exactly, while the surviving nonconstant modes are precisely the all-prime divisor characters
`tau_b(r)`.  This is the promised source--completion incidence, not a later spectral decoration.

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
      `(18d)`--`(18g)` on paper;
- [x] identify the fiberwise-positive producer as impossible by Hudson rigidity;
- [ ] complete a primary-source audit for the precise theta-product/Eisenstein parent identity;
- [ ] formalize `(2)` and `(13)`--`(16)` in Lean without assuming RH or positivity;
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
