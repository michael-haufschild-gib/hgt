# The polarized additive-heat finite part is the rank-one zeta-value Gram

- **ID:** `polarized-additive-heat-finite-part-is-rank-one`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Route-B heat gate
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `additive-heat-aperture-zeta-zero-echo.md`
- **Statement:** The two-parameter polarization of the additive heat aperture has constant
  polyhomogeneous finite part `zeta(s)conj(zeta(w))`.  Hence every finite superposition has
  finite-part energy equal to the square of one scalar zeta-value functional.  The resulting
  positive form has rank one and cannot equal the full Weil form.

## Polarized aperture

For

```text
1/2<Re(s)<1,
1/2<Re(w)<1,
```

use the unnormalized arithmetic vectors

```text
psi_s(n)=n^(-s)
```

and define

```text
K_(s,w)(x)
  =<psi_w,H_x psi_s>
  =sum_(m,n>=1)
     m^(-conj(w)) n^(-s) exp(-pi x(m-n)^2).             (1)
```

The series is absolutely convergent for every `x>0`.  For each fixed difference `m-n`, the inner
sum is controlled by a convolution of the two square-summable power sequences, and the outer
difference sum is Gaussian.

For every finite family `(s_j,c_j)`, positivity of `H_x` gives

```text
sum_(i,j) conj(c_i)c_j K_(s_j,s_i)(x)
  =<sum_i c_i psi_(s_i),
     H_x sum_j c_j psi_(s_j)>
  >=0.                                                  (2)
```

Thus `K(x)` is a positive sesquiholomorphic kernel before any asymptotic extraction.

## Local expansion

Let

```text
f_s(theta)=sum_(n>=1)n^(-s)exp(i n theta).
```

Near `theta=0`, on the two sides,

```text
f_s(theta)
  =A_+(s) theta^(s-1)+zeta(s)+O(theta),   theta>0,

f_s(theta)
  =A_-(s)|theta|^(s-1)+zeta(s)+O(theta),  theta<0,

A_+(s)=Gamma(1-s)exp(-i pi(s-1)/2),
A_-(s)=Gamma(1-s)exp(+i pi(s-1)/2).        (3)
```

Fourier multiplication gives

```text
K_(s,w)(x)
  =integral W_x(theta)conj(f_w(theta))f_s(theta)
     dtheta/(2pi).                                     (4)
```

For `Re(alpha)>-1`, the positive-half Gaussian moment is

```text
integral_(0,infinity)
  [exp(-theta^2/(4pi x))/(2pi sqrt(x))] theta^alpha dtheta

  =(4pi)^((alpha-1)/2)
    Gamma((alpha+1)/2)x^(alpha/2).                     (5)
```

The periodic images in `W_x` are exponentially small near the aperture limit.  Substitution of
(3) into (4), followed by (5), yields

```text
K_(s,w)(x)
  =L(s,w)x^((s+conj(w))/2-1)
   +C(s)conj(zeta(w))x^((s-1)/2)
   +conj(C(w))zeta(s)x^((conj(w)-1)/2)
   +zeta(s)conj(zeta(w))
   +o(1),                                               (6)
```

where

```text
C(s)=(1/2)pi^((s-1)/2)Gamma((1-s)/2)!=0               (7)
```

and the explicit leading singular kernel is

```text
L(s,w)
  =(4pi)^((s+conj(w)-3)/2)
    Gamma((s+conj(w)-1)/2)
    [conj(A_+(w))A_+(s)+conj(A_-(w))A_-(s)].            (8)
```

The hypotheses imply `Re(s+conj(w)-2)>-1`, so the leading Gaussian moment is valid.  Every product
involving an `O(theta)` regular remainder has positive real power of `x` and belongs to `o(1)`.
On the diagonal `w=s`, equation (6) is the previously proved heat-aperture expansion.

## Rank-one finite part

After removing every nonzero polyhomogeneous power in (6),

```text
FP_(x->0) K_(s,w)(x)
  =zeta(s)conj(zeta(w)).                                (9)
```

For a finite superposition

```text
v=sum_j c_j psi_(s_j),
```

polarization and (9) give

```text
FP_(x->0)<v,H_x v>
  =sum_(i,j)conj(c_i)c_j
      zeta(s_j)conj(zeta(s_i))

  =abs(sum_j c_j zeta(s_j))^2.                         (10)
```

Thus the canonical finite-part heat form is the Gram form of the single scalar functional

```text
v |-> sum_j c_j zeta(s_j),                              (11)
```

and has rank one.

The same conclusion holds for normalized vectors after conjugating by the positive diagonal
normalization `zeta(2 Re(s))^(-1/2)`.

## Weil-route consequence

The full Weil form has one divisor-evaluation channel for every nontrivial zero and is not a
rank-one form on its standard test space.  Therefore (9)--(11) cannot supply a factorization

```text
W_zeta(f*tilde(f))=||Jf||^2
```

on a dense Weil class.

Obtaining the divisor from (9) requires taking a logarithm, reciprocal, argument-principle residue,
or logarithmic derivative.  None is a linear polarization of the positive heat energy, and its
positivity is not inherited from (2).  The heat aperture remains a source-built pointwise zero
detector, but it does not provide Weil positivity.

Retaining all higher regular Taylor coefficients yields a positive coefficient Gram involving
`zeta(s-k)`, but positivity of a Taylor-coefficient norm is automatic for arbitrary analytic germs
and supplies no critical-line localization.

## Gates

- [x] polarized aperture convergence and positivity proved
- [x] full constant-order two-parameter expansion proved
- [x] finite part identified with the rank-one zeta-value Gram
- [x] dense Weil-factorization use excluded
- [ ] no Lean formalization planned before polylogarithm boundary asymptotics enter the API
