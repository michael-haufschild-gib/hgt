# Finite divisor data and differential aperture are independent coordinates

- **ID:** `finite-divisor-differential-aperture-orthogonality`
- **Stage:** 2-fully-proven / paper proof complete
- **Type:** THEOREM (paper) / POSITIVE SOURCE--DIVISOR COUPLING LAW / GENERAL HT LANDSCAPE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Multiplication by a nonzero rational base factor preserves minimal algebraic-
  differential order exactly while inserting its divisor. Consequently every finite effective
  divisor occurs on an entire function of every prescribed finite differential aperture and on a
  hypertranscendental entire function. In the functional-equation setting, a symmetric orbit
  polynomial inserts an arbitrary generic off-critical zero orbit without changing differential
  aperture, hypertranscendence, order-one growth, the functional equation, or Schwarz reality.
  Therefore a successful RH invariant must positively couple the infinite arithmetic source to the
  divisor and must detect polynomial orbit insertion.

## 1. Rational gauge invariance of differential aperture

Let `K` be a differential field of characteristic zero, `D` its derivation, and define

```text
J_m(f)=K(f,Df,...,D^m f).                                  (1)
```

For `q in K^x`, Leibniz gives

```text
D^j(qf)=sum_(ell=0)^j binom(j,ell) D^(j-ell)q D^ell f.     (2)
```

For fixed `m`, equations `(2)` form a lower-triangular linear transformation from

```text
(f,Df,...,D^m f)
```

to

```text
(qf,D(qf),...,D^m(qf))                                    (3)
```

whose diagonal entries are all the nonzero element `q`. The transformation is invertible over
`K`; equivalently, apply the same formula to `f=q^(-1)(qf)`. Hence

```text
J_m(qf)=J_m(f)                                             (4)
```

for every `m`.

`[PROVED]` Writing `ap_K` for minimal differential aperture,

```text
ap_K(qf)=ap_K(f).                                         (5)
```

Indeed, `f,Df,...,D^m f` are algebraically dependent over `K` exactly when the transformed jet
tuple `(3)` is. Thus the first derivative level at which dependence occurs is unchanged. The case
`ap_K(f)=infinity` gives the familiar closure consequence

```text
f HT over K iff qf HT over K.                              (6)
```

This is the exact positive gauge law: rational divisor insertion consumes zero differential
aperture.

## 2. Zero-free units of every aperture

Work over `K=C(s)`. Define the exponential cascade

```text
U_0(s)=1,
U_1(s)=exp(s),
U_(n+1)(s)=exp(U_n(s)).                                    (7)
```

Every `U_n` is entire and zero-free. The exact entire-cascade order theorem gives

```text
ap_(C(s))(U_n)=n                                           (8)
```

for every finite `n>=0`.

There is also a zero-free entire HT unit. Hölder's theorem makes `Gamma` HT over `C(s)`. Since DA
elements form a field,

```text
g(s)=1/Gamma(s)                                            (9)
```

is entire and HT. Put

```text
U_infinity(s)=exp(g(s)).                                  (10)
```

If `U_infinity` were DA, then its logarithmic derivative

```text
U_infinity'/U_infinity=g'                                 (11)
```

would be DA. But an ADE for `g'` is an ADE for `g` after shifting every derivative index by one,
so `g` would be DA, a contradiction. Therefore

```text
ap_(C(s))(U_infinity)=infinity.                           (12)
```

## 3. Arbitrary finite divisor at arbitrary aperture

Let

```text
D=sum_(a in A) m_a[a]                                     (13)
```

be any finite effective divisor on `C`. Choose its polynomial

```text
Q_D(s)=product_(a in A)(s-a)^(m_a).                       (14)
```

For `n in N union {infinity}`, define

```text
F_(D,n)=Q_D U_n.                                          (15)
```

Because `U_n` is entire and zero-free,

```text
Div(F_(D,n))=D.                                           (16)
```

Because `Q_D in C(s)^x`, the gauge law `(5)` gives

```text
ap_(C(s))(F_(D,n))=n.                                     (17)
```

> **Finite divisor--aperture orthogonality law.** Finite divisor information imposes no lower or
> upper constraint on differential aperture. Every finite divisor supports functions at every
> finite algebraic-differential order and at hypertranscendental order.

Thus differential complexity and finite zero data are genuinely independent coordinates of the
HT landscape.

## 4. Functional-equation orbit insertion

Let `F` be an entire function satisfying

```text
F(1-s)=F(s),
F(conj(s))=conj(F(s)).                                    (18)
```

For a generic point `rho` off the critical line and off the real axis, define its free orbit

```text
O_rho={rho,1-rho,conj(rho),1-conj(rho)}                   (19)
```

and orbit polynomial

```text
Q_rho(s)=product_(omega in O_rho)(s-omega).               (20)
```

Then

```text
Q_rho(1-s)=Q_rho(s),
Q_rho(conj(s))=conj(Q_rho(s)).                            (21)
```

Consequently `F_rho=Q_rho F` satisfies the same functional equation and Schwarz reality, has the
same entire-function order as `F`, and contains the added off-critical orbit `O_rho`. The gauge law
gives

```text
ap_(C(s))(F_rho)=ap_(C(s))(F).                            (22)
```

In particular, if `F` is HT, so is `F_rho`. Therefore

```text
HT + order-one growth + FE + Schwarz reality
```

is stable under insertion of an arbitrary generic off-critical orbit and cannot itself select the
critical line.

The positive content is not “these properties fail.” It is:

> **Orbit-sensitivity obligation.** Every invariant capable of proving RH must change under
> multiplication by `Q_rho`. Equivalently, it must couple to a global arithmetic/source structure
> that polynomial orbit insertion destroys.

## 5. The required source--divisor coupling

The theorem separates three resources:

```text
differential aperture, finite divisor data, arithmetic source constraint.   (23)
```

The first two are independent by `(17)`. FE and Schwarz symmetry do not couple them by `(18)`--
`(22)`. Hence a viable route must supply a third structure whose compatibility with the divisor is
not rational-gauge invariant. Examples of the required positive carrier are:

1. a self-adjoint realization whose determinant identity fixes the complete divisor, not merely
   the determinant's HT class;
2. a de Branges ordering or Hamiltonian positivity theorem tied to the exact Euler coefficients;
3. a Nyman--Beurling closure theorem whose norm limit transports the completed divisor;
4. Weil positivity on the complete source-defined test space, not on a finite jet or truncation;
5. the full Li hierarchy with a proved source-to-zero equivalence, not a bounded recurrence for its
   generator.

Thus the common positive route law is

```text
RH-capable information
  => infinite source constraint + divisor-sensitive compatibility
     that is not invariant under symmetric polynomial orbit insertion.      (24)
```

## 6. Attacks and boundaries

1. **The multiplier must lie in the base field.** Multiplication by an arbitrary DA or HT function
   need not preserve minimal aperture. The exact theorem is for `q in K^x`.
2. **Finite divisor is load-bearing in the realization theorem.** Its polynomial lies in `C(s)`.
   An arbitrary infinite canonical product may itself carry differential complexity.
3. **Zero-free finite-order HT units do not exist.** Hadamard factorization makes every zero-free
   finite-order entire function an exponential of a polynomial and hence DA. The HT unit
   `U_infinity` therefore has infinite order. This does not affect orbit insertion into an already
   order-one HT function such as a completed zeta carrier: polynomial multiplication preserves its
   order.
4. **The theorem does not move existing zeros.** It proves independent finite orbit insertion, which
   is exactly enough to show that a gauge-invariant property cannot imply RH.
5. **Exact RH criteria are not gauge invariant.** Weil positivity, the complete Li criterion, and a
   genuine self-adjoint determinant identity are expected to detect the inserted orbit. The theorem
   demands that detection rather than rejecting those criteria.

## 7. Parent and novelty verdict

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

The rational gauge lemma is an invertible triangular Leibniz transformation. Finite-aperture units
come directly from the already proved exact exponential-cascade theorem; the infinite-aperture unit
uses Hölder plus standard differential-field closure. Functional-equation orbit insertion is the
polynomial-multiplicative softness mechanism already present in the project and ultimately reduces
to elementary divisor multiplication.

The theorem is valuable because it identifies the exact positive missing resource—source--divisor
coupling—but it is a direct synthesis of established parents and fails the scientific-novelty gate.

## 8. Lean status

The tree contains polynomial orbit factors, analytic-order additivity, and several formal
multiplicative-softness theorems. It does not contain the complete minimal differential-aperture
theory or the exact entire-cascade theorem needed for all `n`, nor Hölder's theorem in the form
needed for `(12)`. A wrapper for rational multiplication would not formalize the whole claim. The
complete unconditional paper theorem remains stage 2.

## Gates

- [x] rational gauge invariance proved at every jet level
- [x] zero-free entire units constructed at every finite aperture
- [x] zero-free HT entire unit constructed
- [x] arbitrary finite divisor realized at every aperture
- [x] FE/Schwarz orbit-insertion law proved
- [x] positive source--divisor coupling obligation stated
- [x] parent reduction and novelty rejection completed
- [ ] complete unconditional Lean formalization
