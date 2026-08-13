# The critical Euler logarithmic derivative is a weighted prime-shift accretivity problem

- **ID:** `critical-euler-weighted-shift-accretivity-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** weighted Laplace RKHS theory, the completed Euler logarithmic derivative, and
  the critical two-channel Weil resolvent law
- **Statement:** The complete critical Euler--Weil Gram kernel is unitarily the Hermitian part of
  one weighted unilateral-shift operator. Each Euler monomial becomes a shift by its logarithm with
  exact critical norm `n^(-1/2)`, and compact support makes the prime cutoff exact. RH is precisely
  accretivity of the completed all-prime operator.

## Weighted Laplace space

Let

```text
H=L2(R_+,e^(-x)dx)                                         (1)
```

and define the weighted Laplace transform

```text
(Lcal g)(z)=integral_0^infinity g(x)e^(-zx)e^(-x)dx.       (2)
```

The evaluation vector at `z` is

```text
k_z(x)=e^(-conjugate(z)x),                                 (3)
```

and therefore

```text
<k_eta,k_z>_H
 =1/(z+conjugate(eta)+1).                                  (4)
```

Thus `Lcal(H)` is the reproducing-kernel space with kernel

```text
k_1(z,eta)=1/(z+conjugate(eta)+1),                         (5)
```

initially on `Re z,Re eta>0` and canonically on its maximal half-plane.

## Exact weighted shifts

For `h>=0`, define

```text
(S_h g)(x)=e^h 1_(x>=h) g(x-h).                            (6)
```

Then

```text
Lcal(S_h g)(z)=e^(-hz)Lcal(g)(z),                          (7)

||S_h g||_H^2=e^h||g||_H^2,
||S_h||=e^(h/2).                                          (8)
```

### Proof

Substitute `x=y+h` in `(2)`:

```text
integral_h^infinity e^h g(x-h)e^(-zx)e^(-x)dx
 =e^(-hz) integral_0^infinity g(y)e^(-zy)e^(-y)dy.        (9)
```

The same substitution in the norm proves `(8)`.

For `h=log n`, equations `(7)`--`(8)` give

```text
n^(-1-z)  <->  n^(-1)S_(log n),
||n^(-1)S_(log n)||=n^(-1/2).                             (10)
```

This is the critical Weil weight. It is not inserted by normalization after the fact; it is the
operator norm forced by the weighted boundary.

## Completed prime-shift operator

Put

```text
X(w)=xi(1/2+w),
L_X(w)=X'(w)/X(w),
F(z)=L_X(z+1/2)=xi'(1+z)/xi(1+z).                         (11)
```

For `Re z>0`, the absolutely convergent completed Euler formula is

```text
F(z)
 =b(1+z)-sum_(n>=2)Lambda(n)n^(-1-z),                     (12)

b(s)=1/s+1/(s-1)-1/2 log pi+1/2 psi(s/2).                 (13)
```

Let `B` denote multiplication by `b(1+z)` on the Laplace RKHS, interpreted on the span of its
kernel vectors. Equations `(10)` and `(12)` give the exact source form

```text
T
 =B-sum_(n>=2)Lambda(n)/n*S_(log n).                      (14)
```

On the kernel-vector core, `(14)` means the locally uniformly convergent multiplier in `(12)`; no
separate convergence of the operator-norm series is asserted or needed.

## Accretivity-kernel identity

For `Re z,Re eta>0`, put

```text
C_F(z,eta)
 =(F(z)+conjugate(F(eta)))
   /(z+conjugate(eta)+1).                                  (15)
```

If

```text
g=sum_j c_j k_(z_j),                                      (16)
```

then reproducing-kernel algebra gives

```text
2 Re <Tg,g>_H
 =sum_(j,k) conjugate(c_j)c_k C_F(z_j,z_k).                (17)
```

Equivalently, `C_F` is the Gram kernel of the Hermitian part `T+T^*` on the kernel core.

Under

```text
w=z+1/2,
v=eta+1/2,                                                (18)
```

equation `(15)` becomes

```text
C_F(z,eta)
 =(L_X(w)+conjugate(L_X(v)))/(w+conjugate(v)).             (19)
```

This is exactly the critical logarithmic-derivative kernel in
`critical-logderivative-two-channel-weil-resolvent-law.md`.

## RH equivalence

The following are equivalent:

```text
(i)   RH;
(ii)  C_F is positive on every finite node set in Re z>0;
(iii) Re<Tg,g>_H>=0 for every g in the kernel-vector core;
(iv)  the completed weighted prime-shift form T is accretive. (20)
```

The equivalence `(ii)<->(iii)<->(iv)` is `(17)`. The critical two-channel theorem proves
`(i)<->(ii)`. Thus the source-side Connes problem is exactly

```text
Re <B g,g>
 >=Re sum_(n>=2)Lambda(n)/n <S_(log n)g,g>
for every source-core vector g.                            (21)
```

This is a positive domination theorem for the **completed sum**. Neither side is asserted to be a
positive operator separately.

## Exact aperture cutoff

Suppose `g` is supported in `[0,A]`. Then `S_h g` is supported in `[h,h+A]`, and hence

```text
<S_h g,g>_H=0 for h>A.                                    (22)
```

Therefore the prime side of `(21)` is exactly finite:

```text
sum_(n>=2)Lambda(n)/n <S_(log n)g,g>
 =sum_(2<=n<=e^A)Lambda(n)/n <S_(log n)g,g>.              (23)
```

In a symmetric interval of diameter `2a`, the same overlap law is `log n<=2a`, or

```text
n<=e^(2a).                                                 (24)
```

This recovers Suzuki's/CCM's exact finite-aperture prime cutoff from support geometry. It does not
truncate the subsequent radial index; that distinction remains the one proved in
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-prime-shift-radial-index-separation-law.md`.

## Prime-character carrier

At cutoff `N=e^A`, the shifts contain the independent translation lengths

```text
{log p:p<=N},
rank_Q=pi(N).                                              (25)
```

The neutral signed-Gamma boundary law bounds every recurrent DA output of the archimedean field by

```text
delta_beta+2m(n+1),
delta_beta in {0,1}.                                       (26)
```

Hence any bounded-complexity proof of `(21)` must realize a complementary shift/feature module of
rank at least

```text
pi(N)-delta_beta-2m(n+1).                                  (27)
```

The weighted shifts in `(14)` are an explicit carrier of that module. Replacing them by Gamma
phases, polynomial jets, or Stokes corrections destroys the exact source operator.

## Positive CCM law

The route has now been reduced to one operator statement:

```text
one archimedean weighted-Laplace boundary form
  + all von Mangoldt shifts with exact critical norms
  -> accretive completed operator T
  -> positive two-channel Weil resolvent kernel
  -> conserved zero aperture Morse charge
  -> RH.                                                    (28)
```

The remaining theorem is not finite-dimensional spectral agreement. It is accretivity of the
closed all-prime form, or an explicit factorization of its Hermitian part, compatible with the
compact-support filtration `(23)`.

## Scientific status

Weighted Laplace shifts, reproducing-kernel accretivity, and the Euler logarithmic derivative are
standard. The exact assembly is useful Connes-route infrastructure but does not clear the novelty
gate.

## References

- The completed Euler logarithmic derivative in `Re s>1`.
- `critical-logderivative-two-channel-weil-resolvent-law.md`.
- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- `signed-archimedean-gamma-orbit-charge-phase-law.md`.

## Lean decision

The formal tree has no weighted Laplace RKHS, unbounded multiplier form, or analytic Euler
multiplier. Formalizing only the shift norm `(8)` would not certify the source identity `(14)` or
the RH equivalence, so no Lean file is added.

## Gates

- [x] weighted Laplace RKHS constructed
- [x] prime monomials converted to exact weighted shifts
- [x] critical `n^(-1/2)` norm derived
- [x] completed Euler shift form identified
- [x] accretivity kernel proved
- [x] RH equivalence proved
- [x] exact compact-support prime cutoff proved
- [x] signed-Gamma complementary carrier budget attached
- [ ] factor the Hermitian part of `T` through a source-defined positive space
- [ ] prove accretivity and RH
