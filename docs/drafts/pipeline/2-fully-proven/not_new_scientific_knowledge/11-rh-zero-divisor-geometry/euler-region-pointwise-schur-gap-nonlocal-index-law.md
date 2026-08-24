# The Euler-region Xi quotient is pointwise contractive but its RH charge is nonlocal

- **ID:** `euler-region-pointwise-schur-gap-nonlocal-index-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** Sondow--Dumitrescu horizontal monotonicity and the generalized
  Hermite--Biehler/Pick negative-index theorem
- **Statement:** On the entire Euler-convergent sampling half-plane, the shifted completed-Xi
  quotient has modulus strictly below one, so every one-node Pick test is positive unconditionally.
  Nevertheless the full Pick-kernel negative index exactly records the off-line divisor. Hence the
  surviving RH datum is irreducibly multi-node correlation, not pointwise size.

## Setup

For `omega>0`, put

```text
Theta_omega(z)
 =xi(1/2-omega-iz)/xi(1/2+omega-iz),                       (1)

S_omega(z,w)
 =i/(z-conjugate(w))
   *(1-Theta_omega(z)conjugate(Theta_omega(w))).            (2)
```

Use the Euler sampling region

```text
U_omega={z:Im z>1/2+omega}.                                (3)
```

For `z=x+iy in U_omega`, set

```text
s_-=1/2-omega-iz=(1/2-omega+y)-ix,
s_+=1/2+omega-iz=s_-+2omega.                               (4)
```

Both `s_-` and `s_+` lie in `Re s>1`, so every value in `(1)` has an absolutely convergent
Euler--Gamma product.

## Pointwise contractivity theorem

`[PROVED]` For every `omega>0` and every `z in U_omega`,

```text
|Theta_omega(z)|<1.                                        (5)
```

Consequently,

```text
S_omega(z,z)
 =(1-|Theta_omega(z)|^2)/(2 Im z)>0.                       (6)
```

### Proof

All nontrivial zeros of `xi` lie in `0<Re s<1`; hence the open half-plane `Re s>1` is zero-free.
Sondow--Dumitrescu prove that on every zero-free open right half-plane the modulus of `xi` is
strictly increasing along each horizontal half-line. The points `s_-` and `s_+` in `(4)` have the
same imaginary part and satisfy

```text
1<Re(s_-)<Re(s_+).                                         (7)
```

Therefore `|xi(s_-)|<|xi(s_+)|`, which proves `(5)`. Equation `(6)` follows directly from `(2)`.

## Nonlocal negative-index theorem

For every nonexceptional `omega>0`, the previously proved Euler Pick theorem gives

```text
ind_-(S_omega|_(U_omega x U_omega))
 =sum_(xi(rho)=0, Re rho>1/2+omega) multiplicity(rho),      (8)
```

with infinity allowed. At exceptional shifts, the same formula holds after canceling the common
divisor of the numerator and denominator in `(1)`.

Equations `(6)` and `(8)` have a sharp consequence:

```text
every one-node Euler Pick matrix is strictly positive,
but an off-line zero forces a negative eigenvalue in a finite matrix
formed from two or more Euler-region nodes.                                (9)
```

The second clause follows from the definition and locality of negative squares: if the index in
`(8)` is positive, some finite Gram matrix is indefinite. Equation `(6)` excludes a one-node
witness.

## Positive correlation hierarchy

Define the first failing correlation order

```text
r(omega)
 =inf{N>=1: there exist z_1,...,z_N in U_omega
             with lambda_min((S_omega(z_j,z_k))_(j,k))<0},  (10)
```

with `r(omega)=infinity` if no such matrix exists. Then

```text
r(omega)>=2 unconditionally,                               (11)

r(omega)=infinity
 <-> no xi-zero has Re rho>1/2+omega                       (12)
```

at nonexceptional shifts, with the standard common-divisor convention otherwise. Thus RH is the
positive all-orders statement

```text
r(omega)=infinity for every omega>0.                        (13)
```

This is not a pointwise modulus conjecture on the Euler region: that modulus theorem is already
true. It is complete positivity of the full source correlation system.

## Exact Euler-factor cocycle

For any scalar functions `f,g`, let

```text
K_f(z,w)=i(1-f(z)conjugate(f(w)))/(z-conjugate(w)).          (14)
```

The identity

```text
K_(fg)=K_f+f(z)conjugate(f(w))*K_g                          (15)
```

is exact. On `U_omega`, write the completed quotient as

```text
Theta_omega=A_omega product_p theta_(p,omega),              (16)

theta_(p,omega)(z)
 =(1-p^(-s_+))/(1-p^(-s_-)),                               (17)
```

where `A_omega` is the explicit polynomial--Gamma quotient. Iterating `(15)` gives the exact
prime--archimedean correlation cascade for every finite Euler product.

At the real anchor `z=iy in U_omega`, one has `0<p^(-s_+)<p^(-s_-)<1`, and therefore

```text
theta_(p,omega)(iy)>1,
K_(theta_(p,omega))(iy,iy)<0.                               (18)
```

So no prime-local factor is a positive Pick carrier in this orientation. The completed quotient is
pointwise contractive only after the one archimedean boundary direction and the complete infinite
Euler cascade are coupled.

## Positive requirement for the Connes--CCM route

The surviving source theorem must have the form

```text
weighted all-prime correlation cascade
  + finite-degree archimedean boundary
  -> every finite Euler-region Pick matrix is positive
  -> transverse negative index is zero
  -> RH.                                                     (19)
```

Finite-prime pointwise positivity, modulus bounds, and one-node margins cannot carry this charge:
they already hold in the full Euler region even if RH is false. The missing invariant is complete
matrix positivity across an unbounded correlation order, or an equivalent index-preserving
factorization of the whole cascade.

This grounds the finite-Gamma boundary law precisely. Completion supplies one projective
archimedean direction, while the prime factors in `(17)` supply the infinite arithmetic phase
carrier. Their incidence must be established before taking a positivity or Fredholm limit.

## Scientific status

Horizontal monotonicity is Sondow--Dumitrescu; the negative-index formula and locality are
classical generalized-Schur theory as specialized in the existing Euler Pick card; `(15)` is the
standard product-kernel identity. Their combination identifies the correct correlation order but
does not clear the novelty gate.

## References

- J. Sondow and C. Dumitrescu, *A monotonicity property of Riemann's xi function and a
  reformulation of the Riemann Hypothesis*, Period. Math. Hungar. 60 (2010), 37--40,
  https://arxiv.org/abs/1005.1104.
- `euler-pick-inertia-offline-zero-count.md` and its Krein--Langer/Alpay--Rovnyak parents.
- `finite-archimedean-gamma-product-boundary-law.md`.

## Lean decision

The formal tree does not contain horizontal Xi monotonicity or the analytic generalized Pick
kernel. Formalizing only `(15)` would be a scalar algebra wrapper, so no Lean file is added.

## Gates

- [x] exact Euler-region quotient fixed
- [x] strict pointwise contractivity proved
- [x] all one-node Pick tests proved positive
- [x] full negative index identified with the off-line divisor
- [x] first failing correlation order defined
- [x] exact Euler-product kernel cocycle proved
- [x] every prime-local anchor contribution shown negative
- [ ] prove complete positivity of the infinite prime--archimedean cascade


## Lean status update (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/PickKernelProduct.lean` and
`formal/GaloisForLFunctions/HTGeometry/PickKernelFiniteProduct.lean` now formalize the exact
one-factor and ordered finite-product Nevanlinna--Pick identities. The latter records the finite
Euler-factor telescoping recursion without analytic assumptions. Both leaves are wired into
`HTGeometry.lean`, leaf-checked with `lake env lean`, target-built, and their new theorem
declarations audit to only `propext`, `Classical.choice`, and `Quot.sound`.

This closes finite algebraic kernel assembly only. It neither proves horizontal Xi monotonicity nor
constructs the analytic generalized Pick kernel, so the card remains at stage 2.

## Lean status update (2026-08-24)

`formal/GaloisForLFunctions/RHTower/XiShiftEulerPointwiseContractivity.lean` now closes the complete
pointwise half of the card for the actual completed-Xi quotient. Reusing the already formalized
unconditional half-strip zero bound and Sondow--Dumitrescu strict horizontal monotonicity, it proves

```text
Im z > 1/2+omega, omega>0 -> |Theta_omega(z)|<1
                              and Re S_omega(z,z)>0.
```

The leaf includes the exact rotation between the centered right-half-plane kernel and the literal
upper-half-plane formulas `(1)`--`(3)`. Exact source check and targeted leaf build pass; all eight
public declarations audit to only `propext`, `Classical.choice`, and `Quot.sound`. It is wired into
`RHTower.lean` without an umbrella build.

Remaining dependency is the full analytic generalized-Pick divisor-index theorem for the actual
shifted-Xi kernel. The new abstract locality/finite-Gram leaf closes locality after such a realization
exists, but does not construct that realization. Card therefore remains stage 2.
