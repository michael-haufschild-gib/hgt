# Euler-region Pick inertia exactly counts off-line zeros

- **ID:** euler-pick-inertia-offline-zero-count
- **Stage:** 2-fully-proven/needs-audit
- **Type:** THEOREM (paper) -- novelty audit open
- **Source:** `shifted-xi-kernel-transverse-index-filtration.md`; localization of negative squares
  to an Euler-convergent uniqueness region
- **Statement:** `[PROVED HERE; CANDIDATE NEW SCIENTIFIC KNOWLEDGE; NOVELTY UNVERIFIED]` For every
  nonexceptional `omega>0`, the number of zeta zeros in `Re rho>1/2+omega`, including multiplicity
  and the value infinity, is the limiting negative inertia of an explicit nested sequence of Pick
  matrices whose entries use xi only at points with real part greater than one. Consequently every
  entry is given by an absolutely convergent infinite Euler product. This is an exact, no-height,
  no-jet recovery of the transverse divisor from the prime-side data.

## Goal

Turn the shifted-kernel divisor recorder into a source-side theorem. The off-line count should be
recoverable without evaluating xi in the critical strip and without knowing any zero ordinates.

## Setup

For `omega>0`, put

```text
Theta_omega(z)=xi(1/2-omega-iz)/xi(1/2+omega-iz),

S_omega(z,w)=i/(z-conjugate(w))
  * (1-Theta_omega(z)conjugate(Theta_omega(w))).
```

Let

```text
U_omega={z: Im z>1/2+omega}.
```

For `z in U_omega`, set

```text
s_minus(z)=1/2-omega-iz,
s_plus(z) =1/2+omega-iz.
```

Then both real parts exceed one. The xi quotient has the absolutely convergent formula

```text
Theta_omega(z)
= pi^omega
  * s_minus(z)(s_minus(z)-1)/(s_plus(z)(s_plus(z)-1))
  * Gamma(s_minus(z)/2)/Gamma(s_plus(z)/2)
  * product_p (1-p^(-s_plus(z)))/(1-p^(-s_minus(z))).       (E)
```

Choose once and for all a sequence `{z_n}` dense in `U_omega`. Define the nested Hermitian matrices

```text
P_(omega,N)=(S_omega(z_j,z_k))_(1<=j,k<=N),
```

and let `nu_-(P)` denote the number of strictly negative eigenvalues of `P`, counted with
multiplicity.

As in `shifted-xi-kernel-transverse-index-filtration.md`, call `omega` nonexceptional when the
entire functions `xi(1/2+omega-iz)` and `xi(1/2-omega-iz)` have no common nonreal zero.

## Theorem

For every nonexceptional `omega>0`,

```text
sum_(xi(rho)=0, Re rho>1/2+omega) multiplicity(rho)
= sup_N nu_-(P_(omega,N))
= lim_(N->infinity) nu_-(P_(omega,N)).                      (P)
```

Both sides may equal infinity. The limit exists because principal-matrix interlacing makes the
integer sequence `nu_-(P_(omega,N))` nondecreasing.

Equivalently, for any integer `m>=0`, zeta has at most `m` zeros in
`Re rho>1/2+omega` if and only if every finite Pick matrix formed from arbitrary points of
`U_omega` has at most `m` negative eigenvalues. In particular,

```text
no zero in Re rho>1/2+omega
iff every Euler-region Pick matrix is positive semidefinite.               (Z)
```

## Paper proof

`[PROVED HERE; NOVELTY UNVERIFIED]`

The shifted-kernel theorem proves that the global negative index of `S_omega` on its meromorphic
upper-half-plane domain is

```text
kappa(omega)
=sum_(Re rho>1/2+omega)multiplicity(rho),                    (1)
```

with the value infinity allowed.

It remains to prove that restricting the sample points to `U_omega` does not reduce the negative
index. Apply the classical locality-of-negative-squares principle for Hermitian kernels that are
analytic in one variable and antianalytic in the other on a connected domain: restriction to any
nonempty open uniqueness set has the same negative index. Alpay--Rovnyak explicitly use this
region-independence in their definition of generalized Schur classes; see D. Alpay and J. Rovnyak,
*Loewner's theorem for kernels having a finite number of negative squares*, Proc. Amer. Math. Soc.
127 (1999), 1109--1117, DOI `10.1090/S0002-9939-99-04618-3`, Section 2 and the cited
region-independence theorem. In the finite-index case, the principle
has the following short reproducing-kernel proof. The kernel sections with `w in U_omega` have dense
span in the reproducing-kernel Pontryagin space, because a vector orthogonal to all of them
represents a meromorphic function vanishing on `U_omega` and hence vanishing identically. A
finite-dimensional negative subspace remains negative under sufficiently small perturbations of a
basis. The infinite-index statement follows by applying the same argument to negative subspaces of
every finite dimension. Therefore

```text
ind_-(S_omega restricted to U_omega)=kappa(omega).           (2)
```

Now let `{z_n}` be dense in `U_omega`. The same uniqueness argument shows that the union of the
spans of its kernel sections is dense. The negative index of the `N`-th span is exactly
`nu_-(P_(omega,N))`. Hence the supremum, and therefore the monotone limit, equals the index in
`(2)`. Combining with `(1)` proves `(P)`.

Finally, if `z in U_omega`, both `s_minus(z)` and `s_plus(z)` lie in `Re s>1`. Substitution of

```text
xi(s)=1/2*s*(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s)
```

and the absolutely convergent Euler products for the two zeta values gives `(E)`. Thus every entry
of every matrix in `(P)` is determined entirely in the ordinary Euler-convergence region. This
proves `(Z)` and the theorem.

## Entry constraint

Let `{xi_t}` be a deformation for which the same construction applies. If an off-line pair enters
the critical line, then for every shift `omega` below its current horizontal distance, the limiting
negative inertia in `(P)` must drop by the pair's right-half-plane multiplicity when the zero crosses
`Re s=1/2+omega`. At the final entry, this spectral-flow front reaches `omega=0`.

Therefore entry cannot be accomplished by changing only critical-strip divisor labels while the
Euler-region Pick-inertia profile stays fixed. The necessary event is global and prime-side:

```text
an eigenvalue of the infinite Euler Pick system must cross zero.
```

No derivative of xi at a zero appears.

## General self-dual completed Euler products

The proof is not specific to zeta. Let `Lambda` be an entire completed Euler product such that its
centered function is of Cartwright class, its Euler product converges absolutely in `Re s>1`, and

```text
Lambda(s)=epsilon conjugate(Lambda(1-conjugate(s))),   |epsilon|=1.
```

Define

```text
Theta_(Lambda,omega)(z)
=epsilon^(-1) Lambda(1/2-omega-iz)/Lambda(1/2+omega-iz).
```

The root-number factor makes this quotient equal to `E_omega#/E_omega` and is invisible in the Pick
kernel. After the same common-divisor convention, the negative index counts the zeros of `Lambda`
in `Re rho>1/2+omega`. Restriction to the region where both shifted arguments have real part greater
than one again preserves the index, while every matrix entry is given by the absolutely convergent
local Euler factors and the explicit archimedean quotient. Hence `(P)` and `(Z)` hold verbatim for
this class.

If `Lambda` has finitely many prescribed poles, first multiply by the corresponding symmetric
pole-clearing polynomial. This changes the high-region formula only by an explicit rational factor
and separates the known polar divisor from the nontrivial zero count.

## Finite prime-side certificate of RH failure

If RH is false, choose a zero `rho=1/2+a+i gamma` with `a>0`. For this fixed ordinate there are
only finitely many xi zeros in the compact horizontal segment `0<=Re s<=1`. Hence one can choose a
rational `omega` with `0<omega<a` for which the pole of `Theta_omega` induced by `rho` is not
cancelled by a common numerator zero. The shifted kernel then has at least one negative square.
Locality of negative squares supplies finitely many sample points in `U_omega` whose Pick matrix has
a strictly negative eigenvalue. By density and stability, the sample points may also be chosen with
rational real and imaginary parts.

Formula `(E)` converges absolutely at those finitely many points. A strictly negative eigenvalue has
a nonzero margin, so sufficiently long finite Euler products, together with standard explicit tails,
certify the same negative inertia. Therefore:

```text
RH false
==> there exists a finite, rigorously certifiable prime-side Pick-matrix witness
    using only zeta Euler products in Re s>1.                 (C)
```

Conversely, any negative eigenvalue in such a matrix gives a negative square of `S_omega`, hence an
uncancelled pole of `Theta_omega` in the upper half-plane and therefore an off-line zeta zero. Thus
`(C)` is an equivalence when the witness format includes its rational `omega`, rational sample
points, and certified Euler-product intervals.

## Why this is stronger than an RH equivalent

- It is cardinal-valued, not Boolean: the matrices count off-line zeros layer by layer.
- It includes infinitely many off-line zeros via unbounded finite-matrix inertia.
- All evaluations occur where the Euler product converges absolutely; no analytic continuation into
  the critical strip is used to form the matrices.
- RH failure has a finite certificate consisting entirely of convergent prime-side data in
  `Re s>1`.
- It separates discovery from exclusion. Proving positivity of all matrices at a given `omega`
  would give a zero-free half-strip, but `(P)` remains an unconditional identity whether RH is true
  or false.

## Novelty and significance audit

- Suzuki (2012) introduced this exact `Theta_omega` and proved the Boolean meromorphic-inner
  criterion for zero-free shifted half-planes.
- Krein--Langer factorization and locality of negative squares are classical operator theory.
  In particular, Alpay--Rovnyak (1999), DOI `10.1090/S0002-9939-99-04618-3`, states that the
  negative-square count of a holomorphic kernel is independent of the region on which it is
  holomorphic. Thus locality itself is a known parent, not claimed novelty.
- Bombieri (2000) counts off-line zeros by negative eigenvalues of finite truncations of the Weil
  form under a finite-exception hypothesis.
- The existing project theorem `multiPair_carrier_exact_neg_inertia` formalizes the finite abstract
  pole carrier by Sylvester inertia, but explicitly leaves the carrier-from-xi/source correspondence
  open. The new content here is that `Theta_omega` supplies an actual xi kernel and that the complete
  index can be sampled entirely in the Euler-convergent uniqueness region.
- The searched sources did not state the exact Euler-region Pick-inertia limit `(P)`, its
  cardinal/infinite form, or the fact that a fixed dense sequence entirely inside the absolute
  Euler-convergence region recovers the transverse divisor count.
- Significance: `(P)` gives a new exact interface between prime data and off-line-zero position. It
  does not itself prove a new zero-free region, so publication significance depends on whether the
  Euler matrices admit structural estimates unavailable in Suzuki's innerness formulation.

## Open core

`[OPEN CORE]` Find a structural factorization, domination, or finite-section estimate for
`P_(omega,N)` directly from `(E)` that bounds its negative inertia without presupposing zero
information. Even the case `nu_-=0` for one `0<omega<1/2` would be a new zero-free strip.

## Log

- 2026-07-10 -- exact high-half-plane Euler Pick-inertia formula proved from shifted-kernel index
  plus locality of negative squares; novelty audit open.
