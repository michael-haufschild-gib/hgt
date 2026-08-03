# The CCM aperture Morse charge exhausts the Hardy off-line model-space index

- **ID:** `ccm-aperture-morse-hardymodel-index-exhaustion-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Suzuki's global screw kernel, Krein--Langer negative-square factorization,
  continuous-kernel exhaustion, and `ccm-aperture-morse-index-conservation-law.md`

## Statement

Let

```text
kappa(a)=Tr 1_(-infinity,0)(A_a)                         (1)
```

be the negative Morse index of the exact restricted Weil operator at aperture `a`. Let

```text
N_+
 =sum_(xi(rho)=0, Re rho>1/2)multiplicity(rho)           (2)
```

with the value `+infinity` allowed. For `omega>0`, let `B_omega` be the inner denominator of the
shifted-Xi quotient graph, so that

```text
dim K(B_omega)
 =sum_(Re rho>1/2+omega)multiplicity(rho).                (3)
```

Then

```text
sup_(a>0) kappa(a)
 =N_+
 =sup_(omega>0) dim K(B_omega).                           (4)
```

Equivalently, for every finite packet of `k` right-half off-line zeros, there is a finite aperture
`a_k` for which

```text
kappa(a_k)>=k.                                           (5)
```

Thus the aperture filtration loses no transverse divisor charge: every Hardy model-space defect
channel is eventually realized as an actual negative direction of a finite restricted-Weil form.

## 1. Global screw-kernel index

Let `gamma` range over the zeros of

```text
z |-> xi(1/2-i z)
```

with multiplicity. Suzuki's unconditional series for the global screw kernel is

```text
G_g(t,u)
 =sum_gamma
   (exp(i gamma t)-1)(exp(-i gamma u)-1)/gamma^2.         (6)
```

Put

```text
phi_gamma(t)=(exp(i gamma t)-1)/gamma.                    (7)
```

For real `gamma`, the corresponding contribution to `(6)` is the positive rank-one kernel

```text
phi_gamma(t)conjugate(phi_gamma(u)).                     (8)
```

For a nonreal conjugate pair `gamma,conjugate(gamma)`, their contribution is

```text
phi_gamma tensor phi_conjugate(gamma)^*
 +phi_conjugate(gamma) tensor phi_gamma^*

 =1/2 (phi_gamma+phi_conjugate(gamma))
       tensor (phi_gamma+phi_conjugate(gamma))^*
  -1/2 (phi_gamma-phi_conjugate(gamma))
       tensor (phi_gamma-phi_conjugate(gamma))^*.        (9)
```

Hence each conjugate pair contributes one negative square. The functional equation supplies the
reflected pair `-gamma,-conjugate(gamma)`; its upper-half member corresponds to the conjugate
right-half zeta zero and contributes the second negative square of an ordinary off-line quartet.
Counting upper-half `gamma` is therefore exactly counting the zeros in `(2)`.

The generalized Nevanlinna function attached to `(6)` has one pole, with multiplicity, at every
upper-half `gamma`. The Krein--Langer pole/index theorem consequently gives

```text
ind_-(G_g)=N_+.                                          (10)
```

This also handles infinitely many off-line zeros: the index is infinite precisely when the pole
count is infinite. Equation `(9)` is the finite factorization underlying the theorem; the
Krein--Langer minimality statement ensures that the positive critical-line part cannot cancel a
nonreal pole's negative square.

## 2. Exhaustion by finite apertures

For a continuous Hermitian kernel `K` on `R times R`, define its global negative index as the
supremum of the negative inertias of all finite point Gram matrices. Let `ind_-(K;[-a,a])` be the
negative index of its integral form on compactly supported `L2(-a,a)` test functions.

Then

```text
sup_(a>0) ind_-(K;[-a,a])=ind_-(K).                      (11)
```

### Lower bound

Choose a finite point Gram matrix of negative inertia `k`, and choose `a` containing all its
nodes. Replace each point mass by an `L2`-normalized bump supported in a shrinking disjoint
neighborhood of that node. Continuity of `K` makes the integral Gram matrices converge to the
point Gram matrix. Strict negative inertia is stable under sufficiently small matrix perturbation,
so `ind_-(K;[-a,a])>=k`.

The screw kernel satisfies

```text
G_g(t,0)=G_g(0,u)=0.                                     (12)
```

If a zero-mean constraint is required, add a compensating bump at the base point `0`. Equation
`(12)` makes its limiting row and column zero, so it does not change the negative inertia.

### Upper bound

Approximate a basis of any finite-dimensional negative subspace of the integral form by step
functions. Each step-function Gram is a norm limit of finite weighted point Grams, hence a
congruence limit of matrices whose negative inertia is at most `ind_-(K)`. Strict negativity is
open, so the negative subspace dimension cannot exceed `ind_-(K)`. This proves `(11)`.

Applying `(11)` to `K=G_g` and using `(10)` gives

```text
sup_(a>0) ind_-(G_g;[-a,a])=N_+.                         (13)
```

## 3. Congruence with the restricted Weil forms

Suzuki's derivative map

```text
D:H_0^1(-a,a)->L_0^2(-a,a)                              (14)
```

is bijective and satisfies

```text
Q_W^a(v,v)=<G_a Dv,Dv>.                                  (15)
```

Passing to the closed forms preserves negative index. Therefore

```text
kappa(a)=ind_-(G_g;[-a,a])                               (16)
```

with the projected zero-mean realization understood on the right. Combining `(13)` and `(16)`
proves the first equality in `(4)`.

The shifted-Xi generalized Schur theorem gives `(3)`. Every right-half zero has some positive
horizontal displacement, so monotone exhaustion as `omega` decreases to zero gives

```text
sup_(omega>0)dim K(B_omega)=N_+,                         (17)
```

proving the second equality and the theorem. `QED`

## Positive CCM consequence

The exact transverse charge now has three rigorously identified realizations:

```text
right-half Xi divisor multiplicity
 =cofinal Hardy denominator-model dimension
 =cofinal finite-aperture restricted-Weil Morse index.   (18)
```

This is an actual index transport, not the observation that three Boolean criteria are each
equivalent to RH. It proves that neither aperture localization nor the continuous screw-kernel
realization can hide an off-line orbit forever.

Combined with monotonicity of `kappa(a)`, every nonzero charge appears at a finite aperture and then
persists. Thus a successful CCM proof must positively conserve the zero charge through the entire
aperture filtration. Equivalently, it must prove that the source-normalized square Evans section
has empty nonpositive divisor at every aperture.

## Scope and classification

The result is a synthesis of Suzuki's screw-kernel representation, the classical Krein--Langer
pole/index theorem, and elementary continuous-kernel exhaustion. It closes a project transport gate
but is not new scientific knowledge.

The finite factorization and exact finite inertia are already represented abstractly in
`RHTower/SeamInertiaCharge.lean`. The analytic screw kernel, its generalized Nevanlinna transform,
and the closed-form exhaustion are absent from Lean, so no wrapper is added.

Primary sources:

- [Suzuki, *Aspects of the screw function corresponding to the Riemann zeta function*](https://arxiv.org/abs/2206.03682)
- [Suzuki, *Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096)

## Gates

- [x] global screw kernel decomposed into critical positive and off-line indefinite packets
- [x] global negative index identified with right-half zero multiplicity
- [x] continuous-kernel negative index exhausted by bounded apertures
- [x] zero-mean projection shown not to lose negative charge
- [x] screw and restricted-Weil aperture indices identified by derivative congruence
- [x] Hardy model-space and aperture Morse charges identified cofinally
- [ ] prove their common value is zero
- [ ] RH
