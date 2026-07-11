# Translation-invariant defect forms are hyperbolic on every off-real orbit

- **ID:** `translation-invariant-defect-form-orbit-classification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Route-A form classification
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** the semisimple theta-convolution defect and elementary unitary character theory
- **Statement:** On a semisimple complex divisor module with real translations acting by
  `T_a e_rho=exp(-i a rho)e_rho`, an invariant Hermitian form can pair `e_rho` only with
  `e_(conj(rho))`.  Every nonreal conjugate pair is therefore a hyperbolic plane in any
  nondegenerate invariant form.  A positive invariant form can be faithful only on real support.

## Setup

Let `Z subset C` be a discrete multiset stable under complex conjugation.  Ignore nilpotent
multiplicity jets and form its algebraic semisimplification

```text
D_Z=direct_sum_(rho in Z_distinct) C e_rho.
```

Real translation acts by

```text
T_a e_rho=exp(-i a rho)e_rho,    a in R.               (1)
```

Let `H` be a Hermitian form satisfying

```text
H(T_a v,T_a w)=H(v,w)                                  (2)
```

for every real `a`.

## Pairing selection rule

For two basis vectors, equations (1)--(2) give

```text
H(e_rho,e_sigma)
  =exp(-i a(rho-conj(sigma))) H(e_rho,e_sigma)          (3)
```

for every real `a`.  If the matrix coefficient is nonzero, the exponential in (3) must be one for
all `a`, so

```text
rho=conj(sigma).                                       (4)
```

Thus a real point can pair with itself, while a nonreal point can pair only with its conjugate.

## Hyperbolic off-real blocks

On the span of `e_rho,e_(conj(rho))` with `Im(rho)!=0`, the matrix of `H` is necessarily

```text
[ 0       c ]
[ conj(c) 0 ].                                         (5)
```

If `H` is nondegenerate on this pair, then `c!=0`.  The eigenvalues of (5) are `+|c|` and `-|c|`.
Hence every nonreal conjugate pair contributes one positive and one negative direction.

For Xi, evenness adds the second pair `-rho,-conj(rho)`.  A free Xi quartet therefore contributes
two hyperbolic planes when both height signs are retained, or one on an upper-height fundamental
half.

## Positivity consequence

A positive definite invariant Hermitian form has zero off-real fibers: equation (5) cannot be
positive unless `c=0`, which makes the form degenerate there.  Therefore

```text
faithful + invariant + positive
  => Z subset R.                                       (6)
```

Conversely, when `Z subset R`, assigning any positive weight to every `e_rho` produces a positive
invariant form on the algebraic direct sum.  Thus existence of some faithful positive invariant
form on the semisimple Xi defect is equivalent to all Xi zeros being real, namely RH.

The theorem classifies, rather than constructs, a source form.  A canonical form may still have
negative diagonal weights at real zeros; positivity there is a separate source requirement.

## Multiplicity warning

The theorem deliberately uses the semisimplification.  On a multiplicity-`m` local jet, translation
has a nontrivial unipotent part when `m>1`.  Full unitary Hilbertization would force `m=1`, as proved
in `theta-convolution-hilbert-analytic-defect-trilemma.md`.  An RH-only route must keep nilpotent
multiplicity data outside the positive semisimple Hilbert form.

## Gates

- [x] invariant coefficient selection rule proved
- [x] off-real block and inertia computed
- [x] faithful positive support implication proved
- [x] Xi quartet and multiplicity consequences delimited
- [ ] no Lean formalization planned before a source form consumes the classification
