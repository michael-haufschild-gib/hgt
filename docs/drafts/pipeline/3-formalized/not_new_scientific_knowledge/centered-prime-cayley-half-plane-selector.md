# Centered prime Cayley half-plane selector

- **ID:** `centered-prime-cayley-half-plane-selector`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[FINITE CONSUMER] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeCayleyHalfPlane.lean`
- **Consumer:** `../../1-in-progress/prime-kirchhoff-matroid-half-plane-rh.md`

## Theorem

For each prime, let

```text
u_p(z)=exp(-log(p) I z),
x_p(z)=(1+u_p(z))/(1-u_p(z)).
```

Lean proves

```text
Im z<0 -> Re x_p(z)>0,
Im z>0 -> Re x_p(z)<0,
Im z!=0 -> 1-u_p(z)!=0.
```

Hence every finite prime aperture lands simultaneously in one open Cayley half-plane, with side
determined only by the sign of the centered imaginary coordinate.  Clearing Cayley denominators
cannot introduce an off-line singularity.

## Positive use

A homogeneous real polynomial with the right-half-plane nonvanishing property is also nonzero when
all variables lie in the left half-plane, by the common sign change `x -> -x`.  Therefore any
source-built homogeneous half-plane-stable prime polynomial becomes a finite centered critical-line
selector under the Cayley evaluation above.  The missing theorem is construction of that stable
source polynomial and its completed Xi comparison, not the prime geometry.

## Formal certificate

- `centeredPrimeCayley`;
- `centeredPrimeCayley_re_pos_of_im_lt_zero`;
- `centeredPrimeCayley_re_neg_of_im_pos`;
- `centeredPrimeCayley_denominator_ne_zero_of_im_ne_zero`.

## Gates

- [x] exact lower-half-plane image
- [x] exact upper-half-plane image
- [x] off-line denominator safety
- [x] exact module build
