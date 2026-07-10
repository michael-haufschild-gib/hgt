# Additive orbit balance for principal-part coefficients

- **ID:** `additive-orbit-balance-principal-parts`
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM (Lean) — not new scientific knowledge
- **Source:** `formal/GaloisForLFunctions/OrbitBalanceAdditive.lean`
- **Statement:** For coefficients in any additive commutative group, every finitely supported
  integer-orbit shift coboundary has total coefficient zero.  Hence a single nonzero coefficient on
  one orbit cannot be a shift coboundary.

## Goal

Replace the integer-divisor-only orbit obstruction by the coefficient-generic theorem required for
meromorphic principal parts.  With coefficient group `C`, the result is the exact algebraic final
step in the multiplicative-cylinder descent for the double-sine defect-coset theorem.

## Main declarations

- `additiveOrbitSum`
- `additiveIntShiftCoboundary`
- `additiveOrbitSum_intShiftCoboundary`
- `ne_additiveIntShiftCoboundary_of_additiveOrbitSum_ne_zero`
- `single_ne_additiveIntShiftCoboundary`

## Scientific status

`[BRIDGE]` This is finite-support augmentation algebra, not new scientific knowledge.  It matters
operationally because the existing `OrbitBalance` theorem had integer coefficients and therefore
could not directly certify a nonzero complex principal-part coefficient.  The new theorem removes
that mismatch without postulating any analytic summability interface.

It supports the paper-level claims:

- `double-sine-defect-coset-differential-matroid`;
- `all-order-multiple-sine-stanley-reisner-differential-matroid`.

The remaining unformalized content is analytic: construct the multiple-sine functions, descend the
paired difference system to a rational multiplicative cylinder, and map each fixed pole order to
this finitely supported orbit datum.

## Gates

- [x] coefficient-generic orbit sum defined
- [x] finite shift coboundary proved to have zero orbit sum
- [x] nonzero-orbit-sum obstruction proved
- [x] lone nonzero principal-part coefficient corollary proved
- [x] exact Lean source check passed
- [ ] analytic principal-part extraction from rational cylinder functions formalized
- [ ] integrated into an unconditional formal proof of the double-sine atomic theorem

