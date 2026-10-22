# Theta center-mixed three-positive orientation law

- **ID:** `theta-center-mixed-three-positive-orientation-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM / SOURCE-SIDE RH PROGRESS
- **Scientific status:** `[CORPUS COMPONENTS PROVED] [CAPSTONE IN PROGRESS] [NOVELTY AUDIT IN PROGRESS] [NOT RH]`

## Exact target

For the completed theta source `K` and every aperture `0<a<1/2`, define

```text
G_a(t)=integral_(r>0) r sinh(ar) K(r/2+t)K(r/2-t) dr.
```

Prove as one dependency-closed theorem:

1. `G_a(t)>0` for every real `t`;
2. every three-node Bochner matrix

   ```text
   [G_a(x_i-x_j)]_(0<=i,j<3)
   ```

   is positive semidefinite;
3. its Fourier transform is the transverse normal derivative of
   `|Xi(b-ia)|^2`;
4. the current is the absolutely convergent sum of completed arithmetic
   product fibres and each fibre is the derivative of its Hermitian energy;
5. the unsummed coupled Wigner cone has an explicit negative point for every
   `a,b>0`.

Consequently, any negative Fourier-sign witness in this source representation
cannot be detected by a test measure supported on at most three points and
cannot follow from pointwise Wigner positivity. Its first possible witness rank
is four, and the missing theorem is a genuinely global center-mixed
interference law.

## Why this answers the orientation objection

The local Julia phase derivative chooses a right-hand divisor before its sign
is read; the functional-equation-complete phase cancels. The center-mixed
Wigner current is instead built directly from the theta source and equals the
unsquared transverse derivative before frequency scalarization. It retains the
frequency `b` and the product-fibre arithmetic phases. Squaring occurs only as
the Hermitian energy whose derivative is being resolved; it does not erase the
normal orientation.

## Current proof inventory

- `thetaCuspCenterMixedDensity_pos`
- `thetaCuspReflectedSourceCorrelationAngle_subadditive_global`
- `thetaCuspCenterMixedThreePointMatrix_posSemidef`
- `hasDerivAt_normSq_XiC_transverse_eq_centerMixedFourierCurrent`
- `thetaCuspCenterMixedFourierCurrent_eq_tsum_sourceProductFiber`
- `thetaCusp_completeWignerGammaXiTransverseEnergyUniversality`
- `thetaCuspCofinalCoupledConeKernel_negative_witness`
- `thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis`

## Open capstone work

- [ ] formalize permutation-invariant three-node Gram positivity;
- [ ] package source positivity, rank-three positivity, transverse derivative,
      product-fibre energy resolution, and negative local witness;
- [ ] verify exact axiom footprint;
- [ ] complete current primary-literature audit;
- [ ] subject manuscript to hostile general-journal review.

## Hostile boundary

This theorem does not prove Fourier nonnegativity and therefore does not prove
RH. Order-three positive definiteness is genuine progress only if stated as a
finite-rank theorem, not advertised as “almost RH.” The paper must distinguish
the classical horizontal-monotonicity equivalence from the new source
representation and unconditional rank-three discharge.
