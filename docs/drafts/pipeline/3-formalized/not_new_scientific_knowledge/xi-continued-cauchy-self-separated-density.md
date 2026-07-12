# Continued Xi Cauchy self-separated density

- **ID:** `xi-continued-cauchy-self-separated-density`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The Xi-divisor Cauchy evaluation vector is norm-continuous in its regular pole,
  and deleting all self-conjugate poles from the continued prime--Gamma generating set does not
  change its Hilbert closure.

## Theorems

`XiWeilCauchyLpContinuity.lean` proves

```text
z_n -> z, XiC(z_n)XiC(z) != 0
  -> CauchyLp(z_n) -> CauchyLp(z) in ell^2(XiZeroCopy).
```

The proof uses analytic isolation of the complete multiplicity-exact Xi divisor and a Tannery
majorant by the fixed square-summable Cauchy vector at `z`.

`XiContinuedCauchySeparatedDensity.lean` proves:

```text
closure(span{CauchyLp(z): z in continued source domain, z != conjugate(z)})
  = continued Cauchy Hilbert subspace,
```

and hence the canonical Xi--Hurwitz orientation vector belongs to this reduced closure.  Real
poles are perturbed vertically inside the centered strip; the local Xi zero gap preserves
regularity and the continued prime--Gamma domain.

## Boundary

This removes self-collisions only.  An explicit finite packet formula still requires simultaneous
avoidance of `z=conjugate(w)` for distinct packet points, or a diagonal derivative extension.
The approximating closure remains target-fed until packet selection is derived from source values.

## Lean certificate

- `RHTower.tendsto_xiWeilCauchyLp`
- `RHTower.ccmContinuedCauchyDomain_of_regular_mem_centeredStrip`
- `RHTower.exists_selfSeparatedContinuedCauchyLp_tendsto`
- `RHTower.selfSeparatedContinuedCauchy_topologicalClosure_eq`
- `RHTower.xiHurwitzOrientationVector_mem_selfSeparatedContinuedCauchyClosure`

Exact module builds pass.  Axiom inspection reports only standard mathlib principles.

## Gates

- [x] mathematical proof complete
- [x] Lean formalization complete
- [x] exact modules build
- [x] axiom audit
- [ ] scientific novelty claim; none is made
