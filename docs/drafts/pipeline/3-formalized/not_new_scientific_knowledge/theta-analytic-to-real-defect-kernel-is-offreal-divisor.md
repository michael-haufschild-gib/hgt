# The analytic-to-real theta-defect comparison has exactly the off-real divisor as kernel

- **ID:** `theta-analytic-to-real-defect-kernel-is-offreal-divisor`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper); terminal Route-A reduction
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** the theta analytic cokernel and the Xi logarithmic-derivative real-boundary measure
- **Statement:** On the algebraic semisimplification of the Xi analytic defect, the canonical map to
  the positive real-boundary defect is projection onto the real zero fibers.  Its kernel is exactly
  the sum of the nonreal zero fibers.  Hence faithfulness of this comparison is equivalent to RH.

## Analytic semisimple defect

Let `Z_Xi` be the distinct complex zero set of

```text
XiC(z)=xi(1/2+i z).
```

The semisimplification of the analytic cokernel of multiplication by `XiC` has algebraic
finite-support core

```text
D_an^alg=direct_sum_(rho in Z_Xi) C e_rho.              (1)
```

The logarithmic-derivative boundary theorem constructs the real defect core

```text
D_real^alg
  =direct_sum_(gamma in Z_Xi intersect R) C e_gamma,    (2)
```

with positive weights equal to the analytic multiplicities.

## Canonical comparison

The comparison from analytic support to the real boundary is restriction to the real spectral
axis:

```text
r(e_rho)=e_rho if rho is real,
r(e_rho)=0     if rho is nonreal.                       (3)
```

Therefore

```text
ker r
  =direct_sum_(rho in Z_Xi, Im(rho)!=0) C e_rho,        (4)

range r=D_real^alg.                                    (5)
```

Both identities follow immediately on the basis and remain valid for any completion on which the
coordinate maps are faithful.

## RH equivalence

By (4), `r` is injective exactly when every Xi zero is real.  Under

```text
s=1/2+i rho,
```

reality of `rho` is exactly `Re(s)=1/2`.  Hence

```text
r is faithful on the analytic semisimple defect
  iff RiemannHypothesis.                                (6)
```

This theorem does not prove injectivity.  It proves that the proposed real-boundary exhaustion is
the RH statement itself after the source and target defects have been constructed.

## Consequence

The positive real-boundary measure is a genuine source object, and the analytic theta cokernel is a
genuine source-first divisor object.  Their comparison supplies no intermediate localization law:
its missing injectivity is exactly the absence of off-line zeros.

Any successful pro-geometric continuation must therefore introduce additional pre-divisor prime
geometry that proves injectivity.  Rephrasing (3) as a faithful functor or purity axiom is circular.

## Gates

- [x] analytic and real semisimple cores identified
- [x] canonical comparison and kernel computed
- [x] faithfulness proved equivalent to RH
- [x] formalized in `RHTower/ThetaAnalyticRealDefectKernel.lean`, including the exact RH equivalence

## Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/ThetaAnalyticRealDefectKernel.lean`
(namespace `RHTower`), wired into the `GaloisForLFunctions.RHTower` umbrella.

| Paper statement | Lean declaration |
|---|---|
| `Z_Xi`, the distinct zero set of `XiC` | `xiZeroSet` |
| `(1)` analytic semisimple core `⊕_ρ C e_ρ` | `analyticDefectCore` |
| `(3)` the comparison `r` | `realBoundaryComparison`, `realBoundaryComparison_apply` |
| `r(e_ρ) = e_ρ` on real fibers | `realBoundaryComparison_single_real` |
| `r(e_ρ) = 0` on nonreal fibers | `realBoundaryComparison_single_nonreal` |
| `(4)` `ker r` is the sum of the nonreal fibers | `mem_ker_realBoundaryComparison_iff` |
| `(5)` `range r` is the real-boundary core `(2)` | `mem_range_realBoundaryComparison_iff` |
| faithfulness is reality of the whole divisor | `injective_realBoundaryComparison_iff` |
| `(6)` faithful `⟺` `RiemannHypothesis` | `injective_realBoundaryComparison_iff_riemannHypothesis` |

The RH bridge uses the corpus coordinate theorem
`RHTower.SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero`, so the equivalence
is with mathlib's `RiemannHypothesis` itself, not with a restated surrogate.

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella import wired,
`#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`.
