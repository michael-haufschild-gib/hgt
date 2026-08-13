# The higher-spin CDD coupling space is a positive Hausdorff cone — formalized

- **ID:** `hausdorff-positive-higher-spin-cdd-cone-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `hausdorff-positive-higher-spin-cdd-cone.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/HausdorffPositiveCddCone.lean`, `HTGeometry/HausdorffStrictCddCone.lean` | necessity of every finite-difference inequality `(10)`; strict complete monotonicity of geometric and CDD couplings |
| `HTGeometry/HausdorffQuadratureWeights.lean`, `HTGeometry/HausdorffQuadratureMeasure.lean`, `HTGeometry/HausdorffNodeComparison.lean`, `HTGeometry/HausdorffMomentTheorem.lean` | **Hausdorff's moment theorem**, absent from mathlib: the quadrature weights, the refinement identity, the exact falling-factorial moment identity, the node comparison `|(k/N)^m − (k)_m/(N)_m| ≤ m²/N`, and both directions with uniqueness |
| `HTGeometry/HausdorffCDDPhaseKernel.lean`, `HTGeometry/HausdorffCDDMeasureSource.lean` | the phase kernel `K(y,θ)` with its zero-shell value, the source transform, its additivity, and the point-source transform |
| `HTGeometry/HausdorffKernelSeries.lean` | equation `(4)` and **`(11) = (13)`**: the phase is the odd-spin sinh series in the source moments |
| `HTGeometry/CddShellRadius.lean`, `HTGeometry/QLadderSource.lean` | the shell-radius dictionary and the geometric q-ladder `(19)` as a strictly positive cone point |
| `HTGeometry/PositiveMeasureExtremeRays.lean` | **extreme rays of the cone of finite positive measures are exactly the point masses** |
| `HTGeometry/HausdorffCddExtremeRays.lean` | the dictionary `(18)`: extreme source ray ↔ elementary paired shell; the zero-shell endpoint `(18a)`, `(18b)`; finite atomic source ↔ finite shell-germ sum |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `hausdorffCompletelyMonotone_iff_exists_source`,
  `existsUnique_hausdorffSource_of_completelyMonotone` — **Theorem A** in both directions with
  uniqueness of the source measure;
- `cddCoupling_strict_completelyMonotone`, `qLadder_strict_completelyMonotone` — the strict cone
  inequalities for CDD shell combinations and for the geometric q-ladder `(19)`;
- `hasSum_hausdorffCDDPhase` — **Theorem B**, `(11) = (13)`: one positive measure generates the
  entire phase germ as the odd-spin series in its moments;
- `isExtremeRayMeasure_iff_smul_dirac` — the general classification: a finite positive measure
  spans an extreme ray of the positive cone iff it is a nonzero finite multiple of a point mass
  (two-valuedness from extremality, then a one-point support by Hausdorff separation);
- `isExtremeRayMeasure_iff_hausdorffAtomSource`,
  `exists_shell_hausdorffCDDPhase_of_isExtremeRayMeasure` — `(18)` on the CDD source cone: the
  extreme rays are the positive point sources, and each is one elementary paired-shell phase ray
  `w·K(y,θ)`;
- `hausdorffCDDPhase_zeroShell`, `exp_I_hausdorffCDDPhase_zeroShell` — `(18a)`, `(18b)`: the
  `y = 0` extreme ray is the ordinary `T T̄` dressing `exp(8 i w sinh θ)`;
- `hausdorffCDDPhase_finiteAtomicSource` — finite atomic source ↔ finite positive shell-germ sum.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/PositiveMeasureExtremeRays.lean
lake env lean GaloisForLFunctions/HTGeometry/HausdorffCddExtremeRays.lean
lake build GaloisForLFunctions.HTGeometry.HausdorffCddExtremeRays
```

## What closed last

The extreme-ray dictionary `(18)`.  Its mathematical content is a classification theorem about the
cone of finite positive measures, which mathlib does not have: extremality forces every measurable
set to carry either no mass or the whole mass, and such a two-valued finite measure on a Hausdorff
second-countable space has a one-point support — two distinct support points would carry disjoint
open sets of full mass.  Transporting the classification through the phase transform gives the
paper's dictionary, with the zero shell reproducing the ordinary `T T̄` factor.

## Boundary

The card's own gate list keeps three items open, and they are open *mathematics*, not missing
formalization: the global regularity classification for non-atomic measures, an explicit
exponentially quasilocal density with a compact-local QFT flow, and a universality theorem deriving
the cone from locality and unitarity rather than from shell input.  The card states explicitly that
positivity implies a local analytic current germ and **not** a global regular factorizing
S-matrix; nothing formalized here claims otherwise.  The remaining formula-level novelty audit is an
external literature obligation.
