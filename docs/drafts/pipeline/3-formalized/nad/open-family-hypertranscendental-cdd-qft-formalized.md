# Open family of regular CDD shell orbits — formalized

- **ID:** `open-family-hypertranscendental-cdd-qft-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `open-family-hypertranscendental-cdd-qft.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/OpenFamilyCDDShell.lean` | the several-seed rational shell `(2)`, its scale orbit `(3)`, the decimation constraint `(4)`, the reflection identity `(5)`, the strip estimates `(6)`–`(7)`, normalization `(11)`, the phase `(14)`–`(15)`, normal convergence of the infinite orbit, and the Claim E stability step |
| `HTGeometry/GeometricCDDConstraint.lean` | the single-seed finite algebra this generalizes |
| `HTGeometry/GeometricCDDBoundarySelection.lean` | the unique one-sided shell response |
| `HTGeometry/ExponentialObservationHypertranscendence.lean` | HT is unchanged by a nonzero DA factor |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(2)`, `(3)` `cddShell`, `cddShellOrbit`, with `cddShell_zero` and `cddShellOrbit_at_zero`;
- `(4)` `cddShellOrbit_succ_constraint` — the exact `q`-decimation constraint: the new scale-zero
  shell is the boundary term left by shifting every older scale;
- `(5)` `cddShell_neg_mul`, `cddShellOrbit_neg_mul`, and the rapidity forms
  `cddShellOrbit_rapidity_neg_mul` (unitarity) and `cddShellOrbit_rapidity_crossing_mul` (crossing);
- `(6)` `geometricCDDCrossingCoordinate_re_pos` — the physical strip `0 < Im θ < π` has positive
  crossing-coordinate real part, via the new `sinh_im`;
- `(7)` `norm_sub_lt_norm_add_of_pos_re` — a positive real seed is strictly closer to a right
  half-plane point than its negative is; hence `norm_cddShell_le_one` and
  `norm_cddShellOrbit_le_one`: **every finite partial product is bounded by one in the strip**;
- real-axis unitarity: `norm_sub_eq_norm_add_of_re_eq_zero` and `norm_cddShell_eq_one`;
- `(11)` `cddShellOrbit_at_zero` — the orbit is `1` at the origin, so `S(0) = -1`;
- `(14)`, `(15)` `cddShellPhase`, `cddShellPhaseSlope`, `hasDerivAt_cddShellPhase`,
  `cddShellPhaseSlope_pos`, `deriv_cddShellPhase_pos` — the multi-seed unwrapped phase, its exact
  slope, and strict monotonicity for every nonempty positive seed with positive multiplicities;
- **normal convergence**: `multipliable_cddShellFactor` and `multipliable_cddShellOrbit` — for
  `0 < q < 1`, a positive seed and a crossing coordinate in the closed right half-plane the one-sided
  scale orbit converges;
- Claim E: `hypertranscendentalOver_cdd_dressing_iff` — a nonzero differentially algebraic dressing
  cannot remove hypertranscendence, so every admissible finite regular CDD dressing of the family
  keeps HT scattering.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/OpenFamilyCDDShell.lean
lake build GaloisForLFunctions.HTGeometry.OpenFamilyCDDShell
```

## What closed last

Normal convergence of the infinite scale orbit.  The corpus had only finite truncations, and mathlib
has the criterion (`multipliable_one_add_of_summable`) but not the estimate.  Writing each shell
factor as `1 + (−2 q^k t)/(a_j + q^k t)` and bounding the denominator below by `a_j` — using that the
real part of `a_j + q^k t` is at least `a_j` on the closed right half-plane — makes the summand
dominated by a geometric series with ratio `q`, and the finite product over seeds and multiplicities
is multipliable because multipliability is closed under products and powers.  That is exactly the
"normal convergence" the card's Claim A asserts, and it is now a theorem rather than a citation.

## Boundary

Claim C uses the Adamczewski–Dreyfus–Hardouin dichotomy for first-order linear `q`-difference
equations and Claim D uses Lechner's inverse-scattering reconstruction; both are cited published
theorems on the card, not project obligations.  The paper card's remaining gates — an external
formula-level novelty audit, a dynamically derived reciprocal Jost duality, a matrix-valued
factorizing extension, and an independent analytic and QFT review — are onward targets and literature
obligations, not formalization gates for the family algebra and convergence certified above.
