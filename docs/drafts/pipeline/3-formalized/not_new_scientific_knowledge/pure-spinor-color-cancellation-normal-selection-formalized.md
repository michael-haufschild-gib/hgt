# Pure-spinor colour-cancellation normal selection — formalization certificate

- **ID:** `pure-spinor-color-cancellation-normal-selection-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `pure-spinor-color-cancellation-normal-selection.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/PureSpinorColorNormalSelection.lean`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [STANDARD MATHEMATICS]`
  `[NO PHYSICAL CLAIM]`

## Formal statement surface

The module works in the existing exact Cartan-coordinate model of the
\(\operatorname{Spin}(10)\) pure-spinor quadrics and defines:

- `PureSpinorColorBivector` — the three-complex-dimensional
  \(\Lambda^2\mathbb C^3\) sector;
- `PureSpinorColorWeakTangent` — the six-complex-dimensional mixed
  \(\mathbb C^3\otimes\mathbb C^2\) sector;
- `pureSpinorColorTangent`;
- `pureSpinorColorWeakTangentVariation`;
- `pureSpinorWeakScalarTangent`;
- `pureSpinorColorlessNormalSecondFundamental`;
- `pureSpinorColorMixedNormalPairing`.

## Unconditional theorems

1. `pureSpinorColorlessNormal_color_mixed_eq`

   The colour-bivector/mixed-sector Cartan polar equals the explicit two-component normal pairing
   \[
   (-c_{12}m_{35}+c_{13}m_{25}-c_{23}m_{15},
     c_{12}m_{34}-c_{13}m_{24}+c_{23}m_{14}).
   \]

2. `pureSpinorColorlessNormal_mixed_color_eq`

   The reverse sector order has the same pairing.

3. `pureSpinorColorlessNormal_color_color_eq_zero`

   Two colour-bivector tangents have zero colourless normal reporter.

4. `pureSpinorColorlessNormal_mixed_mixed_eq_zero`

   Two mixed colour--weak tangents have zero colourless normal reporter.

5. `pureSpinorColorlessNormal_weakScalar_left_eq_zero`

6. `pureSpinorColorlessNormal_weakScalar_right_eq_zero`

   A weak-scalar two-form has zero colourless normal reporter against every Cartan coordinate
   variation in either order.

7. `pureSpinorColorMixedNormalPairing_surjective`

   For every nonzero colour bivector \(c\), the function
   \[
   m\longmapsto\operatorname{pairing}(c,m)
   \]
   is surjective onto the complete colourless normal doublet.

Together these declarations formalize the exhaustive quadratic sector law:

```text
colour × mixed and mixed × colour -> complete colourless normal doublet;
colour × colour                  -> zero;
mixed × mixed                    -> zero;
weak scalar × anything           -> zero.
```

## Dependency and honesty boundary

The module imports only
`GaloisForLFunctions.HTGeometry.PurePairNormalFracture`.
It contains no:

- `sorry`;
- `admit`;
- user `axiom`;
- `opaque`;
- `unsafe`;
- physical premise;
- numerical computation.

`#print axioms` reports only Lean/mathlib's standard logical quotient dependencies:
`propext`, `Classical.choice`, and `Quot.sound`.

The formal theorem does not identify the normal doublet with actuality, Higgs, spacetime, or
gravity. Those remain physical conjectures.

## Verification

Direct leaf check:

```text
lake env lean GaloisForLFunctions/HTGeometry/PureSpinorColorNormalSelection.lean
```

Result: pass, no output and no warnings.

Final module audit:

```text
lake build GaloisForLFunctions.HTGeometry.PureSpinorColorNormalSelection
```

Result:

```text
✔ [8476/8476] Built GaloisForLFunctions.HTGeometry.PureSpinorColorNormalSelection
Build completed successfully (8476 jobs).
```

Formal lint:

```text
scripts/formal_tools.py lint
```

Result: `formal lint passed`. Reported warnings concern pre-existing oversized modules; none
concerns this file.

No Lean or Lake process remained after audit.

## Novelty verdict

The proof is a precise formal extraction from standard pure-spinor and representation geometry.
It is not claimed as new mathematics or new physics. Its research value is to remove one degree of
freedom from the active conjecture: the colourless normal doublet is the full image of one forced
cross-sector Cartan contraction, not an arbitrary selected complement.

## Gates

- [x] paper theorem dependency-closed
- [x] exact coordinate pairing formalized
- [x] all forbidden-sector vanishings formalized
- [x] every-nonzero-colour surjectivity formalized
- [x] direct Lean check
- [x] standard-axiom audit
- [x] formal lint
- [x] final module build
- [ ] supports a proved operational actualization law
- [ ] supports a finite physical prediction

## Log

- 2026-07-29 — formalized and audited after the purity-boundary conjecture was frozen. Kept all
  physical language out of Lean declarations and classified the result as a standard mathematical
  bridge.
