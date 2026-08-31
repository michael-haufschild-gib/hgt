# Lattice-carry transgression, invariant current, and counterflow law -- Lean certification

- **Paper theorem:** ULF-TAFM-8
- **Lean module:** `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedLatticeCarryCurrent`
- **Status:** formalized

## Certified content

The module proves:

1. finite invariant-mass drift/current reconstruction
   `mass * chi = L * integral k`;
2. probability-normalized reconstruction `chi = L * integral k`;
3. zero-carry integrable descent forces neutral drift;
4. lattice gauge covariance and invariance of mean current under integrable coboundaries;
5. exact Hahn traffic/counterflow identity
   `integral |k| - |integral k| = 2 * min(integral k⁺, integral k⁻)`;
6. compensated traffic identity after drift reconstruction;
7. exact serial carry composition through every finite iterate; and
8. bounded phase remainder cannot alter asymptotic winding rate.

The code is generic: no Xi zero, RH hypothesis, divisor-fitted object, or arithmetic receiver occurs
in the module.

## Verification

- Scratch elaboration:
  `lake env lean /tmp/TopologicallyAdmittedLatticeCarryCurrent.lean` -- pass.
- Project-path elaboration:
  `lake env lean GaloisForLFunctions/HTGeometry/TopologicallyAdmittedLatticeCarryCurrent.lean` --
  pass.
- Final targeted leaf audit:
  `lake build GaloisForLFunctions.HTGeometry.TopologicallyAdmittedLatticeCarryCurrent` -- pass
  (`8701/8701`).
- Batched scratch `#print axioms` on all nine significant declarations reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Module is imported by `HTGeometry.UniversalLawField`; umbrella was not built.

No full project, theorem-area, or umbrella build was run.

## Selection boundary

The certification proves compact recurrence can preserve nonzero open drift as microscopic lattice
circulation.  It also proves reflected global current cancellation is nonselective.  Remaining
RH-bearing source obligation is componentwise zero carry/detailed balance, or a source-predeclared
one-sided law forbidding counter-circulation before any zero is chosen.
