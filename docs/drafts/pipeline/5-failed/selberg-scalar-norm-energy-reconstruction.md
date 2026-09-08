# Scalar squared norm alone does not reconstruct periodic-field energy

- **ID:** SELBERG-SCALAR-NORM-ENERGY
- **Stage:** 5-failed — this shortcut only; the full Selberg goal remains active.
- **Parent:** Selberg conjecturing loop, cycle 26.

## Proposed shortcut and exact failure

Claim tested: the scalar squared norm of a smooth period-one complex field determines its full horizontal derivative energy, allowing that energy to be replaced by scalar-amplitude derivative energy.

Take `F_c(z)=exp(i*c*Re(z))`. Both `F_0` and `F_(2*pi)` are smooth and period one. Both have scalar squared norm one and scalar-amplitude derivative zero everywhere. Their actual horizontal derivative energies are respectively zero and `(2*pi)²>0`.

The exact closed Lean witness is `SelbergScalarPhaseToy.scalar_trace_does_not_determine_energy`. These fields are not asserted to be Maass eigenforms, cusp forms, or invariant under inversion. The failure concerns only the stated smooth periodic class. The actual Maass equation plus its eigenvalue still recovers total gradient energy from trace derivatives; this card does not contradict that equation.

## Positive survivor

For the actual finite Maass congruence family, subtract the canonical common real radial slope `c_v=(D_v D)/(2D)` from every component derivative. The squared residual sum is nonnegative. Its full square-completion identity makes this slope the unique minimizer when `D>0`; zero residual is equivalent to all component derivatives being radial with that common slope.

At positive density, full source energy is exactly scalar-amplitude energy plus the residual. The identity multiplied by density holds even at trace zeros. Combining it with the actual Maass equation retains the eigenvalue in an exact Fisher identity. These are source theorems, not abstract value assumptions.

**Paper proof:** dependency closed in [strict mass and radial defect](../3-formalized/selberg-positive-mass-and-radial-defect.md).

**Lean status:** the exact survivor is proved in `SelbergMaassTraceRadial`, including `radialResidual_minimization`, `radialResidual_minimum_unique`, `angularEnergy_eq_zero_iff`, `density_mul_gradientDensity`, and `trace_fisher_identity`. Complete audit is recorded on that linked card. No whole-route impossibility or Selberg counterexample is claimed.
