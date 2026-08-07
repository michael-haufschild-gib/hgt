# Route R Burnol physical dissipativity bridge (2026-08-07)

[LEAN-PROVED] New module `RHTower/BurnolDividedShiftPhysicalDissipativity.lean` identifies Burnol's physical one-sided dilation integral with Route R's Mellin Cauchy multiplier.

Conjecture loop:
1. Actual-zero evaluator orthogonality directly implies divided-shift source flatness: [FALSIFIED], different vectors; strict accretivity gives the opposite off-line.
2. Evaluator and divided shift agree modulo source orthogonal: [CIRCULAR], this is the RH-strength endpoint.
3. Physical dilation-resolvent identity plus scalar port law: [REDISCOVERED] [BRIDGE], survives and is formalized.

Key theorems:
- `integral_burnolShiftWeight_mul_mellinCharacter`
- `integrable_burnolMellinLaplaceKernel_mul_inner`
- `burnolShift_eq_burnolMellinDividedShift`
- `burnolDividedShiftPhysicalPort_eq_inner_mellin`
- `re_burnolDividedShiftPhysicalPort_eq`
- `re_burnolDividedShiftPhysicalPort_pos`
- `burnolXiDividedShiftSourceFlatness_iff_physicalDissipativity`
- `riemannHypothesis_of_burnolXiDividedShiftPhysicalDissipativity`

Exact frontier delta: vector projection flatness is equivalent to one scalar producer
`BurnolXiDividedShiftPhysicalDissipativity`: at each actual right-half Xi divisor, the real part of the explicit fixed co-Poisson dilation autocorrelation port is nonpositive. Existing Cauchy/Herglotz law proves the same port is strictly positive throughout the open right half-plane. Thus the remaining [OPEN CORE] is derivation of this one nonpositive oriented Stokes sign from pre-divisor rational-adelic/Euler–Gamma–Stokes structure.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/BurnolDividedShiftPhysicalDissipativity.lean`: green.
- `lake build GaloisForLFunctions.RHTower.BurnolDividedShiftPhysicalDissipativity`: green.
- `scripts/formal_tools.py lint`: green.
- Axioms: `[propext, Classical.choice, Quot.sound]` only.
- Wired into `RHTower.lean`.
- Card promoted to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/burnol-divided-shift-physical-dissipativity.md`.
