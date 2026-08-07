# Route R: Burnol divided-shift fixed-source leakage (2026-08-07)

Conjecture loop:
1. Reciprocal closure implies zero-locus ladder tightness — falsified: exact aperture type is |Re rho - 1/2|.
2. Finite Mellin-head subtraction implies tightness — falsified: finite corrections do not change exponential type.
3. At an annihilator zero, divided shift is source-orthogonal — falsified, yielding positive survivor: strict accretivity forces quantitatively nonzero fixed-source leakage off the critical line.

New law: for m_rho(t)=1/(rho-(1/2+i*t)), delta=Re rho-1/2>0,
Re m_rho(t)=delta*|m_rho(t)|^2 and hence
Re <f,A_rho f> = delta*||A_rho f||^2.
For source subspace S and f in S,
delta*||A_rho f||^2 <= ||f||*||P_S A_rho f||.
For nonzero f, P_S A_rho f != 0.

Concrete Route R instantiation uses an explicit nonzero sub-window co-Poisson source atom at fixed aperture c=1/2,d=1. Therefore every right-half Xi divisor point has nonzero retained source projection, with a quantitative lower bound.

New Lean files:
- formal/GaloisForLFunctions/HTGeometry/StrictAccretiveMultiplier.lean
- formal/GaloisForLFunctions/RHTower/BurnolDividedShiftSourceLeakage.lean
Umbrellas wired.

Endpoint:
BurnolXiDividedShiftSourceFlatness := every right-half Xi divisor point has zero projection of the fixed-aperture divided-shift atom onto the co-Poisson source.
riemannHypothesis_of_burnolXiDividedShiftSourceFlatness proves RH.

Remaining producer: derive BurnolXiDividedShiftSourceFlatness independently from pre-divisor rational-adelic/Euler-Gamma/Stokes structure. This is one fixed source coordinate, not an unbounded-depth tightness family.

Verification:
- lake env lean on both new files: clean
- lake build GaloisForLFunctions.HTGeometry.StrictAccretiveMultiplier: success
- lake build GaloisForLFunctions.RHTower.BurnolDividedShiftSourceLeakage: success
- scripts/formal_tools.py lint: clean
- endpoint and core theorems axioms: [propext, Classical.choice, Quot.sound]

Do not claim RH proved: source-flatness producer remains open.