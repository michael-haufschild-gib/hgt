# Route R: reflected co-shift Cartier continuation

Formalized and module-built `RHTower/BurnolReflectedCoShiftCartierContinuation.lean`.

Conjecture loop:
1. killed completed Gamma output is sign-blind at all Xi zeros — falsified producer;
2. zero evaluator landing — falsified by existing quantitative separation;
3. positive atomic jump energy — wrong sign;
4. survivor: independent left-half reflected co-shift continuation.

Lean-proved:
- `burnolReflectedCoShiftContinuationSymbol sigma t = -burnolDividedShiftSymbol (1-sigma) t`;
- bounded continuation and exact anti-Herglotz law;
- physical operator equals negative forward divided shift;
- strict negative fixed-source Cartier port;
- coefficient-faithful uniqueness;
- at every right-half `XiDivisorSupport`, reflected output on fixed [1/2,1] co-Poisson atom belongs to actual `soninExtendedSpace`, using Xi→zeta zero and existing Burnol zero-division;
- source lift `burnolXiReflectedCoShiftCartierSourceLift`;
- exact remaining producer `BurnolXiForwardReflectedCartierStokesSewing` implies physical dissipativity and RH.

Open core is no longer unspecified sign manufacture. Prove from pre-divisor Euler–Gamma–Stokes structure:
`burnolDividedShiftPhysicalPort rho = inner f0 (burnolXiReflectedCoShiftCartierSourceLift rho h)`.
This compares two fixed source objects; reflected side is uniquely forced and strictly negative. Do not claim this sewing is proved.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/BurnolReflectedCoShiftCartierContinuation.lean` green;
- `lake build GaloisForLFunctions.RHTower.BurnolReflectedCoShiftCartierContinuation` green;
- axioms only `[propext, Classical.choice, Quot.sound]`.
- Global lint blocked only by unrelated concurrent unreachable modules (21 RHTower + HTGeometry.CriticalGeometricMonodromy).

Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/burnol/burnol-reflected-coshift-cartier-continuation.md`.
