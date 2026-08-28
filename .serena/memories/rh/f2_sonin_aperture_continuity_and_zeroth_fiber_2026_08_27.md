F2 Sonin aperture progress, 2026-08-27. Frontier map is user-declared read-only; never edit or revert its concurrent modifications.

Lean-closed modules wired into RHTower umbrella:
- SoninProjectionApertureStrongContinuity.lean: positive-aperture strong continuity of actual Sonin projection.
- SoninResidualApertureHilbertSchmidtContinuity.lean: generic strong/HS ideal lemmas plus fixed-block weighted residual HS continuity.
- SoninAllPrimeMomentApertureContinuity.lean: dominated all-prime HS continuity, all trace-moment continuity, exact cluster landing, equivalence of moving weld with one exact positive aperture.
- SoninAllPrimeZerothMomentApertureSurjectivity.lean: zeroth trace hits every positive real target; normalized prime-arch moment zero has an exact positive aperture.
- SoninAllPrimeZerothMomentApertureFiberCompactness.lean: exact zeroth-normalization fiber is nonempty compact; all higher defects attain minima; first moment either matches jointly with zeroth or has a uniform positive gap on the fiber.

Direct lake env lean checks and exact per-module lake builds passed. Latest build counts: all-prime continuity 10015, zeroth surjectivity 10016, fiber compactness 10110. Axiom audits show only propext, Classical.choice, Quot.sound. Repository-wide formal_tools lint currently fails only because unrelated concurrent RHTower/HTGeometry modules are not wired to umbrellas; our five imports are present at RHTower.lean lines ~9471-9475. No stale Lean processes from these modules.

Research card appended: docs/drafts/pipeline/1-in-progress/sonin-residual-hs-escape-and-moment-curve-properness.md. Remaining F2 core: decide attained first defect on compact zeroth fiber, then synchronize all moments. Exact all-moment fixed-aperture identity remains unproved; RH not proved.