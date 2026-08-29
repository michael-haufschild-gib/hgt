# CFI critical-boundary singular cancellation

Formalized 2026-08-29.

- Module: `formal/GaloisForLFunctions/RHTower/CoupledFloorMobiusCriticalBoundaryCancellation.lean`
- Card: `docs/drafts/pipeline/3-formalized/cfi-critical-boundary-singular-cancellation.md`
- Closed capstone: `RHTower.coupledFloorMobiusCriticalBoundary_singularCancellation`
- Result: although common upper damping mode has divergent squared norm as delta -> 0+, full lower-minus-upper CFI incidence is square-integrable at delta=0 for every 0<omega<1/2; damped combined incidences converge strongly in L2 to critical carrier.
- New bridge: natural integer envelope for Suzuki coupled error upgraded to every real X>=1 by floor-cell main-term interpolation; gives exp(-2 omega t) critical decay.
- RH chain: singular cancellation -> closed CFI boundary carrier -> existing pre-scalar affine boundary-renormalization/source-response identity -> leaves graph-debt/source-order scalar -> four-unit endpoint -> RH.
- Verification: direct `lake env lean` PASS; targeted module build PASS (10004 replay jobs, 140s); axioms only `propext`, `Classical.choice`, `Quot.sound`. Repo lint nonzero only due unrelated concurrent unreachable modules and existing sorry in HTGeometry/PolynomialProjectiveBoundary.lean.
- Umbrella `formal/GaloisForLFunctions/RHTower.lean` wired at EOF. Frontier map not edited by this work.