Formalized intrinsic nonlinear/non-spectral source-grade Hahn–Jordan selection.

Files:
- `formal/GaloisForLFunctions/HTGeometry/SourceGradeJordanDataProcessing.lean`: scalar Jordan positive/negative parts, reconstruction, mutual exclusion, explicit nonadditivity, TV contraction, exact loss, strict loss.
- `formal/GaloisForLFunctions/RHTower/SourceHorizontalEulerWoldJordanResidualSelection.lean`: prime-labelled Euler/Wold atom density before grade compression; exact pointwise parts; masses `2G_N/H_N^3`, `2W_N/H_N^3`; strict compression loss `4W_N/H_N^3`; post TV `2D_N/H_N^3`; limits `2/3,2/3,4/3,0`; explicit Euler prime-power `k^2` depth sum; selected negative Euler and positive Wold matrices equal prior completed Gamma/polar landings; pair reconstructs linear defect; actual Xi multiplicity, BV endpoint, four orientations preserved; selected `(0,0)` action converts signed BV split exactly into existing compensated energy and hence eventually lies below primitive source budget for nonzero coefficient. Capstone `sourceHorizontalEulerWoldJordanResidualSelection`.

Verification:
- exact `lake env lean` passed;
- exact leaf `lake build GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldJordanResidualSelection` passed (built missing dependency oleans only; no umbrella build);
- axiom audit only `propext`, `Classical.choice`, `Quot.sound`;
- formal lint no proof debt; global reachability remains blocked by six unrelated pre-existing HTGeometry modules.
- wired into `HTGeometry.lean` and `RHTower.lean` without umbrella build.
- Stage-3 card: `docs/drafts/pipeline/3-formalized/source-horizontal-euler-wold-jordan-residual-selection.md`.

Literature frontier: Hahn–Jordan minimality/TV contraction is classical (Fischer 2012; Ali–Silvey 1966; Csiszár 1967); current BV pushforward literature retains residual observables via SDR but supplies no arithmetic Xi selector. Bounded primary search found no Euler/Wold Xi application; novelty unverified.

Route-P next open core: source-natural Xi-fibre physical admission identifying the canonical residual pair, without recompression, with the literal non-spectral conormal contraction/positive selected corner used by the RH endpoint. Ordinary Loewner/equivariant admission is internally RH-equivalent.