# WP04 — OPEN

Main half-integer counting target remains open. No extra premise has been promoted to a producer.

Four compiled bridge leaves now cover exact Stieltjes inversion, endpoint atoms, and radial traces of the normalized canonical exponential:

- `WeilWorkQuantizationKernel.lean`: uniform weighted domination and interval inversion.
- `WeilWorkQuantizationBoundaryPhase.lean`: canonical interval phase on one common full-measure endpoint set.
- `WeilWorkQuantizationEndpointPhase.lean`: endpoint-inclusive limits, with half the atom mass at each endpoint.
- `WeilWorkQuantizationRadialBoundary.lean`: primitive normalized at 2; finite phase limits and exponential radial traces at every height; measurable trace and conjugation symmetry.

All four direct leaf checks and both scratch audits passed. The audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. See PROOF.md for the paper arguments and EVIDENCE.md for commands and exact scope.

For arbitrary `hW`, `exists_fullMeasure_interval_phase` supplies one full-measure endpoint set with vertical interval integral tending to `π μ((a,b])`. `tendsto_exp_four_mul_interval_phase` identifies the corresponding phase limit with `exp(4πi μ((a,b]))`. It does not prove that this phase equals 1.

Difference from starting corpus: fixed-width smoothed counting and singleton radial extraction were already proved. This investigation connects shrinking-width interval phase to the same measure and retains endpoint atoms to construct radial traces everywhere. A parallel current corpus file now constructs an almost-everywhere trace; this overlap is recorded in EVIDENCE.md. The underlying analytic mechanism is classical. Significant scientific novelty is not claimed for these prerequisites.

Active candidate F: after removal of the integer atomic floor of the actual canonical measure, either the residual mass is infinite or `lam(n)=Λ(n)` for every `n≥2`. FINITE-REMAINDER.md contains the paper argument and formal dependency map. Arbitrary finite singular-continuous remainder is included in its proposed scope. Its rigidity conclusion is not yet formalized, and excluding the infinite-remainder alternative remains an additional source obligation for full WP04. Next formal target is a uniform signed truncated contour bound with radial traces and no supplied closed-edge continuity.

All four finished modules are wired into `RHTower.lean`. Latest repository lint failed on eight unrelated unreachable modules; no quantization-module error was reported. No full or umbrella build was run. Existence of a positive input remains WP01's separate problem.
