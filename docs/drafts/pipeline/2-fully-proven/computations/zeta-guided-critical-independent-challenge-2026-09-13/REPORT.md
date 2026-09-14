# Validation of the four access-guided connections

All 16 repeated two-branch calculations completed. The four endpoint pairs remain 29–27, 38–40, 55–54 and 59–57 at both 100 and 160 digits, under two starting displacements and smaller continuation steps.

Independent Euler–Maclaurin evaluations with two truncations checked seven locations on each branch. The worst 160-digit independent target residual was 4.58e-148. The four critical points were refined from their discovery seeds. These checks support finite connections, not a uniform path certificate or a complete critical-point census.

Combined with the earlier graph, these edges give 46 edges and 18 connected components on 64 cached zero labels. Each component contains one escape-like vertex under each of the three tested access directions. The added edges were found because the independently measured access map identified four exceptional vertices. This is evidence that combining the two views can guide reconstruction more effectively than the original local starts alone.

The RH implication remains open. A graph reconstructed only from cached critical-line zeros cannot exclude additional off-line zeros. A proof would need a source-derived construction covering the full divisor and a separate rigidity theorem. The observed finite graph is a research instrument and a target for falsification against arithmetic controls, not a proof premise.

Run `python guard.py experiment.py`. All refined points, branch paths, independent checks, source search, exact environment and original checksums are included. No Lean builds.
