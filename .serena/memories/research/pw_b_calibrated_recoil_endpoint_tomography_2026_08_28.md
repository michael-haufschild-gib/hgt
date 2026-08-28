# PW-B calibrated recoil endpoint tomography (HC33, 2026-08-28)

Formalized and wired `ThetaCuspHawkingParikhWilczekCalibratedRecoilEndpointTomography.lean`.

Construction: divide literal imaginary Borel recoil holonomy by its exact strictly positive grade residual, then couple the recovered common wall factor to HC32's countable physical endpoint-winding basis.

Main kernel theorem: for bounded `c` and nonreal open-strip `s`, all calibrated endpoint responses vanish iff `s.re = 1/2 ∨ c = 0`. No infinite packet dark sector remains. Canonical constant-one packet gives premise-free RH equivalence: RH iff reporter vanishes for every Xi divisor point and every physical scale.

Verification: direct Lean passed; targeted module build passed (11,617 jobs); five endpoints use only `propext`, `Classical.choice`, `Quot.sound`; lint has no HC33 finding.

Novelty boundary: source-specific calibrated holonomy/tomography coupling and joint-kernel theorem were absent from corpus and not found in primary literature searches. This is an endpoint equivalence, not RH: missing source-side theorem must force its universal flatness on Xi support.
