# PW-B infinite dark endpoint-winding separation (HC31, 2026-08-28)

Module
`GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekInfiniteDarkEndpointWindingSeparation`
evaluates corpus's explicit infinite-support three-moment PW-dark vector on literal endpoint winding.

For `q=exp(-1/(4 epsilon))`, `epsilon>0`, response is
`q(1-q)(3-2q)/(1-q/2)>0`. Existing infinite dark matrix's endpoint energy is response squared and
strictly positive. Core theorem:
`schwarzschildParikhWilczekEndpointWinding_defeats_infiniteGradeDarkMatrix`.

Direct Lean and target-only build passed (11614 jobs); six theorem endpoints audit to standard axioms
only. Module wired into `GaloisForLFunctions/RHTower.lean`. Frontier map untouched.

Research consequence: known finite polynomial, arbitrary finite-support, and explicit admissible
infinite three-moment PW dark objects are all separated by literal endpoint winding. Next exact burden
is uniqueness for arbitrary absolutely summable grade sequences from physical endpoint responses,
then oriented recoil coupling.
