# PW-B finite-packet endpoint-winding tomography (HC30, 2026-08-28)

Module `GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFinitePacketEndpointTomography`
proves that every real packet `c : Fin N -> R` is recovered by its literal PW endpoint-winding
responses at `epsilon_j=1/(4(j+1))`, `j : Fin N`.

Key theorem:
`schwarzschildParikhWilczekFinitePacketEndpointResponse_eq_zero_iff`.

Proof: exact endpoint amplitude is `q_j^(k+1)`, with `q_j=exp(-(j+1))`. Remove nonzero row factor
`q_j`; remaining matrix is `Matrix.vandermonde q`. Exponential injectivity gives distinct nodes and
nonzero determinant, so a zero response vector has zero coefficients.

Direct Lean and target-only build passed; five declarations audit to standard axioms only. Module is
wired into `GaloisForLFunctions/RHTower.lean`. Frontier map was not edited.

Research consequence: finite-support darkness is closed for literal PW endpoint winding. Remaining
PW-B core is infinite-support/completion behavior and source-derived oriented recoil coupling before
Xi-divisor specialization.
