# Complete radial transfer determinant: computation report

The complete four-channel first-subtracted radial moment matrix has a numerical rank-loss candidate at

`rho = 0.8807954602325953090357833380600802459842648069200899237510845722 + 0.6341456258016578377777462856707726998831614311851726207066431328 i`.

An argument-principle scan found exactly one zero over 160 fixed tiles covering `0.01 <= Re rho <= 0.99`, `0.1 <= Im rho <= 80`; the independent endpoint-series scan counted one zero in its shared low rectangle. Refinement at 60/100/160 digits drove the hypergeometric determinant residual to `5.44e-63`, `2.50e-102`, and `1.00e-162`; local winding is one. Endpoint series used 653--664 terms per entry and reconstructed the matrix to `1.45e-190` at 190 digits. Every entry is nonzero, with magnitudes between `0.1489` and `0.3492`, while the explicit right-null mixture annihilates both reader rows to working precision.

Boundary decomposition is decisive. Base-period-only and endpoint-boundary-only determinants are respectively approximately `0.230546+0.018672i` and `0.302862+0.040299i`; neither vanishes. Their complete matrix sum does. Rank loss therefore comes from cross-interference between retained bulk-period and endpoint-boundary pieces, not a zero already present in either piece.

The first literal finite-part challenge was invalid: naive subtraction near the endpoint amplified cancellation error to `1e69`--`1e218`, failed every root refinement, and produced a bogus winding two. A frozen algebraically identical `expm1` retry passed its endpoint controls (moderate-point discrepancies `2.60e-102`--`1.01e-101`), recovered the same root to about 35, 52, and 70 digits at 70/110/150-digit precision, and gave winding one and the same shifted-anchor value. Its determinant residuals, about `6.1e-36`, `1.7e-53`, and `3.3e-71`, nevertheless miss the precommitted `10^(-0.55*dps)` gate. Thus this is strong two-representation numerical evidence, not a gate-certified enclosure.

Consequence: strip-wide invertibility of this complete radial transfer factor is numerically false. Availability of nonzero individual channels cannot establish Identification; a nontrivial source mixture can be invisible to both radial readers. This does not evaluate angular coefficients, onset, causal/contact corrections, spacetime faces, complete SS/SV/VV action, or Xi, and the candidate is not claimed to be a zeta/Xi zero.

Recorded guarded runtimes: discovery 53.10 s, independent topology 238.83 s, rejected naive challenge 278.96 s, stable retry 101.41 s. Protocols, raw JSONL, run statuses, and implementations are retained.
