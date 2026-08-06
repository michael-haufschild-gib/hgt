# Route R prime-sieve variation cap reporter (2026-08-06)

Formalized new Route R bridge in `formal/GaloisForLFunctions/RHTower/RouteRPrimeSieveVariationCapReporter.lean`, wired into `RHTower.lean`.

For every prime enumeration `e : ℕ ≃ Nat.Primes`, define source weights
`w_e(n) = sieveDensity (sievePrefix e n) / (e n : ℝ)` and local factor
`q(p) = (1-p⁻¹)(2-p⁻¹)`. Existing telescope gives `HasSum w_e 1`; all weights are positive. Formalized `0 < q(p) < 2`, summability of `w_e(n)q(e n)`, and calibration
`C_e = ∑' n, w_e(n)q(e n)` with `0 < C_e < 2`.

Defined actual all-prime reporter
`R_e(rho) = ∑' n, (w_e(n):ℂ) * ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort (e n) rho`.
Proved absolute convergence and exact factorization
`R_e(rho) = ((primeDepthBVWoldXiCenteredRate rho * C_e : ℝ) : ℂ) * ccmRationalAdelicPrimeXiCartierCoefficient rho`.
Since `C_e>0` and Cartier coefficient is nonzero:
- `R_e(rho)=0 ↔ primeDepthBVWoldXiCenteredRate rho=0`;
- `R_e(rho)=0 ↔ CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho`;
- `(∀rho, R_e(rho)=0) ↔ RiemannHypothesis`.

This is not RH and does not prove reporter zero. Frontier delta: prior bounded all-prime reporter assembly/coefficient-faithfulness burden is closed. Honest remaining producer is now exactly an independent pre-divisor Stokes law forcing `R_e(rho)=0`. Positivity prevents cancellation, enumeration choice, or coarse corona erasure from hiding nonzero mate rate.

Conjecture loop: raw `1/p` reporter diverges; coarse density erases; inverse-density normalization is singular; nested loss increments survive and have mass one. Generic weighted summability is literature; exact Route R identification remains `[NOVELTY UNVERIFIED]`.

Card: `docs/drafts/pipeline/3-formalized/route-r-prime-sieve-variation-cap-reporter.md`.
Verification: direct Lean PASS, formal lint PASS, exact module OLean build PASS. Axioms on main theorems: `[propext, Classical.choice, Quot.sound]`.

Related earlier memories: `mem:route_r/singular_stokes_flat_producer_audit_2026_08_06`, `mem:route_r/phase_quadrature_frontier_2026_08_06`.