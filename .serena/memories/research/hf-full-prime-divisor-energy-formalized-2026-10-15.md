# HF full prime-energy divisor decomposition — verified 2026-10-15

Latest user authorization permits Lean for significant milestone discoveries, overriding the old blanket freeze (see `mem:research/hf-latest-lean-authorization-2026-10-15`). Stay HF; no web, external novelty checks, mathematical numerical experiments, or isolated-prime no-go branch. The overarching unconditional RH goal remains ACTIVE and incomplete.

## Verified milestone Q1

Source: `formal/GaloisForLFunctions/RHTower/WeilPhiDoobDivisorEnergy.lean` (546 lines at completion), namespace `RHTower.PhiDivisorEnergy`. Imported by `formal/GaloisForLFunctions/RHTower.lean` near line 27055.

For R = riemannCuspPoly, define `fiber N u = cuspTerm R 1 u * cuspTerm R N (-u)` and
`divisorEnergy N a = sum (k | N) sum (m | k) Lambda(k/m)*(a m-a k)^2`.

`primeEnergy_nat_eq_tsum_divisorEnergy_compact` (near line 529) proves exactly:
`sum' d : Nat, integral u, phiDoobPrimeJump v d u = sum' N : PNat, integral u, fiber N u * divisorEnergy N (fun m => v(u-log m))`
for every real continuous compactly supported v. The more general bounded-continuous version is `primeEnergy_nat_eq_tsum_divisorEnergy`.

The proof retains BOTH full theta indices and every prime power. No summability, positivity, or RH premise is assumed. `summable_integral_norm_edge` (line 292) proves the absolute integral-norm convergence of the entire (m,d,n) family. `summable_integral_primeJump` and `primeEnergy_divisor_hasSum` verify the original series and the regrouped series. The explicit finite-fiber equivalence is between positive triples (m,d,n) and nested divisor antidiagonals of N=m*d*n. Translation u=x+log m, theta reflection, and `cuspTerm_add_log` give the exact identity. `tsum_divisorEnergy_nonneg` proves aggregate positivity from the original prime energy, NOT the missing full Weil sign.

Analytic envelope: |fiber N u| <= (4*pi^2+6*pi)^2 N^4 exp(-pi*N) (2+exp(2u)+exp(-2u)) exp(-pi*cosh(2u)). Its u-integrability uses the existing real part of `GaloisForLFunctions.RHTower.integrable_besselOrderExpKernel`; triple summability follows from product exponential bounds. All quantitative helpers are private and support the complete identity.

## Validation

Final targeted source command `lake env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilPhiDoobDivisorEnergy.olean GaloisForLFunctions/RHTower/WeilPhiDoobDivisorEnergy.lean` exited 0 with no output/warnings. Core audit `/tmp/hf-divisor-energy-20261015-audit.lean` exited 0. Final natural-index capstone audit `/tmp/hf-divisor-energy-final-20261015-audit.lean` exited 0; its only axioms are propext, Classical.choice, Quot.sound, as for all audited core statements. No sorry/admit/axiom/unsafe declarations, heartbeat increases, full/umbrella builds, commits, or pushes were introduced/performed.

Global `scripts/formal_tools.py lint` exited 1, reporting three unrelated unreachable modules: RHTower.CHMDStage17ComplexWavePacketFactorizationAndCoshSinhDecomposition; RHTower.DeningerMeyerCausalDivision; HTGeometry.ParabolicCauchyAveraging. The HF leaf was already wired into the umbrella and no lint error for it was reported. Do not alter those unrelated branches merely to make this gate green. No running owned commands remain.

## Next work

Resume the MAIN HF sign problem, not more elementary Lean or estimates. Own card: `docs/drafts/pipeline/1-in-progress/hf-unrestricted-prime-blind-positivity-2026-10-15.md`, section “Paper continuation: the full quadratic divisor lift”. Q1 is now formalized. Q2 (weighted Cartesian-product conditional variances on divisor exponents, degree log N) and Q3 (combined Gamma–prime–pole cofactor formula) are PAPER ONLY. The signed theta fiber prevents inferring the RH lower bound from finite graph positivity. The next actual mathematical obligation remains Poisson-compatible compensation in the COMPLETE combined form, preserving the Xi-divisible radical; equivalently the existing odd-sector gap E_arch+E_prime >= mu(v^2). No RH proof or literature novelty claim has been made.
