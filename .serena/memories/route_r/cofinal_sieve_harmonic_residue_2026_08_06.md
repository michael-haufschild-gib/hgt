# Route R cofinal sieve harmonic residue — 2026-08-06

Created and verified `formal/GaloisForLFunctions/RHTower/RouteRCofinalSieveHarmonicResidue.lean`; wired into `formal/GaloisForLFunctions/RHTower.lean`.

Mathematical advance:
- For any enumeration `e : ℕ ≃ Nat.Primes`, restart nested Euler sieve after prefix `N`.
- Tail density `D_{N,n}=∏_{k<n}(1-1/e(N+k))`; loss weights `D_{N,n}/e(N+n)` are positive and have sum 1.
- Reporter `S_N(a)=∑ D_{N,n} a(e(N+n))`.
- For summable prime field `b`, `S_N(b)→0`.
- If `a=c/p+b` modulo `ell^1`, `S_N(a)→c`; coefficient is unique and enumeration-independent.
- Actual critical-wall Gamma field has reporter limits `-1` for positive grade, `0` neutral, `+1` negative.

Key theorems:
- `hasSum_routeRCofinalSieveWeight`
- `tendsto_routeRCofinalSieveHarmonicReporter_zero_of_summable`
- `tendsto_routeRCofinalSieveHarmonicReporter`
- `routeRPrimeHarmonicAsymptotic_unique`
- `routeRPrimeGammaCriticalWallReporter_zeroLimit_iff`
- `routeRPrimeGammaXiCriticalWallReporter_zeroLimit_iff_re_eq_half`

Conjecture loop:
1. unshifted reporter falsified: nonzero ell1 bias;
2. globally normalized tail rejected as representation: divides by vanishing density;
3. literal tail restart proved and formalized.

Exact new open core:
`[OPEN CORE — ROUTE_R_COFINAL_SIEVE_STOKES_ZERO_LIMIT]`
Derive from pre-divisor fixed-source-orientation Stokes/Cartier producer that `S_N(W_{t_rho})→0` for every Xi support point. Formal iff then forces `Re rho=1/2`. Do not claim zero limit; it remains RH-bearing.

Kanban:
`docs/drafts/pipeline/3-formalized/route-r-cofinal-sieve-harmonic-residue.md`
and active Route R card updated.

Verification:
- direct Lean green
- targeted module build green
- `scripts/formal_tools.py lint` green
- axioms exactly `[propext, Classical.choice, Quot.sound]`.
