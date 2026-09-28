# Complete prime-layer compensation by nearby semiprimes — Lean certificate

- **ID:** L-ALL-PRIME-SEMIPRIME-LOCAL-MATCHING
- **Stage:** 3-formalized
- **Paper proof:** [l-all-prime-semiprime-local-matching.md](l-all-prime-semiprime-local-matching.md)
- **Lean modules:** `GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount`, `…SemiprimeWindowCount`,
  `…PrimeCellPartition`, `…MobiusPrimeSemiprimeCellMatching`, `…MobiusSemiprimeTriprimeCellMatching`
  (inputs: `Sieve.ChebyshevThetaBigO` (θ with de la Vallée Poussin error), `Sieve.MertensFirst`,
  `Sieve.MertensSecond`, `Sieve.CellMatching`, `WindowBudget`, `MobiusCubicGammaNorm`,
  `MobiusCubicGammaAtomJets`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake env lean` clean on each module; targeted `lake --old build` of each;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for every theorem below. No computation.

Namespace `RHTower.PrimeCells`; `f_x = atom x`, `‖·‖_δ = gammaNorm δ`, `windowPrimes a b` = primes in
`(a, b]`, `semiprimesIn a b` = squarefree `pr ∈ (a, b]`, `p < r` primes.

| Card item | Lean theorem |
|-|-|
| prime number theorem with log-power error `|θ(t) - t| ≤ C_A t/(log t)^A` (from the corpus `θ(t) - t = O(t e^{-c√log t})`) | `exists_abs_theta_sub_le`, `exp_neg_mul_sqrt_le` |
| window counts via `#(a,b] log a ≤ θ(b) - θ(a) ≤ #(a,b] log b` | `card_windowPrimes_mul_log_le`, `theta_sub_le_card_mul_log`, `abs_theta_increment_le` |
| (2) uniform cell counts: `#{p ∈ (u,v]} ≤ (1+ε)(v-u)/log R`, `#{p ∈ (u/q, v/q]} ≥ (1-ε)(v-u)/(q log R)`, `2 ≤ q ≤ 5` | `exists_card_windowPrimes_le`, `exists_card_windowPrimes_div_ge` |
| cells `J = ⌊(log R)^B⌋`, `h = R/J ∈ [R/(log R)^B, 2R/(log R)^B]`; cell index; cellwise injection | `cell_scale`, `cellIndex_spec`, `cellIndex_eq`, `cellIndex_lt`, `exists_cellwise_injOn` |
| supply `31/30` beats demand; three `q`-families disjoint | `semiprimeTargets_card_ge`, `card_semiprimeTargets`, `mem_semiprimeTargets` |
| `‖∂_x f_x‖_δ² = C_δ x^{-3-δ}` with `C_δ = (δ² + 3δ + 6) 2^{-(7+δ)}` (closed form of the card's Gamma integral), continuous, `≤ 10/128` on `[0,1]` | `gammaEnergy_atomJet_one`, `continuous_derivEnergyConst`, `derivEnergyConst_le` |
| `‖f_x - f_y‖_δ ≤ C|x-y| R^{-(3+δ)/2}` for `x, y ∈ [R, 2R]` | `gammaNorm_atom_sub_band`, `gammaNorm_matched_le` |
| **(1)** injection `φ_R`: primes of `(R,2R]` → `qr`, `q ∈ {2,3,5}`, `r > 5` prime, `|φ(p) - p| ≤ 2R/(log R)^B`, `μ(p) = -1`, `μ(φ(p)) = 1`, atoms disjoint in `(R,2R]` (each occurs once in the source for `N ≥ 2R`), `‖S_R‖_δ² ≤ C R^{1-δ}/(log R)^{2B+2}` | `exists_prime_semiprime_matching` (with `exists_cell_matching_of_counts`, `sum_dipoles_eq_literal`, `matched_energy_sq_le`, `moebius_prime_semiprime`) |
| (4)–(6) semiprime count `A_2(u,v) ≤ (v-u)/log R · (log log R + K)` (cover by `p ≤ √v`, `1/(L - log p) ≤ 1/L + 3 log p/L²`, Mertens' two theorems) | `exists_card_semiprimesIn_le`, `semiprimesIn_subset`, `card_windowPrimes_div_prime_le`, `semiprime_sum_arith` |
| (7) triprime supply `≥ (1-ε)(v-u)/(q log R) · (log log R - K)` per `q`, families disjoint | `exists_card_triprimeTargets_ge`, `card_triprimeTargets`, `card_windowPrimes_triprime_ge`, `card_triTargets`, `triTargets_card_ge` |
| **(3)** two-layer pairing: every prime → semiprime, every unused squarefree semiprime → triprime `qrs`, `5 < r < s`, displacements `≤ 2R/(log R)^B`, literal disjoint subsum, `‖T_R‖_δ² ≤ C R^{1-δ}(log log R)²/(log R)^{2B+2}` | `exists_two_layer_matching` (with `exists_triprime_cell_matching_of_counts`, `two_layer_sum_eq_literal`, `moebius_mul_primes`, `moebius_mul_three_primes`) |

The semiprime demand is bounded directly by the cover `p ≤ √v`, which contains the card's split
`p ≤ √u` plus the omitted range `√u < p ≤ √v`; the triprime supply is bounded below by the explicit
families `5 < p ≤ √(u/q) < r`, which already exclude cofactors in `{2,3,5}`.
