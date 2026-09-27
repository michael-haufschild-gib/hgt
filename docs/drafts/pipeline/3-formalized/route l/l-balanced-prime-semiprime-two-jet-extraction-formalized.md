# Balanced cofactor two-jet extraction — Lean certificate

- **ID:** L-BALANCED-PRIME-SEMIPRIME-TWO-JET
- **Stage:** 3-formalized
- **Paper proof:** [l-balanced-prime-semiprime-two-jet-extraction.md](l-balanced-prime-semiprime-two-jet-extraction.md)
- **Lean modules:** `GaloisForLFunctions.RHTower.MobiusTwoJetBlockTaylor`,
  `…MobiusTwoJetCofactorPacket`, `…MobiusTwoJetPrimeSemiprimePacket`, `…MobiusTwoJetLinearDensity`
  (inputs: `MobiusCubicGammaNorm`, `MobiusCubicGammaAtomJets`, `MobiusBalancedTwoJetSelection`,
  `WindowBudget`, `Sieve.InghamUniformDetectorMellinEveryBaseThetaMass`,
  `Sieve.CoprimeSquarefreeHarmonic`, `GaussSpikeMass`, `MobiusAbelPrefixGramIntegral`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake env lean` clean on each module; targeted `lake --old build` of each;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for every theorem below. No computation.

Namespace `RHTower.CubicGamma`; `α = supplyExp = 71/100`, `f_x = atom x`,
`‖·‖_δ = gammaNorm δ`, `S_N = mobiusCubicSource N`.

| Card item | Lean theorem |
|-|-|
| (3) every-base theta mass at `α = 71/100`; window count `≥ z^α/(16384 log 5R)` | `exists_theta_window_supply`, `card_windowPrimes_ge`, `exists_window_family` |
| four families per block, windows at bases `X/q`, `X/(2q)` inside the quarters | `exists_cofactor_block`, `cofactor_prime_atoms`, `cofactor_doubled_atoms` |
| (4) balanced prefixes, one orientation complete, first moment `≤ L` | `exists_balanced_prefixes` (from `exists_balanced_two_orientations`) |
| (5)–(6) jet norms and second-order Taylor law for pair packets | `gammaNorm_atomJet_le`, `gammaNorm_pairPacket_le`, `exists_block_two_jet` |
| (7) summing the `J` blocks | `cofactor_final_bound`, `cofactor_mL_le`, `cofactor_count_ge`, `packetSet` bookkeeping |
| (8) cofactor packets for all `1 ≤ q ≤ √R`: `R<qr<2R`, `2R<qp<4R`, equal counts `≥ cR/(q log R)`, bound with `q^{-21/50}` | `exists_cofactor_two_jet_packet` |
| literal coefficients `μ(2qr)=μ(q)`, `μ(qp)=-μ(q)` | `moebius_two_mul_mul_prime`, `moebius_mul_prime_of_lt` |
| (1) `A_R ⊆ {2r}`, `B_R ⊆ {p}`, disjoint, `|A|=|B| ≥ cR/log R`, `μ(2r)=1`, `μ(p)=-1`, `P_R = Σ_A f - Σ_B f`, bound | `exists_balanced_prime_semiprime_packet` |
| `‖P_R‖_δ → 0` uniformly in `δ` | `tendsto_twoJet_bound` |
| (2) dyadic packets: disjoint shells, summable majorant uniform in `δ` | `exists_dyadic_prime_semiprime_packets` |
| reduction along `N_J = 2^{J+2}`: residual is a literal subsource at bounded distance; bounded ⟺ bounded | `cofinal_packet_reduction`, `primeSemiprime_cofinal_reduction` |
| distinct cofactors give distinct atoms (unique large prime, parity) | `cofactor_eq_of_mul_eq` (and parity in `exists_linear_density_packet`) |
| (9) `Σ_{q≤Y odd squarefree} 1/q ≥ (log Y)/8 - 7/8` | `sum_inv_odd_squarefree_ge` (from `Sieve.sum_inv_coprime_squarefree_ge`, `Q = 2`) |
| (10)–(11) at `η = 1/10`: equal sign counts `≥ cR`, bound `R^{-2/5-δ/2} + R^{-11/500-δ/2}/log R` | `exists_linear_density_packet_tenth` |
| general `0 < η < 4/29`: exponents `η-(1+δ)/2`, `29η/50-2/25-δ/2` | `exists_linear_density_packet`, `sum_cofactor_rpow_le`, `log_floor_rpow_ge` |
| dyadic summability and cofinal reduction for `P_R^all` | `linearDensity_cofinal_reduction` |

The per-cofactor theorem holds uniformly for `q ≤ √R`, which contains the card's range
`q ≤ R^{1/10}` (and `q ≤ R^η`, `η < 4/29`).
