# All-order discrete Möbius packet identity, horizons, aperture and wedge — Lean certificate

- **ID:** L-DISCRETE-MOBIUS-PACKET-SOBOLEV
- **Stage:** 3-formalized
- **Paper proof:** [l-discrete-mobius-packet-sobolev.md](l-discrete-mobius-packet-sobolev.md)
- **Lean modules:** `GaloisForLFunctions.RHTower.MobiusDiscretePacketGeneralOrder`,
  `…MobiusDiscretePacketHorizon`, `…MobiusDiscretePacketEdgeEstimates`,
  `…MobiusDiscretePacketCriticalHorizon`, `…MobiusDiscretePacketSourceAperture`
  (inputs: `MobiusReciprocalDiscretePacketBridge`, `MobiusRenewalPacketEnergy`,
  `MobiusCofinalCubicEnergyCriterion`, `MobiusCubicSourceMertensEnergy`, `DeningerMertensSummatory`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake env lean` clean on each module; targeted `lake --old build` of each;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for every theorem below. No computation.

Namespace `RHTower.DiscretePacket`. `b_k = MobiusPacketDifference.packet N (1+δ) k`,
`c_k = cubicPacket δ N k = Σ_{1≤n≤N} μ(n) g_k(n)` with `g_k = packetKernel δ k`,
`w_k = binomialWeight (5+δ) k`, `B(N) = finiteGeneralReciprocalEnergy (3+δ) δ N`,
`E = CubicGamma.mertensSaving`. The card's `J` is `m+1`.

| Card item | Lean theorem |
|-|-|
| (3) generic expansion; (4) `c_{J,k} = 4^{-(J-1)} Δ₂^{J-1} b_k`; `1-q_n² = 4n/(n+1)²` | `orderPacket_eq_stepTwoDifference`, `one_sub_node_sq`, `orderGammaHankelEnergy_eq_routeL` |
| (1) `B_{J+δ,δ}(N) = 2^{δ-2J+3} Σ_k C(2J-2+δ+k,k)(Δ₂^{J-1}b_k)²`, summands `≥ 0` | `routeLOrderEnergy_eq_stepTwoDifference`, `stepTwoEnergyTerm_nonneg` |
| (2) cubic case `2^{δ-3}`; one-atom check `2^{-5-δ}`, `b_0 = 2^{-1-δ}`, `b_k = 0` | `routeLCubicEnergy_eq_stepTwo`, `routeLCubicEnergy_one`, `packet_one` |
| RH if (2) has bounded returns on shifts cofinal at zero | `riemannHypothesis_of_stepTwoPacketFrequentlyBounded` |
| (5) `|c_k| ≤ (3/2)e^{-2k/(N+1)}`; `q_n ≤ e^{-2/(n+1)}`; `Σ n^{-3} ≤ 3/2` | `abs_cubicPacket_le`, `node_le_exp`, `sum_inv_cube_le` |
| (5) `C(4+δ+k,k) ≤ C(k+5,5) ≤ (k+5)^5/120`; product formula | `binomialWeight_le_choose`, `binomialWeight_eq_prod`, `binomialWeight_mono`, `binomialWeight_six` |
| (6) tail `≤ 144 (N+1)^6 e^{-2K/(N+1)}` | `cubicPacket_tail_le` |
| `K_P(N)`: tail `≤ 144 (N+1)^{-P}`; bounded energy ⟺ bounded range `k < K_P(N)` | `cubicPacket_tail_horizon_le`, `routeLCubicEnergy_bounded_iff_horizon` |
| `w_k ≤ e^5 k^{4+δ}` | `binomialWeight_le_rpow` |
| (6b)–(6c) the two-part packet bound for `k ≥ 6(N+1)` | `abs_cubicPacket_critical_le` |
| exponential-tail estimate `Σ_{k≥K} k^p x^k ≤ (N+1)K^p x^K` | `rpow_mul_pow_tail`, `critical_rpow_tail` |
| (6a) tail beyond `K(N)` `≤ C[E(N)² log^5 + log³/(N+1)] → 0`, uniform in `δ` | `cubicPacket_criticalTail_le`, `tendsto_criticalTailProfile`, `cubicPacket_criticalTail_small` |
| monotonicity of `g_k` for `2x ≤ k` (discrete form of `g'/g ≥ -4/x + 2k/x²`) | `packetKernel_le_succ`, `packetKernel_nat_mono` |
| (7a) `|M(x)| ≤ C x E(x)`; window form `|M(n)| ≤ C L E(L)` on `[L/4, L]` | `exists_abs_abelMertens_le_all`, `exists_abs_abelMertens_window` |
| finite Abel summation (monotone weight / total variation) | `abs_sum_Ioc_moebius_mul_le_of_monotone`, `abs_sum_Ioc_moebius_mul_le` |
| (7-low) absolute low edge `≤ (M+2)^{-1-δ}e^{-2k/(M+2)}/k` (telescoping primitive) | `abs_sum_low_packetKernel_le`, `rpow_exp_le_lowPrimitive_sub` |
| (7-low-end) Mertens bound on `(⌊L/2⌋, L]` | `abs_sum_lowmid_le` |
| (7b)–(7c) increments `|g_k(x+1)-g_k(x)| ≤ 8x^{-4-δ}` for `x ≥ k`; high edge `≤ C E(U)U^{-2-δ}` | `abs_packetKernel_succ_sub_le`, `abs_sum_high_le` |
| (7d) `w_k|c_k^high|² ≤ e^5 C² E(k)²/k`; `2a_δ(2+δ) = 5+δ` | `weighted_high_le`, `upperExponent_mul` |
| `Σ_k (log k)^p E(k)²/k < ∞` (condensation) | `summable_log_pow_mul_mertensSaving_sq_div` |
| (7) `Σ_k w_k (c_k - c_k^mid)² ≤ C_A`, every `0 < A ≤ 4` (includes `A = 4`) | `sourceAperture_bound`, `weighted_aperture_error_le` |
| absolute high edge at `⌈k^{a_δ+ε}⌉` | `absoluteHighEdge_bound` |
| (8) bounded energy ⟺ bounded wedge `Σ_{k₄≤k<K(N)} w_k (c_k^mid)²`, every set of cutoffs | `routeLCubicEnergy_bounded_iff_wedge` |
| RH from bounded wedge returns on shifts cofinal at zero | `riemannHypothesis_of_wedgeEnergyFrequentlyBounded` |

The Lean proof of (7) splits the low edge at `⌊L_k/2⌋` for every `A ≤ 4` (the paper treats
`A < 4` by the absolute bound alone); the derivative bounds (7b) and the monotonicity criterion are
used in their discrete increment forms.
