# Cubic Möbius prime insertion: dipole amplification and dyadic compensation — Lean certificate

- **ID:** L-PRIME-INSERTION-DIPOLE-JET
- **Stage:** 3-formalized
- **Paper proof:** [l-prime-insertion-dipole-jet.md](l-prime-insertion-dipole-jet.md)
- **Lean modules:** `GaloisForLFunctions.RHTower.MobiusPrimeInsertionDipoleJet`,
  `GaloisForLFunctions.RHTower.MobiusPrimeInsertionLiteralPackets`,
  `GaloisForLFunctions.RHTower.MobiusCubicSourceMertensEnergy`,
  `GaloisForLFunctions.RHTower.MobiusPrimeInsertionMacroscopicPacket`
  (shared: `MobiusCubicGammaNorm`, `MobiusCubicGammaAtomJets`, `MobiusAbelPrefixGramIntegral`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake env lean` clean on each module; targeted `lake --old build` of each; `#print axioms`
  = `propext`, `Classical.choice`, `Quot.sound` for every theorem below. No computation.

Namespace `RHTower.CubicGamma`. `U_q = dilate q`, `D_q F = F - U_q F` (`insertTwo` for `q = 2`),
`v_x = jetProfile x`, `H_x = dyadicJet x`, `R_q = insertionRatio q`.

| Card item | Lean theorem |
|-|-|
| `‖U_q F‖² = q^{-1-δ}‖F‖²` (every `F`), `‖D_q‖ ≤ 1 + q^{-(1+δ)/2}` | `gammaEnergy_dilate`, `gammaNorm_dilate`, `gammaNorm_sub_dilate_le`, `dilate_atom` |
| (1) jet limit `→ R_q`, independent of `x` | `tendsto_insertionEnergyRatio`, `gammaEnergy_jet_insertion_ratio`, `insertionEnergyRatio_scale` |
| (2) `R_2 = 4513/4374`, `R_3 = 283/192`, `R_q > 1 + 1/q` (`q ≥ 3`) | `insertionRatio_two`, `insertionRatio_three`, `insertionRatio_gt`, `one_lt_insertionRatio` |
| finite packets: `ε_q` with ratio `> 1` for `0 < h/x < ε_q` | `exists_insertion_amplification` |
| zero-jet ratios `217/486`, `37/48`; `11/48` vs `91/192` | `gammaEnergy_mass_insertion_ratio`, `mass_insertion_ratio_two`, `mass_insertion_ratio_three`, `three_insertion_mass_and_jet` |
| the three Gamma integrals `9/8`, `9/(8q)`, `144q²(-q²+3q-1)/(q+1)^7` | `gamma_five_jet_integrals` |
| (3) cross-scale law; negative beyond `(3+√5)/2`, positive inside | `gamma_five_mul_gammaInner_atomJet_one`, `gammaInner_atomJet_one_neg_of_separated`, `gammaInner_atomJet_one_pos_iff` |
| (4) `U_2 v_x = v_{2x}`, `D_2(v_x+v_{2x}) = v_x - v_{4x}` | `dilate_jetProfile`, `dyadic_insertion_telescopes` |
| (5) values `27/16+128/243`, `45/32+23040/78125`, chain `< 4/5` | `gammaEnergy_dyadic_pair`, `gammaEnergy_dyadic_telescoped`, `dyadic_rational_chain`, `gammaEnergy_dyadic_contraction` |
| literal four-atom packets, signs `-1,+1,+1,-1`, ratio `→ 283/192` | `exists_literal_fourAtom_sequence`, `fourAtomPacket_eq_insertion` |
| literal dyadic mechanism: eight signs, distinct atoms, ratio `→` quotient `< 4/5`; arbitrarily high | `exists_dyadic_realization`, `exists_high_literal_dyadic_contraction`, `dyadicQuotient_lt` |
| persistence of (5) and (8) for `0 ≤ δ ≤ δ₀` | `exists_dyadic_contraction_delta`, `exists_halfScale_compensation_delta` |
| central packet `B_ε` with margins, norm `≍ ε` | `exists_central_scale`, `gammaNorm_centralPacket_approx` |
| fixed-relative-interval PNT supply | `eventually_card_primes_band`, `eventually_band_supply` |
| (6) macroscopic aligned packet, `< 4/5`, energies `≫ M²R^{-1-δ} ≫ R^{1-δ}/log²R`; literal signs; distinct atoms | `exists_macroscopic_aligned_packet` (`tuplePacket_bounds`, `eightAtom_injective`, `moebius_eightAtom`) |
| Mertens energy bound `‖F_N‖_δ ≪_δ N^{(1-δ)/2}E(N)` | `gammaNorm_mobiusCubicSource_le` |
| (7) complement antiparallel; literal complement; `E(R) log R → 0` | `macroscopic_complement_antiparallel`, `tendsto_mertensSaving_mul_log`, `insertTwo_tuplePacket_eq_literal` |
| (8) `⟨v_x,f_z⟩_0`, values `-20512/531441`, `1/16`, `< 71/1000`, `-237/10000`, `2/3` reduction | `gammaInner_jetProfile_atom_zero`, `dyadicJet_halfScale_inner`, `halfScale_atom_energy`, `dyadicJet_energy`, `halfScale_compensation` |
| (9) literal half-band compensator: `< 2/3 ‖D_2P‖² < 8/15 ‖P‖²` | `exists_halfScale_compensated_packet` (`halfScale_core`) |
