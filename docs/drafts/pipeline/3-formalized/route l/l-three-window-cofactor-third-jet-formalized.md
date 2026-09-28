# Three-window cofactor third-jet extraction — Lean certificate

- **ID:** L-THREE-WINDOW-COFACTOR-THIRD-JET
- **Stage:** 3-formalized
- **Paper proof:** [l-three-window-cofactor-third-jet.md](l-three-window-cofactor-third-jet.md)
- **Lean modules:** `GaloisForLFunctions.RHTower.MobiusMomentSimplexSelector`,
  `…MobiusMomentMatchedPacket`, `…MobiusMomentMatchedFamily`, `…MobiusMomentMatchedAssembly`,
  `…MobiusThreeWindowExtraction`, `…MobiusCofactorLayerExtraction`, `…MobiusCofactorLayerCofinal`
  (inputs: `MobiusOrderedMomentRounding`, `MobiusCubicGammaNorm`, `MobiusCubicGammaAtomJets`,
  `MobiusTwoJetCofactorPacket`, `MobiusTwoJetPrimeSemiprimePacket`, `MobiusTwoJetLinearDensity`,
  `Sieve.InghamUniformDetectorMellinEveryBaseThetaMass`, `Sieve.CoprimeSquarefreeHarmonic`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake env lean` clean on each module; targeted `lake --old build` of each;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for every theorem below. No computation.

Namespaces `RHTower.MomentSelector` (selector) and `RHTower.CubicGamma` (packets);
`α = supplyExp = 71/100`, `f_x = atom x`, `‖·‖_δ = gammaNorm δ`, `S_N = mobiusCubicSource N`,
`m_q = cofactorSupply R q = ⌊(R/q)^α/(32768 log 5R)⌋`.

| Card item | Lean theorem |
|-|-|
| Vandermonde barycentric radius: perturbed vertices keep the barycenter inside with coefficients within `κ` of `1/(d+1)` (continuity of the inverse moment matrix) | `exists_barycentric_radius`, `momentMatrix_nominal`, `continuous_momentMatrix` |
| nodes `1/4,1/2,3/4`, barycenter `(1/2,7/24)`, affine determinant `1/32` | `threeNodes`, `nominalBarycenter_threeNodes`, `det_vandermonde_threeNodes` |
| ordered rounding with varying weights, exact integer count, moment error `≤ 1` per power | `exists_pooled_selection` (from `MobiusOrderedMomentRounding`) |
| (2) finite three-window selector: `ε₀ < 1/8`, exactly `m` literal atoms per side, first and second moment discrepancies `≤ 10` | `exists_three_window_selector` |
| matched selection for `d` moments, discrepancy `≤ 2` per moment; `d+1` separated window nodes | `exists_matched_selection`, `layerNodes`, `layerNodes_bounds`, `exists_window_width`, `exists_window_weights` |
| theta-mass supply of `m_q` primes per window and orientation; `μ(2qr)=μ(q)`, `μ(qp)=-μ(q)`; unique largest prime separates cofactors | `exists_family_block`, `moebius_orientedAtom`, `moebius_two_mul_mul_prime_of_not_dvd`, `moebius_mul_prime_of_not_dvd`, `cofactor_eq_of_largest_prime`, `cofactor_eq_of_shape` |
| order-`d` Taylor bound for a family of cofactors sharing one block length | `gammaNorm_matched_block_le`, `exists_family_packet` |
| (4) `‖∂_x^r f_x‖_δ ≤ K_r R^{-r-1/2-δ/2}` for `x ≥ R` | `gammaNorm_atomJet_le_of_le` |
| (5) per-cofactor bound `C[R^{-(1+δ)/2} + R^{α-3/2-δ/2}q^{1-α} + R^{3α-5/2-δ/2}q^{2-3α}/log R]` | `exists_threeWindow_cofactor_bound` |
| (1) `A_R = {2qr}`, `B_R = {qp}` in `(2R,4R)`, `q ≤ ⌊R^{2/5}⌋` odd squarefree, `r > R/q`, `p > 2R/q`, literal signs, `|A_R| = |B_R| ≥ cR`, bound with `R^{-1/10}`, `R^{-137/500}`, `R^{-11/500}/log R` | `exists_threeWindow_extraction` (parts `threeWindow_part_one/two/three`, counts `threeWindow_count`) |
| uniqueness of the form `qr` | `threeWindow_form_unique` |
| dyadic summability and reduction along `N_J = 2^{J+2}`: bounded ⟺ bounded for full and residual source | `threeWindow_cofinal_reduction` |
| admissible cofactors; odd squarefree `q ≤ R^β`, `β < 1/2`, are admissible | `AdmissibleCofactor`, `admissibleCofactor_of_le_rpow` |
| (7) layered extraction, `d ≥ 1`, `0 < η < 1`: balanced literal signs, counts `≥ cR`, bound `C(R^{-1/2-δ/2} log R + R^{1/2-(d+1)(1-α)(1-η)-δ/2})` | `exists_layer_extraction` |
| dyadic summability of (7) under (6) and the source reduction | `layer_cofinal_reduction` |
| every `η < 1` admits an order `d`; `d = 3` ⟺ `η < 33/58` | `exists_layer_order`, `layer_cofinal_reduction_of_lt_one`, `layer_condition_three_iff` |
