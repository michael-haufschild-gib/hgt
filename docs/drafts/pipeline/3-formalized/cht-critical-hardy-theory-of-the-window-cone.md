# Critical Hardy theory of the window cone (CHT)

- **ID:** cht
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), programme
- **Source:** docs/reports/review-0511/obstacles-summary.md §2.7.1
- **Statement:** Structure of the nested cones `𝒜(c)`: effective uniqueness, margin law, bands, edge profile, datum.

## Goal
Exact finite-level theory of the window cone. A receiver: no sign for ζ is claimed. Lean folder
`formal/GaloisForLFunctions/CriticalHardyTheoryOfTheWindowCone/`, foundational README there.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof, with its Lean declarations

**Margin law.** Cauchy on `|t| = 7/10` of `(1 − t)^{−¼} Φ(x + ½ log(1 − t))` bounds all `F_j`
(`abs_xiShiftedGammaTest_le`). The truncated blind family has energy at most `K exp(3c − (π/6) e^{2(c−13/12)})` on the
whole cone (`exists_nullWeights_tsum_nullEnergy_le`), and `e^{11/6} ≥ 6` gives the Gaussian ceiling
(`exists_bestMargin_le_gaussian`).

**Effective uniqueness.** Near-nullity and Cauchy–Schwarz read `λ − Λ` against `Φ_L ⋆ Y` for any `Y`
(`exists_uniform_pinning`). The Gaussian test `Y_t` has reading `Σ_k (ratKer + expKer)(kn, t)` (`hasSum_atomReading`), and
size bounds uniform in `t ≥ 1`, so the reading is `O((1 + c) e^{−c/4})` on the ray (`exists_norm_readS_windowDefect_le`).
The second difference at step `i` kills `expKer` (`sinh_cube_mul_secondDiff`). Three lines on sectors (`norm_le_of_sector`)
reach `t ± i`, then the poles, where `T(iL)` is the discrete Laplacian of `N D(N)` (`poleT_I_mul`). Inverting gives
`exists_abs_le_of_readS_small`, and then `exists_abs_sub_vonMangoldt_le_exp`.

**Bands.** `ordConnected_bandSet`, `exists_band_width_ge`, `exists_abs_sub_le_of_mem_bandSet`,
`exists_odd_frustrated_on_cone`.

**Edge.** The causal kernel splits into a small-mass part, absorbed in `L¹` above a high level
(`exists_ae_le_of_absorption`), and a bounded part. So window solutions are bounded
(`exists_ae_norm_le_of_window_equation`), and the half-line readout gives `window_edge_law`.

**Datum.** `exists_datumCone_one_eq_empty`, `riemannHypothesis_iff_forall_datumCone_one_zero_nonempty`,
`forall_zero_mem_datumCone_zero_iff`, `exists_one_sub_le_of_datumCone`.

**Hamiltonian, evaluation frame only.** `integral_evalDensity_mem`, `riemannHypothesis_or_evalGram_tends_to_top`.

## Not done
- A5 and the numerical table of §1.15: computations, out of scope.
- De Branges' ordering theorem and the Hamiltonian itself (A41).
- Bridge from the logarithmic window equation to extremals of the completed `W_λ` for general `λ`.
- Pole square and cosh deficit in cone language; they are proved in SWC for `Λ`.
- Rates beyond `e^{−c/1104}`, numerical values of `C, K`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —
