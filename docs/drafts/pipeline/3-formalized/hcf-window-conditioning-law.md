# HCF window conditioning law: heat windows are doubly-exponentially ill-conditioned

- **ID:** C601
- **Stage:** 3-formalized
- **Type:** THEOREM (CANNOT-507)
- **Source:** hcf-exact-layer-loop row 602; MUST-478 (`zeta_weil_margin_superexponential`), MUST-1289 (spectral dictionary)
- **Statement:** There are C > 0 and K₀ such that for all K ≥ K₀ and ε > 0, for all large n the pole hyperplane at heat time K/n contains a real P with Re H_{K/n}(P,P) < (C e^{24√K} e^{−π e^{4√K−1}} + ε)∫heatTest(K/n,P)². Half-width form: L ≥ L₀, K > L²/4, constant C e^{12L} e^{−π e^{2L−1/2}}.

## Goal
Constrain any HCF producer. Window positivity, if true, holds with a doubly-exponentially small normalized margin, so a certificate must be margin-free.

## Gates
- [x] 0 → 1  in-progress: well-posed, composed from MUST-478 and MUST-1289
- [x] 1 → 2  fully-proven: paper proof below
- [x] 2 → 3  formalized: `eventually_exists_poleHyperplane_rayleigh_lt_doubleExp`, `lake build` green, standard axioms
- [ ] 3 → 4  not pursued (no manuscripts)

## Paper proof
1. The radical test f_L = Φ_{≤L−1/4} ⋆ κ₂ is even, because Φ, the symmetric indicator and κ₂ = κ'' − κ/4 are even (κ even gives κ' odd and κ'' even). The convolution of even functions is even (substitute t ↦ −t).
2. ‖W(f_L, f_L)‖ ≤ M∫|f_L|², with M = C e^{12L} e^{−π e^{2L−1/2}} (the MUST-478 proof, with the test named).
3. For even f, W(f,f) = W(Re f) + W(Im f), and ∫|f|² = ∫(Re f)² + ∫(Im f)². A part with ∫ = 0 vanishes identically, so its energy is 0. Hence some part g has ∫g² > 0 and Re W(g) ≤ M∫g². g is real, even, C², vanishes outside [−L, L], and ∫g e^{−x/2} = 0 by splitting f̂(i/2) = 0 into real and imaginary parts.
4. Mollify g with even normalized bumps of radius 1/(k+1). The result u_k is C^∞, even, supported in [−L − 1/(k+1), L + 1/(k+1)], and pole-free since the transform is multiplied by the bump transform. W(u_k) → W(g) (dominated over zeros). ∫u_k² → ∫g², since the convolution converges pointwise for continuous g and |u_k| ≤ sup|g| on a fixed interval. Choose k with ratio < M + ε/2 and half-width A < 2√K.
5. MUST-1289 (Rayleigh form) gives Re H < (ratio + ε/2)∫g_P² eventually.
6. Window form: L = 2√K − 1/4.

## Phase 4 verdict
BRIDGE: it is the HCF image of MUST-478. It is significant only as a producer constraint. No literature analogue exists, because HCF windows are corpus-specific.

## Lean
Module `RHTower/XiGaussianHeatWindowConditioning` (wired after `XiGaussianHeatSpectralDictionary`), standard axioms.
- Main results: `eventually_exists_poleHyperplane_rayleigh_lt_weilMargin`, `eventually_exists_poleHyperplane_rayleigh_lt_doubleExp`.
- Supporting: `zeta_weil_margin_weilRadicalTest`, `weilRadicalTest_neg`, `exists_part_re_W_le`, `realMollify`, `tendsto_integral_sq_realMollify`, `exists_smooth_source_ratio_lt`.

## Log
- 2026-10-12 — proved and formalized (CANNOT-507).
