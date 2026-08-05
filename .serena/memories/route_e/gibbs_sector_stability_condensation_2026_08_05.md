# Sector-collapse layer: stability + condensation reformulation (2026-08-05)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-3 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsSectorStability.lean` (RHTower.GibbsGas),
wired, built, no sorry, axioms clean.

## Paper theorems (N1, N2)
- N1: p_x(z) = ∑_{n sf} z^{ω(n)}e^{−nx} is entire of ORDER 0 (primorial coefficient
  decay), genus-0 Hadamard: p_x(z) = e^{−x}∏(1 − z/z_j), ∑1/|z_j| < ∞.
- N2 (parity cross-ratio law): E_{ν_x}[η] = ∏_j (z_j+1)/(z_j−1); factor modulus < 1 iff
  Re z_j < 0; zero at distance d from −1 contributes ≈ log(2/d) cancellation. Hence
  **(G2)/RH ⟺ zero-condensation: ∑_j log|(z_j−1)/(z_j+1)| ≥ (1/2−ε)log(1/x)** — the
  infinite-volume meaning of "cluster collapse" (R3). NOT YET IN LEAN (needs the corpus
  canonical-product/Hadamard layer — memories: power-canonical-product-lean-layer,
  xi-corpus-analytic-assets — audit before building).

## Lean theorems (N3, k ≤ 3, ALL x > 0)
- `cubic_no_rhp_root`: a₃>0, a₂,a₁≥0, a₀>0, a₃a₀ < a₂a₁ ⟹ no root Re ≥ 0. Proof: root
  s+it; t≠0 ⟹ a₃t² = 3a₃s²+2a₂s+a₁; then a₂a₁−a₃a₀ = −(8a₃²s³+8a₃a₂s²+2a₃a₁s+2a₂²s).
- `triple_gas_hurwitz`: a₃a₀ < a₂a₁ for the gas at EVERY coupling (pq+p < pqr+1).
- `triple_gas_sector_stable` / `pair_gas_sector_stable`: the vortex never crosses the
  imaginary axis (stability holds although reality fails — T3).
- `triple_gas_root_grading`: every zero ζ has ‖1+ζ‖ < ‖1−ζ‖ (per-zero cancellation).

## Open (refined core)
- Sector-collapse conjecture all k (Hermite–Biehler along T0: P_{S∪p}(iω) = P_S(iω,x) +
  iω·P_S(iω,px); two-scale phase lag; Laplace kernel e^{−xE} totally positive in (x,E)).
  k=4 Routh minors pass by hand (pqr+pq+p < min(2pqr+1, pqrs+2p)).
- The zero-counting law: lower bounds on # gas zeros in shrinking disks at −1 = the
  (G2)-bearing quantity after N2+stability grading.

## Lean traps
- re/im of complex root equations: rw z = ↑s + ↑t·I, congrArg Complex.re/im, simp only
  [add_re, mul_re, mul_im, add_im, I_re, I_im, ofReal_re, ofReal_im, zero_re/im,
  pow_succ, pow_zero, one_mul], then close vs hand-stated real equation by
  `linear_combination h` (robust to simp arrangement).
- push_neg deprecated → `rw [not_lt]`. nlinarith wants explicit (q−2)(r−1) ≥ 0 hints.
- `Complex.normSq_eq_norm_sq` + normSq_apply for ‖1+ζ‖ vs ‖1−ζ‖ (difference = 4Reζ).
