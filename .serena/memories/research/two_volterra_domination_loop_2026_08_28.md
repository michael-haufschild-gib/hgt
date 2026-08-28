# Two-Volterra domination producer loop — state after cycles 1–5 (2026-08-28)

Cards: `1-in-progress/source-contraction-two-volterra-domination.md` (hub, full cycle log),
`1-in-progress/theta-krein-pick-congruence.md` (theorem card). Numerics archived:
`2-fully-proven/computations/2026-08-28-two-volterra-domination-loop/`.

## Target
Produce, from the literal theta source and uniformly in rank, the contraction `K₋∘K₊^{−1}` for
`riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`.

## Lean landed (unconditional; axioms standard)
`RHTower/ThetaTailKreinXiCentTiltCollapse.lean`: channel collapse
`thetaTailKrein±Transform c w s = e^{−ws}·(deriv xiCent w ± c·xiCent w)`; all-plane division-free
tilt algebra (`2c(w+y)·xiCentBezoutian = tilt₊tilt₊ − tilt₋tilt₋`, antidiagonal included);
lossless critical boundary `tilt₋ = −conj(tilt₊)` on `Re w = 0`. Also (C₅ thread)
`RHTower/ThetaCuspFifthRootGaussianDeviationMargin.lean`.

## Killed, with witnesses (cards hold details)
C1 shape-classes; C2′ FE-symmetrized single atom (off-axis zero pair; atom zero at w=1/2 = ζ-pole
shadow; `F_Φ = ζ(w+1/2)F_g` exact); C4/E3b all source truncations (causal AND even, N ≤ 10);
Mourre/flow (collapses to Levinson–Montgomery); **C6 semigroup transport (cycle 5): TERMINAL** —
slice-contractive transport ⟺ ∂_σ|ξc|² ≥ 0 ⟺ Sondow–Dumitrescu/Jensen criterion, corpus-owned in
Lean (`strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound`); transport cannot manufacture
strip-pole-freeness.

## Structural facts extracted (receiver web, all exact)
- `λ_c = tilt₋/tilt₊`: Bezoutian = diagonal congruence of λ_c's half-plane Pick matrix; RH ⟺ λ_c
  Schur on Re>0 ⟺ Lagarias positivity ⟺ SD monotonicity ⟺ Jensen disc criterion. Corpus owned the
  Carathéodory form (`riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel`) and SD already.
- Two-wall unconditional control: |λ_c| ≤ 1 on Re ≥ 1/2 (Hadamard + zero-free line); |λ_c| ≡ 1 on
  Re = 0 (Lean). RH ⟺ no strip poles ⟺ `(e^{cw}ξc)′` strip-zero-free ∀c (Speiser family).
- **Wall-normal contraction jets = Laguerre hierarchy** (verified numerically to ε⁴):
  `Re(ξc′ξ̄c)(ε+iτ) = εL₁ + ε³L₂/6 + O(ε⁵)`, `L₁ = Ξ′²−ΞΞ″`, `L₂ = ΞΞ⁗−4Ξ′Ξ‴+3Ξ″²`; equivalently
  σ²-, σ⁴-coefficients of `|ξc(σ+iτ)|² = |Ξ(τ−iσ)|²` are L₁, L₂/12. Lean bridge target: weld tilt
  module to `XiLaguerrePolya`/`LaguerreInequality` via these finite-jet identities.
- Numerics (dps 60): L₁, L₂ violation-free on τ∈[0.2,120] (normalized minima 0.044 / 0.082);
  **no Lehmer dip** in pointwise-normalized L₁ at τ≈7005.1 — the close-pair failure mode is
  invisible to pointwise wall jets at every order: wall-jet producers are structurally blind to
  the actual danger. dps-30 4th-derivative stencils give SPURIOUS L₂ violations — use dps ≥ 60.

## Do-not-revisit
Soft kernel classes; source truncations (both parities); single-place completions; atom induction;
Mourre-as-such; transport/monotonicity/jet reformulations (Jensen web — all receivers);
unconditional-Laguerre-as-producer (strictly weaker than RH).

## Open carriers for the next cycle
1. Singular-completion sewing build arc: promote the global anti-unitary wall relation into the
   superselection frame (`primePoisson_reflection_nonzeroClosedSourceLinearSewing_iff`,
   `everyXiDivisorSyndromeIsInternalOnly_iff_riemannHypothesis` — downstream Lean-complete);
   prerequisite: the Euler-safe Poisson boundary programme's two mathlib gaps
   (`mem: euler-safe-poisson-boundary-programme`).
2. Partial-exclusion budget lane (zero-density/HCF 75% amplification) — the classical ladder the
   corpus is already industrializing.
