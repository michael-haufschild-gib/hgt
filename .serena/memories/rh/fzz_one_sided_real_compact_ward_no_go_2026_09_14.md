# FZZ one-sided radial real-compact Ward no-go (2026-09-14)

- Module: `formal/GaloisForLFunctions/RHTower/FZZCigarOneSidedRadialRealCompactWardNoGo.lean`.
- Exact identity for real q ≠ 0:
  `2 * Re (deriv digamma (1 + q*I)) = q⁻² - π² / sinh(πq)²`.
- Unconditional positivity: `0 < Re (deriv digamma (1 + q*I))` for every real q.
- Hence Halder–Jafferis physical one-sided radial mixed response has strictly negative imaginary part for every momentum, including p=0.
- Any real compact/Hessian response cannot cancel it; actual one-sided radial full-annular Ward defect is nonzero. Route `HJ one-sided radial + real compact Hessian → Ward zero → p=0 → passivity → RH` is killed.
- Strong positive survivor: any cancelling compact response must have strictly positive imaginary part. Surviving source completion requires genuine complex phase/cross-charge data.
- Closed Lean; axioms only `propext`, `Classical.choice`, `Quot.sound`. Direct `lake env lean -j1 ...` passed; targeted leaf `lake build GaloisForLFunctions.RHTower.FZZCigarOneSidedRadialRealCompactWardNoGo` passed; lint passed.
- Cards: `docs/drafts/pipeline/3-formalized/fzz-one-sided-radial-real-compact-ward-no-go.md`, `docs/drafts/pipeline/5-failed/fzz-one-sided-radial-real-compact-ward.md`.
