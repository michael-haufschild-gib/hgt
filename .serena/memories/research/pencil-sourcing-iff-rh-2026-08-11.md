# Attempt 7: sourcing ⟺ RH — the Gauss/Hodge/seam loop is closed (2026-08-11)

Module `RHTower/GaussHodgePencilSourcing.lean` (wired, built, axiom-clean).

The last unproven step ("source Σ_ρ v·char_p(ρ)·e^{inIm ρ} from primes") is now a proved
equivalence, not an open mechanism hunt:
- FE companion `xiZeroCopyFEMode q = exp(ρ − 1/2)` — holomorphic counterpart of the vertical
  mode.
- Sourcing identity: char_p(s)·(e^{s−1/2})ⁿ = char_{p·eⁿ}(s): the companion pencil is the
  one-variable zero current at geometric scales p·eⁿ — exactly explicit-formula (prime-side)
  data.
- Polar law: feMode = e^{rate/2}·verticalMode — the sourcing defect IS the radial mass factor.
- **riemannHypothesis_iff_feMode_eq_verticalMode / _unimodular**: sourcing by the FE companion
  is EXACTLY RH, pointwise per copy.
- Under RH: verticalPencil_eq_flowedScaleCurrent_of_riemannHypothesis — every vertical-pencil
  value is prime-side data.

Programme status: one closed equivalence loop, all links unconditional Lean theorems
(attempts 1–7 on card hodge-sign-wall-constructed-pairing): Hodge sign; H-mass = Burnol seam
energy (two-sided, explicit constants); prime side = moment-curve convexity defect; ℓ¹
extraction + truncation exchange; positivity; coherence budget; conjugate-pair classification;
info-gap impossibility; sourcing ⟺ RH. Non-circular entry point (the true RH wall, now
maximally compressed): an independent evaluation of the vertical pencil, provably requiring
bilinear/conjugate-pair input — Montgomery-type autocorrelation (MRBilinear lane) or a
definitizable Krein intertwiner/spectral realization (corpus versions hypothesis-carried).
