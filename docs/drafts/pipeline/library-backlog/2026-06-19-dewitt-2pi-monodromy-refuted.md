# Library ticket — moonshot REFUTED → 5-failed: 2pi-monodromy-frobenius

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19

## What changed
`moonshot-2pi-monodromy-frobenius.md` moved `0-backlog → 5-failed` (REFUTED; worked by the scientific method
incl. a numerical experiment, archived `computations/2026-06-19-2pi-monodromy-frobenius-test.{py,txt}`).

## For 00-index / 00-status
- Remove from the moonshot/backlog listing; record under 5-failed. This was the set's "test-first / most
  grounded" archimedean-Frobenius moonshot.
- **Result line:** *"The missing archimedean F₁ is NOT the 2πi log-monodromy. (P1) The deck transformation
  `log x↦log x+2πi` is `x↦x·e^{2πi}=x` = the identity on the base field ℂ(x) — it is `π₁`, degree-1, not a
  field endomorphism / σ-Frobenius. (P3, experiment E1) `a_∞=−ζ'(0)=½log2π` is REAL (im=0); its 2π is the
  Stirling/ζ-regularization constant (theta/Gaussian FE), NOT the imaginary monodromy period 2πi. (P4, E2)
  `N(T)=θ(T)/π+1+S(T)` is the archimedean Γ-phase (Riemann–Siegel θ) winding — a degree-1 argument-principle
  zero-count, no Frobenius content (29.0024 vs 29 at T=100). (P2) degree mismatch ω∈H² vs winding∈H¹; (P5)
  ω=0 is realization, decoupled from the zero-count (#275)."*
- **Joint structural takeaway (with the skyrmion refutation, M3):** every archimedean winding in play —
  `κ₋=(1/2πi)∮Z'/Z` (RH axis) and `N(T)=(1/2πi)∮ξ'/ξ` — is a **degree-1** argument-principle winding of the
  archimedean Γ-phase. The archimedean "knot" / `ω∈H²` is **not** a higher or monodromy charge; the windings
  are degree-1 real-analytic Γ-phase objects. (Two moonshots, M2-adjacent and M3, jointly close the
  "topological-charge / monodromy reading of the archimedean knot" lane.)
- **Cross-refs:** `5-failed/moonshot-2pi-monodromy-frobenius.md`, `5-failed/moonshot-prime-skyrmion-no-clock.md`;
  `compute-omega-h2-gl.md §S/§V` (the real a_∞ source), `#275` decoupling, `moonshot-rh-spectral-flow-index`.

## No overclaim
Self-contained standard mathematics + a confirming experiment (mpmath); no new theorem banked. Deliverable =
the no-go ("F₁ ≠ 2πi-monodromy; the archimedean windings are all degree-1") + the corrected provenance of the
shared 2π (archimedean Γ Stirling/theta constant).
