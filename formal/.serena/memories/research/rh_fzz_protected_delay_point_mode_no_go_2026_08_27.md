# FZZ protected continuum-delay scalar point-mode no-go (2026-08-27)

Formalized `formal/GaloisForLFunctions/RHTower/FZZCigarProtectedDelayPointModeNoGo.lean` and wired umbrella.

Literal corpus source is positive-half-line protected delay `v(x)=1_(0,∞)(x)/(exp x-1)`, derived from exact FZZ charge tower in `HTGeometry.FZZCigarScatteringSpectralAsymmetry`.

For every `E : ℝ`, canonical scalar state `-v/(x-E)` satisfies
`|f_E(x)|² ≥ [4(|E|+1)²]⁻¹ x⁻²`
on `0<x<1`, `x≠E`. Positive inverse-square floor implies state is never `MemLp 2 volume`, hence theorem `not_FZZPunctureProtectedContinuumDelayPointMode E`.

Direct Lean passed; targeted build passed 11600/11600; axioms only `propext`, `Classical.choice`, `Quot.sound`. Stage-3 card `docs/drafts/pipeline/3-formalized/fzz-protected-delay-point-mode-no-go.md`.

No-go scope: kills unrenormalized protected delay only in scalar weighted point-spectrum model. Positive survivor is quantitative all-energy floor. Remaining FZZ core: coefficient-faithful backreacted winding/oscillator source that cancels Bose endpoint and target pole, or singular-domain/generalized carrier, plus global zeta-selective landing without divisor insertion.