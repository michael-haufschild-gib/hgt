# Mass-shifted spectral face: critical-error Hardy boundary (2026-08-08)

Unconditional route reduction formalized in `formal/GaloisForLFunctions/RHTower/XiMassCriticalErrorFlux.lean`, wired in `RHTower.lean`.

Core finite identity:
`Prime(H) = Polar(H) - Ecrit(H) F(H) + ∫_(0,H] Ecrit(h) F'(h) dh`
for actual mass Fourier profile, without endpoint-zero assumption.

Formal advances:
- actual derivative under integral: `hasDerivAt_xiMassRealFourierProfile`
- infinite polar term equals `2*pi*g(-i/2)`
- exact norm `2*pi*exp(-sigma*xiMassArchPoleFrequency a)`, independent of u
- corpus `primeMassHalf_le` yields `|Ecrit(H)| <= 2(H+1)e^(H/2)`
- terminal `Ecrit(H)F(H)->0` for every a>1/2 using interior depth d>1/2
- derivative contour shift gives `F'(H)=O_u(e^{-dH})`
- `Ecrit(h)F'(h)` is absolutely integrable on h>0 for each fixed u
- exact infinite source law:
  `Prime(H) -> 2*pi*g(-i/2) + ∫_(0,∞) Ecrit(h)F'(h)dh`

Scientific conclusion: C39 cumulative square-root main mass and terminal Abel flux are artifacts before polar completion. Exact surviving open object is canonical source-defined centered completed-error current `∫ Ecrit F'`; only its uniform-in-u bound remains. C40 Kaiser synthesis is no longer sole avenue and should target this current. PNT magnitude alone remains insufficient.

Docs:
- ignored report `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 updated
- card `docs/drafts/pipeline/3-formalized/mass-xi-critical-error-hardy-boundary.md`
- active C40 card updated

Verification:
- direct Lean compile clean
- targeted lake build green
- #print axioms: only propext, Classical.choice, Quot.sound
- global lint blocked only by unrelated concurrent unreachable modules; new module wired and no forbidden declarations.
