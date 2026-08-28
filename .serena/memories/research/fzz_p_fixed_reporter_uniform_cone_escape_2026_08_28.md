# FZZ-P fixed-reporter uniform cone escape (2026-08-28)

Formalized in `formal/GaloisForLFunctions/RHTower/FZZCigarParityFixedReporterUniformConeEscape.lean`; wired into `formal/GaloisForLFunctions/RHTower.lean`.

For the HC6 stabilized flow with `e=exp(Pt)`, `k=(Q/R)(e-1)`, pullback sends arbitrary Hermitian coefficients
`(a,b,c,d)` to
`(e^2 a-2ekb+k^2d, eb-kd, ec, d)`.

Literal Fermi monotonicity proves `alpha=Q/R>1`. Set
`E_beta=2 alpha/(alpha-1)`,
`U_beta=log(E_beta)/P>0`.
Then `exp(P U_beta)=E_beta` and
`E_beta+1 < alpha(E_beta-1)`.

If a reporter is initially in HC3's detector cone, `|b|<=|d|`. Cone membership at multiplier `e` would give
`|eb-d alpha(e-1)|<=|d|`, hence triangle inequality forces
`alpha(e-1)<=e+1`. At `E_beta` this contradicts the strict source identity. Thus one source-defined positive time ejects every initially separating fixed reporter simultaneously. No fixed reporter survives all nonnegative time. Arbitrary first-coordinate counterterms cannot repair it because HC3 cone membership is independent of `a`.

Cards:
- `docs/drafts/pipeline/3-formalized/fzz-p-fixed-reporter-uniform-cone-escape.md`
- `docs/drafts/pipeline/5-failed/fzz-p-fixed-hermitian-all-time-detector-no-go.md`

Verification: direct Lean, target-only build, scoped forbidden-token scan, diff check, and axiom audit passed. Axioms only `propext`, `Classical.choice`, `Quot.sound`. Frontier map untouched.
Novelty status: corpus and exact-object literature audits found no collision; not absolute priority claim.