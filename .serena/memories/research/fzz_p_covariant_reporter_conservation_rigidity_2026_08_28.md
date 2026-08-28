# FZZ-P covariant reporter conservation rigidity (2026-08-28)

Formalized in `formal/GaloisForLFunctions/RHTower/FZZCigarParityCovariantReporterConservationRigidity.lean`; wired into `formal/GaloisForLFunctions/RHTower.lean`.

For stabilized flow multiplier `e=exp(Pt)`, shear `k=(Q/R)(e-1)`, define `q=k/e=(Q/R)(1-exp(-Pt))`. The moving Hermitian reporter `(q^2,q,0,1)` uniquely pulls back to unit diagonal coefficients `(0,0,0,1)`. Therefore
`H_(q^2,q,0,1)(Phi_t u)=H_D(u)`
for every real time and state.

Uniqueness is coefficient-level: the four pulled coefficient equations equal unit diagonal iff the reporter equals `(q^2,q,0,1)`.

On centered Mellin carriers, moving readings agree under functional reflection iff `rho.re=1/2` for every time. The full reflected reading difference is conserved exactly, so every off-wall carrier stays unmatched. Universal matching over open-strip parity-Mellin divisor modes at any beta,t is equivalent to the original unit-diagonal matching, hence equivalent to RH.

Cards:
- `docs/drafts/pipeline/3-formalized/fzz-p-covariant-reporter-conservation-rigidity.md`
- `docs/drafts/pipeline/5-failed/fzz-p-covariant-conservation-selection-no-go.md`

Verification: direct Lean, target-only build, scoped forbidden-token scan, diff check, and axiom audit passed. Axioms only `propext`, `Classical.choice`, `Quot.sound`. Frontier map untouched.
Novelty: corpus and exact-object literature audit found no collision; not absolute priority claim.