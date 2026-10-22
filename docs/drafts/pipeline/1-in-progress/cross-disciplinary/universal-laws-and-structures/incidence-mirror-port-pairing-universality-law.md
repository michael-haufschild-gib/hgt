# Incidence-mirror port-pairing universality law

- **ID:** incidence-mirror-port-pairing-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of `IncidenceCarrier`, `IncidenceMirrorOrientation`, and
  `IncidenceRamification`
- **Statement:** A positive-real reciprocal FE mirror makes the critical-line seam incidence obey
  `r(-τ)=λ/r(τ)`; its critical heights and the corresponding multiple-zero pencil ports therefore
  occur in exact reflected pairs.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit complete; final audit pending

## Corpus inputs

- `incidence_mirror`
- `incidence_im_eq_zero_on_line`
- `seamIncidence_analyticAt`
- `seam_critical_iff_port`
- the critical-line identity `1-linePt(τ)=linePt(-τ)`

## Proof

`[PROVED HERE]` Write `r(τ)` for the real seam incidence.  Applying the corpus FE mirror theorem
at `linePt τ`, using `1-linePt τ=linePt(-τ)` and the real-valued seam theorem, gives

`r(-τ)=λ/r(τ)`.

Both anchor and target are nonzero on the seam, so `r(τ)≠0`.  Analyticity of the two carriers and
anchor nonvanishing make `r` differentiable.  Differentiating the reciprocal reflection gives

`r'(-τ)=λ r'(τ)/r(τ)^2`.

Because `λ>0` and `r(τ)≠0`, `r'(-τ)=0` exactly when `r'(τ)=0`.  Applying the corpus port criterion
at `τ` and `-τ` converts this critical-height equivalence into equality of the reflected
order-at-least-two port loci.  No computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.IncidenceMirrorPortPairingUniversalityLaw`
- Main theorem:
  `RHTower.incidenceMirrorPortPairingUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/IncidenceMirrorPortPairingUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Searches across meromorphic-function pencils, reciprocal functional equations, ramification,
  real critical loci, and multiple-zero pairing found adjacent work on real critical values and
  pencils, but no theorem matching the exact FE seam law together with reflected critical-height
  and pencil-port equivalence.
- Eremenko--Gabrielov, *Rational functions with real critical points and the B. and M. Shapiro
  conjecture*
  ([paper](https://www.math.purdue.edu/~eremenko/dvi/shapiro44.pdf)), concerns circle reality of
  rational maps whose critical points are real, not reciprocal FE reflection of a pencil ratio.
- Literature on zeros/critical-point pairing, such as
  [arXiv:1305.6105](https://arxiv.org/abs/1305.6105), is probabilistic and unrelated to the exact
  reflected ramification law here.

No exact literature match was found.  Door 2 remains open rather than claimed closed.

## Log

- 2026-07-23 — Terminal sibling audit exposed the missing composition from reciprocal incidence
  mirror to ramification/port pairing.
- 2026-07-23 — Main theorem exact-checked warning-free, wired into the RHTower umbrella, and
  post-proof collision search found no matching reflected-port law.
