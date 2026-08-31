# Positive channel scalarization no-go for shared four-route Ward endpoint

- **ID:** SW-PSD-CHANNEL-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** internal corpus: `SourceGammaChannelResolvedNaturalityNoGo`
- **Statement:** Every nonzero positive-semidefinite Hermitian scalarization of the two fitted prime--Gamma channels has zero total genuine-boundary energy exactly at horizontal grade zero; a zero scalarizer is boundary-blind.

## Goal

Close fixed positive finite-channel postprocessing in
`source/Gamma naturality -> shared HB/FZZ-P/PW-B/RBH Ward endpoint -> RH`.

## Gates

- [x] 0 → 1  in-progress: source-pure statement, exact source-boundary vectors, route passport
- [x] 1 → 2  fully-proven: complete proof below, `[PROVED HERE]`
- [x] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Proof

Let `d(t)=2^(-t)-3^(-t)`. Corpus gives genuine prime-two and prime-three boundary outputs
`(0,d(t))` and `(-d(t),0)`. For a Hermitian PSD matrix `A`, their total quadratic energy is

`(Re A₀₀ + Re A₁₁) |d(t)|²`.

Both diagonal terms are nonnegative. If `A != 0`, at least one is positive: if both vanished,
PSD kernel rigidity applied to both coordinate vectors would kill both columns, hence `A=0`.
Thus total energy vanishes iff `d(t)=0`. Equality of the positive real powers `2^(-t)` and
`3^(-t)` is the existing shared-ghost rigidity condition, hence iff `t=0`. At `t=0` both source
boundaries vanish. If `A=0`, energy vanishes at every grade. `[PROVED HERE]`

On an actual Xi divisor take `t=2 Re(rho)-1`. Universal vanishing for any fixed nonzero PSD `A`
is therefore equivalent to RH and, by the existing endpoint equivalence, to simultaneous HB,
FZZ-P, PW-B, and RBH Ward balance.

## Novelty audit

Corpus search found coordinate-projected and full-vector naturality, but no arbitrary Hermitian
PSD scalarization classification. August 2026 primary-literature search found Witt-vector and
operator-positivity background, not this prime--archimedean source-boundary theorem.

## No-go closure

- **Exact killing mechanism:** every nonblind PSD scalarizer preserves the same squared cross-prime leak.
- **Strongest positive survivor:** irreducible source dynamics must force cross-prime leak itself to vanish; no fixed positive channel metric can manufacture that law.
- **New insight:** off-diagonal channel coupling is irrelevant because literal source boundaries occupy opposite coordinate axes.
- **Lean module:** `GaloisForLFunctions.RHTower.SourceGammaChannelPositiveHermitianScalarizationNoGo`
- **Lean capstone:** `RHTower.sharedWardPositiveHermitianChannelScalarizationRouteKilled`
- **Audit:** direct `lake env lean`, target-only `lake build`, standard axioms only
- **Status:** paper proof dependency-closed and Lean-formalized.

## Log

- 2026-08-31 — paper proof closed after corpus and literature hostile audit
- 2026-08-31 — Lean capstone closed and wired
