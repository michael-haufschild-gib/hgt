# Two-prime deletion and the complete third-band envelope

- **ID:** thim-two-prime-deletion-full-third-band
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Scope:** Close the remaining `2 ∣ k` and `3 ∣ k` third-band case; propagate
  the resulting full `4N` envelope through radical/power checkpoints and short windows.

## Plan and gates

1. [x] Reread objective/README and search current corpus; locate exact missing case.
2. [x] Dependency-closed paper proof of two-prime convex identity and full third band.
3. [x] Verify APIs in scratch; formalize actual source and audit all declarations.
4. [x] Wire leaf, index/lint, update ledger/memory, audit artifacts, clean scratch.

`update_plan` unavailable; this card tracks work. README remains read-only.

## Corpus and classical baseline

Hybrid searches `active sawtooth energy defect stability calibrated endpoint reconstruction`
and `two prime deletion third band damped convex combination four horizon`, restricted
to THIM, returned complete inventory coverage (74228 files, no pending inventory files;
generations 1453857/1453865), partial=false. Compiler metadata is mixed/source-only;
candidate applicability must be checked in Lean. All candidate/source-argument lists
inspected. Existing `pmPowerDamped_prime_deleted_response` handles one prime; existing
third-band envelope needs a missing prime among two and three. No two-prime convex
identity found by indexed search or exhaustive field-source text search.

Classical baseline: multiplicativity of `μ(n)n^(-ε)`, the divisor-product identity
`τ_ε(n)=∏_{p∣n}(1-p^(-ε))`, Dirichlet complementary-divisor splitting, and discrete
polarization. Relative to [TH10](https://arxiv.org/abs/1009.5281) and
[CMS16](https://arxiv.org/abs/1612.03136), the new package is a **New formulation**:
an exact two-prime deletion operator becomes a convex combination and closes a
project-specific finite-band gap. No external novelty claim or exhaustive literature
audit. Baseline algebraic constituents are Known/Corollary.

## Paper proof [PROVED HERE]

Write `c(u)=μ(u)u^(-ε)`, `τ(u)=Σ_{d∣u}c(d)`, and
`F_p(u)=1` when `p∣u`, otherwise `1-p^(-ε)`.
For any prime p, `τ(pu)=F_p(u)τ(u)` and `c(pu)=(F_p(u)-1)c(u)`.
For distinct primes p,q, `p∣qu ↔ p∣u`, so with `A=F_p(u)F_q(u)`:

`τ(pqu)-c(pqu)-c(pu)-c(qu) = A τ(u)+(1-A)c(u)`.

This follows by expanding the four coefficient terms, whose sum including `c(u)`
is `A c(u)`. It also holds when u contains p or q, including repeated prime powers.
For ε≥0, each F lies in [0,1], hence A∈[0,1]; both τ(u) and c(u) lie in [-1,1]
for u≥1. The response therefore lies in [-1,1]. For u≥2 the existing stronger
mass bound `τ(u)+|c(u)|≤1` gives absolute response at most `max A (1-A)`.

In `3N<k≤4N`, the complementary-divisor formula deletes only quotients 1,2,3.
If either small prime is absent, the existing single-prime theorem applies.
Otherwise write k=2·3·u (u≥1); k/2=3u and k/3=2u, so the identity above closes
the missing case. Combined with the established range through 3N:
`|s_N(c,k)|≤1` for every `2≤k≤4N`, ε≥0.

Squarefree support transports this envelope to every positive power of such k,
and to arbitrary positive endpoints whose horizon-radical representative is at
most 4N. Polarization then gives `2D≤-E≤0`, including rough-start short windows.
At ε=0 this specializes to literal Möbius weights. No general global sign claim
follows when the canonical representative lies above 4N.

## Boundaries

No numerical experiments, full builds, added axioms, heartbeat changes, README
edits, commits, or pushes. Parameter assumptions specify the unconditional theorem
domain; no unproved mathematical conjecture is assumed.

## Formal verification and integration

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TwoPrimeDeletionAndFullThirdBandEnvelope.lean`.
- SHA256: `74b5080b021d4dbee345046d41aa37b137b21c7aa5219678cc7c7b3675782399`.
- 19 public theorems, one public definition, one private helper. All 21 axiom
  closures are exactly `{propext, Classical.choice, Quot.sound}`.
- Final source passed `lake --old env lean -o <leaf.olean> <leaf.lean>` with exit 0,
  no warnings; scratch axiom audit exited 0. No full/umbrella build. Required
  dependency source hashes and compiled-artifact freshness revalidated against
  prior source audits.
- Artifact audit passed: source hash, all declarations/closures, 20 baseline
  docstrings and unique API entries, compiled-artifact freshness, unique umbrella
  import, MainTheorems reachability, whitespace and forbidden-declaration checks.
- Evidence: `logs/thim-two-prime-{lean,axioms,index,lint}.txt` and
  `logs/thim-two-prime-audit.json`. Global lint exits 1 for exactly four unrelated
  structural findings: three unwired ArithmeticPositivityTheory leaves
  (`FactorialCollarIrrationalityAndSpacing`, `RankOnePoleReadoutAndZeroNullspace`,
  `SourceRelativeSchurMarginAndPerturbationCalculus`) and the existing field-root
  registration complaint for `TransHorizonIncidenceMechanics.lean`. No new-leaf,
  forbidden-declaration, or stale-generated-file error.
- All owned processes reached terminal status; six owned `/tmp` scratch files
  removed. Ledger and Serena memory preserve the theorem and exact limits.
- Next unproved candidate: isolate quotient 4 in the fourth band and determine
  whether the dyadic coefficient pair reduces to a single-prime contraction.
  No `5N` claim. Seventh contribution complete; continuing THIM goal stays active.
