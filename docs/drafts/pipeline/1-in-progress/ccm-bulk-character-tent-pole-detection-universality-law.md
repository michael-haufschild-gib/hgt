# CCM bulk-character tent-pole detection universality law

- **ID:** LAW451
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus theorem-posting closure
- **Statement:** A nonzero edge-free physical prime Fourier channel whose character rate lands on a critical-line zeta zero forces the matching moving-tent observable to have a genuine pole there.

## Goal

Connect finite physical-aperture character tomography to meromorphic divisor recovery through their
literal shared rectangular amplitude. Turn a nonzero measured prime channel into a pole certificate,
without RH or a two-width fallback.

## Gates

- [x] 0 → 1  in-progress: common `rectangularWindowAmplitude` carrier and parameter match found
- [x] 1 → 2  fully-proven: dependency-closed factor-to-pole proof below
- [x] 2 → 3  formalized: Lean theorem
  `ccmBulkCharacter_nonzero_forces_tentPoleUniversality`; exact-file check green
- [ ] 3 → 4  publication-ready: standalone paper pending

## Approach

For an edge-free packet, the exact bulk theorem factors the physical character amplitude as

`exp(k·rate) · rectangularWindowAmplitude (k-m) rate · twistedPrimeSum`.

If the measured amplitude is nonzero, its rectangular factor is nonzero. Put
`ρ = 1/2 + rate`. A positive aperture and nonzero integer character make `rate` nonzero and purely
imaginary, hence `Re ρ = 1/2`, `ρ ≠ 1`, and `ρ ≠ 1/2`. If `ζ(ρ)=0`, the tent genuine-pole theorem at
width `k-m` applies because `ρ-1/2=rate`; `m≤k` supplies nonnegative width. Thus
`PcalObservable (k-m)` has no finite punctured-neighborhood limit at `ρ+1/2`.

## No-go closure

Not applicable: positive survivor.

## Log

- 2026-07-23 — generated from
  `CCMPhysicalPrimeApertureCharacterTomography` and `TentDivisorRecovery`, with the continuation
  mechanism supplied by `PrimePolarContinuation`
- 2026-07-23 — corpus research found the bulk factorization and pole theorem separately, but no
  theorem converting a nonzero physical character channel into a pole certificate
- 2026-07-23 — exact Lean check passed; wired into `GaloisForLFunctions.RHTower`
- 2026-07-23 — post-proof arXiv mechanism search found Fourier expansions and unrelated windowed
  zeta calculations, but no physical prime-character-to-moving-tent-pole theorem
