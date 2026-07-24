# Gamma factorial projective-jet closure constants universality law

- **ID:** gamma-factorial-projective-jet-closure-constants-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of the first-, second-, homogeneous projective-second-,
  and projective-third Gamma factorial harmonic-residue limits
- **Statement:** Two nonlinear raw jet-defect ratios eliminate both harmonic microscope scale
  and observation point, converging universally to `-1/9` and `-1/6`.

## Goal

Extract scale- and point-free constants from the independently proved Gamma factorial
first/second/third projective residue channels.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed warning-free
- [x] 3 → 4 novelty audit: no exact statement found in searched literature

## Corpus inputs

- `tendsto_gammaFactorialFirstJetDefect_div_harmonicScale`
- `tendsto_gammaFactorialSecondJetDefect_div_harmonicScale`
- `tendsto_gammaFactorialSecondJetProjectiveDefect_div_harmonicScale`
- `tendsto_gammaFactorialThirdJetProjectiveDefect_div_harmonicScale_sq`
- `gammaHarmonicMicroscopeScale_ne_zero`

## Proof

**[PROVED HERE]** Fix `x ≠ 0` and write `H_n` for the Gamma harmonic microscope scale. The
existing residue laws give

`F_n/H_n → -2/x`,

`S_n/H_n → 6/x²`,

`P_n/H_n → 2/x³`,

`T_n/H_n² → -6/x⁴`,

for first-jet, second-jet, homogeneous projective-second, and projective-third defects.
The second limit is nonzero. Hence continuous multiplication and division yield

`[(P_n/H_n)(F_n/H_n)] / (S_n/H_n)²
  → [(2/x³)(-2/x)] / (6/x²)² = -1/9`,

and

`[T_n/H_n²] / (S_n/H_n)²
  → (-6/x⁴) / (6/x²)² = -1/6`.

For every sufficiently deep pole, `H_n ≠ 0`. If `S_n=0`, both normalized and raw divisions are
zero; otherwise field cancellation gives exact equality with the raw ratios
`P_n F_n / S_n²` and `T_n / S_n²`. Eventual congruence therefore transports the two limits to
the raw defects. Both constants are nonzero. No computation is used. ∎

## Strict gain over corpus endpoints

Existing modules normalize each defect by the hidden harmonic scale, and the scale-free ratio
law retains explicit dependence on `x`. No theorem forms these nonlinear projective closure
ratios. The new pair cancels both nuisance quantities and produces observation-independent
constants.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.GammaFactorialProjectiveJetClosureConstantsUniversalityLaw`
- Main theorem:
  `gammaFactorial_projectiveJetClosureConstantsUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/GammaFactorialProjectiveJetClosureConstantsUniversalityLaw.lean`
- Result: passed warning-free on 2026-07-23.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Performed only after exact Lean proof passed. Searches for the paired constants, projective
Gamma/factorial jet ratios, harmonic-residue higher jets, and nonlinear derivative invariants
found literature on ordinary Gamma asymptotic approximations and derivative error bounds, but no
statement forming these two raw-defect ratios or deriving the point- and scale-free limits
`-1/9` and `-1/6`.

Closest background:

- Yang–Tian, *Two asymptotic expansions for gamma function developed by Windschitl's formula*,
  arXiv:1712.08039.
- Mortici–Qi, *Asymptotic formulas and inequalities for gamma function in terms of tri-gamma
  function*, arXiv:1312.5881.
- NIST DLMF, Chapter 5, Gamma Function.

These sources concern standard approximations or polygamma asymptotics, not the proved
projective closure law. This is a negative search result, not a priority claim.

## Log

- 2026-07-23 — higher-jet and scale-free terminal modules exposed four common-scale residues.
- 2026-07-23 — corpus search found no raw projective closure ratios or constants `-1/9`, `-1/6`.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact-file Lean check passed warning-free; module wired into RHTower umbrella.
- 2026-07-23 — post-proof novelty search found no exact literature collision.
