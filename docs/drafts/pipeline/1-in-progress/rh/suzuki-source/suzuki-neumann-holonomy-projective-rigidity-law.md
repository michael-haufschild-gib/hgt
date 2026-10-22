# Suzuki Neumann-holonomy projective rigidity law

- **ID:** suzuki-neumann-holonomy-projective-rigidity-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized; hostile literature audit passed)
- **Source:** Bottom-up closure of full-frequency Neumann holonomy, affine jump decomposition,
  and finite resolvent update
- **Statement:** Away from degenerate shifts, frequencies, and characteristic divisors, the
  Neumann holonomy cancels exactly when endpoint central jets are projectively aligned. The full
  shifted jump then equals its Euler--Gamma truncation, and finite updates reduce the condition to
  vanishing of one endpoint/tangent projective determinant.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and consumers read
- [x] Internal noncollision audit
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Internal noncollision audit

Exact repository research queries for `Suzuki Neumann holonomy projective alignment cancellation`,
`centered projective shift numerator rigidity affine sewing`, and `Neumann holonomy finite update
projective tangent determinant` found the decomposition and update formulas but no zero-locus or
function-level cancellation classifier.

## Paper proof

For nonzero `a`, `alpha`, `beta`, `z`, `sin(a z)`, endpoint characteristics, and distinct shifts,
the exact holonomy formula is a nonzero scalar times

`(centralJetAlpha * WBeta(z) - centralJetBeta * WAlpha(z)) / (WAlpha(z) WBeta(z))`.

Hence holonomy vanishes exactly when the cross numerator vanishes, equivalently when the two
central jets define the same projective characteristic value. The exact jump decomposition says
the full shifted source is its Euler--Gamma truncation plus this holonomy, giving the second
equivalence. Under finite update `WBeta = W + (beta-alpha)J` and
`centralJetBeta = centralJet + (beta-alpha)tangentJet`, the cross numerator is

`(beta-alpha) * (centralJet * J(z) - tangentJet * W(z))`.

Distinct shifts cancel the first factor, proving the projective-tangent criterion. `[PROVED HERE]`

## Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/SuzukiFullFrequencyNeumannHolonomy.lean`

Capstones:

- `suzukiNeumannHolonomyCorrection_eq_zero_iff_projectiveAlignment`
- `suzukiJumpWeylCandidate_shiftedNeumann_eq_iff_projectiveAlignment`
- `suzukiNeumannHolonomyCorrection_finiteUpdate_eq_zero_iff_projectiveTangent`

Exact direct check passed:

```text
lake env lean GaloisForLFunctions/RHTower/SuzukiFullFrequencyNeumannHolonomy.lean
```

## Hostile literature noncollision audit

Post-proof searches covered Suzuki screw functions, Xi canonical systems, Neumann channels,
Weyl functions, affine sewing, finite resolvent updates, projective characteristics, and tangent
determinants. Nearest primary sources were Suzuki's
[screw-function study](https://arxiv.org/abs/2206.03682),
[screw-line applications](https://arxiv.org/abs/2209.04658),
[Xi canonical-system construction](https://arxiv.org/abs/1204.1827), and
[2026 Weil-form synthesis](https://arxiv.org/abs/2606.09096). None states this affine-sewn
full-frequency Neumann holonomy, its exact projective cancellation locus, or the finite-update
tangent-determinant classifier. Verdict: `NO COLLISION FOUND`; no priority claim.

## Log

- 2026-07-21 — Found during post-Law-37 current-delta scan. Internal duplicate audit and
  dependency-closed paper proof pass; Lean implementation written in source module so direct
  checking does not require a premature dependency build.
- 2026-07-21 — Entire source module passes exact direct Lean check. Hostile literature audit found
  no matching projective cancellation law. Exhaustion restarted.
