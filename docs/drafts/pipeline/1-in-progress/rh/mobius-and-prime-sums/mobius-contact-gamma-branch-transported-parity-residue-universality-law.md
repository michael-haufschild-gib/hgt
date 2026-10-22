# Möbius-contact Gamma branch-transported parity-residue universality law

- **ID:** mobius-contact-gamma-branch-transported-parity-residue-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of Möbius-contact adjacent-parity asymptotics and the
  Möbius-contact factorial connection-tensor law
- **Statement:** In every jet grade and at every fixed Gamma pole branch, inverse
  contact-connection transport carries the adjacent odd/even factorial-microscope limits to a
  common intrinsic branch residue; their scale-free quotient remains the same nonzero even-zeta
  invariant.

## Goal

Connect two separate corpus mechanisms rather than merely conjoin them: the adjacent
odd/even Gamma factorial asymptotics live initially in the branch-zero factorial fiber, while the
connection-tensor theorem transports intrinsic covariant residues to every pole branch. The law
must identify the transported analytic limits with those branch residues and expose the
branch-independent projective quotient.

## Gates

- [x] 0 → 1 in-progress: full source read, corpus research search, well-posed theorem, source-pure
  attack
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check and RHTower umbrella import
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `tendsto_mobiusContactGammaOddCorrection`
- `tendsto_mobiusContactGammaEvenFiniteTail`
- `tendsto_mobiusContactGammaCrossParityRatio`
- `mobiusContactGammaCrossParityRatio_limit_ne_zero`
- `mobiusContactGamma_completeConnectionTensorUniversality`

## Proof

**[PROVED HERE]** Fix parity index `r`, branch `b`, and nonzero microscope coordinate `x`.
Write `j = 2r+1` and

`T_b = ‖(-2 - contactCharge(b))/2‖^{-j}`.

The connection-tensor law at grade `j = Fin.last(2r+1)` states

`‖Res_b,j‖ = T_b j!`.

The untransported adjacent parity laws state

`Odd_r(n,x) → 2 j! ζ(2r+2)`,

`Even_r(n,x) → -j!`,

and

`Odd_r(n,x)/Even_r(n,x) → -2 ζ(2r+2) ≠ 0`.

Continuity of multiplication by the fixed scalar `T_b` gives

`T_b Odd_r(n,x) → 2 ‖Res_b,j‖ ζ(2r+2)`

and

`T_b Even_r(n,x) → -‖Res_b,j‖`.

The common transport cancels in the quotient, whose existing limit is therefore independent of
the pole branch. This simultaneously identifies both analytic channels with one intrinsic
branch residue and proves their projective zeta ratio is connection-flat. ∎

## Strict gain over corpus endpoints

The adjacent-parity theorem contains only the initial factorial fiber. The connection-tensor
theorem contains no polygamma asymptotic channel. Their composition produces all-branch analytic
limits, with a shared transported residue amplitude and branch-independent quotient; no existing
corpus endpoint states this transport law.

## Lean formalization

- Main theorem:
  `mobiusContactGamma_branchTransportedParityResidueUniversality`
- Module:
  `GaloisForLFunctions.RHTower.MobiusContactGammaBranchTransportedParityResidueUniversalityLaw`
- Verification:
  `lake env lean GaloisForLFunctions/RHTower/MobiusContactGammaBranchTransportedParityResidueUniversalityLaw.lean`
  passed without warnings.
- Umbrella:
  imported by `GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Post-proof searches found standard polygamma Taylor/asymptotic expansions, their zeta values,
Gamma pole residues, and classical Gamma recurrence/reflection formulas. They did not find an
all-branch theorem transporting adjacent factorial-microscope parity limits through a
contact-connection tensor to one covariant residue while preserving a nonzero projective
even-zeta ratio. Relevant comparison points:

- NIST DLMF, Gamma asymptotic expansions:
  `https://dlmf.nist.gov/5.11.E7`
- Polygamma Taylor, pole, and asymptotic formulas:
  `https://en.wikipedia.org/wiki/Polygamma_function`
- “On the Asymptotic Expansions of the (p,k)-Analogues of the Gamma Function and Associated
  Functions”:
  `https://www.mdpi.com/2075-1680/14/1/55`

Novelty remains a negative-search conclusion, not a claim of bibliographic completeness.

## Log

- 2026-07-23 — generated from residual all-order-parity/connection-tensor terminal pair.
- 2026-07-23 — rejected branch-zero substitution as cosmetic because the corpus already gives the
  explicit factorial limit.
- 2026-07-23 — corpus research found no all-branch transport theorem for both adjacent parity
  channels.
- 2026-07-23 — dependency-closed paper proof completed before Lean implementation or literature
  search.
- 2026-07-23 — exact-file Lean verification passed; module wired into RHTower umbrella.
- 2026-07-23 — post-proof literature audit found no exact or equivalent law.
