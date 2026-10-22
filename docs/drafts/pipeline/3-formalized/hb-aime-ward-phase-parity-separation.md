# HB AIME/Ward phase-parity separation

## Status

Paper proof and Lean formalization complete 2026-08-28. Promoted to stage 3. Frontier map remains read-only and was not modified.

## Route

HB, with HC43 Ward transmutation to FZZ-P, PW-B, and RBH.

## Corpus basis

- `d4FundamentalQNMCrossBranchAIMENumerator_neg`: actual AIME numerator is cubic and changes sign under seed half-turn.
- `d4BMMixedHorizonOpticalSourceProjection_eq`: actual BM mixed-horizon optical source projection uses a quadratic Einstein carrier.
- HC43: nonzero-seed BM projection is a faithful linear carrier of signed Deninger/FZZ/PW/RBH Ward coordinate.
- Corpus search found no existing theorem coupling these two actual amplitudes or performing their two-phase separation.

## HC44 conjecture

For a fixed normalization `c`, define the coupled return

`R_c(A,q) = AIME(A, xiSpectralPoint q) + c * BMProjection(A,0,q)`.

Then BM projection is phase-even while AIME is phase-odd, so

- `(R_c(A,q) + R_c(-A,q))/2 = c * BMProjection(A,0,q)`;
- `(R_c(A,q) - R_c(-A,q))/2 = AIME(A,xiSpectralPoint q)`.

For nonzero `A`, simultaneous cancellation at `A` and `-A` is impossible for every `c`, because odd AIME component is nonzero at every Xi descendant. For nonzero `A,c`, vanishing even component remains exactly critical-line placement and hence has universal RH strength.

## Positive survivor

Exact two-phase tomography separates nonlinear source dynamics by phase parity: odd sample is unavoidable AIME residue; even sample is common signed Ward receiver. This rules out every fixed additive quadratic Ward counterterm as the missing third-order AIME cancellation channel. If one phase is tuned to cancel, the opposite phase is exactly minus twice the nonzero AIME numerator. Viable HB dynamics must contain a genuinely cubic `++-` term.

## Lean artifact

`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMEWardPhaseParitySeparation`

Main results:

- actual BM mixed-horizon projection is seed-half-turn even;
- exact half-sum/half-difference tomography;
- no simultaneous two-phase cancellation for nonzero seed;
- exact doubled opposite-phase residue after one-phase cancellation;
- calibrated even sample equals Deninger Ward charge;
- even zero locus is critical-line placement and universal even cancellation is RH-strength.

All declarations are unconditional. No new axioms, premises, `sorry`, `admit`, `opaque`, or `unsafe` declarations are introduced.

## Bounded novelty audit

Search date: 2026-08-28. Primary-source search covered third-order absorption-induced mode excitation (Sberna et al., arXiv:2112.11168), observed nonlinear ringdown modes (Cheung et al., arXiv:2208.07374), quadratic Teukolsky QNM excitation (Ma--Yang, arXiv:2401.15516), and phase-amplitude QNM excitation beyond GR (Silva et al., arXiv:2404.11110). These sources distinguish nonlinear orders and excitation mechanisms but do not couple actual AIME and BM Ward amplitudes, prove half-turn tomography, identify a Deninger/FZZ/PW/RBH even component, or give the exact doubled opposite-phase no-go. This is a bounded no-match finding, not an exhaustive literature-wide novelty claim.

## Conjecture loop

- HC44-A: actual BM projection is seed-half-turn even — proved in Lean.
- HC44-B: exact sum/difference tomography — proved in Lean.
- HC44-C: simultaneous two-phase cancellation no-go — proved in Lean.
- HC44-D: even channel zero locus and universal RH endpoint — proved in Lean.

## Verification audit

- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingAIMEWardPhaseParitySeparation.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMEWardPhaseParitySeparation`: passed, 12,005 jobs.
- `#print axioms` for all ten public theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Module wired into `GaloisForLFunctions.RHTower` umbrella; no umbrella build was run.
- Formal lint contains no HC44 error. Global lint remains red only on unrelated pre-existing unreachable owned modules.
