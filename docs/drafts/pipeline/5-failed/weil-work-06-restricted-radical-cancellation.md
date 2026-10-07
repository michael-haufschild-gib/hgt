# WP06: restricted radical cancellation families

- **ID:** WP06-C0-C1g
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** [WP06 proof register](../../../reports/weil-work/results/06-deficit/PROOF.md)
- **Statement:** Separately translated positive mixtures cannot have vanishing repair cost after spectral normalization; finite coherent mixtures on one geometric grid cannot cancel all positive powers of its base.

## Goal

Construct positive mixtures near the Riemann radical, with vanishing arithmetic repair cost and spectral density at least one on a prescribed off-zero compact set. These two restricted families fail. The broader C, C1 and C2 constructions remain open.

## Gates

- [x] Exact families, normalization, and arithmetic values specified.
- [x] Complete paper proofs of both obstructions and their positive survivors.
- [x] C0 uniform coercivity theorem built, directly audited, and axiom-audited.
- [x] Final strengthened C1g target build, direct source audit, and two-theorem axiom audit passed; umbrella wired.

## Approach

C0 uses positive mixing without coherent cross terms. C1g allows arbitrary finite complex coherent coefficients at shifts `j log b`, for a fixed integer b≥2 and cutoff L≥log b+1. No coefficient-size restriction is imposed in the C1g obstruction.

## No-go closure

- **Exact killing mechanism:** C0 retains a fixed positive value at n=2 per unit spectral density. For C1g, sampled autocorrelation is convolution of the kernel correlation sequence with the real coefficient covariance sequence. A nonzero coefficient family has positive covariance trace, so its outer coefficient cannot disappear.
- **Strongest positive survivors:** C0 gives a uniform quantitative coercivity law, including arbitrary translations, weights and different cutoffs. C1g gives the exact additive outer-support law: if R and D are the last nonzero kernel and covariance indices, the last nonzero actual correlation occurs at R+D with value C(D)κ(R); all later sampled correlations vanish. This invariant holds for every real spacing c>0 and L≥c+1. Integer-power rigidity is its specialization.
- **New insight:** Coherent cancellation changes the surviving arithmetic index, but on one geometric grid its outer index and coefficient are determined exactly. This does not give a degree-uniform lower cost, and it does not constrain the dense rational-ratio grid proposed in C2.
- **Status:** CLOSED. Paper proofs dependency-closed in PROOF. C0 Lean theorem: `RHTower.WeilSpectral.exists_logValue_two_ge_translated_radical_density`, module `WeilWorkDeficitRadicalTranslateObstruction`. C1g Lean theorems: `RHTower.WeilSpectral.geometric_radical_outer_autocorrelation` and `RHTower.WeilSpectral.logValue_geometric_radical_eq_zero_iff`, module `WeilWorkDeficitGeometricRadicalObstruction`. Final direct source audit, target rebuild (82s), and both public axiom audits pass. Only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Final formal lint has seventeen unrelated reachability errors, none in WP06.
- **Novelty:** Elementary corpus specialization of standard finite autocorrelation/Laurent-polynomial algebra. No external scientific novelty claimed. The positive invariant is exposed explicitly rather than counting the impossibility statement itself as salvage.

## Log

- 2026-10-07 — C0 and C1g paper attacks and exact positive survivors formally closed. Broader WP06 goal remains ACTIVE and UNSOLVED; next construction is C2, with polynomial coefficient cost still open.
