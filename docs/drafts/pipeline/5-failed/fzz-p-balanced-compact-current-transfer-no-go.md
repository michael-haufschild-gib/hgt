# FZZ-P balanced compact-current transfer no-go

- **ID:** fzz-p-balanced-compact-current-transfer
- **Stage:** 5-failed
- **Type:** FALSIFIED (specified carrier, not FZZ-P)
- **Statement:** Feeding external compact charge into the neutral radial Fourier characteristic cannot orient the balanced external-Gamma sector.

## Goal

Test the proposed chain `ordered external-BRST compact current → integrated mixed replica--radial Ward law → vacuum-delay saturation → RH` in the balanced external sector of Halder--Jafferis, arXiv:2402.00932v3, (4.1)--(4.3), where compact momentum is `p=0` and radial momentum `P` is independent.

## No-go closure

- **Exact mechanism:** The existing `fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral` uses integer compact `p` as radial Fourier momentum. At `p=0` it is identically `1`, independent of both coupling depths. The cyclic ordered angular integral is `1/2`, not the inverse-frequency formula valid only for `p≠0`; its diagonal compact--radial current is therefore real `1/2` for every Halder--Jafferis radial `P`. Lean also proves that no source-fixed predicate of this pair of constant carriers can select `P=0`.
- **Strongest positive survivor:** Keep compact charge zero and radial Fourier momentum `P` independent. Compact integration then equals the literal cross-depth radial coherence, whose imaginary part is nonzero away from `sin(P(u₁-u₂)/exp v)=0`. This is a diagnostic carrier, not a derived full torus Ward source.
- **Route consequence:** Retire only the direct compact-charge-fed current transfer. FZZ-P still requires source-derived, nonfactorized radial/order coupling with screening, phase frame, normalization and counterterms; the result supplies no RH premise.
- **Status:** Paper argument is immediate from the exact zero-momentum characteristic and triangular ordered integral. Both obstruction and positive survivor are closed in `FZZCigarParityBalancedExternalCompactCurrentNoGo.lean`; direct Lean check and targeted `lake build --old GaloisForLFunctions.RHTower.FZZCigarParityBalancedExternalCompactCurrentNoGo` passed. No full or umbrella build was run.
