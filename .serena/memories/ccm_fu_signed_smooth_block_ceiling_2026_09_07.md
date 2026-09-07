# CCM-FU: signed smooth block ceiling (2026-09-07)

Goal ACTIVE: unconditional RH proof/falsification via CCM-FU. RH, SD1, PE4, full signed Abel bound, exact successor and greedy envelope selection OPEN. User explicitly requires frontier map READ-ONLY: never edit docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md, including on goal replay. STATUS unchanged because new result is route-specific. No commits/pushes by this task; concurrent agents committed some new files during the turn, preserve their edits.

## New closed actual-source theorem
Let R(n)=divisorHyperbolaSmoothRemainder n and a=divisorHyperbolaSmoothMean=log(2*pi)/2-gamma-1/6. For EVERY s>=1,
sum_(n=s*s..(s+1)*(s+1)-1) R(n) <= (2s+1)*a.
There is no additive upper error (old absolute block error <=15). The coefficient is optimal: uniform block bound by (2s+1)*C iff a<=C, using the old absolute error and arbitrarily long blocks.

New modules / public names, all namespace RHTower:
- HarmonicGeometricSecondCorrection.lean: harmonic_mascheroni_geometric_lower_second (line74), log_symmetric_entropy_le_quartic (line127).
- DivisorSmoothSignedBlockCeiling.lean: sum_divisorHyperbolaSmooth_square_block_le_mean (line209), sum_divisorHyperbolaSmooth_square_block_ceiling_iff (line228).
Both wired in RHTower.lean, without an umbrella build.

## Paper mechanism
c=s(s+1); H_s-gamma-(log s+log(s+1))/2 >= lambda=1/(6c)-1/(30c^2).
Proof: derivative of atanh(t)-t-t^3/(3(1-t^2))+2t^5/(15(1-t^2)^2) = 8t^6/(15(1-t^2)^3)>=0; antitone corrected harmonic sequence tends to gamma.
Entropy pair (1+t)log(1+t)+(1-t)log(1-t) <= t^2+t^4/(6(1-t^2)); derivative uses old log_le_geometric_cubic. Also log(1-t^2)<=-t^2.
Pair R(c-j)+R(c+j), use exact Stirling upper, new harmonic lower, j^4<=s^2*j^2, sum j^2=c(2s+1)/6.
Block excess <=(2s+1)*[-1/(4c)+(2c+1)/(30c^2)+1/(12s^2)+1/(36s(s+2))].
Bracket = -(13(s-2)^3+107(s-2)^2+252(s-2)+138)/(180s^2(s+1)^2(s+2)) <=0 for s>=2.
s=1 block exact log12-9+12gamma; pi>3, analytic log2/log3 and gamma<.577216 prove bound. No numerical source data.

## Boundary / next hard work
Complete unweighted block sign DOES NOT control varying sqrt Abel weights or terminal partial block. These remain before deriving the global unit envelope (candidate K1(N)<=sqrtN/8) / closing remaining unit factor-two comparison. Then arbitrary signed mixed-state successor still needs proof; do not claim this source block lemma proves selection or RH. This turn examined signed least-gain extension/finite retained-field descent and attacked the unresolved unit-channel comparison component. Existing finite retained-field pool orders / bounded batches ALREADY closed; their uniform preparation/cofinal coverage remain absent, do not repackage them as progress. No numerical experiment this turn: block theorem derived analytically.

Cards:
- Moved own stage1 card to docs/drafts/pipeline/3-formalized/ccm-fu-signed-smooth-block-ceiling.md; complete paper proof, exact scope and audit limitation.
- Updated docs/drafts/pipeline/1-in-progress/ccm-fu-bounded-quotient-profiles.md with current source ceiling and remaining weighted/partial-block gap.
- Frontier map NEVER written; no STATUS entry added.

## Validation / cleanup
Both complete scratch checks and exact source-file checks with lake env lean passed without warnings. Only two new leaf oleans emitted. Actual corpus imports checked (not merely minimal scratch copies). Four new public theorems axiom-audited ONCE, all only propext, Classical.choice, Quot.sound. No old capstone re-audited. Only later source edit trimmed trailing whitespace (no proof change).
Declaration index refreshed, formal lint final exit0 (existing large-file warnings). Initial lint exit1 was concurrent MontgomeryPrimeAmpMoments missing umbrella; its owner wired it, justified one repeat then success. git diff --check passed.
Targeted Lake packaging audit remains PENDING: prior --old/exact leaf Lake build expanded into prerequisites. Do NOT repeat known expensive Lake --old/preflight paths. No Lake build or umbrella/full build this turn. Report exact-file proofs honestly, no claimed Lake build success.
An unrelated Claude Lake build +VonMangoldtSquarePowerMoments temporarily removed dependencies while rebuilding, causing two actual-import scratch failures for PrimeDepthBVWoldReesCoronaContractionNoGo and RouteRFixedTraceTailRoos. Left that build alone. Continued with literal definitions in a minimal scratch, then verified actual imports after all 4233 own transitive oleans available. Do not rebuild those modules or audit them.
All owned process handles terminal: harmonic emit67331 exit0; scratch44195/22172 initial errors;96456/40164 missing concurrent olean errors; core15965/71759 errors;6802 success; actual79071 success; leaf58564 success; axioms10156 success; index78522 success; lint90155 exit1 then28763 exit0. No owned Lean/Lake left running. Five owned /tmp files deleted via Path.unlink: ccm_fu_geometric_second.lean, ccm_fu_signed_block.lean, ccm_fu_signed_block_core.lean, ccm_fu_signed_block_axioms.lean, ccm_fu_signed_block_lint.log. Final deletion check no remaining files. No RunPod jobs or artifacts this turn.

Lean practical notes: importing full source introduces notation collisions with unspaced <=s token (use spaces around ≤). A let followed on next line by negative expression needs semicolon after let to avoid continuation parsing. Several field_simp calls close goals entirely: do not append ring or suppress warnings. Nat s*(s+1)-j membership needs explicit polynomial identity and Nat.sub_le before omega. New source exact-file compilation uses imported means and checked old bounds; no added axioms or numeric certificates.
