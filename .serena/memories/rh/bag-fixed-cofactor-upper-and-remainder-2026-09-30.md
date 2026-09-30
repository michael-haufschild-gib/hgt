# BAG C20.3 / F45: fixed-cofactor small channels and actual remainder

Sole user scope: find/formalize independent recurrence producer. RH goal remains active and unmet.

## Proved final leaf
`formal/GaloisForLFunctions/RHTower/SmoothAFEReflectedChannelUpper.lean` (335 lines), namespace `RHTower`, imports cofactor-cell stability, chi power envelope, PNT prime windows. Eight public exports:
- `exists_reflectedPrimalPositiveCoefficient_fixedCofactor_upper`: fixed d in (0,1/2), D>0, N<=D*n, t>=N, all r>0: actual coefficient norm <= C N^(-1/2).
- `exists_reflectedPrimalLargePrimeChannel_upper`: same envelope for each p>N/D channel, every phase.
- `exists_reflectedPrimalLargePrimeChannel_energy_upper`: scalar channel energy <= C/log N eventually, all t>=N,r>0,phases.
- `exists_eventually_reflectedPrimalChannel_dot_upper`: simultaneous fixed finite nodes d,b, common t in [5N/4,7N/4], all directions u: each channel dot <= C N^(-1/2)||u||.
- `exists_eventually_reflectedPrimalConditional_energy_upper`: same quantifiers, sum squared channel dots <= C/log N ||u||^2.
- `eventually_reflectedPrimalConditional_energy_le`: uniform eventual <= epsilon ||u||^2.
- `integral_normSq_steinhausCarrier_sub_smooth`: exact second moment of full finite carrier minus smooth background equals sum over large primes/cofactors of coefficient squared norms, under arithmetic seam N<Y^2.
- `exists_reflectedPrimalCarrier_sub_smooth_meanSquare_upper`: actual reflected-primal full-minus-smooth remainder at Y=N/D has mean square <= C/log N, every t>=N,r>0 eventuallyN.
Use D=2K for C19. Constants can depend on fixed D,d,b but never N,r,phase,common height.

`SmoothAFECofactorCellStability.lean` now publicly exports `norm_smoothAFECutoff_le_one` through its already proved private helper.

Both final leaves compiled warning-free with `lake --old env lean <leaf> -o <existing build path>`. New leaf wired to umbrella. `/tmp/BagChannelUpperAudit.lean` audits eight exports plus shared cutoff export; `/tmp/bag-channel-upper-axioms.log` reports only propext, Classical.choice, Quot.sound. No proof debt. `/tmp/bag-channel-upper-lint.log` global gate exits1 on21 unrelated unreachable modules; no BAG issue. Whitespace clean. Passing scratch `/tmp/BagChannelUpper.lean` retained.

## Frontier
C20.3 closed. It supplies actual remainder L2 decay and maximal-channel estimates, NOT full-carrier low-moment decay, same-event centre/target law, or deterministic orbit transfer. Do not claim recurrence.

C20.2 remains missing: unconditional normalized full multiplicative first-mean decay. Harper primary arXiv1703.06654 sections4.1–4.3 reduces upper bound to Euler product/barrier mass and barrier failure estimates, using tilted random-walk Proposition5. Not a Lean premise. Deep corpus search `/tmp/bag-critical-barrier-deep.json` completed: partial=false, no execution errors, 63337/63337 files inventoried, compiler evidence mostly pending/stale and semantic coverage unmeasured. Inspected all20 candidates and20 source arguments: no applicable critical Euler-product random-walk barrier theorem. Rejected generated ingredient set (scalar half-Lipschitz sign fact plus finite-circle convexity does not prove a barrier law). Targeted lexical query `"random walk" barrier` returned zero hits; exhaustive phrase searches returned only contextual/irrelevant hits. New exact theorem is visible in lexical index: `/tmp/bag-channel-upper-index-check.json`, total1, correct leaf/line274. No owned Lean/search process remains active. Current scratch fragments/name probes archived at `/var/folders/h4/zrd73pg91clb__kg1kzrlcph0000gn/T/bag-superseded-c20-upper-2_mnson6`. Next genuinely missing task is to find/prove full-carrier low-moment decay and its source dependencies; do not keep adding receivers. C20.2 weighted Abel transfer is paper-derived below, not formalized. Final F45 proof/axiom/lint checks are complete.

Paper Abel transfer recorded on card: decreasing nonnegative w_n=n^-beta W(rn/N), finite Abel summation bounds expected weighted norm by positive combination of E|S_n|. Fixed finite prefix contributes bounded constant; epsilon sqrt n tail contributes <=epsilon C_beta N^(1/2-beta), uniformly r>0. Actual normalized full carrier vanishing follows only AFTER base unweighted decay proved. Do not introduce a receiver assuming that missing theorem.

Main card and working log: docs/drafts/pipeline/1-in-progress/bagchi-quantitative-sparse-recurrence{,-working-log}.md. BAG frontier row updated with F45.