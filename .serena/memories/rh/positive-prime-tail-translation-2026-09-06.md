# Positive prime-tail translation: closed coefficient/continuation audit

No qualifying novel RH architecture or RH proof established. Goal remains ACTIVE. Proposed global chain is literal zeta coefficients -> new zero-forced arithmetic relation -> strict off-line contradiction -> RH; both decisive links remain missing. This result is classical audit evidence, not an approved successor.

## Exact closed result

`formal/GaloisForLFunctions/RHTower/PrimeTailTranslation.lean`, namespace `RHTower.PrimeTailTranslation`, defines real completely multiplicative coefficients with a(p)=1 for p<=N and a(p)=p^(-t) otherwise, a(0)=0. Their ordinary absolutely convergent Dirichlet series on Re(s)>1 equals F_Nt(s)=zeta(s+t)*product_(p<=N)(1-p^(-s-t))/(1-p^(-s)).

For t>=0: coefficients are positive on positive integers, <=1, and exactly one through N. The finite quotient is analytic/nonzero on Re(s)>0; `continued_zero_iff` gives exactly the translated zeta zeros (general shift may retain a shifted pole). Weighted squared errors sum_(n>=1)|a_n-1|^2/n^(2sigma) tend to zero for every sigma>1/2, even for arbitrary nonnegative shift schedules t_N.

At shift two, F_N2 is analytic and nowhere zero throughout Re(s)>0. For every real 0<sigma<1 its real part is positive, while zeta(sigma)<0 via the existing paired eta identity. Therefore these continued values do NOT converge to zeta at ANY real point of (0,1). This is a symbolic sign proof, no zero hypothesis or computation. Zero-free approximants alone would not prove nonconvergence; the sign theorem is essential.

Premise-free capstone: `positive_zero_free_tail_approximation` bundles all fixed-shift-two claims. No functional equation imposed on approximants; no single different function matches all coefficients. Stronger topologies with proved arithmetic estimates remain outside this obstruction. Failure of continuation limits also at regular nonzero points cannot alone detect zeta zeros.

## Artifacts

- Full dependency-closed paper proof, Lean claims, ancestry, scope: `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/positive-prime-tail-translation.md`.
- Failed specified continuity principle: `docs/drafts/pipeline/5-failed/prime-tail-coefficient-continuation.md`.
- Old `1-in-progress/prime-tail-translation-audit.md` was moved, no references remain.
- `universal-law-field/STATUS.md` adds self-contained MUST-TAIL1 after MUST-PREFIX1.
- Main `rh-corpus-architecture-audit-2026-09-05.md` adds result and fixes stale final 'sole provisional successor' summary to no qualifying architecture.
- Single import wired into `formal/GaloisForLFunctions/RHTower.lean` near PrimeTail modules.

## Novelty/no-go closure

Explicit shifted Euler product plus finite correction and paired alternating zeta sign: classical mathematics, no new mechanism claimed. Primary references checked: DLMF 25.2.E11 Euler product and 25.2.E3 alternating identity; adjacent arithmetic derivations paper (impan product/91275) and Emmons 2011 publisher abstract only. Neither asserted to contain exact packaged theorem. Positive survivor strengthened to arbitrary shift schedules, translated-zero identity, and all real-strip nonconvergence; all closed. NO POSITIVE SALVAGE FOUND as a new RH producer. Do not rename this as radical architecture.

## Validation and process discipline

Scratch `/tmp/hgt-prime-tail-translation-WNVmhQ`: scratch and direct production `lake env lean` checks PASS. Final `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.PrimeTailTranslation` PASS, only leaf rebuilt against cached dependencies. Imported `Audit.lean` checks all 26 public theorems, each standard dependencies only propext/Classical.choice/Quot.sound. Repository formal lint PASS with large-file warnings. Scoped whitespace/local links/26-theorem audit coverage/forbidden-token scan/unique umbrella import PASS. Research index refreshed and finds34 declarations (7 defs +26 public theorems +1 private theorem). All owned Lean/Lake sessions terminal; process check found none. No full/umbrella build and no experiment/Runpod job launched this turn. Shared dirty tree preserved; no commit.

Earlier broad discovery/proof-body audits rejected two-product gauge occurrence (already retired), commuting formal involution receiver without source action, and PrimeShiftResidueClosability (RH-equivalent criterion). Search used current AND/prefix `formal_tools.py research` plus rg. Many capped discovery queries are not exhaustive proof-body coverage. User exclusions remain fully in force: no spectral/Gamma/Weil/Hedenmalm/Suzuki/Connes/Burnol/Hilbert-Polya or relabelled classic RH core.

Prior memory: `mem:rh/helson-finite-prefix-divisor-freedom-2026-09-06`.
