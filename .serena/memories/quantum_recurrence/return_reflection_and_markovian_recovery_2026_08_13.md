# Return reflection and Markovian recovery (2026-08-13)

Active master remains `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.

New Stage-2 cards:
- `docs/drafts/pipeline/2-fully-proven/autonomous-return-complexity-reflection-law.md`
- `docs/drafts/pipeline/2-fully-proven/markovian-return-recovery-complexity-reflection-law.md`

Proved paper results:
1. Closed autonomous Choi/unitary flow, inverse-closed gate dictionary. If `delta_R=d_Ch(U_R,I)`, robust complexity at `t` and `R-t` radius-interlaces with additive error `delta_R`. Exact projective returns give exact complexity palindrome.
2. Stronger shellwise law: every exact circuit length incidence count and every nonnegative length partition function (including Abel/Green endpoint accessibility) radius-interlaces; exact returns give equality shell-by-shell. First-entrance path mass is not claimed because reversal swaps prefixes/suffixes.
3. CPTP semigroup extension in diamond norm. If `delta_R=||Lambda_R-id||_diamond`, then `Lambda_(R-t)` is an explicit `delta_R` recovery for every `Lambda_t`; distinguishability loss anywhere is at most relative `delta_R`. Inverse unitary words give shellwise and complexity reflection at errors `epsilon -> epsilon+delta_R`.
4. Exact full-channel Markovian recurrence makes every intermediate channel CPTP-invertible, hence unitary. Genuine dissipation and exact full-channel recurrence are incompatible. Classical core; quantitative circuit-incidence composition priority open.

Scientific boundary:
- This closes recurrence-side decline as an independent Brown obligation. Forward growth + return automatically produces reversed decline.
- It does not prove forward first-cut growth, plateau duration scale, or first return scale.
- Exact remaining Brown core remains fixed-error finite-scale moving-centralizer undistortion / nonadaptive gate tracking against ordinary static local Hamiltonians.
- Abel incidence, plateau density, palindrome, and simulation Lipschitz bounds permit exponentially long incubation and cannot imply first cut.

No Lean was written or run due shared refactor. No Lean process started. External audit checked Brown--Susskind 2018, Oszmaniec et al. PRX 2024, and classical CPTP inverse literature (Nayak--Sen quant-ph/0605041).