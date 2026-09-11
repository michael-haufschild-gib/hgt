# EDQ compulsory logarithmic prime compensation — 2026-09-11

Goal remains OPEN: unconditional RH/falsification. Chain Euler deletion → cofinal subpower ceiling for complete signed physical source/current → off-line exclusion → RH. Frontier map remains READ ONLY; do not repeat this forcing-size proof as new progress.

## New closed Lean result
`formal/GaloisForLFunctions/RHTower/EulerDeletionLogPrimeForcing.lean`, 471 lines, namespace `RHTower.DeletionLogPrimeForcing`. Five public defs: coeff, forcing, c2, logSource, dilationPackets. Seven public theorems: c2_lower (99), coeff_sum_eq_hyperbola (113), coeff_sum_limit (159), mean_limit (277), norm_forcing_le (345), linear_energy_bounds (372), compensated_renewal (447).

Literal correction B_N = Σ_{q≤N} Λ(q) H_{floor(N/q)} b_q, H_m=Σ_{d≤m}µ(d)/d, b_q=bdGen(1/q) in original BDCarrier. Exact compensated identity J_N=-A_N-B_N, J_N=Σµ(n)log(n)b_n, A_N=ΣΛ(q)[Σ_{m≤N/q}µ(m)b_{qm}−H_{N/q}b_q]. Positive-ray equivalent D_q b_m=b_{qm}−b_q/m. Earlier raw renewal cannot silently lose B_N when transferred to compensated G_N.

`linear_energy_bounds`: ∃c,C>0, eventually c N≤‖B_N‖²≤C N, no arithmetic hypothesis. `norm_forcing_le`: ‖B_N‖≤8(log4+4)√N. The mean/N→c2/2, c2=Σ_{d≥1}µ(d)/d²≥1/4. Proof |H_m|≤2 via exact initial endpoint; ψ(x)≤Cpsi x; prefix absolute mass≤2Cpsi K; weighted Abel upper bound; signed hyperbola S_N=Σ µ(d)/d ψ(N/d), PNT+Tannery dominated by Cpsi/d²; reciprocal coefficient mass O(logN); physical-window |mean|³≤8 moment energy with moment≤2Cpsi N². Positive c2 lower bound is analytic telescoping, not numerical evaluation. This disproves correction-negligibility, NOT RH.

## Mathematical survivor and open target
On paper, existing `DeletionStretchedEnergy.primitiveEnergy_factorial_rate` q=6 plus modular norm comparison gives ‖G_k‖≤C√k/(log k)^3 eventually. Exact vector Abel J_N=logN G_N−Σ_{k<N}log((k+1)/k)G_k; split at √N to get ‖J_N‖=o(√N). Thus ‖A_N+B_N‖/‖B_N‖→0 and ‖A_N‖/‖B_N‖→1. These relative limits are PAPER ONLY, not theorems of the new leaf, and do not improve the power in the known G_N ceiling. Do not confuse a component's linear energy floor with a floor for its signed sum. Next hard target remains complete signed logarithmic gcd-group budget retaining both packets jointly; no receiver or cofinal subpower upper bound was proved here.

## Validation
Complete `lake env lean /tmp/...proof...lean` passed without diagnostics. Final leaf-only `lake build --old GaloisForLFunctions.RHTower.EulerDeletionLogPrimeForcing` passed; new leaf built in 9.9s, cached dependency diagnostics replayed. No full/umbrella build. Import wired once into RHTower.lean; index refreshed once. `python3 scripts/formal_tools.py lint --check-generated` PASSED with existing large-file warnings. Exactly seven new public theorems audited via separate scratch `lake env lean`; every axiom list exactly [propext, Classical.choice, Quot.sound]. No old-theorem re-audit, added axiom, admission or numerical premise. All owned build/check/index/lint processes reached terminal success. Temporary search/proof/audit files are being removed at turn completion.

## Documentation
- `docs/drafts/pipeline/1-in-progress/edq-compensated-log-renewal.md`: paper proof, failed negligible-correction conjecture, positive survivor, paper-only leading joint cancellation, search/transfer audit.
- `docs/drafts/pipeline/3-formalized/edq-log-prime-forcing.md`: closed statements and validation.
- Main EDQ core-attack card appended section Compensated logarithmic renewal: compulsory linear forcing.
- STATUS added one route-independent MUST-RETAIN-COMPENSATION-THROUGH-HISTORY entry. Frontier was not edited.

## Searches / computation
Five 120s OR deep/method searches, 2 rounds/all views/no module cap, for logarithmic history, prime-graph adjoint, Tauberian energy, recurrence bootstrap, Mangoldt harmonic convolution. All partial at gen823349, pending coverage, interrupted/deadline retrieval; Qdrant unavailable on history. Proofideas/ingredientsets empty; candidates predominantly source_only, history stale source, compensation stale compiler snapshot. No exhaustive absence claim. Actual chosen PNT/Tannery/window ingredients verified in Lean.
Recent broad arXiv avalanche search led to Janssens–Moll–Schindler 2609.08666v1 Sep8; appendix majorization assumes positive charge weights and iid uniform independent positions. No transfer to actual signed Möbius Gram. Bernstein–Szego orthogonality and constructed Cayley contraction also lacked source identification; do not repackage them as a source bound.
RunPod `157.157.221.29:27094` refused a THIRD SSH attempt. Endpoint question remains pending. Frozen log-gcd experiment remains NOT RUN, protocol unchanged. REPORT count updated to three refusals. No computation moved locally/elsewhere, no remote process created. See mem:rh/edq-logarithmic-gcd-budget-2026-09-11 for protocol and preceding failed transfers.
