# Leftovers goal ledger (goal set 2026-10-05)

Goal: formalize every card in this folder unconditionally in Lean and move it to `3-formalized/`.
One row per card; rewrite the row in place when status changes; history goes to the card logs.

| Card | Status | Remaining |
|-|-|-|
| beurling-prime-deletion-perron-region | DONE → `3-formalized/leftovers/` | Main theorem `exists_isAlphaBetaSystem_of_betaZero_lt` + window `exists_deletion_exponent_window` (25 modules, audited, wired) |
| combination-mode-reducibility-baker-bridge | DONE → `3-formalized/leftovers/` | Effective Baker (`Matveev.effectiveBakerBound_holds`), σ>¾ threshold (`EdgeCoboundary.summable_edgeTerm_iff`), Hermite criterion, support ≤ d |
| projective-horizon-hankel-secant-stratification | IN PROGRESS | (4),(5),(6),(7), CM, normality all Lean-closed (`hankel_smooth_iff`, `squareCatalecticant_iff`, `isIntegrallyClosed_hankelSecantRing`); left: rational singularities (resolution + higher direct images) |
| smooth-stein-order-two-autonomous-ade-frequency-rank | TODO | entire geometric theorem (Stein surface, CR/contact, Weinstein); needs manifold infrastructure |
| route-e-cofactor-amplified-e3-token-supply | IN PROGRESS | MT Thm 1.2 via KDIW programme (card `1-in-progress/kuznetsov-deshouillers-iwaniec-watt-lean-programme`): K1–K5 Lean-closed: Kuznetsov (1.20) `kuznetsov_opposite_sign`; same-sign inequality; DI Prop 3 (1.26)/(1.27); **DI Theorem 2** `large_sieve_gamma0` (Γ₀(Q), `C_ε|H|(K²+N^{1+ε}/Q)`); next DI Thms 5–12 → DI twisted fourth moment (= MT Lemma 3.5(ii)) → MT Thm 1.2 |
| route-e-forbidden-support-e3-stability | IN PROGRESS | same MT Thm 1.2 input (FS4), (FS7); shares the KDIW programme |
