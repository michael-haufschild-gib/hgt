# Library ticket — claim-review row #10 paper-review: VALID (closed form verified); resolves a prior flag

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19

## Outcome
`lean-claim-review-row-010-pk-li-secular-change-of-basis` — **paper-review DONE, VERDICT VALID**
(`../0-backlog/lean-claim-review-row-010-pk-li-secular-change-of-basis.md`). The `P_k` closed form
`P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}` (`P_k=Σ_ρρ^{-k}`, `−ξ'/ξ=ΣP_k s^{k-1}`) is **verified** — derived
term-by-term from `log ξ` (pole cancellation; digamma → `−(−1)^kζ(k)/2^k`; `ζ'/ζ`→`−a_{k−1}`; `(s−1)`-pole
→`1`) and numerically cross-checked (`P_2` vs Σ over 400 zeros + tail). The Li↔secular change of basis is
the Newton/binomial **triangular ℤ** transform (`λ_n=−Σ_j\binom{n}{j}(−1)^jP_j`), standard Li–Keiper.

## For 00-status
- **#10:** no downgrade — confirmed valid at paper level; ledger `THEOREM (Lean)` tag appropriate pending
  Leaner's SecularMoments.lean name/scope check (analytic identity vs formal change-of-basis). Grade
  BRIDGE/IMPORT (Li–Keiper/Voros).
- **Resolves a prior flag:** `../2-fully-proven/tate-prime-rigidity.md` provenance note called the row-#10
  closed form "unverified." **It is now verified correct.** (tate-prime-rigidity's logic used the proven #11
  instead and stands unchanged; the provenance note can be softened to "verified, not relied upon.")

## For Leaner (2→3)
Verify `li_secular_pointwise` / `secular_li_pointwise_inv` encode §A (closed form) + §B (triangular ℤ iff);
indexing/ring conventions; whether the Lean states the analytic `Σρ^{-k}` identity or only the formal
change-of-basis. `lake build` + `check_axioms.sh`.

## No new claim
Verification/audit of an existing ledger row; the closed form is classical (Li–Keiper/Voros).
