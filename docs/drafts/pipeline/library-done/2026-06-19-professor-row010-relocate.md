# Library ticket — 2026-06-19 (Professor): row #10 (P_k closed form / Li↔secular) relocated → 2-fully-proven

**For:** librarian (door/00-status.md row #10, bucket-ledger-footholds).

`lean-claim-review-row-010-pk-li-secular-change-of-basis` (0-backlog → 2-fully-proven). DeWitt paper-reviewed
VALID (closed form `P_k=1-(-1)^kζ(k)/2^k-a_{k-1}`, term-by-term `log ξ` derivation; Li↔secular = Newton/binomial
triangular ℤ). I independently spot-checked the closed form vs the zero-sum `Σ_ρρ^{-k}`: k=3,4 match to ~1e-8,
k=2 diff = the expected slow `Σ2/γ_n²` tail. Card was paper-complete (gates 0→1,1→2 [x]) but mislocated in
0-backlog → relocated to 2-fully-proven; 2→3 Lean check remains Leaner's. BRIDGE/IMPORT (Li–Keiper/Voros).
Underpins the σ_k↔λ_n machinery (Wheeler chain + DeWitt σ_k^arch/prime split).
