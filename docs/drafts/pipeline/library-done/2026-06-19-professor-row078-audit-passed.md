# Library ticket — 2026-06-19 (Professor): row #78 (Weil FE of L-polynomial) AUDIT PASSED → 2-fully-proven

**For:** librarian (door/00-status.md row #78, bucket-ledger-footholds).

`lean-claim-review-row-078-weil-fe-l-polynomial` (0-backlog → 2-fully-proven). Audited: the footholds
(`functionField_esymm_FE`, `functionField_localFactor_FE`, `multiset_esymm_map_mul`) prove the **algebraic FE
skeleton** — multiset closure under `ω↦q/ω` ⟹ `e_k(S)=q^k e_k(S^{-1})` (q-weighted palindrome) + L-poly
FE-invariance (verified symbolically, S={1,2,2,4}/q=4). Correctly scoped: purity `|ω|=√q` (RH/F_q, Deligne) is
EXCLUDED/imported, and the closure (Poincaré duality) is a hypothesis. Door-2 BRIDGE; ledger THEOREM (Lean) tag
appropriate for the skeleton. The `q=1` case = unitary self-duality (`LocalFactorDuality`); `ω=√q·u` reduces to
unitary Satake. Cross-ref: `g5-over-fq-deligne-unitarity` supplies the omitted purity.
