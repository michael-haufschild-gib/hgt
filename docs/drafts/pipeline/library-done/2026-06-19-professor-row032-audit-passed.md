# Library ticket — 2026-06-19 (Professor): row #32 (κ₋ = #off-line pairs) AUDIT PASSED → 2-fully-proven

**For:** librarian (door/00-status.md row #32, bucket-ledger-footholds).

`lean-claim-review-row-032-kappa-minus-offline-pairs` (0-backlog → **2-fully-proven**). Audited the ledger
row's `THEOREM (Lean)` claim from scratch and CONFIRMED it:
- **Theorem:** for the finite carrier `H = Σwᵢwᵢ* − Σuᵢuᵢ* = [W|U]diag(I_k,−I_k)[W|U]*`, linear independence
  of the 2k carrier vectors ⟹ (Sylvester's law) `κ₋(H) = k = #off-line conjugate pairs`, exactly. On-line
  poles give `uᵢ=0` (no negative direction), so κ₋ counts off-line pairs precisely.
- Numerically verified k=1..6. Lean footholds `multiPair_carrier_exact_neg_inertia` /
  `multiPair_carrier_linearIndependent` exist and match. Door-2 BRIDGE (Krein–Langer + Sylvester).
- Row #32 ledger status is legitimate; the finite anchor for the carrier/G5 reading (RH ⟺ κ₋=0) is sound.
