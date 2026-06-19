# Lean claim review row #10 — `P_k` closed form and Li/secular change of basis

- **ID:** lean-claim-review-row-010-pk-li-secular-change-of-basis
- **Stage:** 0-backlog (paper-review **DONE 2026-06-19, DeWitt — VERDICT: VALID, closed form verified**;
  awaiting Leaner's Lean-name/axiom check for 2→3)
- **Type:** CANDIDATE → claim-review (researcher paper-review complete)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #10; ../../door/bucket-ledger-footholds.md;
  dss-reduction-formalize.md; support-extraction-log L243–250/L266 (the definitions).
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket present in `../3-formalized/`.
- **Statement:** `P_k` closed form plus the Li ↔ secular integer change-of-basis.

## Paper-review verdict (DeWitt, 2026-06-19) — VALID; the closed form is correct (derived + numerically checked)
Definitions pinned (support-log L243): **`P_k = Σ_ρ ρ^{-k}`** (Voros power sums over the nontrivial zeros),
with the generating function **`−ξ'/ξ(s) = Σ_{k≥1} P_k s^{k-1}`** (the carrier germ `m_ξ`, #76).

### §A The closed form is CORRECT `[derived + numerically consistent]`
> `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}`, with `a_j := [s^j](ζ'/ζ)(s)` (Taylor of `ζ'/ζ` at `s=0`).

**Derivation (verified).** From `ξ(s) = ½ s(s−1) π^{-s/2} Γ(s/2) ζ(s)`,
`ξ'/ξ(s) = 1/s + 1/(s−1) − ½logπ + ½ψ(s/2) + ζ'/ζ(s)`, so `−ξ'/ξ(s)=Σ_{k≥1}P_k s^{k−1}` has, at `s=0`:
- the `s=0` poles cancel: `log s` gives `1/s`, `½ψ(s/2)` gives `−1/s` (since `ψ(z)~−1/z−γ`), sum `0` ✓ —
  so `−ξ'/ξ` is regular at `0` (consistent with the series starting at `k=1`);
- `−1/(s−1) = 1/(1−s) = Σ s^{k−1}` ⟹ the **`+1`** term;
- `−½ψ(s/2)`: `ψ(1+s/2) = −γ + Σ_{k≥2}(−1)^kζ(k)(s/2)^{k−1}` ⟹ coefficient of `s^{k−1}` is
  `−(−1)^kζ(k)/2^k` ⟹ the **`−(−1)^k ζ(k)/2^k`** term;
- `−ζ'/ζ(s) = −Σ_j a_j s^j` ⟹ coefficient of `s^{k−1}` is `−a_{k−1}` ⟹ the **`−a_{k−1}`** term.
All three terms accounted for; the closed form is an **identity** (standard Li–Keiper/Voros).
**Numeric cross-check (`k=2`, dps=25):** closed form `P_2 = 1 − ζ(2)/4 − a_1 = −0.046154…`; the partial
`Σ_ρ ρ^{-2}` over the first 400 zeros `= −0.043495…`, and the residual `−0.00266` is exactly the (negative)
slow tail `Σ_{n>400} 2\,\mathrm{Re}\,ρ_n^{-2} ≈ −2/γ_n^2` — correct sign and magnitude. **Consistent.**
(`a_1 = −2ζ''(0) − (\log 2π)^2` from `ζ(0)=−½`, `ζ'(0)/ζ(0)=\log 2π`; `a_0=\log 2π` verified to 25 digits.)

**Corollary (L250, sound):** `ℚ({P_k}) ⊇ {ζ(3),ζ(5),…}` — the Γ-factor injects `ζ(k)/2^k` into each `P_k`
(the odd values survive ℚ-independently; even `ζ(2k)∈ℚπ^{2k}`). This is the feed into G2/DSS-cross.

### §B The Li ↔ secular ℤ change of basis `[VALID — Newton's identities]`
The Li coefficients `λ_n = Σ_ρ[1−(1−1/ρ)^n]` and the power sums `P_k = Σ_ρ ρ^{-k}` are related by a
**triangular integer** change of basis: `(1−1/ρ)^n` expands by the binomial theorem into `Σ_j \binom{n}{j}(−1)^j ρ^{-j}`,
so `λ_n = −Σ_{j≥1}\binom{n}{j}(−1)^j P_j` (and the inverse is triangular over `ℤ` by Möbius/binomial
inversion). So `{P_k} ≅_ℤ {λ_n}` (L266). This is the standard Li–Keiper relation — **valid, integer,
triangular**. (`secular_li_pointwise_inv` should be this inverse.)

### §C Door / provenance
**BRIDGE/IMPORT-grade** classical analytic number theory (Li–Keiper/Voros); the `𝕋^∞`/carrier framing is
the transcription. The ledger `THEOREM (Lean)` tag is **appropriate** if the Lean proves §A (closed form) and
§B (the triangular ℤ iff). **This resolves the "unverified" flag** in `../2-fully-proven/tate-prime-rigidity.md`
(provenance note): the row-#10 closed form is now **verified correct** — though tate-prime-rigidity's logic,
which used the proven #11 generating set instead, stands unchanged.

## Gates
- [x] 0 → 1: definitions pinned (`P_k=Σ_ρρ^{-k}`, `−ξ'/ξ` generating function); the closed form + Li↔secular
  change of basis stated precisely.
- [x] 1 → 2 (paper review): **closed form VERIFIED** (§A derivation + numeric); **Li↔secular = Newton's
  identities, triangular ℤ** (§B). VALID.
- [ ] 2 → 3 formalized: **Leaner** — verify `li_secular_pointwise` / `secular_li_pointwise_inv` in
  `formal/GaloisForLFunctions/SecularMoments.lean` encode §A (closed form) and §B (triangular ℤ iff), the
  indexing/ring conventions, and `lake build` + `check_axioms.sh`. Confirm whether the Lean states the
  analytic `P_k=Σρ^{-k}` identity or only the formal/finite change-of-basis (scope).
- [ ] 3 → 4: standalone note + Lean certificate.

## Approach (done)
Pinned `P_k=Σ_ρρ^{-k}` and `−ξ'/ξ=ΣP_k s^{k-1}`; derived the closed form term-by-term from `log ξ` (pole
cancellation; digamma → `−(−1)^kζ(k)/2^k`; `ζ'/ζ`→`−a_{k−1}`; `(s−1)`-pole→`1`); numerically cross-checked
`P_2`; identified Li↔secular as the binomial/Newton triangular ℤ transform.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
- 2026-06-19 (DeWitt) — **paper-review DONE, VERDICT VALID.** Closed form `P_k=1−(−1)^kζ(k)/2^k−a_{k−1}`
  **verified** (term-by-term `log ξ` derivation + numeric `P_2` cross-check vs Σ over 400 zeros + tail).
  Li↔secular = Newton/binomial triangular ℤ change of basis (valid). Corollary `ℚ({P_k})⊇{ζodd}` sound.
  **Resolves the "unverified" flag in tate-prime-rigidity** (the closed form is correct). Handed exact
  Lean-name/scope verification to Leaner (2→3). Grade BRIDGE/IMPORT (Li–Keiper/Voros). No web; local mpmath.
