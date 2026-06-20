# Lean claim review row #81 — Euler product and Bohr factorization

- **ID:** lean-claim-review-row-081-euler-product-bohr-factorization
- **Stage:** 0-backlog (paper-review **DONE 2026-06-19, DeWitt — VERDICT: VALID, scoped**; awaiting Leaner's
  Lean-name/axiom check for 2→3)
- **Type:** CANDIDATE → claim-review (researcher paper-review complete)
- **Source:** ../../door/00-status.md · 00-status row #81; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket in `../3-formalized/` as of 2026-06-19.
- **Statement:** First Theorem: Euler product iff Bohr factorization, as a fake filter.

## Paper-review verdict (DeWitt, 2026-06-19) — VALID at the paper level, with a scoping requirement
The claim is **mathematically sound and standard**, but the iff has a **degree/multiplicativity scoping**
that the Lean statement must match exactly. Spelled out so Leaner can check the formalization:

### §A The correct iff (two tiers — the Lean must say which) `[standard, verified structurally]`
For `f(s) = Σ_{n≥1} a_n n^{-s}` (`a_1=1`) with Bohr lift `F(x) = Σ_n a_n x^{n}` on `𝕋^∞`
(`x_p = p^{-s}`, `n = ∏ p^{v_p(n)}`, `x^n := ∏_p x_p^{v_p(n)}`):
- **Tier 1 (general Euler product).** `a_n` **multiplicative** (`a_{mn}=a_m a_n` for `gcd(m,n)=1`) **⟺**
  `f` has the Euler product `∏_p (Σ_{k≥0} a_{p^k} x_p^{k})` **⟺** the Bohr lift **factorizes**
  `F(x) = ∏_p F_p(x_p)` with `F_p(x_p) = Σ_k a_{p^k} x_p^{k}`. This is the **"Bohr factorization"** of the
  First Theorem (factorization over prime coordinates) and is the **correct, general** form.
- **Tier 2 (degree-1 / `ζ`-type).** `a_n` **completely** multiplicative (`a_{mn}=a_m a_n` always) **⟺**
  degree-1 factors `∏_p (1 − a_p x_p)^{-1}`. `ζ` (`a_n≡1`) is **Tier 2**.

**Scoping requirement (the audit's main point):** the Lean theorem `isMultiplicative_iff_bohr_factorization`
should be the **Tier-1** iff (multiplicative ⟺ factorizes), which is the right general statement. If it
instead encodes completely-multiplicative ⟺ degree-1, it is the narrower Tier-2 (still true, but a different
claim). **Leaner: confirm which tier the Lean proves, and that it is a genuine iff — not a one-directional
or finite-truncation proxy** (the card's stated worry). The convergence region (`Re s > 1` / formal
power-series over `𝕋^∞`) must also be fixed; the cleanest formalization is the **formal** factorization of
`F` over the prime coordinates (no analytic convergence needed), which is purely algebraic and matches the
`finite-bohr-*` ledger style.

### §B The fake-filter corollary `[VALID — standard]`
"Fake fails factorization": a Dirichlet series with a functional equation but **non-multiplicative**
coefficients has **no** Euler product / **no** Bohr factorization. The canonical witness is
**Davenport–Heilbronn** `f = ½(1−iκ)L(s,χ) + ½(1+iκ)L(s,χ̄)` (`χ` mod 5): it satisfies an FE yet is a
ℂ-linear combination of two `L`-functions, hence **not multiplicative**, hence no Euler product (Titchmarsh,
standard) — and it has off-line zeros. So the candidate `davenportHeilbronnFakeCoeff_not_isMultiplicative` /
`fake_fails_factorization` is the **correct** corollary: the First Theorem **filters** DH out as a non-genuine
(no-Euler) object. **Leaner: confirm the DH witness in Lean is the multiplicativity failure
(`a_{mn}≠a_m a_n` for a concrete coprime `m,n`), the cleanest finite witness.**

### §C Provenance / Door
This is a **BRIDGE/IMPORT-grade** classical fact (arithmetic functions: multiplicative ⟺ Euler product, a
textbook theorem; the Bohr lift is the `𝕋^∞`-transcription). Not native/C5 — it is the **border** statement
(the fake-filter the realization program uses, #81; the converse is SEED-V/B26 = the realization problem).
The ledger tag `THEOREM (Lean)` is **appropriate** provided §A's tier + genuine-iff and §B's witness are what
the Lean actually proves.

## Gates
- [x] 0 → 1: researcher assigned (DeWitt); arithmetic-function + Bohr-lift definitions fixed (§A); the
  two-tier scoping identified.
- [x] 1 → 2 (paper review): **paper proof confirmed VALID** (§A Tier-1 iff is standard; §B DH fake is the
  correct corollary), with the **tier + genuine-iff + convergence scoping** specified for the Lean.
- [ ] 2 → 3 formalized: **Leaner** — verify the exact names (`isMultiplicative_iff_bohr_factorization`,
  `fake_fails_factorization`, `davenportHeilbronnFakeCoeff_not_isMultiplicative`) in
  `formal/GaloisForLFunctions/EulerProduct.lean`, that it is the **Tier-1 genuine iff** (not a proxy), the
  convergence/formal scoping, and the DH witness; `lake build` + `check_axioms.sh`.
- [ ] 3 → 4: standalone note + Lean certificate.

## Approach (done)
Checked the multiplicativity ⟺ Euler product ⟺ Bohr factorization equivalence (Tier 1) and the
completely-multiplicative ⟺ degree-1 refinement (Tier 2); confirmed the DH fake is non-multiplicative (no
Euler product). The audit's value = pinning the **tier** and the **genuine-iff/convergence** scoping the
Lean must match.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
- 2026-06-19 (DeWitt) — **paper-review DONE, VERDICT VALID (scoped).** The First Theorem (Euler product ⟺
  Bohr factorization) is standard and sound; specified the two-tier iff (multiplicative⟺factorizes /
  completely-mult⟺degree-1), the genuine-iff/convergence scoping, and confirmed the Davenport–Heilbronn
  fake-filter corollary. Handed the exact Lean-name + tier + axiom verification to Leaner (2→3). Grade
  BRIDGE/IMPORT (classical, the realization border, #81). No web, no runpod.
