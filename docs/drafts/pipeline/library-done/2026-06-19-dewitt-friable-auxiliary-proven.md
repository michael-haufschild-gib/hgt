# Ledger ticket — DeWitt — friable-dirichlet-auxiliary developed (0-backlog → 2-fully-proven, BRIDGE)

**For:** librarian. **Type:** stage flip + row edits (00-status row #103; cross-link #15, #122).

**What changed (card `0-backlog/friable-dirichlet-auxiliary.md` → `2-fully-proven/...`).** Object N5 built as
a first-class native auxiliary space; pillars A (Bombieri–Vaaler) and B (proven uniform zero estimate)
discharged on it; **obstruction C made explicit at `s=1`** and reduced to a posed bound. Grade BRIDGE.

**The result.** For the friable auxiliary `F(s)=Σ_m λ_m n_m^{-s}` (`λ_m∈ℤ`, `n_m=∏p^{m_p}`):
`F^{(T)}(1) = (−1)^T Σ_m λ_m (m·ℓ)^T/n_m`, and `(m·ℓ)^T` expands multinomially into a ℚ-linear form in
degree-`T` prime-log monomials `∏_p(log p)^{a_p}`. So the race's only ungoverned term (obstruction C) =
**effective algebraic independence of `{log p}`** (a quantitative Schanuel for prime logs), height-bearing
⟹ escapes the §17.3 height vacuum.

**Degree filtration (ties #122 to Schanuel).** `T=1`: linear forms in `{log p}` = ℚ-linear independence =
elementary = `corank=∞`. `T≥2`: products of logs = ℚ-algebraic independence = "rung above Baker", `γ_n` at
degree `n`. **So Professor's corank→trdeg identity (#122) over ℚ is exactly the linear→algebraic-independence
upgrade for prime logs** — corank=∞ free (T=1), trdeg=∞ Schanuel-hard (all T). FF has it trivially (corank 1,
single `ln q`).

**Suggested 00-status edits.**
- Row #103 (friable Dirichlet auxiliary, was CANDIDATE): retag → THEOREM (paper)/native object, BRIDGE,
  2-fully-proven; note "object built; A,B discharged; C reduced at s=1 to effective Schanuel for prime logs."
- Row #15 (obstruction C, OPEN CORE): annotate "explicit form (DeWitt): C = effective alg. independence of
  `{log p}` = quantitative Schanuel for prime logs, via the friable auxiliary at s=1; the degree-T
  log-monomial linear form is the posed bound."
- Row #122 (corank–transcendence): annotate "the corank→trdeg gap over ℚ = the linear→algebraic-independence
  upgrade for `{log p}` (friable-auxiliary §6)."

**Door-2:** FAILS (Dirichlet polynomials + Siegel + Vandermonde + multinomial algebra = parents). BRIDGE;
the residual C-bound (Schanuel for prime logs) is the open Fields-Medal core, correctly external.

---
**Addendum (2026-06-19, same session).** Added §5a **surjectivity lemma** to the friable-auxiliary card:
the coefficient map `λ ↦ (C_a)` is surjective onto degree-`T` log-monomial forms ⟹ the §5 reduction is a
**two-way equivalence**: obstruction-C-governed ⟺ effective algebraic independence of `{log p}` (both
directions). "Difficulty conserved / no bypass" is now a **theorem**. For row #15: strengthen "reduced to a
posed bound" → "*equivalent* to a posed bound (Schanuel for prime logs), proven both directions." Grade
unchanged (BRIDGE); core stays Fields-Medal open.
