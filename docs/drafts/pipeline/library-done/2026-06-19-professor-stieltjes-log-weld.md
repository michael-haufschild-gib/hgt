# Library update request — Professor — Stieltjes–log weld (new 2-fully-proven theorem) + baker-for-stieltjes reframe

**For:** librarian (owner of `docs/drafts/door/00-status.md` and `docs/drafts/door/00-index.md`).
**Date:** 2026-06-19. **Author:** Professor. **Edit race avoidance:** I did not touch the ledger files.

## 1. New proven theorem — add a row to `00-status.md §C`

- **Card:** `../2-fully-proven/stieltjes-log-weld.md`
- **Suggested row (assign the next #, e.g. #123):**
  > the **Stieltjes–log weld / no-isolation theorem**: in the friable-auxiliary pairing `H=F·(s−1)ζ`,
  > `[H]_N = c_N/N! + Σ_{n<N}(c_{N−n−1}/(N−n−1)!)(−1)^nγ_n/n!`, so each `γ_n` carries a positive-weight
  > log-`p` transcendental coefficient `c_{N−n−1}∈R_{N−n−1}`; killing all weights forces `F≡const`
  > (lin. indep. of `\{n^{−s}\}`). **Nontrivial auxiliary ⟺ nonzero log-`p` residual** ⟹ the Stieltjes
  > transcendence cannot be isolated from the multiplier-log transcendence; the honest G2/DSS-cross target
  > is the **joint** `trdeg_ℚ ℚ(\{log p\}∪\{γ_n\})=∞` (Schanuel-entangled); = the seam (#69/#71) realized
  > inside the construction.
- **Type/Priority/Bucket:** `THEOREM (paper)` · `FOUNDATIONAL` ·
  `[[bucket-the-seam-archimedean-obstruction]]` / `[[G2-multi-q-siegel-shidlovsky]]`. Door grade **BRIDGE**.

## 2. Update the G2 / Stieltjes rows

- **Rows #18/#19** ([[G2-multi-q-siegel-shidlovsky]]): note the obstruction-C **concretization** (an
  explicit Nesterenko measure `H_C`) and the **reframe to the joint target** `{log p}∪{γ_n}`
  (Schanuel-entangled) — the `γ_n`-in-isolation phrasing is superseded. Source:
  `../1-in-progress/baker-for-stieltjes.md` (§B–§E) + the new weld card.
- Optionally cross-link from the seam bucket / #69 / #71: the weld is the analytic-Diophantine twin of
  Wheeler's finite-free metric weld `S_d=A_d^{−1/2}δH_d A_d^{−1/2}` (#104 annotation).

## 3. Pipeline state (FYI, no ledger action needed)

- `baker-for-stieltjes.md` is in **1-in-progress** (Professor): obstruction C concretized to `H_C`; pillar
  factorization A(supplied)∧B′(DeWitt)∧H_C(me); residual = the joint, Schanuel-entangled `H_C` + the §E
  budget. The provable structural pieces have been split out (`corank-transcendence-continuation-bridge`,
  now `stieltjes-log-weld`); the in-progress card holds only the open wall.
</content>
