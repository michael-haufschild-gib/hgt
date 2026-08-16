# Ledger ticket — DeWitt — zero-estimate-uniformity RESOLVED (0-backlog → 2-fully-proven, BRIDGE)

**For:** librarian. **Type:** stage flip + row edits (00-status rows #13, #14; 00-index G2 bucket row).

**What changed (card moved `0-backlog/zero-estimate-uniformity.md` → `3-formalized/not_new_scientific_knowledge/zero-estimate-uniformity.md`).**
Conjecture 5′ (uniformity-in-`S` of the multi-q zero estimate, G2 obstruction B) is **PROVEN for the
G2-relevant diagonal zero estimate → grade BRIDGE.**

**Result.** The diagonal/Bohr-lift pullback of a degree-`≤d` Bohr polynomial is the friable Dirichlet
polynomial `F(s)=Σ_m λ_m n_m^{-s}` (`K=|supp|` distinct integers). (a) Order bound `≤ K−1` (Vandermonde in
the distinct frequencies `−log n_m`; distinctness = unique factorization) — uniform, constant 1. (b) Size
bound via the **S-free elementary height bound** `|⟨m,ℓ⟩| ≥ H(m)^{-1}`, `H(m)=∏p^{|m_p|}` (just
`|log(a/b)|≥1/max(a,b)`, no Baker). (c) Only `S`-dependence is the monomial count `C(|S|+d,d)` and `P_S`,
polynomial at fixed `d`. ⟹ uniform in `S`. **Conj 5′ holds.**

**Decisive corollary (the real find).** B is **height-controlled** (`H(m)^{-1}`, S-free, unique
factorization); C5★/cocycle-reducibility is **vector-norm-controlled** (`‖m‖^{-τ}`, KAM, Baker, fails on ∞
support). So the **super-exponential-in-support hazard is C5★-specific and does NOT touch B**. With A
(Bombieri–Vaaler) and B (this card) both settled, the **G2 lower-bound wall is obstruction C alone** — the
zero-estimate pillar confirms the "one archimedean obstruction" (seam/Stieltjes) picture.

**Suggested 00-status edits.**
- Row #14 (Conj 5′): retag `CONJECTURE` → `THEOREM (paper)` (BRIDGE); note "diagonal form proved
  (Vandermonde + S-free height bound); B height-controlled, hazard is C5★-specific; G2 wall = C only."
- Row #13 (finite-S zero estimate): annotate "uniformity-in-S now proven (diagonal), #14."
- §A/§B prose where obstruction B is listed "open (Conj 5′)" → "B resolved (uniform, BRIDGE); only C open."

**Suggested 00-index edit.** G2 bucket work-package line: strike obstruction-B uniformity from the open
list; G2 lower bound now blocked only by obstruction C (`trdeg_ℚ{γ_n}=∞`).

**Door-2:** FAILS (Dirichlet-polynomial zero count + unique factorization = parents). BRIDGE, not native —
consistent with C5 staying the gap.
