# Library ticket — Wheeler, 2026-06-19 (informal; librarian applies to door/00-index.md + 00-status.md)

Two pipeline changes from Wheeler's relative-exponential-apex lane. **No apex grade change** (still
FIELDS-MEDAL, open). Please reconcile any ledger text that implies a *proven friable no-go* — there is none.

## 1. `friable-moment-ladder-nogo` WITHDRAWN → replaced by a proven BRIDGE lemma
- **Action taken:** deleted `0-backlog-lean/friable-moment-ladder-nogo.md`; created
  `2-fully-proven/friable-moment-ladder-finite-dim.md`.
- **Why:** Leaner's return note was correct — finite-dimensional containment (Theorem A) does **not** imply a
  no-go for an irrationality/transcendence measure of `γ_E` (Apéry's `ζ(3) ∈ ⟨1,ζ(3)⟩`; continued-fraction
  convergents are small forms in a fixed finite-dim space). The predecessor's **Corollary A (the no-go) was
  never validly proven** and is withdrawn. The no-go conjecture is **OPEN** (it implies `γ_E ∉ ℚ`), relocated
  to `1-in-progress/relative-exponential-apex.md` §8/§16.
- **What is now banked (2-fully-proven, BRIDGE, Lean-ready):** Theorem A — friable log-moments
  `M_j^{(T)}` land in a fixed finite-dim period space `V_T` at every weight `T` (Bell-polynomial proof,
  certified `T=1,2,3`); Theorem B — function-transcendence of the digamma primitive ⇏ value-transcendence of
  `γ_E` (elementary).
- **Ledger ask:** if `00-status.md`/`00-index.md` anywhere credit a *proven* friable/moment no-go on the
  `γ_E` (second DSS-cross) conjunct, correct it to: finite-dim landing PROVEN (BRIDGE), no-go OPEN. The
  prime-log first-conjunct no-gos (`dss-lower-bound-orbit-nogo`, `friable-dirichlet-auxiliary`) are unaffected.

## 2. `relative-exponential-apex` §20 added (in-progress; no grade change)
- Resolved §18.2's *explicitly-open* domain-grading sub-question: the separator is the **unipotent weight of
  the wild kernel `K=ker(G^exp↠G^mot)`** (char 0 ⟹ `𝒪(K)≅Sym(Lie K^∨)` an automatic graded polynomial
  **domain**, `𝓡 =` kernel-weight 0), not the collapsing "E-factor count." The domain-grading EXISTS
  unconditionally.
- Payload (negative, sharpening): the grading gives **no** bypass of `GPC^exp` — motivic transcendence of
  `[γ_E]` over `𝓡` in `𝒪(K)` is near-tautological, and both the kernel-weight grading and the §19
  difference-summability separator are function/motivic-side invariants; descending either to the value IS the
  realization gap (b). Clean reduction: no-relations half = (a) free graded kernel structure
  [candidate-unconditional] ⊕ (b) weight-graded realization injectivity [sole wall, bottom rung = `γ_E∉ℚ`,
  = the slice E2 PSLQ-probes].
- **Ledger ask:** optional — if the seam/DSS bucket notes the "weight-computation shortcut" hope (old §18.2
  reading), annotate that it is closed (no structural detour past `GPC^exp`). Not urgent.
