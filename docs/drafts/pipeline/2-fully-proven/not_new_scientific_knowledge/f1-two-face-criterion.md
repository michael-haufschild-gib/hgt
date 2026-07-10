# The F₁ obstruction decomposes into two orthogonal invariants: flow-imbalance D ⊕ multiplier-corank

- **ID:** f1-two-face-criterion
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper, consolidation) — grade **BRIDGE (substrate)**. Proven: the two-face decomposition,
  the F_q/ℚ values, and necessity. Sufficiency = open D5 frontier.
- **Priority:** FOUNDATIONAL
- **Source:** consolidation of DeWitt's **flow face** (`../1-in-progress/moonshot-2pi-monodromy-frobenius.md`
  iter-10/11 — the global orbit-degree `D` = ω/index/ground-state) + Professor's **corank face**
  (`archimedean-corank-no-collapse.md`, #399) + #191 (RH/DSS decoupling) + #130, #1, #121. Chat id=399/401.
- **Statement.** The obstruction to a single base / single Frobenius (`F₁`) decomposes into **two orthogonal
  invariants** of the scaling structure:
  - **flow-imbalance `D`** = the global σ-orbit-degree of the scaling multiplier (= the ω / index /
    ground-state — the realization face, #191);
  - **multiplier-corank** = the prime value-group rank (`{log p}` ℚ-independence — the DSS / transcendence
    face).

  | place field | flow-imbalance `D` | corank | F₁ |
  |---|---|---|---|
  | over `F_q` | `0` | `1` | **exists** (single Frobenius, Deligne) |
  | over `ℚ`  | `+1` (purely archimedean) | `∞` (`{log p}` LI) | **missing** |

  > **Criterion.** `F₁` exists ⟺ (`D = 0`) ∧ (corank finite). The two coincide (→ trivial) over `F_q` and
  > **split** over `ℚ` (flow-dim 1 vs corank ∞); they are orthogonal (`∂_s` cannot collapse corank, #399).

## Proven content
- **`D` over ℚ = +1, purely archimedean:** archimedean Γ multiplier orbit-degree `+1` (`div=[0]−[∞]`, #130);
  every finite place orbit-degree `0` (dilation `σ_p` constant multiplier; the Γ-symbol attempt Morita `Γ_p`
  is unit-valued, `../5-failed/per-place-source-a-gamma-carriers.md`). [DeWitt]
- **`D` over `F_q` = 0:** no archimedean place (no Γ). [Door-5]
- **corank over ℚ = ∞:** `{log p}` ℚ-independent (unique factorization, #1); `∂_s ∈` completion of `⟨θ_p⟩` is a
  self-removing relation and cannot collapse the ∞-independent system (`archimedean-corank-no-collapse`, #399,
  three arguments: product-formula dependence, self-removing relation, finite-enrichment-can't-collapse-∞).
  [Professor]
- **corank over `F_q` = 1:** rank-1 value group `⟨q⟩` (#121). [banked]
- **Orthogonality:** flow-dimension (# archimedean derivations = 1) and multiplier-corank are independent;
  coincide (→1) over `F_q`, split (1 vs ∞) over ℚ. [Professor #399]
- **Necessity:** a genuine `F₁` (single Frobenius) is an **automorphism** (invertible ⟹ no one-sided
  imbalance ⟹ `D=0`) generating a **rank-1** value group (corank finite). So `F₁ ⟹ (D=0) ∧ (corank finite)`.
  [structural — airtight]

## Open (the D5 frontier)
- **Sufficiency** (`D=0 ∧ corank finite ⟹ F₁ exists`): verified at `F_q` (Deligne). The general `⟸` — that
  these are the **only** obstructions, i.e. the construction of the absolute / `F₁` object — is the open **D5**
  frontier. Over ℚ both invariants are nontrivial (`D=+1`, corank `∞`), with **corank `∞` the dominant /
  binding obstruction** (#191, the DSS axis), so the criterion correctly predicts `F₁` missing.

## Significance — #191 made precise
The two faces **are** the #191 RH/DSS decoupling, now with the `F₁` criterion making it exact:
- **flow / realization axis** (`D`; RH-side polarization; DeWitt's ω lane) — *necessary*, the "1";
- **corank / DSS axis** (value-independence; Wheeler's apex) — the *dominant* `∞`.
RH-relevant positivity lives on the flow face; transcendence/DSS on the corank face; `F₁` needs **both**, and
only `F_q` has both trivial.

## Door passport — BRIDGE (substrate)
- **Door-2:** the `F_q` case is Deligne; `D` is the #130 orbit-degree; corank is `{log p}` LI — each a parent.
  The **consolidation** (two orthogonal faces; `F₁` needs both) is a **D2 unification** (one criterion across
  `F_q`/ℚ), not a single-parent theorem.
- **Door-5:** over `F_q` both faces coincide at `1`/`0` (the single Frobenius) — the cleanest confirmation.

## Gates
- [x] 0 → 1  in-progress.
- [x] 1 → 2  fully-proven: the orthogonal flow/corank decomposition, the `F_q`/ℚ values, necessity. Grade
  BRIDGE (substrate). Sufficiency = open D5 (flagged, out of scope).
- [ ] 2 → 3  formalized: `D` and corank ride existing anchors (#130 orbit-degree; `linearIndependent_log_primes`
  #1; #121 degree collapse); the two-face statement is a packaging over them.
- [ ] 3 → 4  publication-ready: folds into the seam / `F₁` exposition as the two-face decomposition.

## Cross-references
- `../1-in-progress/moonshot-2pi-monodromy-frobenius.md` (iter-10/11) — the flow face (`D` = ω/index).
- `archimedean-corank-no-collapse.md` (Professor #399) — the corank face (the proven no-collapse).
- `seam-two-lattices-archimedean-residue.md` (#128) — the eigenvalue/CC-class seam reading (complementary).
- `../5-failed/per-place-source-a-gamma-carriers.md` — the per-place falsification (every finite place `D=0`).

## Log
- 2026-06-19 (DeWitt) — banked the two-face consolidation per Professor's suggestion (id=401). **Proven:** the
  orthogonal flow/corank decomposition, the `F_q`/ℚ values, and necessity (`F₁ ⟹ both trivial`). **Open (D5):**
  sufficiency (the general `⟸`). Makes #191's RH/DSS decoupling precise. Grade BRIDGE (substrate).
