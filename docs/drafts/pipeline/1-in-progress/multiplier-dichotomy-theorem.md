# The multiplier-dichotomy theorem — constant ⟹ holonomic/decoupling, polynomial ⟹ differential-hypertranscendent

- **ID:** multiplier-dichotomy-theorem
- **Stage:** 0-backlog
- **Type:** THEOREM (paper) target — the **first provable theorem** of the reorientation
- **Priority:** FOUNDATIONAL
- **Source:** the framing card `two-sources-of-hypertranscendence.md` (this is its extractable theorem);
  Hölder 1887 (Γ); van der Put–Singer + Adamczewski–Dreyfus–Hardouin (the difference→differential bridge);
  00-status rows #2, #3
- **Statement (to shape).** A rank-1 difference module `(M, σ)` over the relevant base, `σ e = a(z)e`, splits
  by the **multiplier type** of `a(z)`:
  > **(constant multiplier)** `a ∈ ℂ^×` ⟹ `M` is **holonomic / decoupling**: its solution is a
  > `q`-hypergeometric / Euler-type factor satisfying a finite linear `q`-difference equation, with an
  > **abelian, finite-dimensional** difference-Galois group (`⊂ 𝔾_m`). This is the **prime lane** (`σ_p`,
  > `a=1/p`): Source B, per-lane holonomic, the axis-mode/decoupling regime.
  > **(non-constant polynomial multiplier)** `a(z) ∈ ℂ[z]∖ℂ` ⟹ `M` is **differential-hypertranscendent**:
  > its solution (a `Γ`-type product) satisfies **no algebraic differential equation**. This is the
  > **archimedean lane** (`σ_∞`, `a = s/2π`): Source A, Hölder 1887.

  **One sentence:** the constant-vs-polynomial multiplier is *exactly* the line between Source B (prime,
  difference-tame per lane, BRIDGE) and Source A (archimedean, differential-wild, Hölder) — and it is a
  **theorem**, the first the reorientation can actually prove.

## Why this is the foundational first theorem
The whole Source-A/Source-B architecture (vision, charter §2, N1⁺) is currently a *framing*. This card turns
the framing's central dichotomy into a **provable, Lean-certifiable** statement — the reorientation's first
banked result. It also sharpens the charter's borders: the polynomial-multiplier place is *why* `Γ` is a
differential-Galois border (Source A alone), and the constant-multiplier places are *why* the prime lanes
decouple (Source B alone is BRIDGE).

## The proof, sketched (what to verify)
- **Constant case:** `σ e = a e`, `a∈ℂ^×`, `a` not a root of unity (`a=1/p`): the solution is the
  geometric/Euler factor; `q`-difference-algebraic of order 1; group `⊂𝔾_m`. Standard (vdPS); the per-prime
  base case is already ledgered (`localEulerFactor_q_difference`, G1 bucket #67 §18).
- **Polynomial case:** `σ e = a(z)e`, `deg a ≥ 1` (`a=s/2π`, the `Γ`-recurrence): the solution is a `Γ`-type
  product. **Differential hypertranscendence** follows from Hölder's method, or — for the difference→
  differential transfer — from **Adamczewski–Dreyfus–Hardouin** (a difference equation with non-constant
  multiplier whose solution were differentially algebraic would force a forbidden differential-difference
  relation). Pin the exact theorem invoked; isolate what is *import* (Hölder/ADH) vs *proved here* (the
  dichotomy statement and its base cases).
- **The dichotomy itself** (the clean if-and-only-if on `a(z)`'s degree) is the new content; the two cases
  rest on a classical theorem each, but the **statement that multiplier-degree is the dividing line** is the
  reorientation's organizing theorem.

## Door passport
- **Door-2:** each *case* is a parent (vdPS / Hölder–ADH) ⟹ the cases are BRIDGE/IMPORT. The **dichotomy as
  the Source-A/B divide** is the framing payload, not itself C5 (the C5 weld uses both lanes jointly — the
  cross-term card). Grade honestly: a clean BRIDGE-grade foundational theorem, like G1.
- **Door-5:** over `F_q` every place is constant-multiplier (Frobenius) ⟹ only the constant case ⟹ no
  Source A ⟹ holonomic/rational (Weil). The dichotomy predicts the `F_q`/ℚ split.

## Gates
- [ ] 0 → 1  in-progress: the dichotomy stated precisely; both cases' classical inputs pinned (vdPS;
  Hölder/ADH); import-vs-proved-here split written; Door passport
- [ ] 1 → 2  fully-proven: both cases proven (constant ⟹ holonomic/abelian; polynomial ⟹ differential-
  hypertranscendent), the dichotomy as the multiplier-degree divide established; `F_q` shadow
- [ ] 2 → 3  formalized: Lean — the constant-case base (`localEulerFactor_q_difference`, already ledgered)
  and the multiplier-degree split; the polynomial case likely an import-gap (Hölder/ADH) — mark it
- [ ] 3 → 4  publication-ready: "the multiplier-degree dichotomy of rank-1 difference modules: the
  archimedean–prime divide"

## Cross-references
- `two-sources-of-hypertranscendence.md` — the framing this theorem grounds (the dichotomy is its 1→2 gate,
  extracted here as a dedicated provable target). **Coordinate; this is the theorem-execution.**
- `gamma-module-construction.md` — the polynomial-multiplier worked example (`M_∞`, `a=s/2π`).
- `../../door/G1-difference-holder.md` — the constant-case (Source B) per-prime ledger floor.

## Log
- 2026-06-19 — created in 0-backlog as the **first provable theorem** of the reorientation: the
  multiplier-degree dichotomy (constant ⟹ holonomic/decoupling = Source B; polynomial ⟹ differential-
  hypertranscendent = Source A = Hölder). Extracted from the `two-sources` framing as a dedicated,
  Lean-certifiable target. First step = pin the two classical inputs (vdPS; Hölder/ADH) and the
  import-vs-proved-here split.
</content>
