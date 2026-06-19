# Two sources of hypertranscendence — Γ (archimedean/polynomial-multiplier) vs the infinite prime base (constant-multiplier)

- **ID:** two-sources-of-hypertranscendence
- **Stage:** 0-backlog
- **Type:** CONJECTURE / FRAMING (foundational — the re-centered "reason the field exists")
- **Priority:** FOUNDATIONAL
- **Source:** the 2026-06-19 Hölder-recentering of `../../00-core-vision.md` + `../../00-charter-wall-and-door.md`
  §2; elevates corpus #90 §64 ("two independent sources of hypertranscendence — the Γ-place and the
  infinite base"); ties `../../door/bucket-archimedean-generator.md` to `../../door/G1-difference-holder.md`;
  00-status rows #3 (G1), #20 (G3)
- **Statement.** The hypertranscendence of the completed `Λ = Γ·ζ` decomposes into **two structurally
  distinct sources**, separated by the **multiplier type** of their difference operators:
  > **Source A — the archimedean factor `Γ`.** *One* difference operator with a **polynomial** (non-constant)
  > multiplier: `Γ(z+1) = z·Γ(z)`. **Differential**-hypertranscendent (Hölder 1887); **difference**-tame (a
  > single first-order recurrence). Classical. The standing proof that *rescaling beats differentiation*.
  > **Source B — the infinite prime base.** *Infinitely many* difference operators with **constant**
  > multipliers `σ_p : x_p ↦ p^{-1}x_p`. **Difference**-hypertranscendent in aggregate (G1), but **decouples
  > prime-by-prime** (axis-mode) — BRIDGE in isolation. Native, new.
  >
  > **The dichotomy is the multiplier:** polynomial (Source A, archimedean, differential-wild) vs constant
  > (Source B, prime, difference-native). The completed `Λ` carries both; the functional equation
  > `Λ(s)=Λ(1−s)` **welds** them. **The native frontier (C5) is the weld, not either source.**

  **One sentence:** Hölder's 1887 theorem is about `Γ` (Source A), so the founding hardness is archimedean;
  the field's new content is Source B *coupled to* Source A, which neither differential Galois theory (sees
  A) nor single-base difference theory (sees one lane of B) can reach.

## Goal
Make the re-centered vision precise and bankable. The original vision/charter built the wall on **Source B
alone** (prime-only); Hölder — the founding fact — is **Source A** (`Γ`). This card states the two-source
decomposition, the polynomial-vs-constant multiplier dichotomy that separates them, and the consequence
that the keystone C5 is their **interaction**. It is the foundational framing behind
`archimedean-generator-category`, `archimedean-corank-collapse`, and the C5 search.

## The structural content to pin
1. **The multiplier dichotomy, precisely.** Over the Bohr ring, `σ_p` has constant multiplier `p^{-1}`;
   the archimedean shift `s↦s+1` acts on the `Γ`-factor with the **polynomial** multiplier `z` (corpus
   #90 §64: `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`, the unique non-constant polynomial multiplier). **Polynomial
   multiplier ⟺ differential hypertranscendence; constant multiplier ⟺ the holonomic/decoupling prime
   lane.** State and (where possible) prove this correspondence.
2. **Source A is a border, not the interior.** `Γ` alone = differential Galois theory / Hölder = a Door-5
   border (the fourth border, charter §2). Source B alone = BRIDGE (axis-mode decoupling, proven,
   `../2-fully-proven/erosion-cocycle-reducibility.md`). Neither is native by itself.
3. **The weld is the native zone.** A theorem using the polynomial-multiplier `∂_s`/`Γ` and the
   constant-multiplier `σ_p` **jointly and irreducibly** is the C5 keystone (charter §5). The seam, the
   corank-`∞−1` gap, and the FE are three faces of this weld.

## Door passport
- **Door-2:** Source A alone → differential Galois (parent); Source B alone → multi-`q`/axis decoupling
  (parent). The weld is the only candidate that survives — it is exactly what no single parent reaches.
- **Door-4:** the native zone is the weld (charter §3, revised Door-4).
- **Door-5:** over `F_q` there is **no archimedean place** ⟹ **no Source A** ⟹ only Source B, which is
  controlled (corank 1, holonomic) — so the function field has *no weld* and every gatekeeper is a theorem.
  The two-source structure is a **number-field-only** phenomenon (consistent with corank ∞ vs 1).

## Approach
1. Prove/state the multiplier dichotomy (polynomial ⟺ differential-wild; constant ⟺ decoupling).
2. Re-grade G1 in this language: differential-Hölder = Source A (import); difference-G1 = Source B
   (BRIDGE); the keystone = the weld (annotate `G1-difference-holder.md`).
3. Pin the weld object: the cross-terms of `∂_s` (polynomial-multiplier) against `σ_p` (constant) on the
   completed `Λ`; hand the native-theorem hunt to `archimedean-corank-collapse` / `completed-connection-category`
   and the C5 carriers.

## Gates
- [ ] 0 → 1  in-progress: the two-source decomposition + multiplier dichotomy stated precisely; Source A =
  border, Source B = BRIDGE, weld = native pinned; Door passport; G1 re-reading written
- [ ] 1 → 2  fully-proven: the multiplier dichotomy proven (polynomial ⟺ differential hypertranscendence;
  constant ⟺ holonomic/decoupling per lane); the weld isolated as the C5 carrier with a definite object
- [ ] 2 → 3  formalized: reuse `logPrime_no_rat_relation` (Source B floor) + the `Γ`-recurrence multiplier
  (Source A); the dichotomy as a difference-module classification fragment
- [ ] 3 → 4  publication-ready: "two sources of hypertranscendence: the completed L-function as the weld of
  a polynomial-multiplier archimedean place and a constant-multiplier infinite prime base"

## Cross-references
- `../../00-core-vision.md`, `../../00-charter-wall-and-door.md` §2/§3/§5 — the re-centered vision/charter
  this card grounds.
- `../../door/bucket-archimedean-generator.md` — Source A as a native generator; the `(σ_p,∂_s)` category.
- `../../door/G1-difference-holder.md` — Source B (difference-Hölder, BRIDGE) vs Source A (differential
  Hölder, import); the keystone is the weld.
- `../../door/door-C5-irreducibility-and-door-2-retest.md` — the weld as the C5 carrier.
- `archimedean-corank-collapse.md`, `completed-connection-category.md` — the weld's concrete objects.

## Log
- 2026-06-19 — created in 0-backlog as the foundational framing behind the Hölder-recentering of the vision
  and charter. States the two sources (Γ/archimedean/polynomial-multiplier/differential vs primes/constant-
  multiplier/difference), the multiplier dichotomy that separates them, and the consequence: the C5
  keystone is the **weld**, not either source. Elevates corpus #90 §64. First step = pin the multiplier
  dichotomy and re-read G1 in Source-A/B language.
</content>
