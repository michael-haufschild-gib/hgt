# F_1 Hodge–Riemann via the q→1 limit — the regularized tangent of Deligne's Weil II

> **⚠ rh-corp reconciliation (2026-06-19): NOT NEW — `docs/rh-corp` route #3** (q→1 Deligne/Hurwitz tower,
> ranked **10–15%**; `speculation.md` §2). The "obstruction = the q-family geometry" verdict is rh-corp's own:
> *"the existence problem is almost the whole F₁ object in disguise."* Per rh-corp the live route is the
> **faithful κ₋=0 source proof** (#1); measured/limit positivity is dust-blind (`next_round.md:57–61`).
> **Re-derivation, not a fresh lead.**

- **ID:** f1-hodge-riemann-qto1-limit
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (attack route on the bedrock's open core) — **open**
- **Source:** the open core of `f1-hodge-index-theorem.md`; the sibling route `f1-hodge-riemann-modular-route.md`;
  corpus #90 (B35 `q→1` / Kurokawa absolute zeta); imports: Deligne Weil II (each `q`), Faltings/Hriljac
  (Arakelov Hodge index over ℚ), Soulé / Connes–Consani / Manin (F_1 as `q→1`), Kurokawa (absolute zeta)
- **The route.** The F_1 Hodge–Riemann positivity has **two proven templates** bracketing it, and is their
  meeting point:
  > **Template 1 — Deligne (each `q>1`):** the Frobenius eigenvalues on `H¹_{ét}(C/F_q)` satisfy
  > `|α_i|=q^{1/2}` (purity = the Hodge index over `F_q`). Holds for **every** finite `q`.
  > **Template 2 — Faltings/Hriljac (ℚ, finite-dim):** the Arakelov intersection form on an arithmetic
  > surface has **Hodge-index signature `(1,n)`** — the `(1|∞)` shadow of the Weil form (#94/#137) is its
  > regularized version.
  >
  > **The F_1 target is the `q→1` limit of Template 1, regularized as in Template 2.** As `q→1` the eigenvalues
  > `α_i → 1` (purity becomes vacuous at leading order), so the RH content sits in the **first-order /
  > tangent** term: the **rescaled** eigenvalues `β_i = \lim_{q→1}(α_i − \sqrt q)/(\sqrt q\,\log q)` are the
  > **ζ-zeros**, and the F_1-purity is `\{β_i\}⊂iℝ` — the **tangent of Deligne's purity at `q=1`** (Soulé/
  > Kurokawa regularization). So **F_1 Hodge–Riemann = the regularized `q→1` derivative of Weil II.**

  **Verdict reached:** the open core is **bracketed by two proven theorems** (Deligne `q>1`, Faltings ℚ) and
  is precisely their **regularized `q→1` interpolation**. The obstruction is localized: Deligne's proof is
  **per-`q`** and does not deliver the `q→1` **derivative** — the missing structure is the **`q`-family /
  the F_1-curve as the degenerating limit** (the "tangent space at `q=1`"). open; but now a
  limit of proven theorems, not a void.

---

## §1 Why `q→1` is the F_1 limit, and where RH hides `[the reduction]`

`ζ_{C/F_q}(s)=\frac{P(q^{-s})}{(1−q^{-s})(1−q^{1-s})}`, `P(t)=∏_i(1−α_i t)`, `|α_i|=q^{1/2}` (Deligne). As
`q→1`:
- denominators `→0` (double); `P`'s zeros `α_i→1`; the zeta **degenerates** — handled by **Kurokawa's
  absolute zeta `ζ_{F_1}`** (the regularized limit, corpus #90).
- purity `|α_i|=q^{1/2}→1` is **vacuous at leading order**; the content is the **tangent**: write
  `α_i=\sqrt q\,e^{iθ_i}` (purity = `θ_i∈ℝ`); the rescaled `θ_i/\log\sqrt q → γ_i` give the **ζ-zeros**, and
  **F_1-purity = `γ_i∈ℝ` = RH**. So **RH is the first-order (`d/dq` at `q=1`) shadow of Deligne's purity.** ∎

## §2 The bracket — bounded by two proven theorems `[the structure]`

| | statement | status |
|---|---|---|
| `q>1` (Deligne) | `θ_i∈ℝ` (Frobenius on the circle) | **proven** |
| `q→1` regularized (F_1) | `γ_i∈ℝ` (zeros on the line) = **RH** | **open (the target)** |
| ℚ Arakelov (Faltings) | intersection form has signature `(1,n)` | **proven** (but finite-dim / not the ζ-zeros) |

The F_1 Hodge–Riemann is the **interpolation**: it inherits *purity* from Deligne (each `q`) and the
*`(1,n)` Hodge-index signature* from Faltings — both proven — and must combine them in the regularized
`q→1`/infinite-dim limit. **The positivity is "true on both sides"; the gap is the limit/interpolation.**

## §3 The obstruction, localized `[honest]`

Deligne's purity is proven **per fixed `q`**; it gives no information about the **`q`-derivative** (the
`q→1` tangent), because the proof has no `q`-family structure — there is no "curve over the `q`-line." The
missing object is exactly the **F_1-curve as the limit/total space of the family `C/F_q` as `q→1`** (Soulé's
F_1-variety, Connes–Consani's arithmetic site, Durov's generalized schemes). So:
> **F_1 Hodge–Riemann ⟺ a uniform/differentiable-in-`q` Weil II**, whose `q→1` tangent is RH. The obstruction
> is the **`q`-family geometry**, not the positivity at any fixed point (which is Deligne).

## §4 Consistency with the modular route (the two attacks meet)
The regularization that defines the `q→1` limit is the **`ζ`-regularization** = the **modular/KMS structure**
(`f1-hodge-riemann-modular-route`): in Bost–Connes, `q` plays the role of the **temperature/symmetry**, and
`q→1` is a **critical-temperature limit**. So the `q→1` limit (Kurokawa) and the modular GNS positivity
(Tomita–Takesaki) are **the same regularization seen twice** — the absolute-zeta limit *is* the modular
state's partition function at the limiting temperature. The two routes should be developed together.

## §5 Door / grade / scope
- **The bracket (§§1–2) is BRIDGE/structural** — it places the target between two **proven** theorems
  (Deligne, Faltings) as their regularized `q→1` interpolation.
- **The open core (§3) is open** = a uniform/`q`-differentiable Weil II / the F_1-curve as the
  `q→1` family. **No proof claimed.** Value: the open core is now a **limit of proven theorems** with a
  **localized obstruction** (the `q`-family geometry), and it **meets the modular route** at the
  regularization (§4).

## Gates
- [x] 0 → 1  in-progress: the `q→1` reduction + where RH hides (§1); the two-template bracket (§2); the
  localized obstruction = the `q`-family geometry (§3); consistency with the modular route (§4); Door/scope.
- [ ] 1 → 2  the bracket banked: §1 (the tangent/rescaling) made rigorous against Kurokawa's `ζ_{F_1}`; the
  two templates (Deligne, Faltings) verified as the bounds; the obstruction stated as the lone residual.
- [ ] 2 → 3  formalized: the `F_q` purity floor (`functionField_esymm_FE`, `|α|=q^{1/2}`) and the
  Arakelov `(1,n)` signature shadow (`Q_W=𝔇`, #94).
- [ ] 3 → 4  publication-ready: "RH as the `q→1` tangent of Weil II, between Deligne and Faltings."

## Cross-references
- `f1-hodge-index-theorem.md` — the positivity this attacks; `f1-hodge-riemann-modular-route.md` — the
  sibling route (they meet at the regularization, §4).
- `f1-hodge-cohomology-construction.md` — the object; `deligne-weil-ii-transport-audit.md` — the `F_q` template.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — #90 (`q→1` / Kurokawa absolute zeta).

## Log
- 2026-06-19 — created in 1-in-progress and **worked** (Anti-LLM-Cage: a second attack route). Framed the
  F_1 Hodge–Riemann positivity as the **regularized `q→1` limit of Deligne's Weil II**, **bracketed by two
  proven theorems** (Deligne purity each `q>1`; Faltings Arakelov Hodge-index `(1,n)` over ℚ). RH = the
  **first-order `q→1` tangent** of purity (rescaled Frobenius angles → the zeros; Soulé/Kurokawa). **Localized
  obstruction:** Deligne is per-`q`, so the gap is the **`q`-family geometry** (the F_1-curve as the `q→1`
  limit) — not the positivity at any fixed `q`. **Meets the modular route** at the regularization (`q` =
  temperature; `q→1` = critical limit; Kurokawa `ζ_{F_1}` = the BC partition function). open;
  no proof claimed.
</content>
