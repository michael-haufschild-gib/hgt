# The wild (Source-A) data has a uniform per-place Γ_v carrier — {Γ_ℝ, Morita Γ_p} all Source-A

- **ID:** per-place-source-a-gamma-carriers
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — a structural extension of the multiplier dichotomy; grade **BRIDGE**.
- **Priority:** FOUNDATIONAL (grounds the p-adic F₁ route with an explicit arithmetic carrier)
- **Source:** Wheeler's p-adic F₁ route (chat id=268: `{Frob_p}`, Morita `Γ_p`, Diamond's p-adic Euler
  constants); `multiplier-dichotomy-theorem.md` (#134, polynomial multiplier ⟹ non-CC ⟹ Source A),
  `two-sources-of-hypertranscendence.md` (#130), `completed-base-archimedean-coordinate.md` (#132, R⁺'s
  archimedean Γ-symbol `g=Γ_ℝ`).
- **Statement.** The archimedean Source-A Γ-symbol of R⁺ (`g=Γ_ℝ(s)=π^{−s/2}Γ(s/2)`, #132) is **not the
  unique** Source-A object: Morita's p-adic Gamma `Γ_p` (one per prime) is **also Source-A**. Concretely,
  `Γ_p` satisfies the **polynomial-multiplier** recurrence
  `   Γ_p(n+1) = −n·Γ_p(n)  (p∤n),   = −Γ_p(n)  (p|n)`
  (multiplier `−s`, degree 1 — verified combinatorially from `Γ_p(n)=(−1)^n∏_{0<j<n,\,p∤j}j`), so by the
  multiplier dichotomy (#134) it is **non-CC = Source A**. Hence the **wild / Source-A Γ-data has a uniform
  per-place carrier `{Γ_v}_v`**: `Γ_ℝ` at `v=∞` and `Γ_p` at each finite `v=p`, all polynomial-multiplier
  (Source A). The wild data is **not confined to ∞** — it has an explicit arithmetic home at every place.

## Goal
Give Wheeler's p-adic F₁ route (the missing single Frobenius = the synthesis of `{Frob_p}`/`{Γ_p}`) an
**explicit, verified carrier** for the wild data, by extending the multiplier dichotomy (#134) and the R⁺
Γ-symbol (#132) from the single archimedean place to **all places**. This is the structural floor under the
value-lift; the value-lift (the complex↔p-adic comparison) is the open apex (Wheeler's, below).

---

## §1 Morita `Γ_p` is Source-A `[PROVED HERE — combinatorial, verified]`
Morita's p-adic Gamma on positive integers: `Γ_p(n)=(−1)^n∏_{0<j<n,\,p∤j}j`. Its successive ratio:
```
   Γ_p(n+1)/Γ_p(n) = −·(n-th factor if p∤n, else 1) = −n   (p∤n),   = −1   (p|n).      [verified, exact]
```
So `Γ_p` satisfies a first-order difference equation with **polynomial multiplier `−s`** (the p-adic analogue
of `Γ(z+1)=zΓ(z)` and of `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`, #132). By the multiplier dichotomy (#134): a non-constant
polynomial multiplier is **not** constant-up-to-coboundary (CC), hence `Γ_p` is **non-CC = Source A** — the
hypertranscendental side, exactly like `Γ`/`Γ_ℝ`. ∎ `[mpmath/integer check: p=3,5, n=1..13, exact]`

## §2 The uniform per-place Γ_v family `[the structural payload]`
Collecting §1 with #132/#134:
```
   place v        Γ-symbol Γ_v        recurrence multiplier      grade
   ----------     -------------       -------------------------  --------
   ∞ (archimedean) Γ_ℝ=π^{−s/2}Γ(s/2)  s/2π   (polynomial)        Source A  (#132/#134)
   p (finite)      Morita Γ_p          −s     (polynomial)        Source A  (§1)
```
So **every place carries a Source-A Γ_v** with a polynomial multiplier. The Source-B / CC objects are the
prime **dilations** `σ_p` (multiplier `p^{−1}`, constant), which are a *different* structure (the Euler/Bohr
multiplicative lane), not the `Γ_v`. **Correction to the naive reading of #130/#134** ("∞ is the unique
Source-A place"): that is the statement about the **dilation lane** (`σ_p` Source-B, `σ_∞` the archimedean
shift). On the **Γ-symbol lane**, Source-A is **universal** — `Γ_v` at every `v`. The wild data is spread over
all places, with `{Γ_p}` its finite-place carriers.

## §3 The open apex — the complex↔p-adic comparison = F₁ `[Wheeler's, flagged]`
What this card does **not** prove (and explicitly hands to Wheeler's p-adic route): that the archimedean wild
value `γ_E` (and the `{γ_n}`) is **synthesised from / comparable to** its p-adic avatars (Diamond's p-adic
Euler constants via `Γ_p`). That comparison is a **period comparison** (Gross–Koblitz-type: Gauss sums =
`Γ_p`-values) — the **value-lift**, the missing F₁, **open / FIELDS MEDAL**. This card supplies only the
**existence of the per-place Source-A carriers** `{Γ_v}`; gluing them (the comparison) is the apex. *(Honest
scope: I do not claim `σ_p` and `Γ_p` are two realizations of one object — that identification IS the open
comparison, not a theorem.)*

## §4 Door passport — BRIDGE
- **Door-2:** §1–§2 are the multiplier dichotomy (#134) applied to a second family of classical objects
  (Morita `Γ_p`); single-parent (p-adic analysis + #134). **BRIDGE.** The native/apex content is §3 (the
  comparison), open.
- **Door-5:** over `F_q(C)`, the wild Γ-data is absent (corank 1, #121); there is no `Γ_v` lane, so this
  per-place Source-A structure is **number-field-only** — what ℚ adds, now seen to be spread over all places
  (∞ **and** the p-adic shadows), not just ∞.

## Gates
- [x] 0 → 1  in-progress: `Γ_p` Source-A proved (§1, verified); the per-place Γ_v family (§2); the apex (§3)
  flagged; Door passport.
- [x] 1 → 2  fully-proven: §1 (Morita `Γ_p` polynomial multiplier ⟹ Source-A, #134) verified combinatorially;
  §2 the uniform per-place Source-A Γ_v family + the dilation-lane/Γ-symbol-lane correction; grade BRIDGE. The
  comparison/value-lift (§3) is explicitly out of scope (Wheeler's open F₁).
- [ ] 2 → 3  formalized: PARTIAL Lean anchor done for the finite integer recurrence
  (`../3-formalized/morita-gamma-finite-recurrence.md`, `moritaGammaFinite_succ`). Remaining unformalized
  payload: p-adic analytic continuation, the Source-A grade via #134, and the uniform per-place `Γ_v`
  family/comparison layer.
- [ ] 3 → 4  publication-ready: folds into the archimedean-generator / F₁ exposition as the per-place wild carrier.

## Cross-references
- Wheeler's `relative-exponential-apex` (the p-adic F₁ route, id=268) — this is its verified carrier floor; the
  value-lift/comparison (§3) is its apex.
- `multiplier-dichotomy-theorem.md` (#134), `two-sources-of-hypertranscendence.md` (#130) — the dichotomy this
  applies; `completed-base-archimedean-coordinate.md` (#132) — the `Γ_ℝ` symbol `g` this extends to `{Γ_v}`.
- `computations/2026-06-19-morita-gamma-p-source-a.py` — the recurrence verification.

## Log
- 2026-06-19 — Professor: created from Wheeler's p-adic F₁ route (id=268). **Verified** Morita `Γ_p` has
  polynomial multiplier `−s` (combinatorial, exact) ⟹ Source-A by #134; so the wild Γ-data has a **uniform
  per-place carrier `{Γ_v}`** (Γ_ℝ at ∞, Γ_p at each p), extending R⁺'s single Γ-symbol. **Corrected my own
  chat overstatement** (id=276→277): `σ_p` (Source-B dilation) and `Γ_p` (Source-A p-adic Γ) are not literally
  two realizations of one object — that comparison IS the open F₁ (Gross–Koblitz period, Wheeler's value-lift,
  §3). Banked only the verified carrier existence (BRIDGE); the comparison is the apex. Door-5: number-field-only.
  → 2-fully-proven.
- 2026-06-19 — Leaner: added the partial formalized anchor `../3-formalized/morita-gamma-finite-recurrence.md` for the exact finite Morita recurrence. Lean theorem `moritaGammaFinite_succ` proves the two recurrence branches from the finite product formula. The parent remains in `2-fully-proven`; p-adic analytic continuation, Source-A classification via #134, and the uniform per-place `Γ_v` payload are still paper-level.
