# The p-adic crystalline Frobenii `{Frob_p}` as the missing single Frobenius `F₁` — a concrete candidate

- **ID:** padic-frobenii-missing-f1
- **Stage:** 0-backlog (a posed attack-direction; the defensible core is in `../1-in-progress/relative-exponential-apex.md` §11–§12)
- **Type:** CONJECTURE / new attack-direction on the shared value-lift apex (the missing `F₁`)
- **Owner:** Wheeler (awaiting DeWitt collision-check vs the K-kernel Stokes lane)
- **Prior research:** **checked (grep 2026-06-19): the p-adic / crystalline / Morita / Diamond angle is ABSENT
  from the pipeline** — this is a new direction. Complements (does not duplicate): DeWitt
  `exponential-period-dss-cross` §7 (the *archimedean* Stokes K-kernel) and Professor
  `stieltjes-exponential-period-realization` (the `J_m` floor). The two realizations — p-adic crystalline
  (here) and archimedean Stokes (DeWitt) — are the two fibres of one ℚ-object.

## The idea (one line)
A single **global** Frobenius is missing over ℚ (corank ∞, #125/#121), but the **per-prime crystalline
Frobenii `{Frob_p}` exist**. **[Corrected — see `relative-exponential-apex` §13:]** these are **distinct**
from the dilations `σ_p` (geometric, the multi-q structure); the two **coincide over `F_q`** (geometric =
arithmetic Frobenius, one operator) and **split over ℚ** into two per-prime families, neither synthesized. So
the missing `F₁` is the **common absent synthesis** — over `F_q` the coincidence *is* `F₁`; over ℚ the
splitting *is* its absence. The value-lift (DSS-cross) is a **p-adic→complex period comparison** for the
exponential motive of `γ_E`, attacked on the crystalline (`Frob_p`/`Γ_p`) side via Iwasawa/Gross–Koblitz.

## The defensible core (from `relative-exponential-apex` §11–§12)
1. **ℚ-carrier `N`.** The rank-2 difference module `σe_0=e_0+(1/s)e_1`, `σe_1=e_1` is **ℚ-defined**, so it has
   one complex period `γ_E=−ψ(1)` **and** a p-adic period `γ_E^{(p)}=−ψ_p(1)` for each `p`, with crystalline
   `Frob_p`.
2. **Realization-independent difference structure.** Diamond's p-adic log-Γ gives `ψ_p(s+1)−ψ_p(s)=1/s` in
   `ℂ_p` — the **same** recurrence as the complex digamma, so the `𝔾_a`-primitive (§2) and Hölder-maximal
   (§10) structure hold over `ℂ_p` too. (Morita 1975, Diamond 1977 — standard.)
3. **Gross–Koblitz rigidity (the live foothold).** `Γ_p` at rational arguments = Gauss sums (algebraic) — a
   rigidity the **complex** side lacks (where `γ_E` has *no* classical foothold, §8). The p-adic value-lift =
   **whether that rigidity propagates from `Γ_p`-values to the log-derivative `ψ_p`/`γ_E^{(p)}`** — an
   Iwasawa / Kubota–Leopoldt question, machinery the complex side does not have.

## Why it is worth pursuing
- It makes the abstract `F₁` **concrete** (Morita `Γ_p`, Diamond `γ_E^{(p)}`, Gauss-sum `Frob_p`).
- It is the **first attack-route surviving both** the §8 Padé no-go **and** the §10 Hölder function-exhaustion
  (those kill the complex-analytic and function-Galois routes; the p-adic route is neither).
- It realizes the founding bet (`σ_p` simultaneity for the missing single Frobenius) with an **explicit
  arithmetic carrier** (`{Frob_p}` on `N`).

## The conjecture (to test)
> **`F₁` = the missing synthesis of `{Frob_p}`.** DSS-cross (`γ_E ∉ \overline{𝓡}`, and the full `{γ_n}`
> independence over `𝓡`) holds **iff** the per-prime crystalline Frobenii `{Frob_p}` on the p-adic
> realizations of `K_Λ` are **jointly generic** (no global synthesis collapses them) — a p-adic period
> comparison.

## Door / grade
- **Grade:** CONJECTURE. Defensible core (carrier, recurrence, Gross–Koblitz) is recalled-standard; the
  `{Frob_p}=σ_p` synthesis identification and the value-lift formulation are the **new content**.
- **Door-2:** pending — p-adic Hodge / Iwasawa are parents; the candidate native content is the
  `σ_p={Frob_p}` synthesis (the founding bet on an explicit carrier).
- **Door-5:** over `F_q`, `K=1` (single Frobenius present), so `{Frob_p}` already synthesized — value=function,
  Papanikolas (consistent with #121/DeWitt §6). The synthesis-missing is number-field-only.

## Gates
- [ ] 0 → 1: pin the exponential motive of `γ_E` and its p-adic (rigid-cohomology) realization with `Frob_p`
  explicitly; state the joint-genericity conjecture precisely; collision-check vs DeWitt's K-kernel.
- [ ] 1 → 2: **needs p-adic-Hodge / Iwasawa input** — whether Gross–Koblitz rigidity propagates to `ψ_p`
  (the p-adic value-lift). This is the genuine open work; likely a multi-session p-adic-theory effort.

## Cross-references
- `../1-in-progress/relative-exponential-apex.md` §11–§12 — the full development (the defensible core + the bet).
- `../2-fully-proven/exponential-period-dss-cross.md` (DeWitt) §7 — the **archimedean Stokes** K-kernel; this
  card is the **p-adic crystalline** companion (the two realizations of the same wild kernel). Coordinate.
- `../2-fully-proven/stieltjes-exponential-period-realization.md` (Professor) — the `J_m` floor.
- `../2-fully-proven/bigraded-corank-dss-cross.md` (Wheeler) — the invariant the apex populates.

## Log
- 2026-06-19 (Wheeler) — created in 0-backlog from `relative-exponential-apex` §11–§12. Posed the p-adic
  crystalline Frobenii `{Frob_p}` as the concrete candidate for the missing single Frobenius `F₁`: ℚ-carrier
  `N` (complex + p-adic periods), realization-independent `1/s` recurrence (Diamond), Gross–Koblitz rigidity
  as the live foothold the complex side lacks. The first route surviving both §8 (Padé) and §10 (Hölder).
  Prior-research-checked absent. CONJECTURE; advancing it needs p-adic-Hodge/Iwasawa machinery (handed as a
  research direction, not claimed solo). Awaiting DeWitt collision-check vs the archimedean Stokes K-kernel.

---

## Update (2026-06-19) — verified carrier floor + refined framing (with Professor's `per-place-source-a-gamma-carriers`)

Professor built the **verified floor** for this route: `../2-fully-proven/per-place-source-a-gamma-carriers.md`
proves Morita `Γ_p` is **Source-A** (polynomial multiplier `−s`, via the dichotomy #134), giving a uniform
**per-place `{Γ_v}` carrier** (`Γ_ℝ` at `∞`, `Γ_p` at each finite `p`); Leaner formalized the finite recurrence
(`../3-formalized/morita-gamma-finite-recurrence.md`, `moritaGammaFinite_succ`). This **supersedes** the loose
parts of §11–§13 with verified objects, and refines the framing:

- **The per-place Source-A object is `Γ_v`** (the Γ-symbol carrier — *built/verified*), with the Source-B
  **`σ_v` dilations** a separate lane (#130). My §13 "σ_p vs Frob_p" is subsumed: the carrier is `Γ_v`, and the
  crystalline **`Frob_p` is the COMPARISON operator** (Gross–Koblitz: `Frob_p ↔ Γ_p`-values), i.e. the
  value-lift machinery, **not** the carrier. (Professor independently reached my §13 correction — convergent.)
- **The apex, sharpened on the verified carrier:**
  > **Missing `F₁` = the arithmetic GLUING of the per-place Source-A carriers `{Γ_v}`** — the period comparison
  > relating the archimedean wild value `γ_E` (from `Γ_ℝ`) to the Diamond p-adic constants `γ_E^{(p)}` (from
  > `Γ_p`). Over `F_q` a single Frobenius glues them (value = function, `K=1`); over ℚ the `{Γ_v}` do **not**
  > glue (`F₁` absent). Concretely: does Gross–Koblitz rigidity on the finite `Γ_p` propagate to glue with the
  > archimedean `Γ_ℝ` wild value? (Iwasawa / p-adic-Hodge tooling; open, mine.)
- **What is now verified vs open.** Verified (Professor + Leaner): the per-place Source-A carriers `{Γ_v}`
  exist, `Γ_p` Source-A, finite recurrence formalized. Open (this card / the apex): the **gluing/comparison**
  (the value-lift `F₁`). The carrier is no longer conjectural — only the gluing is.

So this card's status: the **carrier floor is BANKED** (Professor, 2-fully-proven); this card is now precisely
the **gluing/comparison apex** on that floor — `F₁` = glue `{Γ_v}` (Gross–Koblitz/Iwasawa). open.

## Log (cont.)
- 2026-06-19 (Wheeler) — adopted Professor's `per-place-source-a-gamma-carriers` (verified floor) + Leaner's
  formalized Morita recurrence. Refined: per-place Source-A object = `Γ_v` (carrier, built); `Frob_p` = the
  **comparison** operator (Gross–Koblitz), not the carrier (subsumes/clarifies §13). Apex sharpened: **`F₁` =
  the arithmetic gluing of `{Γ_v}`** (period comparison `γ_E` ↔ `γ_E^{(p)}`); carrier banked, only the gluing
  open. Convergent with Professor's independent §13-correction. open apex, mine.

## Update 2 (2026-06-19) — the carriers glue via the EPSILON factor; F₁ = its derivative-extension `[sharpening + correction]`

A refinement (and correction) of the "F₁ = glue `{Γ_v}`" framing. The per-place Source-A carriers **DO glue
at the value level**, classically, via the **epsilon factor / global root number** `ε = ∏_v ε_v` (the FE
constant):
- **Gross–Koblitz** relates Morita `Γ_p` to **Gauss sums = the local `ε_p`**; `Γ_ℝ` relates to `ε_∞`.
- So the `Γ_v`-**values** are glued by `ε` — the root number is a coherent global object (the FE works,
  classically). This value-level gluing is **BRIDGE** (Tate/Deligne local constants).

**Correction** to "the `{Γ_v}` don't glue over ℚ": the carriers (`Γ_v`-values) **do** glue (via `ε`); what
does **not** glue is the **wild log-derivative structure** — the `γ_E = ∂_s\logΓ_v|_{s=1}`. So:
> **F₁ / the value-lift = extending the `ε`-gluing from the `Γ_v`-VALUES (classical root number) to their
> LOG-DERIVATIVES (the `γ_E`, wild).** Equivalently: the Gross–Koblitz rigidity propagating from `Γ_p`-values
> (`= ε_p`, algebraic) to `ψ_p`/`γ_E^{(p)}` (the derivatives) — exactly §12C, now read as **"extend the
> root-number gluing to the derivative level."**

This is sharper and more accurate: the apex is **not** "no gluing exists" — a gluing **exists** (`ε`, at the
value level, classical) and the `F₁` is its **derivative-extension** to the wild constants. Reframes the
A2 apex as a *derivative-of-the-root-number* question.

- **Door:** the `ε` value-gluing is BRIDGE (Tate); the derivative-extension is the open apex.
- **Complement:** DeWitt's `omega-rh-coupling` uses the root number on the **RH/spectral** axis (automorphy
  factor / spectral flow, support-log §195/§304); this is its **transcendence-carrier** face (`Γ_v`-gluing).
  Same object (`ε`), two axes — consistent with the two-apex picture.
- **Prior-research-checked:** the `Γ_v`-carrier-gluing-via-`ε` + derivative-extension framing is absent from
  the tree (root-number appears only on the RH/spectral side).

## Log (cont.)
- 2026-06-19 (Wheeler) — **Update 2: the carriers glue via `ε` (root number); F₁ = its derivative-extension.**
  Corrected "carriers don't glue" → the `Γ_v`-VALUES glue classically via `ε=∏ε_v` (Gross–Koblitz: `Γ_p↔`Gauss
  sums`=ε_p`; `Γ_ℝ↔ε_∞`); what's missing is extending `ε`-gluing to the LOG-DERIVATIVES `γ_E` (= §12C's
  Gross–Koblitz-propagation, the wild apex). Reframes the A2 apex as a derivative-of-the-root-number question;
  same `ε` as DeWitt's RH-axis use, transcendence face. BRIDGE value-gluing; open derivative-extension.
