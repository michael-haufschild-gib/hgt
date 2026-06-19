# Deligne Weil-II → ℚ/F_1 transport audit — which steps cross, and the one that does not

> **⚠ rh-corp reconciliation (2026-06-19): NOT NEW — supports `docs/rh-corp` route #2/#3** (F₁/Connes/Hodge
> & q→1 Deligne; `speculation.md` §2). The "what ℚ lacks vs `F_q`" audit is folklore in the F₁ program; rh-corp
> ranks these below the **faithful κ₋=0 source proof** (#1). **Re-derivation, not a fresh lead.**

- **ID:** deligne-weil-ii-transport-audit
- **Stage:** 1-in-progress
- **Type:** ANALYSIS (locating the bedrock's missing ingredient) — **BRIDGE** (an audit of imports)
- **Priority:** FIELDS MEDAL (locates the FIELDS-MEDAL residual)
- **Source:** companion to `archimedean-weil-ii-bedrock.md`; imports Deligne, *La conjecture de Weil II*
  (Publ. IHÉS 52, 1980); Deninger (cohomological RH program), Connes–Consani (F_1); #88 (the F_1 Rosetta)
- **Goal.** Deligne's Weil II **proves the positivity** (purity `|α|=q^{w/2}` = RH) over `F_q`. The bedrock
  (`archimedean-weil-ii-bedrock`) is whether it transports to ℚ/`F_1`. This card **audits the proof step by
  step** and pins the **single** step that fails — turning "the bedrock is the F_1 foundation" into "the
  bedrock is *one specific missing object*."

  > **Audit verdict:** all analytic/formal steps transport (ℚ has `ζ`, the FE+Γ-factor, the Rankin–Selberg
  > moments). The **one** step that does not is the **finiteness + polarization** input: Deligne's positivity
  > is forced on a **finite-dimensional `H¹_c` carrying a Poincaré-duality (cup-product) polarization**; over
  > ℚ there is **no finite-dimensional cohomology and no geometric polarization** — `Spec ℤ` is not
  > finite-type over a field, the archimedean/`F_1` base is absent. **The missing ingredient is exactly the
  > `F_1`/Deninger cohomology with its archimedean Poincaré polarization** (= the orthogonality theorem's
  > polarization, geometrically sourced).

  *Caveat: Deligne's proof is recalled at the structural level (not re-read line-by-line this session);
  the step list and the located gap should be checked against Deligne 1980 §§1–3 before banking.*

---

## The audit (step → does it transport to ℚ?)

| # | Deligne's step (over `F_q`) | ℚ analog | Transports? |
|---|---|---|---|
| 1 | `L = ∏_x \det(1−\mathrm{Frob}_x t^{\deg x})^{-1}` (Euler product) | `ζ(s)=∏_p(1−p^{-s})^{-1}` | **yes** |
| 2 | Grothendieck: `L = ∏_i \det(1−\mathrm{Frob}\,t|H^i_c)^{(-1)^{i+1}}` — zeros = Frobenius eigenvalues on `H¹_c` | the zeros *should* be a Frobenius spectrum — **but on what `H¹`?** | **NO** (no cohomology) |
| 3 | Rationality + FE of `L` (from Poincaré duality on the curve) | `ζ`'s FE — **but with a Γ-factor** (the archimedean place) | **partial** (FE yes; via Γ, an *addition*) |
| 4 | Pass to tensor powers `F^{⊗k}` / Rankin–Selberg; coefficients `≥0` | moments `ζ²=Σd(n)n^{-s}`, Rankin–Selberg — exist | **yes** (analytically) |
| 5 | **Finite-dimensionality** of `H¹_c` ⟹ `L` of each tensor power is a **polynomial** (finitely many zeros) ⟹ the positivity argument **terminates** and forces `|α|=q^{w/2}` | `ζ` has **infinitely many** zeros; the would-be `H¹` is infinite-dimensional; the finite argument **does not terminate** | **NO** (no finiteness) |
| 6 | **Poincaré-duality polarization** (cup product) gives the sign/positivity that pins the eigenvalues to the circle | the polarization is the archimedean Weil form `Q_W` (orthogonality thm) — but it has **no geometric (cup-product) source** over ℚ | **NO** (no geometric polarization) |

**Steps 1, 3(FE), 4 transport.** **Steps 2, 5, 6 fail — and they are one failure:** there is no
finite-dimensional cohomology with a geometric Frobenius and a Poincaré-duality polarization, because the
**archimedean/`F_1` base is missing** (#88 §5).

## The single missing ingredient (the located bedrock)

Collapsing steps 2/5/6: the bedrock needs a cohomology `H¹_{F_1}` with
1. an **archimedean Frobenius** whose spectrum is the zeros `{γ}` (regularized / infinite-dimensional —
   Deninger's `ζ`-regularized determinant; corpus #90 `Γ = ζ-reg det D`);
2. a **Poincaré-duality polarization** — a cup-product pairing whose positivity is RH; this is precisely the
   orthogonality theorem's **archimedean polarization `Q_W`**, now demanded with a **geometric source** (a
   self-duality of `H¹_{F_1}`), not merely as the analytic Weil form.

So Deligne's positivity transports **iff** `(H¹_{F_1}, \mathrm{Frob}_\infty, Q_W)` exists with `Q_W ⪰ 0`
forced by duality. **That object is the `F_1` foundation (D5).** The audit shows the *rest* of Deligne's
machine is already present over ℚ — the gap is exactly this one geometric object.

## Why the session's results sharpen, not solve, this
- **Orthogonality:** identifies item 2 (the polarization) as the load-bearing datum — the cohomology's
  *duality*, not its cycles. Narrows D5 to "build the polarization with a geometric source."
- **ω purely archimedean (#27 §R):** confirms steps 5/6's failure is archimedean, not a defect of the prime
  side (the multiplicative part is already acyclic/handled).
- **Constraint-not-flow:** `\mathrm{Frob}_\infty` is the order-2/weight constraint (the FE), regularized —
  Deninger's `D`, not a Hamiltonian. So `H¹_{F_1}` is a *constraint cohomology* (BRST/cohomology of the FE),
  consistent with the "no flow" theorem.

## Verdict / Door passport
- **The audit is BRIDGE** (it sorts known imports). Its value: it turns "bedrock = F_1" into "bedrock = one
  object `(H¹_{F_1}, \mathrm{Frob}_\infty, Q_W)` — steps 2/5/6 of Weil II, all archimedean."
- **The missing object is FIELDS-MEDAL / open** (Deninger–Connes). No proof claimed.
- **Honest risk:** the step list is a structural recollection of Deligne 1980; the *located gap* (finiteness
  + geometric polarization) is robust to the details (it is the standard "Spec ℤ is not a curve over a field"
  obstruction), but the per-step transport claims should be verified before banking to 2-fully-proven.

## Gates
- [x] 0 → 1  in-progress: the step audit written; steps 1/3/4 transport, 2/5/6 fail; the single missing
  object `(H¹_{F_1},\mathrm{Frob}_\infty,Q_W)` located; session-results sharpening; Door passport.
- [ ] 1 → 2  verified-and-banked: the audit checked against Deligne 1980 §§1–3; the located gap confirmed; the
  reduction graded BRIDGE; feeds `archimedean-weil-ii-bedrock` §2–§3.
- [ ] 2 → 3  n/a (audit).
- [ ] 3 → 4  publication-ready: paired note "what Weil II needs that ℚ lacks: one cohomology + one
  polarization."

## Cross-references
- `archimedean-weil-ii-bedrock.md` — the bedrock this audit serves (justifies its §2–§3).
- `../2-fully-proven/orthogonality-meta-theorem.md` — item 2 (the polarization) is its content.
- `../../door/bucket-the-seam-archimedean-obstruction.md`, **#88** — the F_1 Rosetta; the missing Frobenius.
- `weil-positivity-operator.md` (#88 §8, `H_W=−Δ_prime+V_arch`) — the analytic shadow of `Q_W`.

## Log
- 2026-06-19 — created in 1-in-progress and **worked** (user: "work the ω/bedrock"). Audited Deligne's
  Weil-II positivity proof step by step: steps 1 (Euler product), 3 (FE, via Γ), 4 (Rankin–Selberg moments)
  **transport** to ℚ; steps 2 (cohomological `L`), 5 (finite-dimensional `H¹_c`), 6 (Poincaré polarization)
  **fail** — one archimedean/`F_1` failure. **Located the bedrock as a single object**
  `(H¹_{F_1},\mathrm{Frob}_\infty,Q_W)` = the `F_1`/Deninger cohomology with its archimedean polarization.
  Flagged the Deligne recollection for verification. BRIDGE audit; the missing object is the FIELDS-MEDAL
  residual.
</content>
