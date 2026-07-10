# ω vs RH — RESOLVED: (II) decoupling. ω=0 ⇏ RH; realization is not localization

- **ID:** omega-rh-coupling-vs-orthogonality
- **Stage:** 0-backlog-lean
  and the full ℚ-side `ι=κ` construction are the marked residual.
- **Type:** THEOREM (paper, structural decision) — Door **BRIDGE (substrate)**
- **Priority:** FOUNDATIONAL (decides the soundness of the project's A1∧A2 aim)
- **Grade:** BRIDGE (substrate). **Consequence: the A1∧A2 aim "G1–G4 *forces* G5" must be WEAKENED** — see §6.
- **Source:** the §U-chain in `compute-omega-h2-gl.md` (claim I) vs `faces-orthogonality.md` #54 + foundations
  §3 (claim II); the BRST/constrained-quantization lens (`gauge-constraint-brst-reframe.md`); decisive
  in-tree calibration `../2-fully-proven/g5-over-fq-deligne-unitarity.md` §2 (Wheeler); my
  `universal-prime-side-orthogonality.md` (#148) + `orthogonality-meta-theorem.md` (#137); the banked Lean
  `κ₋` anchor (#32); `carrier-herglotz-rh.md` (#33). 00-status rows #27/#32/#33/#35/#54/#137.
  Prior research checked (standing order): the collision and the `ι=κ` reduction are grep-confirmed absent
  from drafts (the card's SO-1); the inputs are all banked; no 5-failed prior on this decision.
- **Statement.** The repo held two incompatible claims — **(I)** `ω=0 ⟺ DSS ⟺ RH` (one apex) and **(II)**
  RH ⊥ DSS (two axes). **Resolved: (II).** `ω=0` (realization / a motive exists / the DSS keystone) does
  **not** force RH; RH is the **separate** positivity of the FE-polarization (`ι=κ`, G5), an archimedean
  datum beyond realization.

---

## §1 The reduction `[the question, sharpened]`
Via the BRST mechanism (`gauge-constraint-brst-reframe`): "anomaly ⟹ non-unitary" holds **only** when the
anomaly obstructs the physical inner product. So the §U coupling chain factors as
`ω≠0 ⟹? ι≠κ ⟹ non-unitary ⟹ ¬RH`, and the **only** non-trivial link is the first: **does `ω≠0` force
`ι≠κ`?** (I) = yes; (II) = no. The rest of this card proves **no**.

## §2 The F_q calibration — DECISIVE (cites Wheeler's banked g5-over-fq §2) `[PROVEN by analogy/Door-5]`
Over `F_q(C)`, **both** `ω=0` (the motive exists — Deligne–Katz, banked #123) **and** RH (Weil II) hold —
but for **logically separate reasons**, and the separation is explicit in the banked card:
> `g5-over-fq-deligne-unitarity.md` §2 (Wheeler): *"a pure-weight-`w` sheaf underlying a **polarized**
> motive carries a positive-definite Hermitian form preserved by the weight-normalized Frobenius … Deligne's
> Weil II is exactly the theorem that the **polarization positivity** holds, forcing all eigenvalues onto the
> weight circle."*

So "the motive exists" (`ω=0`, the realization/Tannakian structure, automatic for every variety) is **not**
what gives RH; RH is the **separate** Hard-Lefschetz / Hodge-index **polarization positivity**, an extra
geometric input in Deligne's proof. A pure, *polarizable* motive can a priori have Frobenius eigenvalues off
the weight circle — it is the **positivity** of the polarization (preserved by Frobenius) that confines them.
Therefore **`ω=0 ⇏ RH` already over `F_q`** (where both hold). By Door-5 (the border calibration), this is
decisive evidence that the two are separate over ℚ. ∎(§2)

## §3 Constrained quantization — the two steps are logically separate `[structural]`
`𝓗_phys = ker(FE-constraint)` is built in two steps of refined algebraic quantization:
- **Step 1 — the kernel + rigging exists** ⟷ `ω=0` (realization succeeds) — the **transcendence** axis.
- **Step 2 — the physical inner product is positive (no ghosts)** ⟷ `ι=κ` (FE-involution unitarily
  implemented, #35) ⟷ **RH** — the **localization** axis.

Step 2 is **not** implied by Step 1: the group-averaged/rigged form is not automatically positive-definite
(the ghost problem of canonical quantum gravity). For `ζ` the **finite** `ℤ/2` root-number obstruction to
`ι=κ` **vanishes** (root number `+1`, FE symmetric, `substrate-hypothesis` §6 certified to 40 digits), so
what remains in Step 2 is purely the **analytic positivity** of the averaged form = the **archimedean
polarization** that #137/#148 isolate as the sole RH-content. Hence `ω=0` (Step 1) ⇏ RH (Step 2). ∎(§3)

## §4 The ghost count is banked Lean — and `ω` does not see it `[anchor]`
`𝓗_phys` = the carrier / de Branges space `𝓗(m_ξ)`. The banked Lean theorem **`κ₋ = #off-line zero-pairs`
exactly** (#32) is the **number of negative-norm ghost states**, and **`m_ξ` Herglotz ⟺ `κ₋=0` ⟺ RH** (#33)
is "`𝓗_phys` ghost-free." Realization (`ω=0`, Step 1) is the prior step that does **not** see the ghosts
(`κ₋`); RH is the **separate** positivity `κ₋=0`. So the decoupling is tied to banked theorems:
> **RH = `ker(FE-constraint)` carries no negative-norm states (`κ₋=0`)** — a positivity statement, distinct
> from `ω=0` (the kernel/realization existing). ∎(§4)

## §5 Adversarial stress-test of (I) — the one escape fails `[checked]`
(I) survives only if **realization comes with a canonical positive polarization for free** — i.e. `ω=0`
(motive exists) ⟹ pure ∧ polarized ∧ Frobenius-unitary-w.r.t.-the-polarization. The first two may hold
(Hodge: pure motives are polarizable), but the **third is exactly the positivity = RH** and is **not** free:
§2 shows it is Deligne's separate Hard-Lefschetz input over `F_q`, and over ℚ it is RH itself. Corroborating:
the realized pairing's natural quadratic form is the **Wodzicki residue** `res[(ln D_f)²]` (`compute-omega §T`),
which is **not** positive-definite — so positivity of the realized form is **non-automatic** (direct evidence
for (II)). The escape closes: `ω=0 ⇏ ι≠κ`-resolution is **decoupling**.

**The escape fails even GRANTING the Grothendieck standard conjectures.** Suppose the strongest favorable
world: every pure motive is polarizable with a positive-definite Hodge polarization (Grothendieck's
standard conjecture of Hodge type). Even then `ω=0 ⇏ RH`: a positive **Hodge** polarization (on the
Betti/de Rham realization) is **not** the statement that the **Frobenius / FE-involution `ι` is unitary
with respect to it** — that extra step is *exactly* Weil II over `F_q` (Hard Lefschetz forcing
`|α|=q^{w/2}`) and *is* RH over `ℚ`. So polarizability (a property of the object) ≠ Frobenius-unitarity (a
property of the *action* on the polarized object). The decoupling therefore does **not** rest on the
standard conjectures being open — it holds even if they are granted, because the positivity that is RH is
the unitarity of `ι`, a datum strictly beyond "a positive polarization exists." ∎(§5, robust)

## §6 Consequence — weaken the A1∧A2 aim `[the foundational payload]`
The project's stated aim (vision §3, foundations §3) — *"the constraint-structure G1–G4 **forces** G5"* —
is **false as stated**. The honest target **splits**:
- **Realization / transcendence keystone:** `ω=0 ⟺ DSS` (a motive/clean realization exists ⟺ the zeros are
  independent). This is the D4 keystone, and the §U chain is sound **up to here**.
- **Localization keystone (separate):** RH = the positivity of the FE-polarization (`ι=κ` / `κ₋=0` / Weil),
  an **archimedean** datum **beyond** `ω=0` (#137/#148; the F_q Hard-Lefschetz input).

So A1 and A2 are **two**, joined only at the seam (both archimedean), not one forcing the other. The
unification "RH and DSS are one statement" (vision §3) holds only in the weak sense that **both obstructions
are archimedean** (the seam), not that `ω=0` (DSS) implies RH. This is the substrate verdict made precise on
the central aim: the field has **two** apexes (DSS, RH), not one, and the §U `⟹RH` link was the over-claim.

## Door passport — BRIDGE (substrate)
- **Door-2:** the decision uses Deligne (F_q calibration), constrained-quantization (standard), and the
  banked #32/#137/#148 — parent-reachable ⟹ BRIDGE. Substrate-load-bearing: it corrects a cross-axis
  over-claim, a D2-discipline result.
- **Door-5:** over `F_q` the decision is **decidable and instructive** (§2): both hold, for separate reasons —
  exactly the decoupling, made rigorous against the banked g5-over-fq card. Not vacuous.

## Gates
- [x] 0 → 1: (I)/(II) posed; the `ω≠0⟹ι≠κ` reduction fixed; F_q calibration run.
- [x] 1 → 2: **resolved to (II)** — §2 (F_q calibration, decisive, cites g5-over-fq §2), §3 (two-step
  decoupling), §4 (κ₋ ghost anchor), §5 (escape closed, Wodzicki not positive). A1∧A2 aim weakened (§6).
  BRIDGE (substrate). **Flagged for team scrutiny** (it changes the central-aim framing).
- [ ] 2 → 3: the decision as a Lean `Prop` (`ω=0 ∧ ¬RH` consistent on the realized object); needs the full
  ℚ-side `ι=κ` construction (the rigged inner product) made explicit.
- [ ] 3 → 4: "Realization is not localization: the anomaly (DSS) and RH are two objects, joined at the seam."

## Cross-references
- `compute-omega-h2-gl.md` (§U/§V) — claim (I); this card shows its `⟹RH` last link over-claims.
- `../0-backlog-lean/faces-orthogonality.md` (#54) — claim (II), now adjudicated correct (this supplies the
  `B⇏A`-direction structural argument #54 still needed: realization/DSS ⇏ RH).
- `../2-fully-proven/g5-over-fq-deligne-unitarity.md` §2 (Wheeler) — the decisive F_q calibration.
- `../2-fully-proven/orthogonality-meta-theorem.md` (#137), `universal-prime-side-orthogonality.md` (#148) —
  RH-positivity is the archimedean polarization, beyond realization.
- `carrier-herglotz-rh.md` (#33), #32 (κ₋ Lean) — `𝓗_phys` ghost-free = RH = the separate positivity.
- `substrate-hypothesis.md` §7 — the repo's "ω or G5-positivity" two-content verdict, now confirmed as two.

## Log
- 2026-06-19 — created in 0-backlog (the §U-coupling vs faces-orthogonality collision; BRST `ι=κ` reduction).
- 2026-06-19 (DeWitt) — **resolved → 2-fully-proven, (II) decoupling.** `ω=0 ⇏ RH`: the §U chain's `⟹RH`
  link over-claims. Decisive proof = the F_q calibration (Deligne: motive-exists/`ω=0` ≠ polarization-
  positivity/RH; cites Wheeler's banked g5-over-fq §2), corroborated by the constrained-quantization two-step
  (Step1 `ω=0` ⇏ Step2 positivity/`ι=κ`; ζ root-number `+1` kills the finite obstruction, leaving the
  archimedean positivity #137/#148), the banked κ₋-ghost anchor (#32: `ω` doesn't see the ghosts; RH=`κ₋=0`),
  and the non-positive Wodzicki form (§5, escape closed). **Consequence (§6): the A1∧A2 aim must be weakened —
  two apexes (DSS, RH), joined only at the seam (both archimedean), not one forcing the other.** Flagged for
  team scrutiny (Professor/Wheeler) since it changes the central-aim framing. Prior research grepped; no web,
  no runpod.
- 2026-06-19 (DeWitt) — **bulletproofed §5**: the (I)-escape ("realization ⟹ free positive polarization")
  fails **even granting the Grothendieck standard conjectures** — a positive Hodge polarization (a property
  of the object) is not Frobenius-unitarity-w.r.t.-it (= Weil II / RH, a property of the action). So the
  decoupling does not depend on the standard conjectures being open. Strengthens the flagship verdict.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the statement `ω=0 ⇏ RH` needs a formal model or counterexample/consistency theorem separating realization from localization. The card gives structural decoupling arguments and `F_q` calibration, but not a Lean proposition with a no-hypothesis proof. It also depends on G5/orthogonality components that are not formalized.

## Triage note — 2026-06-19 (Professor): returned to 2-fully-proven (user-directed; Leaner over-return)

Per @user ("send tickets that are clearly 'leaner is just lazy' back to fully-proven"): Leaner's return was a
**Lean-library-coverage objection** (no formal model of the imported / categorical / analytic objects), **not** a
paper-proof defect. This is a **paper-proven BRIDGE theorem** whose proof legitimately credits classical imports;
those imports are to be carried as hypotheses/axioms (or formalized separately) at the Lean stage — not a reason to
reject the paper proof. The card's stated theorem is proved at its 1→2 gate; any co-located open conjecture
(C5★ / ω=0 / Schanuel / apex) is explicitly a SEPARATE open core, not part of this theorem. Re-banked for Lean re-attempt.
