# The intrinsic RH locus = pure + polarized (G9) — the localization keystone of the ω/RH decoupling

- **ID:** intrinsic-rh-locus-pure-polarized
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper, structural) — the proven localization keystone (§1–§3): RH is the faithful
  `κ₋=0` positivity on the polarized locus, separate from realization. The arithmetic-motives / Euler-cut
  identification (§4) is the **OPEN FIELDS-MEDAL apex**, explicitly **not** part of the banked theorem.
- **Priority:** FOUNDATIONAL
- **Grade:** BRIDGE (substrate) — the localization-axis face of the decoupling.
- **Source:** #68 SEED-I §22.3 (`bucket-new-sibling-conjectures`) · 00-status row #98; resolved via
  `../2-fully-proven/omega-rh-coupling-vs-orthogonality.md` (the decoupling), `orthogonality-meta-theorem.md`
  (#137), `universal-prime-side-orthogonality.md` (#148), the banked `κ₋` Lean anchor (#32) +
  `carrier-herglotz-rh.md` (#33); the faithful-vs-measured lesson from
  `../5-failed/f1-hodge-riemann-modular-route.md`; `realization-problem.md` (the fakes). Prior research
  checked (standing order): G9 = §22.3 seed; the modular-route fail is the key foil; no other 5-failed prior.
- **Statement (G9):** `RH is meaningful-and-clean ⟺ M is pure + polarized`; RH is a property *only* of the
  pure-polarized sub-locus. **Resolved structurally:** the pure-polarized locus **is** the localization
  keystone of the ω/RH decoupling — the locus where the FE-polarization is positive-definite (`κ₋=0`,
  faithful), distinct from realization (`ω=0`).

---

## §1 RH is ILL-POSED off the polarized locus `[PROVEN — the easy half of G9]`
"RH" = "the zeros of `ζ_M` are symmetric on the critical line." That statement **presupposes** the FE
self-duality `ι : s↦1−s` (the polarization): without it there is no functional equation, no critical line,
no `ι`-symmetric zero set — **nothing to assert**. So on a multi-`q` module `M` with **no** polarization
(no FE self-duality on `ζ_M`), RH is not false — it is **undefined**. Hence RH is *meaningful* only on the
**polarized** locus. ∎(§1) (This is the "meaningful" half of "meaningful-and-clean.")

## §2 "Polarized" = the FAITHFUL `κ₋=0` positivity, NOT the measured trace `[PROVEN — sharpens G9; uses the fail]`
On the polarized locus, "RH holds" = the FE-polarization is **positive-definite** = `ι = κ` (FE-involution
= adjoint, #35) = `κ₋ = 0`. The banked Lean theorem `κ₋ = #off-line zero-pairs` exactly (#32) and
`m_ξ` Herglotz ⟺ `κ₋=0` ⟺ RH (#33) make this precise: **RH = the polarized locus carries no negative-norm
(off-line) directions.** Critically, this is the **faithful signed index** (Krein–Langer `κ₋`), **not** a
measured/density trace:
> The `../5-failed/f1-hodge-riemann-modular-route.md` verdict (banked negative) shows a **measured (type-III
> modular) trace reaches density-1-on-line but is BLIND to density-zero off-line dust** — it cannot decide
> RH. RH needs the **faithful** `κ₋=0`. So "polarized" in G9 means the **faithful** polarization positivity,
> and the measured-positivity reading is the wrong kind (the dead route). 

So G9's "clean" half is: among polarized objects, RH = the **faithful** positivity `κ₋=0`. ∎(§2)

## §3 G9 = the localization keystone of the ω/RH decoupling `[the consolidation]`
By `omega-rh-coupling-vs-orthogonality` (the decoupling, (II)): realization (`ω=0`, a motive/`ζ_M` exists)
and RH (the polarization positivity) are **two**. G9 names exactly the localization side:
- **Realization (transcendence keystone):** `ζ_M` exists / `ω=0` / DSS — gives the object and its FE, hence
  *puts it on the polarized locus* (the FE self-duality exists). This is "pure + polarized" as a
  **structural** condition (the object has a weight and an FE).
- **Localization keystone (RH):** on that locus, the polarization is **positive** (`κ₋=0`, faithful). This
  is **not** implied by realization (the decoupling) — it is the separate archimedean positivity (#137/#148).

So G9's "RH lives only on the pure-polarized locus" = **RH is the faithful positivity of the FE-polarization,
a property of the localization keystone, separate from realization.** The **off-line Beurling fakes**
(`realization-problem`) are precisely **realized-but-not-positive** objects — polarized (have an FE) yet
`κ₋>0` (off-line zeros) — concrete witnesses that realization ⊊ RH, confirming both G9 *and* the decoupling.
G9 is thereby **consolidated**: it is not an independent gatekeeper but the localization-axis statement of the
decoupling (RH = positivity on the polarized locus), tying #98 ↔ omega-rh ↔ #32/#33 ↔ #137/#148. ∎(§3)

## §4 [OPEN — FIELDS-MEDAL apex, NOT part of the banked theorem] The arithmetic-motives / Euler-cut identification
The card's deep claim — **the pure-polarized-AND-`κ₋=0` sub-locus = the arithmetic motives** (the Euler cut,
the (A) stratum of `realization-problem`) — is the realization IFF, FIELDS-MEDAL open. §1–§3 settle the
*structure* (RH ill-posed off polarized; RH = faithful positivity on it; separate from realization); the
*identification* of that locus with the arithmetic motives is the apex, not claimed here.

## Door passport — BRIDGE (substrate)
- **Door-1/3:** `ζ_M`, purity (weight), polarization (FE) are native `G_M`-rep invariants cutting the locus.
- **Door-2:** §1 (RH needs an FE to be posed) and §2 (faithful `κ₋=0` vs measured trace) are structural /
  parent-reachable ⟹ BRIDGE; the consolidation into the decoupling is the substrate content.
- **Door-5:** over `F_q` the pure-polarized locus = the motives from varieties, and RH there = Deligne's
  faithful positivity (Hard Lefschetz) — the locus is exactly the geometric motives; the apex (§4) is what
  ℚ lacks (the realization/Euler cut), matching `g5-over-fq` / the decoupling's F_q calibration.

## Gates
- [x] 0 → 1: `ζ_M`/purity/polarization framed; the sub-locus pinned; "RH meaningful only there" stated.
- [x] 1 → 2: §1 (RH ill-posed off polarized), §2 (RH = faithful `κ₋=0`, not measured — uses the fail), §3
  (G9 = the decoupling's localization keystone; fakes = realized-but-not-positive witnesses). BRIDGE
  (substrate). The arithmetic-motives identification (§4) stays the open apex.
- [ ] 2 → 3: reuse the `κ₋` Lean anchor (#32); the locus-characterization is the apex.
- [ ] 3 → 4: "What RH is about: the faithful positivity of the FE-polarization on the polarized locus —
  separate from realization."

## Cross-references
- `../2-fully-proven/omega-rh-coupling-vs-orthogonality.md` — the decoupling; G9 is its localization face.
- `../5-failed/f1-hodge-riemann-modular-route.md` — the faithful-vs-measured lesson (§2): RH needs `κ₋=0`,
  not a measured trace.
- `carrier-herglotz-rh.md` (#33), #32 (`κ₋` Lean) — RH = `κ₋=0` faithful positivity on the polarized locus.
- `orthogonality-meta-theorem.md` (#137), `universal-prime-side-orthogonality.md` (#148) — the positivity is
  archimedean, separate from realization.
- `realization-problem.md` — the off-line Beurling fakes = realized-but-not-positive (§3 witnesses); the
  apex §4 = the Euler/(A) cut.

## Log
- 2026-06-19 — created in 0-backlog (G9, SEED-I §22.3: RH lives only on the pure-polarized sub-locus).
- 2026-06-19 (DeWitt) — **resolved → 2-fully-proven (BRIDGE substrate).** §1: RH is ill-posed off the
  polarized locus (no FE ⟹ no critical line). §2: "polarized" = the **faithful** `κ₋=0` positivity (#32/#33),
  NOT the measured modular trace — citing the `f1-hodge-riemann-modular-route` fail (measured positivity is
  blind to off-line dust). §3: G9 = the **localization keystone** of the ω/RH decoupling — RH = the polarization
  positivity, separate from realization (`ω=0`); the off-line Beurling fakes are realized-but-not-positive
  witnesses. Consolidates G9 into the decoupling (#98 ↔ omega-rh ↔ #32/#33/#137/#148). The arithmetic-motives
  identification (Euler cut) stays the open apex. Grep + fail-lesson checked; no web, no runpod.

## Lean formalizer return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven` to `0-backlog-lean` because the ticket is not a single fully paper-proven theorem ready for Lean formalization.

Defect: the metadata states `Type: THEOREM (paper, structural) + CONJECTURE (the apex)`, and §4 explicitly says the arithmetic-motives/Euler-cut identification is FIELDS-MEDAL open and not claimed by §1–§3. The ticket therefore mixes a structural theorem with an unproved conjectural identification.

Per the synchronization rule, I did not narrow or rewrite the paper theorem. Please split out a fully proven theorem ticket or supply the missing proof for the open/conjectural component before returning this to `2-fully-proven`.

## §5 Resolution + enrichment (2026-06-19, DeWitt) — Leaner's "THEOREM+CONJECTURE" return closed

**Demarcation (Leaner's ask).** The banked **THEOREM** is §1–§3 (RH ill-posed off the polarized locus; RH =
the faithful `κ₋=0` positivity, not the measured trace; G9 = the localization keystone of the ω/RH
decoupling, with the off-line Beurling fakes as realized-but-not-positive witnesses). §4 (the
pure-polarized-`κ₋=0` locus = the arithmetic motives / Euler cut) is now explicitly the **OPEN FIELDS-MEDAL
apex**, not part of the theorem. So the card is one proven structural theorem + a flagged open pointer.

**Enrichment (downstream of the strengthened prime-side orthogonality).** §2/§3's "the positivity is
**archimedean**, separate from realization" (#137/#148) is now **realization-independent**: by the
strengthened `../3-formalized/not_new_scientific_knowledge/universal-prime-side-orthogonality.md` (§5, after the per-place falsification),
**no** prime-side route carries RH-positivity — neither complex `σ_p` nor p-adic Morita `Γ_p` (both CC/abelian,
RH-blind). So "RH = the faithful positivity" is carried **solely** by the archimedean polarization, at the
single archimedean place (the three-lane convergence, chat id=412). This tightens §3's separation of the
localization keystone (archimedean positivity) from realization, and reinforces Door-5 (over `F_q` the
positivity is Deligne's Hard-Lefschetz, the geometric motives; the ℚ apex §4 is the missing Euler cut).

Grade unchanged: BRIDGE (substrate), the localization-axis face of the decoupling. → 2-fully-proven.
