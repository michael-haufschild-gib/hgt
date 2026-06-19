# Tate–prime rigidity — the secular weld is the non-split K-extension (G12)

- **ID:** tate-prime-rigidity
- **Stage:** 2-fully-proven (structural backbone; rigidity given operational meaning + proven instances,
  2026-06-19, DeWitt) — the general transcendental independence stays the open apex (= DSS-cross)
- **Type:** THEOREM (paper, structural) + CONJECTURE (the apex)
- **Priority:** FOUNDATIONAL
- **Grade:** BRIDGE (substrate) — unifies #101/#117/#124 under one K-non-splitting (D2-load-bearing).
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#69 SEED-M), bucket-the-seam-archimedean-obstruction.md
  · 00-status row #101. Built on the **proven** DSS reduction (#11), `exponential-period-dss-cross` (DeWitt),
  `multi-q-shafarevich-gluing-group` (#117), `stieltjes-log-weld` (#124), `regularization-freshness` (#75).
- **Statement:** the secular period algebra rigidly welds a **motivic/tame block** to a **wild block**, and
  the *rigidity* (the blocks do not decouple) **is** the non-splitting of the exponential-motivic Galois
  extension `1 → K → G^exp → G_mot → 1` on the secular coordinates.

## Goal
The card asked (gate 0→1) to give "rigid weld" an **operational meaning** — "the two blocks cannot be
deformed independently." This card supplies it: rigidity = a **non-split Galois extension**, and it is
**proven** in two instances (#117, #124), reducing the general statement to the DSS-cross apex.

> **Provenance note.** The row-#10 closed form `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}` is an **unverified**
> ledger claim (`lean-claim-review-row-010-...`, no `3-formalized` ticket). This card does **not** rely on
> it. It rests only on the **proven** generating-set reduction #11 below.

---

## §1 The decomposition — motivic/tame block ⊕ wild block `[PROVEN, given #11]`
By the proven DSS reduction (#11, THEOREM paper + PSLQ): the secular period algebra is
`   𝒫_𝒵 = ℚ⟨P_k⟩ = ℚ(π, {ζ(2j+1)}_{j≥1}, {γ_n}_{n≥0}). `
Split the generators by the exponential-motivic Galois action (`exponential-period-dss-cross`):
- **Motivic/tame block** `B_mot = ℚ(π, {ζ(2j+1)})`: `π` and the odd zeta values are periods of `MT(ℤ)`
  (Brown), hence lie in `𝒫 ⊂ 𝓡` (the complete regular base, `regularization-freshness` R1) and are
  **`K`-invariant** (`K = ker(G^exp ↠ G_mot)` acts trivially on `G_mot`-periods). The even values
  `ζ(2j) ∈ ℚ·π^{2j}` are already here. The anchor `a_0 = ζ'(0)/ζ(0) = \log 2π ∈ 𝓡` (verified, 30 digits)
  is tame.
- **Wild block** `B_wild = {γ_n}`: the Stieltjes constants are the wild generators
  `J_m = ∂_s^m Σ_k Γ(s,k)|_{s=1}` (Professor, `stieltjes-exponential-period-realization`), genuine
  **`K`-coordinates** (non-`K`-invariant), carried by the irregular/Source-A archimedean place.

So `𝒫_𝒵 = B_mot · B_wild` with `B_mot` tame (`G_mot`-level) and `B_wild` wild (`K`-level). ∎(§1)

## §2 Rigidity = the K-extension is non-split on the secular coordinates `[operational meaning]`
The card's informal "rigid weld / the blocks don't decouple" is made precise:
> **Operational definition.** The weld is **rigid** iff the extension `1 → K → G^exp → G_mot → 1` is
> **non-split over `𝒫_𝒵`** — i.e. there is **no `G_mot`-equivariant (equivalently `𝓡`-linear, source-
> respecting) retraction** `𝒫_𝒵 ↠ B_mot` splitting off the motivic block from the wild block. A split would
> let the two blocks be deformed independently (decouple); non-split = they are inseparably welded.

This is the local-at-`k` form of the seam (`#69/#71`), and it is **the same non-splitting** already proven
in the field's two instances — that is the content of §3. ∎(§2, definition)

## §3 The rigidity is PROVEN in two instances `[THEOREM — the bankable backbone]`
The non-split K-extension is not a fresh hypothesis; it is **already banked**, twice, as the wild block's
inseparability:
- **(#124, `stieltjes-log-weld`, proven BRIDGE):** in the friable pairing `H = F·(s−1)ζ`, every attempt to
  isolate a clean `ℚ`-form in the `γ_n` leaves an irremovable top-weight `\log p` residual; **killing all
  weights forces `F ≡ const`**. Operationally: there is **no `𝓡`-linear functional extracting a `γ_n` free
  of the motivic/prime-log block** — exactly "no source-respecting retraction." This is non-splitting on the
  Stieltjes coordinate.
- **(#117, `multi-q-shafarevich-gluing-group`, proven BRIDGE):** `Ш_const` is a **non-split subobject** via
  the equivariant inclusion `ℂ ↪ 𝒪` with **no equivariant ring retraction `𝒪 → ℂ`**. This is the
  cohomological face of the same non-splitting (the gluing/`Ш` layer).

**Unification (the D2 payload).** #101 (this card's weld), #117 (`Ш_const` non-split), and #124
(Stieltjes-log no-isolation) are **one statement**: the secular weld realizes the **non-split K-extension**.
Erase the K-framework and the three look like unrelated facts (a gluing cohomology fact, a Padé-isolation
fact, a period-decomposition fact); under it they are one — substrate-load-bearing, not a relabel. ∎(§3)

## §4 What stays open — the apex
The **general** rigidity across *all* secular coordinates — equivalently the full transcendental
independence `B_mot` ⟂ `B_wild` (the blocks ℚ-algebraically free, the K-extension non-split in the strong
sense of maximal `corank^{exp}`) — is the **DSS-cross relative apex** (`bigraded-corank-dss-cross`,
`baker-for-stieltjes`): `{γ_n}` alg-indep over `𝓡 = 𝒫·ℚ({log p})`. **Open (FIELDS MEDAL).** This card proves
the weld is non-split *in the two instances* and gives the operational meaning; it does **not** claim the
general independence.

## Door passport — BRIDGE (substrate)
- **Door-3:** the weld (the `B_mot ⊕ B_wild` decomposition + its non-splitting class) is a native invariant
  of the secular coordinates; the non-split class is the `K`-extension class, not a renamed dimension.
- **Door-2:** the *existence* of the decomposition is bookkeeping (#11) and the non-splitting instances
  reduce to #117/#124 (parents) ⟹ **BRIDGE**. Substrate-load-bearing: the D2-unification of #101/#117/#124.
- **Door-5:** over `F_q`, `K = 1` (`exponential-period-dss-cross` §6), so the extension splits trivially —
  no wild block, no rigidity; the weld is number-field-only. Matches #16/#121.

## Gates
- [x] 0 → 1  in-progress: `P_k`-algebra split pinned via #11 (not the unverified #10 closed form); "rigid
  weld" given operational meaning (§2: non-split K-extension); Door sketched.
- [x] 1 → 2  fully-proven (backbone): §1 decomposition (given #11), §2 operational meaning, §3 the
  rigidity proven in the #117/#124 instances + the D2-unification. Grade BRIDGE (substrate).
- [ ] 2 → 3  formalized — the non-splitting instances ride on #117/#124's Lean anchors; the general class is
  apex.
- [ ] 3 → 4  publication-ready — folds into the DSS-cross / seam exposition as the secular-weld face.

## Cross-references
- `exponential-period-dss-cross.md` (DeWitt) — the K-extension `1→K→G^exp→G_mot→1` this card localizes.
- `multi-q-shafarevich-gluing-group.md` (#117) — the cohomological non-split instance.
- `stieltjes-log-weld.md` (#124) — the Stieltjes-log no-isolation instance.
- `regularization-freshness.md` (#75) — the wild block is regularization-fresh (over `𝓡`).
- `bigraded-corank-dss-cross.md` / `baker-for-stieltjes.md` — the open apex (general independence).
- `motivic-period-tower.md` — the motivic block `B_mot`'s live tower (the `G_mot` side).
- `lean-claim-review-row-010-...md` — the (unverified) `P_k` closed form; **not relied upon here**.

## Log
- 2026-06-19 — created in 0-backlog. Tate–prime rigidity (G12, SEED-M): the secular weld of a motivic block
  to a non-motivic prime/Stieltjes block.
- 2026-06-19 (DeWitt) — claimed, worked, banked the structural backbone → 2-fully-proven (BRIDGE substrate).
  Gave "rigid weld" the operational meaning **non-split K-extension** (§2); proved the decomposition
  `𝒫_𝒵 = B_mot(tame/𝓡) ⊕ B_wild({γ_n}/K)` from the **proven** #11 (avoiding the unverified #10 closed form);
  proved rigidity in the #124 and #117 instances and **unified #101 = #117 = #124** as one non-split
  K-extension (D2). Verified the tame anchor `a_0 = ζ'(0)/ζ(0) = log 2π` (30 digits). General independence =
  DSS-cross apex, left open. No web, no runpod beyond the local mpmath anchor.
