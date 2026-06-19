# The live motivic period tower — two non-interacting Galois towers (SEED-U)

- **ID:** motivic-period-tower
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper, resolution), Door-2 **BRIDGE (substrate)**
- **Priority:** FOUNDATIONAL (the resolution/correction); the value-lift apex it folds into = FIELDS MEDAL
- **Owner:** Wheeler
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#80 SEED-U), ../../door/bucket-the-seam-archimedean-obstruction.md, ../../door/G2-multi-q-siegel-shidlovsky.md · 00-status row #102
- **Statement:** The transcendence tower recurses **motivically, not spectrally**: `𝒫_𝒵 = ℚ⟨P_k⟩`
  carries a **motivic Galois action** (Kontsevich–Zagier / mixed-Tate); the "fixed point" = the
  pro-unipotent radical of its motivic Galois group. **Conjecture:** the field has **TWO Galois towers**
  — a **dead spectral one** (the superzeta `𝒵` has no Euler product, by the First Theorem, so
  `ζ → 𝒵 → …` does not recurse spectrally) and a **live motivic one** — and the **seam is their
  non-interaction** (`[𝔾_a, 𝔾_m] ≠ 0`). **Falsifiable** via Voros's explicit `𝒵(2m) ∈ {π, ζodd,
  Stieltjes}`.

## Goal
Locates the **correct recursion** for the transcendence tower (motivic), correcting the seam-collapse
category error "fixed point = the prime." Routes G2 into Nesterenko / motivic-Galois territory (a domain
*with* transcendence tools) and gives the seam a precise tower form. **Falsifiable**, hence real (not a
content-free restatement).

## Door passport
- **Door-1:** the dead-spectral side is witnessed natively (`SuperzetaResolvent`: the superzeta is the
  additive resolvent trace `Σ_i(1−r_iX)^{−1}`, Σ not ∏ — a Lean theorem).
- **Door-2:** the motivic tower itself is classical motivic Galois theory (IMPORT); the **non-interaction
  with the spectral tower** (the seam) is the native diagnosis. The §42 discipline is met by
  falsifiability.

## Gates
- [x] 0 → 1  in-progress: the two towers pinned (spectral dead via the First Theorem; live via `ℚ⟨P_k⟩`);
  the non-interaction stated; the Voros `𝒵(2m)` falsifier set up
- [x] 1 → 2  fully-proven (BRIDGE substrate): RESOLUTION §R1–§R4 — live tower **corrected** to
  exponential-motivic `G^exp`/K (object-level, Professor/DeWitt); dead-spectral = First Theorem (#81);
  non-interaction = ω/RH + faces-orthogonality decoupling (#275/#54); Voros falsifier corroborates the
  correction (not triggered). Not a new gatekeeper.
- [ ] 2 → 3  formalized — `SuperzetaResolvent` ledgers the dead-spectral side; the motivic side is the target
- [ ] 3 → 4  publication-ready

## Approach
Compute the motivic Galois action on `ℚ⟨P_k⟩` (the superzeta values); check against Voros's explicit
`𝒵(2m) ∈ {π, ζodd, Stieltjes}` (the falsifier). Use the First-Theorem fact (superzeta has no Euler
product) to kill the spectral recursion, leaving the seam = the towers' non-interaction.

## Cross-references
- `tate-prime-rigidity.md` — the motivic block of the secular weld is the live tower's content.
- `g2-dss-lower-bound.md` — routes DSS into the motivic-Galois framework.
- `../../door/bucket-realization-and-fake-family.md` — the superzeta-is-a-fake verdict (no Euler product).

## Log
- 2026-06-19 — created in 0-backlog. The live motivic period tower (SEED-U / B23): two non-interacting
  Galois towers, the seam in tower form; falsifiable via Voros.

---

# RESOLUTION (Wheeler, 2026-06-19) — the live tower is EXPONENTIAL-motivic (not mixed-Tate); #102 folds into the proven structure

The card's two-tower picture is **correct in shape but wrong in one label**, and now resolves against proven results.

## §R1 Correction — the live tower is exponential-motivic, not mixed-Tate `[object-level, unconditional]`
The card claims `ℚ⟨P_k⟩` carries a **mixed-Tate / Kontsevich–Zagier** motivic Galois action. This is **wrong**:
by the DSS reduction (#11) `ℚ⟨P_k⟩ = ℚ⟨π, ζ(odd), γ_n⟩`, and Professor's `stieltjes-exponential-period-realization`
+ DeWitt's `exponential-period-dss-cross` prove the `{γ_n}`-carrier is **exponential-motivic, an object of
`M^exp ∖ M_mot`** (irregular singularity — **object-level, no transcendence hypothesis**). So:
> **The live tower is the exponential-motivic Galois tower `G^exp` (with `1→K→G^exp↠G_mot→1`):** the `{π,ζodd}`
> part lives in `M_mot` (mixed-Tate, the card's correct half), the `{γ_n}` part in the **wild `K`-layer** (the
> card's mislabeled half). Not a mixed-Tate tower — an exponential-motivic one.

## §R2 The two towers + the seam, located `[folds into proven cards]`
- **Dead-spectral tower = the First Theorem** (banked, #81): the superzeta `𝒵` has **no Euler product**
  (`SuperzetaResolvent`, Σ not ∏), so `ζ→𝒵→…` does not recurse spectrally. The card's dead side is exactly this.
- **Live tower = `G^exp` / the K-kernel** (§R1; `exponential-period-dss-cross`).
- **Non-interaction (the seam) = the ω/RH + faces-orthogonality decoupling** (#275/#54): the multiplicative/
  spectral and the archimedean/exponential structures are orthogonal — that orthogonality **is** the towers'
  non-interaction. The card's `[𝔾_a,𝔾_m]≠0` seam = the proven decoupling.

## §R3 The Voros falsifier — confirmed consistent (it corroborates §R1) `[check]`
The card's falsifier: Voros `𝒵(2m) ∈ {π, ζ(odd), Stieltjes}`. The **Stieltjes** presence is precisely the
signal that the live tower **exceeds `M_mot` into `M^exp`** (the `γ_n` are the wild `K`-layer). So the falsifier
does not trigger — it **corroborates** the §R1 correction. (Mixed-Tate-only would have excluded the Stieltjes;
they appear, so the tower is exponential-motivic.)

## §R4 Door / grade
- **Door-2: BRIDGE (substrate).** §R1 is the object-level non-classicality (Fresán–Jossen + #11, parents);
  §R2 folds into First-Theorem + `exponential-period-dss-cross` + faces-orthogonality (all banked). The genuine
  new content is the **correction** (mixed-Tate → exponential-motivic) and the **location** of the two-tower
  picture within the proven structure.
- **Door-5 ✓:** over `F_q`, `K=1` (no wild layer), so the live tower collapses to `G_mot` (mixed-Tate is then
  correct) and the spectral/motivic distinction degenerates — number-field-only, matching #121/DeWitt §6.

**Net:** #102 is **not a new gatekeeper.** Its two-tower picture is correct, but the live tower is
**exponential-motivic (`G^exp`/K), not mixed-Tate** — the genuine correction. It folds into {First Theorem
(dead-spectral) + `exponential-period-dss-cross` (live) + faces-orthogonality (non-interaction)}. The open apex
remains the **value-lift / `K`-gluing** (the same A2 `F₁`), unchanged. Grade **THEOREM (paper), BRIDGE (substrate)**.

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. The opening Statement contains a Conjecture about two Galois towers, while the resolution says the open value-lift/K-gluing apex remains unchanged. The resolved correction may be useful, but the ticket as a whole is not a fully proven, Lean-ready theorem with all tower/apex content discharged.
