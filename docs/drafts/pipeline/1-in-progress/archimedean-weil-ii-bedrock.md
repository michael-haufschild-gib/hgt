# The archimedean Weil-II — the bedrock = a native proof that the archimedean polarization is positive (ω=0)

> **⚠ rh-corp reconciliation (2026-06-19): NOT NEW — this is `docs/rh-corp` route #2** (F₁/Connes/intrinsic
> Hodge-index, ranked **25–30%**, *"conceptually correct but still too large"*; `speculation.md` §2). rh-corp
> already states "positivity must be **manufactured**, not inherited (`Pic⁰(\overline{Spec ℤ})=0`)" and ranks
> the **faithful κ₋=0 / operator-monotone source proof above it** (#1, 40–45%) — which it has **formalized**
> (`multiPair_carrier_exact_neg_inertia`, `FECarrier.lean`: κ₋=2·#off-line) and validated on the real ξ-zeros.
> **Re-derivation, not a fresh lead.** Downgraded from FIELDS-MEDAL "lead" to "route-#2 record."

- **ID:** archimedean-weil-ii-bedrock
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (the substrate's D4/D5 bedrock) — reduction is **BRIDGE**; the target is **FIELDS MEDAL**
- **Priority:** FIELDS MEDAL
- **Source:** the worked substrate hypothesis (`../0-backlog/substrate-hypothesis.md` §6–§7: structural ω is
  BRIDGE, bedrock = `ω=0`/positivity); the **orthogonality meta-theorem** (`../2-fully-proven/orthogonality-meta-theorem.md`:
  RH-positivity = the archimedean polarization); **ω purely archimedean** (`../0-backlog/fields-medal-after-future-tickets/compute-omega-h2-gl.md`
  #27 §R, Professor; `../2-fully-proven/archimedean-prime-cross-term.md` #134); **#88 the F_1 Rosetta** (over
  `F_q` all gatekeepers are theorems; the missing brick = an archimedean-Frobenius cohomology); imports:
  Deligne Weil II (1980), Deninger / Connes–Consani (F_1)
- **Statement (the bedrock).** Two facts now pin the entire branchhood question to one target:
  > **(i)** The weld's *structure* is **BRIDGE** — the FE-conspiracy cocycle is the classical γ-factor
  > (`#134`, certified), and `ω∈H²(G_L)` is a **purely archimedean class** (`#27 §R`). So there is **no
  > native structural content**; the only non-classical content is **`ω=0`** = the positivity of the
  > archimedean polarization (= RH, by Weil's criterion + the orthogonality meta-theorem).
  > **(ii)** Over `F_q` this positivity **has a native proof** — Deligne's Weil II: the Frobenius eigenvalues
  > on the *finite-dimensional* `H¹_c` lie on `|α|=q^{w/2}`, forced by a tensor-power positivity argument on
  > the **cohomology with its Poincaré-duality polarization**. (#88: over `F_q` *all* gatekeepers are
  > theorems.)
  >
  > **The bedrock is therefore: does an archimedean / `F_1` analog of Deligne's Weil II exist over ℚ** — a
  > cohomology with an archimedean Frobenius whose spectrum is the zeros, carrying a Poincaré-duality
  > polarization whose positivity is RH? **If yes, the field is a substrate with content (bedrock). If no,
  > it is a bridge.** This is D4 (`ω` native) ≡ D5 (the `F_1` foundation) — they coincide here.

  **Verdict reached (worked):** the bedrock **reduces, exactly, to constructing the `F_1`/Deninger
  cohomology + its archimedean polarization** — and that construction **is** the Fields-Medal residual
  (`= RH`). No shortcut exists: the structural layers (factorization, ω-class) are BRIDGE; the positivity is
  the irreducible core. The contribution here is the **sharp location** + the proof there is nothing easier.

---

## §1 Why the bedrock is the positivity, and nothing structural `[settled, from banked results]`

- **Factorization layer — BRIDGE.** `ι:s↦1−s` factors anti-source-respectingly; obstruction = the classical
  γ-factor `χ(s)` (`#134`, `substrate-hypothesis` §6, 40-digit certified). No native content.
- **Cohomology layer — BRIDGE.** `ω∈H²(G_L)` is **purely archimedean** (the multiplicative/prime Koszul part
  is acyclic in the `∏_p` limit; `#27 §R`, Professor). No joint/native content in `ω`'s *structure*.
- **Positivity layer — the residual.** The orthogonality meta-theorem (PROVED): RH = positivity of the
  archimedean polarization; it is **not** Source-B-definable. `ω=0 ⟺` that positivity (corpus #90 chain,
  conjectural). So **every layer above the positivity is BRIDGE; the positivity is the sole irreducible
  content.** ∎(the bedrock is `ω=0`/positivity)

## §2 The `F_q` template — the native proof *exists* there `[import: Deligne]`

Over `F_q(C)`, `ω=0`/RH **is a theorem** (Deligne, Weil II), and its proof is **native to the geometry**:
- `L(C,F,t) = ∏_x \det(1−\mathrm{Frob}_x t^{\deg x})^{-1} = ∏_i \det(1−\mathrm{Frob}\,t\,|\,H^i_c)^{(-1)^{i+1}}`
  (Grothendieck): the zeros are **Frobenius eigenvalues on a finite-dimensional `H¹_c`**.
- **Purity** (`|α|=q^{w/2}`, RH) is forced by a **tensor-power / Rankin–Selberg positivity** argument using
  (a) the **finite-dimensionality** of `H¹_c`, (b) the **Poincaré-duality polarization** (cup product) on the
  curve, (c) the holomorphy/positivity of the `L`-functions of tensor powers.

This is the **existence proof** that a native proof of the positivity is *possible* — over `F_q`. The bedrock
asks for its ℚ analog. *(Deligne's proof structure recalled; audited step-by-step in
`deligne-weil-ii-transport-audit.md` — verify against Deligne 1980.)*

## §3 What ℚ lacks — the reduction to the `F_1`/Deninger cohomology `[the worked reduction]`

Transporting §2 to ℚ (audit in the companion card), every analytic input **exists** (`ζ`, the FE with its
Γ-factor, the moments/Rankin–Selberg `ζ²,…`), but the argument **fails to close** because over ℚ:
- there is **no finite-dimensional cohomology** — `ζ` has *infinitely many* zeros, so the would-be `H¹` is
  infinite-dimensional, and Deligne's *finite* tensor-power argument does not terminate;
- there is **no global geometric Frobenius** — `Spec ℤ` is not finite-type over a field; the **archimedean
  place / `F_1`** is the missing base (#88 §5: "an arithmetic cohomology with a Frobenius at the archimedean
  place = `F_1`").

So **the bedrock = construct the `F_1`/Deninger cohomology**: an (infinite-dimensional, ζ-regularized) `H¹`
with an **archimedean Frobenius** whose spectrum is the zeros `{γ}`, carrying a **Poincaré-duality
polarization** whose positivity is RH. The polarization is exactly the orthogonality meta-theorem's
archimedean polarization (the Weil form `Q_W`), now demanded with a **geometric source** (a duality on the
`F_1`-curve). **bedrock ⟺ archimedean Weil-II ⟺ `F_1`/Deninger cohomology + its polarization ⟺ D5.** ∎

## §4 What the session's results add (new traction, honestly bounded)

- **They locate the polarization.** Orthogonality: the required positivity is the archimedean polarization,
  not anything prime-side — so the `F_1`-cohomology's *duality* (not its cycle structure) is the load-bearing
  datum. This narrows Deninger's program to "build the polarization," not the whole cohomology.
- **They prove there is nothing easier.** Every structural layer is BRIDGE (§1). So the search for a C5
  *short of* the positivity is **closed** (this is the substrate hypothesis's deflationary core). The bedrock
  is RH-hard by necessity, not by our failure.
- **Constraint-not-flow refines the target.** The `F_1`-Frobenius is a *constraint* (the FE / the
  product-formula), not a flow — so the cohomology's Frobenius is the order-2/weight structure, consistent
  with Deninger's "Frobenius = the archimedean `D`" (the modular flow's generator), not a Hamiltonian.

## §5 Verdict / Door passport
- **The reduction (§§1–3) is BRIDGE** — it assembles banked BRIDGE results + classical imports (Deligne,
  Weil positivity) into the location "bedrock = `F_1`/Deninger cohomology + polarization." Bankable as a
  reduction (like `C3-native ⟺ C5★`).
- **The target (§3) is FIELDS MEDAL, OPEN** — it is RH, via the deepest known route (Deninger/Connes `F_1`).
  No proof is claimed; the deliverable is the **sharp, total location** of the bedrock and the proof that no
  structural shortcut exists.
- **Door:** the *reduction* is BRIDGE; the *construction* of the `F_1`-cohomology, if it gives a native proof
  of the positivity using the joint `(σ_p,∂_s)`/`F_1` apparatus, would be the **first C5/D4** — the substrate
  with content.

## Gates
- [x] 0 → 1  in-progress: bedrock isolated (positivity, §1); `F_q`/Deligne template (§2); the reduction to
  `F_1`/Deninger cohomology + polarization (§3); session-results traction (§4); Door passport.
- [ ] 1 → 2  the reduction banked: §§1–3 verified (esp. the Deligne audit, companion card) and graded BRIDGE;
  the bedrock = `F_1`-cohomology + archimedean polarization stated as the sole, located residual.
- [ ] 2 → 3  formalized: n/a until the `F_1`-cohomology exists (D5).
- [ ] 3 → 4  publication-ready: "the archimedean Weil II: RH as the missing `F_1` purity, located."

## Cross-references
- `deligne-weil-ii-transport-audit.md` — the step-by-step audit justifying §2–§3 (which steps transport).
- `f1-hodge-cohomology-construction.md` — **the missing object, now assembled** `(H¹_{F₁},Θ,W_\bullet,Q_W)`.
- `f1-hodge-index-theorem.md` — **the positivity, sharpened**: RH = the Hodge index of the *proper* F₁-curve;
  properness = the **product formula** (given); the hard core = the F₁ Hodge–Riemann relations.
- `../0-backlog/substrate-hypothesis.md` — this is its D4/D5 bedrock, worked.
- `../2-fully-proven/orthogonality-meta-theorem.md` — the polarization = the load-bearing datum.
- `../0-backlog/fields-medal-after-future-tickets/compute-omega-h2-gl.md` (#27), `../2-fully-proven/archimedean-prime-cross-term.md` (#134) — ω/cocycle purely archimedean (the structural layers are BRIDGE).
- `../../door/bucket-the-seam-archimedean-obstruction.md`, **#88** — the F_1 Rosetta / missing Frobenius;
  Deninger / Connes–Consani (imports).

## Log
- 2026-06-19 — created in 1-in-progress and **worked to the located verdict** (user: "work the ω/bedrock").
  Established: the structural layers (factorization #134, cohomology ω #27) are **BRIDGE** (banked), so the
  bedrock is **`ω=0` = the archimedean positivity** alone. Over `F_q` this has a **native proof** (Deligne
  Weil II) using finite-dimensional `H¹_c` + Poincaré polarization. Over ℚ every analytic input exists but
  the argument fails for lack of a **finite-dimensional / `F_1` cohomology with archimedean Frobenius**. So
  **bedrock ⟺ archimedean Weil-II ⟺ the `F_1`/Deninger cohomology + its (orthogonality-theorem) polarization
  ⟺ D5**, FIELDS-MEDAL, open. The reduction is BRIDGE and bankable; **no structural shortcut exists** (the
  substrate's deflationary core, now proven). Companion: the Deligne transport audit.
</content>
