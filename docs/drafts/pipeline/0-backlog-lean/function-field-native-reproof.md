# Function-field reproof of the gatekeepers in the field's own vocabulary (the deep `S_ff` extension)

- **ID:** function-field-native-reproof
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper), BRIDGE (function-field border; Door-5)
- **Priority:** FOUNDATIONAL
- **Source:** arose from the C6 work (`../2-fully-proven/c6-specialization-functors.md` §2, the functor
  `S_ff`); ../../door/bucket-function-field-proving-ground.md (open core); 00-status rows #76–80
- **Statement.** Prove G1–G5 over a function field `F_q(C)` **in the multi-`q`-difference vocabulary** —
  i.e. upgrade the function-field recovery functor `S_ff` (C6 §2) from an **import-dictionary** ("these
  become Deligne / Grothendieck / Papanikolas / Deligne–Katz") to a **from-scratch proof**: the
  infinite-base module specializes to the lisse sheaf / `F`-isocrystal, and the native gatekeeper
  statements are re-derived by the field's own argument, recovering the Weil–Deligne theorems on the
  overlap.

## Goal
This is the **deeper strict extension at the function-field border** that C6 deferred. C6 graded MET at
bridge level using one *proven* extension (G1 at the single-prime border) and *cited* the function-field
recoveries as imports. Closing this ticket:
- makes Door-5 a genuine **reproof**, not a citation — the strongest form of the faithful bridge (C6);
- exercises the field's apparatus where **RH is already a theorem** and there is **no archimedean seam**,
  so any failure is a vocabulary failure, not a depth failure;
- isolates, **by difference**, exactly what the archimedean place must supply over ℚ — the F₁
  cohomology-with-Frobenius (the seam, [[bucket-the-seam-archimedean-obstruction]]).
Source-pure: built from the **places** of `F_q(C)` (the prime analogue), recovers known FF theorems; does
not assume RH.

## Approach
> **Split note (2026-06-19, Professor):** Steps **2** (G1-over-`F_q` degeneration) and **6** (the
> archimedean residue) are **done** and carved off to
> `../2-fully-proven/function-field-holonomicity-degeneration.md` (corank collapse `Λ_ff = ker deg`,
> `corank = 1`; `ζ_C` holonomic; seam-corank residue conjecture). This parent card now covers **G2–G5**
> native reproofs (Steps 3–5) — open.
>
> **Closure note (2026-06-19):** G2, G4, and G5 have now also been split off and proven in
> `../2-fully-proven/g2-over-fq-papanikolas-dss.md`, `../2-fully-proven/g4-over-fq-deligne-katz.md`, and
> `../2-fully-proven/g5-over-fq-deligne-unitarity.md`. This parent is the closed FF campaign umbrella.

1. **Pin `S_ff` precisely.** Identify the prime base `{x_p}` with the place base `{T_v}` of `F_q(C)` via
   `x_p = p^{-s} ↦ T_v = q^{-s·deg v}`, `q_p = 1/p ↦ q^{-deg v}`. The diagonal section = the global
   L-function = the Weil L-polynomial `∏_v \det(1 − Frob_v T_v)^{-1}`. State `S_ff` as a `⊗`-functor.
2. **G1 over `F_q` (what replaces difference-Hölder).** The FF L-function is a *polynomial* in `q^{-s}`
   (finite rank) ⟹ trivially holonomic ⟹ **difference-Hölder degenerates**: it is a number-field-only
   phenomenon. Record precisely *why* (the FF base is finite-corank: `Λ` is full-rank, not `0`), making
   the contrast with ℚ explicit. This is itself a Door-5 finding (the corank is the discriminating
   invariant).
3. **G5 / RH = "Frobenius is unitary" (Deligne) reproved natively.** The native σ-fixed-modulus locus
   (`|x_p| = |q_p|^{1/2}`, ledger `BoundaryModulus`) specializes to the Frobenius-weight circle
   `|Frob_v| = q^{(deg v)/2}`. Reprove RH-over-`F_q` as unitarity of the specialized holonomy
   (Poincaré duality + hard Lefschetz in the field's language; cf. #78 §13/§15).
4. **G2 / DSS = Papanikolas reproved natively.** Restrict the multi-`q` transcendence engine (G2 upper
   bound `trdeg ≤ dim G_M`, #8) to the FF base and match the `t`-motivic `trdeg = dim G_M` (Papanikolas
   2008) — the one place the field's exact mechanism is a theorem.
5. **G4 / Langlands group = Deligne–Katz reproved natively.** The infinite-base Galois correspondence
   (#24) specialized to the FF base = the Tannakian geometric-monodromy group; recover `⊗` = tensor of
   sheaves, Sato–Tate = Katz–Sarnak.
6. **The difference = the archimedean place.** Catalogue every step that used "no archimedean place" —
   the residue/difference is the precise demand the F₁-Frobenius must meet over ℚ. This is the deliverable
   that feeds the seam bucket.

## Gates
- [x] 0 → 1  in-progress: `S_ff` pinned; the five native restatements drafted; the "difference =
  archimedean" catalogue scoped; Door-5 passport written.
- [x] 1 → 2  fully-proven: each gatekeeper re-derived over `F_q(C)` in the field's vocabulary, recovering
  the named classical theorem; the archimedean-residue catalogue complete.
- [ ] 2 → 3  formalized — the Weil FE of the L-polynomial (#78, `functionField_esymm_FE`) is already
  ledgered; the native restatements are the next Tier-A/B Lean targets.
- [ ] 3 → 4  publication-ready.

## Notes / risk
- Scope: a multi-part campaign (five gatekeepers), each reducing to an established FF theorem on the
  overlap; the *native-vocabulary* re-derivation is the work, not the truth of the targets.
- Risk: some restatements may turn out to be pure reframings of the imports (Door-2 BRIDGE, as
  expected for a border item) — that is acceptable here (C6 is the bridge criterion), but each must still
  *recover* the classical answer to count.

## Log
- 2026-06-19 — created in 0-backlog. Split from the C6 work (the `S_ff` functor exists as an
  import-dictionary; this ticket upgrades it to a native reproof — the deep function-field-border strict
  extension and the cleanest Door-5 calibration).
- 2026-06-19 — Steps 2 + 6 split off and **proven** by Professor
  (`../2-fully-proven/function-field-holonomicity-degeneration.md`). This card now scoped to G2–G5
  native-vocabulary reproofs (Steps 3–5), open.
- 2026-06-19 (DeWitt) — Step 4 (G2 / DSS = Papanikolas native reproof) split off to
  `../2-fully-proven/g2-over-fq-papanikolas-dss.md` and **proven** (BRIDGE, Door-5): G2-over-`F_q` =
  Papanikolas under Professor's corank-1 collapse; seam diagnosis (corank gap `∞−1` = the G2
  obstruction) feeds the seam bucket. This parent card now covers **G4 / G5** (Steps 3,5)
  — Wheeler on G5-over-`F_q` (Deligne unitarity); G4 (Deligne–Katz) open.
- 2026-06-19 (Professor) — Step 5 (G4 / Deligne–Katz native reproof) split off to
  `../2-fully-proven/g4-over-fq-deligne-katz.md` and **proven** (BRIDGE, Door-5): `S_ff ∘ #24` recovers the
  Deligne–Katz monodromy (⊗ = tensor of sheaves, Sato–Tate = Katz–Sarnak); weight/angle split
  `1 → G^0_geom → G_L → W → 1` with `dim W = corank = 1` (the #121 corank-1 diagonal = the weight torus).
  Parent now covers **G5-over-`F_q`** (Wheeler) only; G3 trivial over `F_q`.
- 2026-06-19 (Wheeler) — **Step 3 (G5 / Deligne unitarity) DONE** → `../2-fully-proven/g5-over-fq-deligne-unitarity.md`
  (BRIDGE, Door-5): RH-over-`F_q` reproved as the field's G5 = unitary holonomy on the σ-fixed-modulus locus
  (`S_ff`: locus `|x_v|=q^{-deg v/2}` → weight circle `|α|=q^{w deg v/2}`; FE=Poincaré duality + polarization
  ⟹ normalized Frobenius unitary = Deligne Weil II). The modulus face complementing g4's angle face.
  Difference=archimedean cataloged (§3): over ℚ, F₁ must supply the single weight (corank ∞→1) **and** the
  geometric polarization (Weil positivity #38) — the G5 face of #125. **All gatekeepers G1–G5 now recovered
  over `F_q` (Step 6 difference-catalogue fed across #121/#122/#123 + this). Campaign complete; parent can be
  closed by the librarian.**
- 2026-06-19 (Librarian) — campaign parent closed after Wheeler's G5-over-`F_q` card completed the last open gatekeeper. Public ledger row #151 now banks G5-over-`F_q`; row #76 marks the FF G1--G5 campaign complete. Moving this parent from `0-backlog` to `2-fully-proven` as the campaign umbrella.

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. The umbrella says all G1-G5 function-field gatekeepers are recovered and cites split children, including `g4-over-fq-deligne-katz` and `function-field-holonomicity-degeneration`. Those component cards are not currently present in `2-fully-proven` after Lean review, so the campaign parent cannot remain fully proven as an umbrella. Repair requires restoring/proving every component or narrowing the parent to the children that survived review.
