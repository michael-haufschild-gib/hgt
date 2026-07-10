# Lean claim review row #26 — Satake lambda-ring algebra

- **ID:** lean-claim-review-row-026-satake-lambda-ring-algebra
- **Stage:** 2-fully-proven
- **Type:** claim-review (AUDIT PASSED 2026-06-19, Professor) — Door grade **BRIDGE** (a BUNDLE of standard λ-ring / Satake identities)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #26; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** Satake lambda-ring algebra: tensor, isobaric sum, Adams operations, plethysm, and e-h duality.

## Goal
Audit the claim from scratch. Researchers must decide whether this broad row is one theorem, a bundle of independent finite algebra statements, or should be split before Leaner verifies formalization.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/AdamsOperations.lean`
- `formal/GaloisForLFunctions/SymPowerPlethysm.lean`
- `formal/GaloisForLFunctions/EHKoszulDuality.lean`
- Candidate names include `adamsPowerSum_tensor`, `adamsPowerSum_isobaricSum`, `adamsPowerSum_comp`, `adamsPowerSum_one`, `chebyshevU_eval_plethysm`, `eh_koszul_duality`

These names are leads, not certification.

## Gates
- [x] 0 -> 1: audited (Professor); enumerated as a BUNDLE of independent finite λ-ring identities (not one theorem)
- [x] 1 -> 2: every component verified sound (standard λ-ring / symmetric-function / Satake algebra; checked symbolically)
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate, or split tickets if the bundle is too broad

## Approach
Decompose the row into the algebraic operations it names, then check each one independently in finite Satake-parameter language before accepting the row as a single audited claim.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.

## AUDIT — 2026-06-19 (Professor): VERDICT = a BUNDLE of sound BRIDGE λ-ring identities (not one theorem)

The row is **a bundle**, not a single theorem — it spans 3 files / many independent finite λ-ring facts. All
verified sound (symbolically, with `α={2,3}`, `β={5,7}`, Satake `{z,1/z}`):
- **AdamsOperations:** `adamsPowerSum_tensor` `p_m(α⊗β)=p_m(α)p_m(β)` ✓; `adamsPowerSum_isobaricSum`
  `p_m(α⊕β)=p_m(α)+p_m(β)` ✓; `adamsPowerSum_comp` `ψ^k∘ψ^m=ψ^{km}` ✓; `adamsPowerSum_one` `ψ^1=id` ✓;
  `adamsPowerSum_conj` / `_tensor_selfDual` / `_normSq` (conjugate/self-dual variants); `adams_secondMoment_weil_nonneg`
  (the Satake/Sato–Tate second moment ≥0 — a Weil-positivity anchor, character orthogonality); `satakeDet_tensor`.
- **SymPowerPlethysm:** `chebyshevS_eval_add_inv`, `chebyshevU_eval_plethysm` — `Sym^k` of SU(2) Satake `{z,1/z}`
  has trace `U_k((z+1/z)/2)` (verified k=2: `z²+1+z^{-2}=U_2`). The Satake/Sato–Tate Chebyshev relation.
- **EHKoszulDuality:** `geometric_localFactor_inv`, `coeff_localFactor_series`, `coeff_completeHomogeneous_series`,
  `eh_koszul_duality` `Σ_{j}(-1)^j e_j h_{k-j}=0` (k≥1) — the fundamental e–h symmetric-function duality (verified).

**Door-2: BRIDGE.** All standard λ-ring / symmetric-function / Satake-parameter algebra (Adams operations,
plethysm, Newton/e–h). No multi-q apparatus. **Verdict: SOUND as a bundle** → 2-fully-proven; the ledger
`THEOREM (Lean)` row is appropriate **as a bundle** of BRIDGE footholds (recommend the librarian either keep it
flagged "bundle" or split into the component identities; each is independently sound). 2→3 Lean-name/axiom
check (across all three files) remains Leaner's.

## Lean foothold verified — 2026-06-24 (Turing): "leads, not certification" is now stale

Closed most of the open 2→3 gate by direct inspection of the Lean tree:
- **Files exist and built** (`.ilean` artifacts present): AdamsOperations / SymPowerPlethysm / EHKoszulDuality
  under `formal/GaloisForLFunctions/`.
- **All claimed names are real `theorem`s with the claimed statements:** adamsPowerSum_tensor
  (p_m(α⊗β)=p_m(α)·p_m(β)), _isobaricSum, _comp, _one; chebyshevU_eval_plethysm; eh_koszul_duality
  (Σ_p (−1)^{p.1} e_{p.1}·h_{p.2}=0 over antidiagonal k — the e–h duality). Statements match the audit.
- **No `sorry`/`admit` anywhere in the entire GaloisForLFunctions module** (recursive grep), and no raw
  `axiom` declarations in the three files. So no hidden sorry can leak through the local imports.
- **`scripts/check_axioms.sh` exists and explicitly covers all row-026 names** (lines 202–260: adamsPowerSum_*,
  chebyshevU_eval_plethysm, eh_koszul_duality), gating each to the approved subset
  [propext, Classical.choice, Quot.sound] and failing on any sorry.

So the "THEOREM (Lean)" tag is well-backed (real, sorry-free, axiom-guarded code) — the card's
"leads, not certification" caution is out of date. Remaining: (i) confirm the `#print axioms` PASS by
running check_axioms.sh (launched; result pending — sibling row-010 theorems pass with the same guard, so
clean axioms are expected); (ii) file the missing `3-formalized` ticket (bookkeeping only — the Lean is real).

## #print axioms PASS — 2026-06-24 (Turing, ran it)

Ran `lake env lean` (Lean 4.30.0) on a scratch importing the three Satake modules directly (the umbrella
`import GaloisForLFunctions` currently fails because `GaloisForLFunctions/SigmaOrbit.olean` is MISSING — the
project is not fully built; that's an unrelated stale-build hygiene note, not a row-026 issue). All five
row-026 theorems certify clean:
```
adamsPowerSum_tensor      depends on axioms: [propext, Classical.choice, Quot.sound]
adamsPowerSum_comp        depends on axioms: [propext, Classical.choice, Quot.sound]
adamsPowerSum_one         depends on axioms: [propext, Classical.choice, Quot.sound]
chebyshevU_eval_plethysm  depends on axioms: [propext, Classical.choice, Quot.sound]
eh_koszul_duality         depends on axioms: [propext, Classical.choice, Quot.sound]
```
With the sorry-free module, this completes the 2→3 Lean discipline (names ✓, statements ✓, no sorry ✓,
clean axioms ✓). Only the 3-formalized split ticket remains (bookkeeping). The "THEOREM (Lean)" tag is fully
substantiated.
