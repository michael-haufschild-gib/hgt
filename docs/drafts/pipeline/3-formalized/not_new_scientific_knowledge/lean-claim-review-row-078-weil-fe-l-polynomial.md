# Lean claim review row #78 — Weil functional equation of the L-polynomial

- **ID:** lean-claim-review-row-078-weil-fe-l-polynomial
- **Stage:** 3-formalized
- **Type:** claim-review (AUDIT PASSED 2026-06-19, Professor) — Door grade **BRIDGE** (esymm/multiset FE skeleton; purity excluded)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #78; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; matching split certificate:
  `../3-formalized/function-field-local-factor-fe-algebra.md`.
- **Statement:** Weil functional equation of the L-polynomial.

## Goal
Audit the claim from scratch. Researchers must distinguish the finite multiset/self-dual polynomial algebra from the full imported Weil theorem over function fields. Leaner checks the formalization only after that scope is fixed.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/RHTower/FunctionFieldFE.lean`
- Candidate names: `functionField_esymm_FE`, `functionField_localFactor_FE`, `multiset_esymm_map_mul`

These names are leads, not certification.

## Gates
- [x] 0 -> 1: audited (Professor); scope fixed = the ALGEBRAIC FE SKELETON (multiset closure ω↦q/ω ⟹ L-poly FE), NOT the full Weil theorem (purity |ω|=√q is excluded/imported)
- [x] 1 -> 2: scoped skeleton confirmed sound (esymm homogeneity + closure hypothesis ⟹ q-weighted palindrome + L-poly FE-invariance); verified symbolically
- [x] 2 -> 3 formalized: Leaner verified exact theorem names by scratch file; `#print axioms` reports only
  the allowed standard subset; `lake build` green; `scripts/check_axioms.sh` PASS.
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Review the reciprocal-root multiset algebra behind the local factor functional equation, then compare that finite algebraic skeleton to the stronger function-field theorem named in the row.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.

## AUDIT — 2026-06-19 (Professor): claim VERIFIED, correctly scoped (algebraic FE skeleton)

Read `FunctionFieldFE.lean` — the file is **honestly scoped**: it formalizes the *algebraic core* of the Weil
FE and **explicitly excludes** the purity `|ω_i|=√q` (RH for curves, Deligne/Weil II). Three footholds:
- **`multiset_esymm_map_mul`:** `e_k(c·S)=c^k e_k(S)` (esymm homogeneity under scaling). Elementary, true.
- **`functionField_esymm_FE`:** IF the eigenvalue multiset `S` is closed under `ω↦q/ω` (the weight-1 /
  Poincaré-duality pairing — a HYPOTHESIS), THEN `e_k(S)=q^k e_k(S^{-1})` (the q-weighted palindrome of the
  L-polynomial coefficients). **Proof:** `S=q/S ⟹ e_k(S)=e_k(q·S^{-1})=q^k e_k(S^{-1})` (homogeneity). ✓
- **`functionField_localFactor_FE`:** `∏(1−ωT)` invariant under `ω↦q/ω` (polynomial-level FE).

**Verification (symbolic).** Self-dual multiset `S={1,2,2,4}`, `q=4` (closed under `ω↦4/ω`): `e_k(S)=q^k e_k(S^{-1})`
for all `k=0..4` (1=1, 9=9, 28=28, 36=36, 16=16); equivalently `e_4·e_k=q^k e_{4-k}` (16·9=4·36 etc.); the
L-polynomial `16T⁴−36T³+28T²−9T+1` is the q-weighted palindrome, FE-invariant. ✓

**Scope (the audit's key distinction, correctly drawn by the file).** Formalized = the FE SYMMETRY from the
closure hypothesis (elementary multiset/esymm algebra). NOT formalized = (i) that the eigenvalues ARE closed
under `ω↦q/ω` (Poincaré duality — imported), (ii) purity `|ω|=√q` (RH/F_q — Deligne, imported). The `q=1`
case is the unitary self-duality `ω↦ω^{-1}` (`LocalFactorDuality`); after `ω=√q·u` the pairing becomes `u↦u^{-1}`
(reduces to the unitary Satake machinery).

**Door-2: BRIDGE.** Elementary symmetric-function / self-dual-multiset algebra; the q-weighting is the Weil
pairing. The ledger `THEOREM (Lean)` tag is **appropriate** for the scoped skeleton. **Verdict: SOUND** →
2-fully-proven; 2→3 Lean-name/axiom check remains Leaner's. (Cross-ref: the `g5-over-fq-deligne-unitarity`
recovery supplies the purity the skeleton omits.)

## Lean certification — 2026-06-19 (Leaner)

Verified the exact Lean names from scratch:
`GaloisForLFunctions.multiset_esymm_map_mul`,
`GaloisForLFunctions.functionField_esymm_FE`, and
`GaloisForLFunctions.functionField_localFactor_FE`. `#print axioms` for all three uses only
`[propext, Classical.choice, Quot.sound]`, and the theorems are already included in
`scripts/check_axioms.sh`. The scoped row #78 claim is fully covered by the split stage-3 certificate
`../3-formalized/function-field-local-factor-fe-algebra.md`; purity/Weil II remains explicitly out of scope.
