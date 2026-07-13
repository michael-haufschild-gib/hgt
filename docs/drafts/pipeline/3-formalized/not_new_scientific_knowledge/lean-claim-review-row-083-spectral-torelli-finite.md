# Lean claim review row #83 — finite spectral Torelli

- **ID:** lean-claim-review-row-083-spectral-torelli-finite
- **Stage:** 3-formalized
- **Type:** claim-review (AUDIT PASSED 2026-06-19, Professor) — Door grade **BRIDGE** (Newton / symmetric-function faithfulness)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #83; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean, finite)`; matching split certificate:
  `../3-formalized/finite-power-sum-spectral-torelli.md`.
- **Statement:** Spectral Torelli: `{s_m}` determine `xi`, in the finite sense claimed by the ledger.

## Goal
Audit the claim from scratch. Researchers must pin down the finite statement precisely and separate it from any infinite or actual-`xi` reconstruction claim. Leaner checks formalization after that scope review.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/RHTower/SpectralTorelli.lean`
- Candidate names: `spectralTorelli_faithful`, `spectralPoly_coeff_zero`, `selfDual_spectralPoly_coeff_real`

These names are leads, not certification.

## Gates
- [x] 0 -> 1: audited (Professor); finite statement = FAITHFULNESS (power sums ↔ multiset), NOT actual-ξ reconstruction (correctly excluded by the file)
- [x] 1 -> 2: confirmed sound (polynomial↔multiset↔power-sums bijection via Newton, char 0); verified symbolically
- [x] 2 -> 3 formalized: Leaner verified exact theorem names by scratch file; `#print axioms` reports only
  the allowed standard subset; `lake build` green; `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Review finite multiset reconstruction from power sums/Newton identities and decide exactly what "determine `xi`" means in this finite ledger row.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean, finite)` ledger row.

## AUDIT — 2026-06-19 (Professor): claim VERIFIED, correctly scoped (faithfulness only)

Read `SpectralTorelli.lean` — honestly scoped to the **injectivity/faithfulness** half of B29 (the file states
it explicitly excludes the image / three-cut (E)/(A)/(P) characterization, RH, DSS, realization).
- **`spectralTorelli_faithful`:** the monic spectral polynomial `∏_{ρ∈s}(X−ρ)` faithfully determines the zero
  multiset `s` (inverse map `Polynomial.roots`). Via Newton identities (char 0), the secular power sums
  `s_m=Σ_ρ ρ^m` are equally faithful coordinates.
- **`spectralPoly_coeff_zero` / `selfDual_spectralPoly_coeff_real`:** the constant coefficient; self-dual
  multiset ⟹ real coefficients.

**Verification (symbolic).** Multiset `{2,3,3,5}` reconstructed exactly from its power sums `[13,47,187,803]`
via Newton → `e=[13,61,123,90]` → monic `X⁴−13X³+61X²−123X+90` → roots `{2,3,3,5}`. Distinct multiset
`{2,2,4,5}` has distinct power sums. So `multiset ↔ e_k ↔ monic poly ↔ power sums` is bijective. ✓

**Door-2: BRIDGE.** Fundamental theorem of symmetric functions + Newton's identities (char 0) + the
polynomial↔roots bijection. Elementary, true. The ledger `THEOREM (Lean, finite)` tag is appropriate for the
faithfulness statement.

**Scope (the audit's key point, correctly drawn by the file).** Formalized = FAITHFULNESS (the spectrum
determines the *finite* multiset). NOT formalized = (i) the **image** (which multisets are genuine ξ-zero
sets — the hard inverse problem), (ii) any **actual/infinite ξ** reconstruction, (iii) RH/DSS. So "spectral
Torelli" here is the easy (injectivity) direction, not the inverse problem. **Verdict: SOUND** →
2-fully-proven; 2→3 Lean check remains Leaner's.

## Lean certification — 2026-06-19 (Leaner)

Verified the exact Lean names from scratch:
`GaloisForLFunctions.esymm_eq_of_powerSum_eq`,
`GaloisForLFunctions.powerSum_torelli`,
`GaloisForLFunctions.esymm_eq_of_powerSum_eq_le`,
`GaloisForLFunctions.powerSum_torelli_finite`,
`GaloisForLFunctions.exists_powerSum_ne_of_ne`,
`GaloisForLFunctions.spectralTorelli_faithful`,
`GaloisForLFunctions.spectralPoly_coeff_zero`, and
`GaloisForLFunctions.selfDual_spectralPoly_coeff_real`. `#print axioms` for the finite Torelli and spectral
faithfulness theorems uses only `[propext, Classical.choice, Quot.sound]`, and the theorems are already included
in `scripts/check_axioms.sh`. The scoped row #83 claim is fully covered by the split stage-3 certificate
`../3-formalized/finite-power-sum-spectral-torelli.md`; actual/infinite `xi` reconstruction remains explicitly
out of scope.
