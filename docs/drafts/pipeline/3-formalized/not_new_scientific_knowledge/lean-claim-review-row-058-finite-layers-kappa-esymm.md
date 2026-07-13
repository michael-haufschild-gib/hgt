# Lean claim review row #58 — finite `kappa_-` and elementary-symmetric layers

- **ID:** lean-claim-review-row-058-finite-layers-kappa-esymm
- **Stage:** 3-formalized
- **Type:** claim-review (Lean-certified split; AUDIT DONE 2026-06-19, Professor) — verdict: VALID as a CONJUNCTION of two separate BRIDGE footholds; NOT a combined theorem
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #58; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)` resolved by split certificates in `../3-formalized/`: row #32 for `kappa_-` and `finite-esymm-algebraic-independence.md` for the esymm layer.
- **Statement:** both finite layers are ledgered: exact `kappa_-` and elementary-symmetric algebraic independence.

## Goal
Audit the claim from scratch. Researchers must decide whether this compound row is a legitimate combined theorem or simply references two separate finite Lean footholds. Leaner verifies formalization only after the row is scoped.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/HTGeometry/CarrierCauchy.lean`
- `formal/GaloisForLFunctions/HTGeometry/SpectrumGenericity.lean`
- Candidate names: `multiPair_carrier_exact_neg_inertia`, `spectrum_esymm_algIndep`

These names are leads, not certification.

## Gates
- [x] 0 -> 1: audited (Professor); decision = SPLIT (row #32 κ₋ RH-face + finite DSS-face esymm), see verdict
- [x] 1 -> 2: both footholds confirmed sound (precise statements below); compound row = their conjunction, no unification content
- [x] 2 -> 3 formalized: Leaner verified exact theorem names by scratch file; `lake build` green; `scripts/check_axioms.sh` PASS; compound row certified only as a split/conjunction, not a combined theorem
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate, or split tickets if needed

## Approach
Review the RH finite layer (`kappa_-`) and the DSS finite layer (`esymm` algebraic independence) independently, then determine whether the A1/A2-unification row asserts anything beyond their conjunction.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.

## AUDIT — 2026-06-19 (Professor): VERDICT = conjunction of two separate BRIDGE footholds; NOT a combined theorem

This compound ledger row asserts two finite layers. Audited each from scratch and the compound claim.

**Layer 1 — RH-face, exact `κ₋`** (`multiPair_carrier_exact_neg_inertia`, CarrierCauchy.lean). **SOUND** —
fully audited in `row-032` (→ 2-fully-proven): `H=[W|U]diag(I_k,−I_k)[W|U]*`, carrier independence ⟹ Sylvester
⟹ `κ₋ = #off-line conjugate pairs`. BRIDGE (Krein–Langer + Sylvester). Numerically verified k=1..6.

**Layer 2 — DSS-face, `esymm` algebraic independence** (`spectrum_esymm_algIndep`, SpectrumGenericity.lean).
**SOUND but it is the FORMAL fact, not arithmetic DSS.** The Lean statement is
`AlgebraicIndependent ℚ (fun i:Fin n => MvPolynomial.esymm (Fin n) ℚ (i+1))` — the elementary symmetric
*polynomials* `e_1,…,e_n ∈ ℚ[X_1,…,X_n]` are algebraically independent. That is exactly the **fundamental
theorem of symmetric polynomials** (proof: `esymmAlgHom_injective` — `ℚ[Y]→Sym`, `Y_i↦e_i`, is an iso). It is
the **generic/formal finite shadow** of the DSS genericity face: the *generic* n-point spectrum has full
trdeg n. It says **nothing about the arithmetic** of the actual ζ-zeros (the `e_i` evaluated at the true
zeros being alg. independent numbers = the real DSS content, FIELDS-MEDAL/Schanuel, untouched here). Door-2:
strips to the fundamental theorem of symmetric polynomials — **BRIDGE (trivial)**.

**The compound-row question — VERDICT.** Row #58 asserts **nothing beyond the conjunction** Layer1 ∧ Layer2.
The two are facts about **orthogonal structures**: Layer 1 = negative inertia of the carrier Pick/Cauchy form
(localization), Layer 2 = formal symmetric-polynomial independence (genericity). They share only "the
spectrum" as a common object; no theorem links them. **An "A1/A2-unification" reading is REJECTED** — it would
contradict the project's proven **A1/A2 decoupling** (#191/#54: RH-polarization and DSS-genericity are two
seam-joined apexes, neither forcing the other). The conjunction of a localization fact and a genericity fact
is **not** a unification.

**Disposition (per the card's split gate).** SPLIT, do not keep as a "combined theorem":
- Layer 1 (κ₋) → `row-032` (2-fully-proven, done).
- Layer 2 (esymm) → ledger as a **separate** precise foothold: "the formal elementary-symmetric polynomials are
  ℚ-algebraically independent (fundamental theorem of symmetric polynomials) — the generic/formal finite shadow
  of the DSS genericity face; NOT arithmetic transcendence of the zeros." BRIDGE.
- Row #58 as a *combined/unification* theorem: **does not exist** — recommend the librarian re-ledger row #58
  as two separate rows and drop the "combined" framing. The audit itself (both layers sound, conjunction not
  unification, esymm = formal-shadow) is the deliverable → 2-fully-proven.

**Net scientific point:** this reaffirms the A1/A2 decoupling at the finite-layer level and prevents an
overclaim — the `esymm` foothold is the FORMAL genericity shadow (fundamental theorem of symmetric
polynomials), categorically distinct from the arithmetic DSS apex (Schanuel, open). No combined RH⊗DSS theorem
is hiding in row #58.

## Leaner certification — 2026-06-19

Verified exact Lean names by scratch file with `import GaloisForLFunctions`:
- `GaloisForLFunctions.multiPair_carrier_exact_neg_inertia`
- `GaloisForLFunctions.spectrum_esymm_algIndep`

`multiPair_carrier_exact_neg_inertia` is certified separately by row #32 in `3-formalized`. The esymm layer is
certified separately in `finite-esymm-algebraic-independence.md` via `spectrum_esymm_algIndep`, whose statement is
`AlgebraicIndependent Q (fun i : Fin n => MvPolynomial.esymm (Fin n) Q (i+1))`. `#print axioms` for both row #58
footholds reports only `[propext, Classical.choice, Quot.sound]`.

This moves row #58 only as a Lean-certified split/audit certificate. It does not assert a combined RH-face/DSS-face
unification theorem.

Verification commands:
- `cd formal && lake env lean /tmp/row058_check.lean`
- `cd formal && lake build GaloisForLFunctions`
- `bash scripts/check_axioms.sh`
