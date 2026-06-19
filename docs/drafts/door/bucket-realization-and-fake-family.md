# Bucket X5 — Realization & fake-family

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`.
**Scope (one line).** Genuineness is the **Euler cut (A)**, not the positivity cut (P): positivity
alone passes the fakes (Davenport–Heilbronn), so any RH criterion must be conjoined with
arithmeticity — and the deepest open question is the **converse** (realization): does (positivity ∧
genericity ∧ FE) ⟹ Euler-realized?
**Work package this seeds.** Settle the **realization problem** (is the organizing law Euler ⟺
two-faces an IFF?), and bake the **fake-family filter** into every positivity/unitarity criterion.

> **Why this is its own bucket.** It is the precise, repeatedly-confirmed reason **positivity cannot
> prove RH by itself** — the integrality/no-margin lesson in inverse-problem form. It governs how every
> other bucket's "RH ⟺ positive" claim must be qualified.

---

## Genuineness = the Euler cut, not positivity — the three cuts (#75)
- §2 the inverse-problem image `Φ({ξ})` = **THREE INDEPENDENT cuts** on moment space:
  - **(E)** existence/realizability (order-1, FE-symmetric divisor),
  - **(A)** arithmeticity = Euler product (the `EulerProduct.lean` firewall),
  - **(P)** positivity = RH (Li/Bogomolov).
  **RH is ONLY cut (P).** The fakes (Davenport–Heilbronn) live in `(E)∧¬(A)` and **can satisfy
  Hankel-positivity without being genuine** ⟹ **positivity (P) does NOT imply arithmeticity (A).** *Any
  criterion that "sees RH" from positivity alone has confused (P) with (A) and will pass a fake.*
- §1 Spectral Torelli (PROVED, ledger `powerSum_torelli`): the secular moments `{s_m}` **determine** ξ
  (Hadamard + FE) — the coordinates are FAITHFUL, justifying Object-X. *(Caveat: finite version =
  symmetric-function theory, likely IMPORT under Door-2; the infinite resolvent/Hadamard passage is
  native Tier-B.)*
- §3 **overdetermination = the defining equation of genuineness:** each `s_m` is computable two ways
  (zeros `Σ_ρ ρ^{−m}` vs primes via `−ξ'/ξ`); a genuine spectrum is the **overdetermined locus where
  they agree for all `m`** (image thin, infinite-codimension). Candidate **G17 (overdetermination):**
  "RH-bearing objects = the zero-side=prime-side overdetermined locus ∩ (E)∧(A); the explicit formula
  is its equation system."

## RH is rare in the moduli of prime systems (#84 — Diamond's off-line examples)
- The moduli `𝓟` = cone of positive prime measures `dΠ`; ℤ is one point. Stratified (Beurling–Diamond):
  PNT ⊃ continuation ⊃ **Euler/genuine (the §9 firewall stratum, THIN, cut by multiplicativity NOT
  positivity)** ⊃ RH. **KEY IMPORT (Diamond–Montgomery–Vorhauer): Beurling systems with zeros OFF the
  line EXIST** ⟹ off-line zeros are **GENERIC** in `𝓟`; RH is a special/non-generic stratum, and the
  ℤ-point's RH is **arithmetic-forced** (requires the Euler structure). *Concrete witness that
  genuineness is the Euler cut, and that RH is rare in the deformation family.*
- §3 the tangent/deformation map `δΠ↦δ{γ}` = the explicit formula; ℤ = a critical point of the
  "RH-defect" functional; **RH = ℤ is a MINIMUM** (Bogomolov-minimality, B7). (→ [[G5-unitarity-gatekeeper]],
  [[bucket-the-no-margin]])

## The realization problem — the converse of the First Theorem (#85 SEED-V, #98)
- **SEED-V (#85, B26) — the deepest cell:** "Transcendence creates the spectrum" = the **CONVERSE** of
  the First Theorem. First Theorem: *Euler product ⟹ two-faces structure*; B26 = *(Face A positivity ∧
  Face B genericity ∧ FE) ⟹ realized by an Euler product* = **the realization problem (grand conjecture
  #7):** `∃ source-built g with g⋆g* = Ω_∞ − prime-comb`. **"Is the organizing law an IFF?"** Directly
  the A1/A2 unification as a realization statement (a `g` realizing both positivity and genericity).
- #98 Attack 5 / synthesis: **RH ⟺ ξ ∈ LP ⟺ ξ is an LP-limit** — RH is a
  **closedness/identification problem, not a positivity one** (positivity is automatic along the LP
  family, each step a Pólya–Schur multiplier `e^{x/p}`; the content is that the *arithmetic* limit
  lands on ξ). *= the realization problem #7 / B6 / B34.* Ledger floor: `MultiplierScaling`
  (`sigmaScale_splits`). (→ [[G5-unitarity-gatekeeper]] LP-limit face)

## The superzeta is itself a "fake" — the First Theorem adjudicates (#80)
- The superzeta `𝒵(w)=Σ_ρ ρ^{−w}` has **no Euler product** (frequencies `{log ρ}` not on a ℚ-LI
  multiplicative base) ⟹ by the First Theorem it is a "fake" — the transcendence tower `ζ→𝒵→…` does
  **not** recurse spectrally. *"Fixed point = the prime" is a seam-collapse category error.* Ledger
  witness `SuperzetaResolvent` (Σ additive, not ∏). A model of the field rejecting its own wild
  conjecture by its own First Theorem. (→ [[bucket-the-seam-archimedean-obstruction]] for the live
  *motivic* tower SEED-U)

## The fake-family filter (the discipline, from `testing.md` + the corpus)
- A genuine mechanism must **reject the known non-examples** (Davenport–Heilbronn, Epstein). The field's
  First Theorem (`EulerProduct.lean`, incl. a concrete mod-5 fake coefficient witness): **no Euler
  product ⟹ no Bohr-lift factorization, detectable at a finite `n`** — *pre-spectral.* A new criterion
  that passes a fake is wrong.
- **Anti-circularity:** a construction must be **source-pure** (built from primes/μ/ζ-data, not the
  zeros it constrains). The κ₋ carrier theorems are source-pure by design (so they convert the wall into
  a tide gauge but cannot themselves conclude κ₋=0).

---

## Status & the governing rule
- **PROVED / ledgered:** the (E)/(A)/(P) cut structure rests on the First Theorem (`EulerProduct.lean`)
  + Torelli (`powerSum_torelli`); the superzeta-fake verdict (`SuperzetaResolvent`); the LP finite floor
  (`MultiplierScaling`). The off-line Beurling examples are an **IMPORT** (Diamond–Montgomery–Vorhauer).
- **The governing rule for the whole corpus:** every "RH ⟺ positive/unitary" claim in
  [[G5-unitarity-gatekeeper]] / [[bucket-the-no-margin]] must be **conjoined with the Euler cut (A)** or
  it is provably insufficient (passes a fake). Positivity is necessary, never sufficient.

## Open core / the work package
**The realization problem (SEED-V / #7):** is `Euler product ⟺ two-faces` an **IFF**? Equivalently, does
the prime-deformed LP family's limit *identify* with ξ (#98)? This is the converse of the field's only
theorem and the A1/A2 unification stated as existence-of-`g`.

## Cross-references
- [[G5-unitarity-gatekeeper]] — must be conjoined with the Euler cut to reject fakes.
- [[bucket-the-no-margin]] — the no-margin/integrality lesson is the same "genuineness = Euler cut."
- [[G4-multi-q-picard-vessiot-and-langlands-group]] — `ω=0` (Tannakian/motive) is the realization's
  algebraic shadow.
- [[bucket-A1-A2-unification-the-carrier]] — realization = "∃ g realizing both faces."
