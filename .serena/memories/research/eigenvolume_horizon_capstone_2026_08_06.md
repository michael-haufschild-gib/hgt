# Capstone + pullback law: Theorem A for genuine prime divisors (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(stage 2).  **Modules 12 and 13 of this card's lineage.**

## `EigenvolumeHorizonCapstone.lean` (module 12)

| Theorem A item | declaration |
|---|---|
| prime divisor below a prime divisor | `divisorBelow` |
| integer order of a rational form `a/b` | `formOrder` |
| **finiteness of the divisorial support** | `finite_formOrder_support` |
| **(2),(5) horizon is a reduced divisor** | `formOrder_eq_neg_one` |
| **(3) total invariance** | `formOrder_ne_zero_iff` |
| **(4) unramified off the horizon** | `ramificationIndex_eq_one_off_horizon` |

`B` normal Noetherian domain, self-map `φ : B →+* B`.
`formOrder a b P := (orderAt P a).toNat − (orderAt P b).toNat : ℤ` — signed, so poles are
representable.

**The `Algebra B B` clash was avoided entirely** by phrasing well-definedness and surjectivity of
`divisorBelow` as `comap`-shaped hypotheses (`hwd`, `hsurj`), which `PrimeDivisorLyingOver.lean`
discharges in the `Algebra` formulation.  No `letI := φ.toAlgebra` was needed.

## `EigenvolumePullbackLaw.lean` (module 13) — `hlaw` discharged

`orderAt_ne_top`, `orderAt_mul`, `orderAt_toNat_spec`; then
`formOrder_pullback_shiftLaw`: pullback of `a/b` is `(φ a · J)/(φ b)`, so if
`orderAt P J = e − 1` then `formOrder (φ a * J) (φ b) P + 1 = e * (formOrder a b Q + 1)`.
Adding the **eigenvolume condition** `∀ P, formOrder (φ a * J) (φ b) P = formOrder a b P`
gives `eigenvolume_shiftLaw`, hence `eigenvolume_formOrder_eq_neg_one`,
`eigenvolume_formOrder_ne_zero_iff`, `eigenvolume_ramificationIndex_eq_one_off_horizon`
**with `hlaw` no longer a hypothesis**.

Remaining data is geometric, not valuation-theoretic: (a) the eigenvolume condition,
(b) `orderAt P J = e P − 1` for a general normal domain (proved here only in the Eisenstein
presentation, `TameEisensteinDifferentExponent.lean`).

### Lean traps hit here
- `rw [hqa]` where `hqa : orderAt Q a = ↑(orderAt Q a).toNat` **loops** (rewrites inside its own
  RHS).  Fix: `obtain ⟨na, hna⟩ : ∃ n : ℕ, orderAt Q a = (n : ℕ∞)` so the nat is opaque.
- `push_cast` in ℕ∞ is unsafe (`ring` fails, ℕ∞ is not a ring).  Use explicit
  `Nat.cast_add`/`Nat.cast_mul` rewrites; do the `push_cast`/`ring` in ℤ only.
- Section `variable`s that appear only in the *proof* are not auto-bound — need
  `include h₁ h₂ in` **before the docstring** (same placement rule as `omit ... in`).

## Card lineage (13 modules, all axiom-clean)

`RamificationPoleFixedPoint`, `EigenvolumeRamificationSystem`, `TameEisensteinDifferentExponent`,
`TopExteriorPowerDeterminant`, `LocalRamificationOrderLaw`, `RingOrdRamification`,
`DivisorSupportFinite`, `PrimeDivisorLyingOver`, `LocalizationAtPrimeDivisorDVR`,
`PrimeDivisorOrder`, `PrimeDivisorPullbackOrder`, `EigenvolumeHorizonCapstone`,
`EigenvolumePullbackLaw`.

## Remaining

1. The different exponent `e − 1` beyond the Eisenstein presentation.
2. Scheme-level passage: rational top form = coframe top wedge; `AlgebraicGeometry.ord` pullback
   law; `AlgebraicCycle` is a mathlib stub.
3. Corollary B (MMP) — far out.
