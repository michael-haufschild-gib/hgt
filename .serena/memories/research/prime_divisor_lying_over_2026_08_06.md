# Surjectivity of the divisor map proved — every abstract hypothesis now discharged (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(still stage 2, but the local model is now hypothesis-free).

## New module

`GaloisForLFunctions/HTGeometry/PrimeDivisorLyingOver.lean`

| statement | declaration |
|---|---|
| zero ideal contracts to zero | `comap_bot_eq_bot` |
| **prime over a prime divisor is a prime divisor** | `height_eq_one_of_comap_height_eq_one` |
| **every prime divisor downstairs is dominated** | `exists_heightOne_comap_eq` |

Hypotheses: integral extension of domains with injective structure map
(`[Algebra.IsIntegral R S] [FaithfulSMul R S]`).  All axiom-clean.

## Proof route

`height p ≥ 1`: `p = ⊥` would give `q = comap ⊥ = ⊥`, contradicting
`Ideal.ne_bot_of_height_eq_one`.
`height p ≤ 1`: for prime `p' < p`, `Ideal.IsIntegral.comap_lt_comap` (incomparability) gives
`comap p' < q`; then **feed `hq : q.height = 1` into `Ideal.height_le_iff` directly** to get
`(comap p').height < 1`, hence `= 0` (`Order.lt_one_iff`), hence `comap p' = ⊥`
(`Ideal.height_eq_zero_iff_eq_bot`, needs `IsDomain`), hence `p' = ⊥`
(`Ideal.eq_bot_of_comap_eq_bot`).  Then `Ideal.height_bot` finishes.
Lying over: `Ideal.exists_ideal_over_prime_of_isIntegral q ⊥ (by rw [comap_bot_eq_bot]; exact bot_le)`.

## Lean traps hit

- `Ideal.height_le_iff` is stated with `{n : ℕ}` and `p.height ≤ ↑n`, so a goal `p.height ≤ 1`
  with the **ℕ∞ literal** does not match.  State the `have` as `≤ ((1 : ℕ) : ℕ∞)` and
  `rw [Nat.cast_one]` afterwards.
- Using `height_add_one_le_of_lt_of_isPrime` forces ℕ∞ arithmetic (`h + 1 ≤ 1 ⟹ h = 0`), which
  `exact?`/`simp`/`omega` all fail on.  **Going through `height_le_iff` avoids arithmetic
  entirely** — much better route.
- `IsIntegral.comap_lt_comap` lives in namespace `Ideal`, i.e. `Ideal.IsIntegral.comap_lt_comap`.

## Card status: the abstract system is now fully instantiated

Every hypothesis of `EigenvolumeRamificationSystem.lean` is a theorem in the local Noetherian
model:
- `hlaw` — `ramificationShiftLaw_frac` (`LocalRamificationOrderLaw.lean`), forms with poles;
- `1 ≤ e` — `one_le_ord_map_uniformizer` (`RingOrdRamification.lean`), needs **locality**;
- `hfin` — `finite_heightOneSupport_frac` (`DivisorSupportFinite.lean`);
- surjectivity — `exists_heightOne_comap_eq` (this module).
Plus (7) `TopExteriorPowerDeterminant`, the `e−1` `TameEisensteinDifferentExponent`, and the
sharpened step 4.

Remaining: only the passage from this model to a smooth projective variety — identifying a
rational top form with a coframe top wedge, and transporting the local law along a morphism of
schemes (`AlgebraicGeometry.ord` pullback law; `AlgebraicCycle` is still a stub).  See
`research/ring_ord_ramification_bridge_2026_08_06`.

## Repo hazard

Lint gate reports another agent's unwired untracked `HTGeometry.QuadraticTransportCost`.
Earlier today the same gate reported a `sorry` in `RHTower/MobiusCriticalTransportAssembly.lean`.
Always `git status` first.
