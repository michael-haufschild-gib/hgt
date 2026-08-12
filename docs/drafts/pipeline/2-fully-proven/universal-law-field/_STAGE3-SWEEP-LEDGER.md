# Universal-law-field stage-3 sweep ledger

**Scope correction (2026-08-12).**  This sweep owns only the cards *directly* in
`docs/drafts/pipeline/2-fully-proven/universal-law-field/`.  Every card inside a subfolder belongs
to a different agent and is not audited or promoted here.

A card is `DONE` only when every displayed theorem is closed unconditionally in Lean, the modules
are wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`, the axiom print is clean, and the
card has been moved into `docs/drafts/pipeline/3-formalized/universal-law-field/`.

| # | Card | Status |
|---|---|---|
| 1 | `beurling-cross-system-blindness-of-multiplicative-regularization-law.md` | NEEDS-LEAN — card flagged [NO LEAN]; corpus parent MultiplicativeRegularizationBlind.lean exists, necessity axiom N1 needs its own module |
| 2 | `c1-o-open-core-reduction-theorem.md` | NEEDS-LEAN — assembly card flagged [NO LEAN — user directive]; components are in-tree |
| 3 | `condensed-phase-probabilistic-death-modulus-budget-and-gaussian-fluctuation-law.md` | NEEDS-LEAN — audit which clauses already have modules |
| 4 | `critical-locus-hessian-classification-and-crystalline-transversality-law.md` | IN PROGRESS — Theta1 certified, Theta2 second-jet identity, Theta3.2 and Theta3.1 kernel identity certified (CriticalLocusQuadrupleEvenness, CrystallineShadowTransversality). Left: Theta2 per-zero necessity/mixture (detector-predicate layer), Theta3.1 integral packaging, Theta4 (configuration-family IFT layer) |
| 5 | `eigen-pair-prime-identification-derivation.md` | PAPER-INCOMPLETE — card states D3–D6 open; only D1–D2 are derived, so full formalization is blocked on the paper proof |
| 6 | `finite-amplifier-width-cap-and-fejer-ratio-barrier-law.md` | NEEDS-LEAN — frame-level discharge of ULF-INV-4 open core |
| 7 | `g-u-structure-admission-split-law.md` | NEEDS-LEAN — typing-grade split law flagged [NO LEAN — directive] |
| 8 | `nonvacuous-independence-and-polarization-import-law.md` | BLOCKED-ON-PREREQ — quantitative core certified (SelbergSpectralParameter); the rest is citation-level and needs a hyperbolic-surface spectral layer (Laplace spectrum, Eisenstein series, Maass-Selberg truncation, Selberg trace formula and zeta) absent from mathlib and the corpus |
| 9 | `odd-coordinate-mechanism-universal-law-set.md` | NEEDS-LEAN — law set; Law 6 proved here |
| 10 | `parity-duality-rg-shell-splitting-and-multiplicative-resolution-cap-law.md` | NEEDS-LEAN — signed-sector and organ-scope law |
| 11 | `pole-purchase-escape-and-collision-gap-law.md` | NEEDS-LEAN — necessity axiom N6 and amplification-gap opening |
| 12 | `route-q-ratio-gate-decision.md` | BLOCKED-ON-NUMERICS — gate mechanism certified (DivisorHeightRatioGate: height damping, unconditional geometric decay, `9 < c` implies the gate); remaining inputs are gamma_1 > 9 (verified-zero computation) and a signed-moment lower bound (zero-location input) |
| 13 | `specification-consistency-polarization-independence-and-cusp-concentration-law.md` | NEEDS-LEAN — consistency and independence metatheorem for the inverse-theory axioms |

Completed and promoted:

- `source-formation-harmonic-mechanics/source-native-five-shadow-formation-fusion-and-selection-gate-law.md` — 2026-08-11 (FF.19/FF.20 receiver clauses added)
- `source-formation-harmonic-mechanics/bilateral-reflection-formation-energy-unitarity-selection-law.md` — 2026-08-11

- `pole-unit-formation-mechanics/pole-unit-scale-cocycle-correction-jet-reconstruction-and-divisor-memory-law.md` — 2026-08-11
- `complete-test-closure-mechanics/complete-atomic-fourier-hankel-order-and-inertia-fusion-law.md` — 2026-08-11
  (Theorem 5.1 closed by a new complex-Hermitian inertia layer: `HermitianInertia`,
  `CompleteAtomicInertiaFusion`; Theorems 3.1 and 4.1 also closed in concrete matrix form)
- `transverse-information-fusion-mechanics/prime-boolean-mass-hankel-recurrence-transverse-information-law.md` — 2026-08-12
  (new module `PrimeBooleanFusionSourcePacket`: Mass norm identity, moment/Hankel block,
  three-organ conservation and its clock-gap form, two-parameter QFI with the infimum form, the
  single-clock degeneration, the literal prime Gibbs coordinates with the exact half-density
  damping, the `σ`/label half of the reconstruction theorem, the unit-norm Boolean state on
  `ℓ²(𝒫(F))` with its norm recurrence, and the refutation of the zero-transverse-information
  criticality selector.  At the prime source the clock energy moment is derived, so no
  nondegeneracy hypothesis survives)

Cross-area findings during this sweep (not universal-law-field cards, recorded so they are not lost):

- `formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/SocleNoLimit.lean` does not elaborate and is
  not wired into any umbrella.  It is mathlib-drift damage, not an unfinished proof: one `linarith`
  needed `ratio_temperatureParameters` rewritten in the goal as well as the hypothesis (fixed here),
  and the remainder are `measurable_pi_apply … |>.natCast`, `isProbabilityMeasure_map`, and a
  `Finset.sum_mul` rewrite that no longer matches.  Repairing it is a drift task, not a card task.
- The lint gate also reports `HTGeometry.CriticalSchurIdealInertiaTransport`,
  `HTGeometry.EllipticGammaJetRealization` and `RHTower.XiMassRadialRiemannLebesgue` unreachable
  from their area umbrellas.  Those belong to another session's in-flight work; do not rewire them
  blind.

## Lint-gate status during this sweep

The formal lint gate cannot be brought green while another session is writing to the tree.  Two
error classes appear, both from that session, neither from the universal-law-field sweep:

1. `owned module unreachable from theorem-area umbrella` — currently `RHTower.Sieve.Vinogradov*`,
   `RHTower.Suzuki*`, `RHTower.XiResolvent*`, `HTGeometry.ConstraintMotiveRelativity.*`,
   `HTGeometry.CriticalSchurIdealInertiaTransport`.  These are modules added but not yet wired.
2. `stale generated file` for `LEAN_API.md`, `LEAN_GAPS.md`, `LEAN_OVERVIEW.md` — they are stale
   again within minutes of `formal_tools.py index` because Lean files keep changing underneath.

Every module this sweep added is reachable: all twelve are imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`, which `GaloisForLFunctions.HTGeometry`
imports.  Verified module by module.  Re-run the gate when the other session is idle.

## Handoff: next action per in-scope card (2026-08-12)

Dependency order matters — the Θ package is upstream of two other cards.

1. `critical-locus-hessian-…` **(do first)**. Certified: Θ1 (`CriticalLocusQuadrupleEvenness`),
   Θ2's second-jet identity, Θ3.2 and Θ3.1's kernel identity (`CrystallineShadowTransversality`).
   Next: Θ4 (finite evaluation blindness) — needs a configuration-family implicit-function layer;
   then Θ2's per-zero necessity/mixture — needs a detector-predicate layer; then Θ3.1's integral
   packaging against `h`.
2. `odd-coordinate-mechanism-universal-law-set`. A **synthesis card**: Laws 1/2/3 carry no proofs
   of their own, they cite Θ1, Θ2(i)–(v), Θ4. Do not prove anything here until Θ4 lands; then this
   is assembly plus Laws 5 and 6.
3. `finite-amplifier-width-cap-…`. Recorded as a frame-level discharge of Θ4 — also waits on Θ4.
4. `nonvacuous-independence-…`. Core certified (`SelbergSpectralParameter`). Blocked on a
   hyperbolic-surface spectral layer (Laplace spectrum on `Γ\ℍ`, Eisenstein series,
   Maass–Selberg, Selberg trace formula and zeta) absent from mathlib and the corpus.
5. `route-q-ratio-gate-decision`. Mechanism certified (`DivisorHeightRatioGate`). The two residual
   inputs are verified-zero computations, which the session's Lean rule 4 excludes; treat as
   blocked-by-directive rather than open.
6. `eigen-pair-prime-identification-derivation`. Read before attempting: the card states D3–D6 are
   unproved **on paper**, so there is no proven theorem to formalize. Confirm, then leave at
   stage 2 with that recorded.
7. Independent, not yet read under the corrected scope — audit each for displayed theorems first:
   `beurling-cross-system-blindness-…`, `pole-purchase-escape-…`,
   `parity-duality-rg-shell-splitting-…`, `specification-consistency-…`,
   `condensed-phase-probabilistic-death-…`, `g-u-structure-admission-split-law`,
   `c1-o-open-core-reduction-theorem`.
   The `[NO LEAN — user directive]` tags on the last two predate the current goal and are stale;
   treat them as targets, not exemptions.

Reusable infrastructure built during this sweep, corpus-wide: `HermitianInertia` (Sylvester's law
for complex Hermitian matrices), `CompleteAtomicInertiaFusion`, `QuotientFusionProjectionGenesis`,
`CartanWorkProperness`, `FormationCompletionExchangeCalibration`, `InteractionDegreeEscape`,
`CrystallineShadowTransversality`, and the `AbelianZetaGas` socle layer.
