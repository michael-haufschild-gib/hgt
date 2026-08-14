# Top-level new_scientific_knowledge stage-2 → stage-3 sweep ledger

Goal (session hook): formalize unconditionally every proven theorem of every TOP-LEVEL card in
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge (subfolders excluded — other agents),
move each card to 3-formalized. No premises/hypotheses standing for analytic inputs, no axioms,
no abstract-wrapper credit. Module builds foreground, one process; axiom audit via scratch file;
wire umbrellas. 27 top-level cards remain as of 2026-08-14.

## Promoted 2026-08-13 (10)
prolate-dunster-exact-arcsine-leakage-limit; mass-shifted-characteristic-apex-energy-boundary-law;
gibbs-batch-entropy-production-nullspace-lift; gibbs-diagonal-entropy-response-no-go;
route-e-deninger-vacuum-finite-dilation-fracture; mass-shifted-projective-low-edge-anchor-cofinal-
spread; hedenmalm-finite-source-port-obstruction; hedenmalm-root-flux-modular-charge-faithfulness;
rank-two-commutator-parity-multiplicity-balance; route-r-reciprocal-log-fisher-half-density-
entrance-wall.

## Promoted 2026-08-14
- route-e-whole-anchor-capacity-displacement-conservation-law — new module
  `RHTower/MobiusWholeAnchorTerminalDensityCollapse.lean` (o(1) density collapse (3),
  capacity–column composition `exists_column_ge_of_card_le`/`exists_column_ge_theta` = (2)+(4),
  proposed-band (5)/(6) `exists_wholeAnchorTerminalUniverse_card_le_proposedBand` +
  `exists_column_ge_proposedBand`, aux `one_le_logLog_of_sixteen_le`). Built + axiom-clean, wired
  into RHTower umbrella.

## NEW SHARED ANALYTIC INFRASTRUCTURE (2026-08-14) — the route-e analytic cluster runs on this
- `HTGeometry/RpowKernelRemainder.lean` — `tendsto_rpowKernelRemainder`: g→0 and |K t| ≤ C t^(a-1)
  ⇒ (∫_2^x g K)/x^a → 0. Wired into HTGeometry umbrella.
- `RHTower/PrimeRpowLogSumAsymptotic.lean` — `thetaError t = θ t / t - 1`,
  `tendsto_thetaError` (PNT relative form, from Sieve.chebyshevTheta_sub_id_isBigO),
  `abs_thetaError_le` (≤ log 4 + 1 globally on [2,∞)), measurability/integrability,
  `primeRpowLogSumIoc_eq` (Abel vs θ, weight t^(a-1)),
  `integral_derivRpow_mul_theta_eq`, and
  **`tendsto_primeRpowLogSumIoc : (∑_{2<p≤x} p^(a-1) log p)/x^a → 1/a`** for every a > 0.
  Wired into RHTower umbrella. All axiom-clean.
  Reusable corpus pieces it builds on: `RHTower.primeLogWeight`, `sum_primeLogWeight_eq_theta`
  (PrimeRpowAbelSummation.lean), `HTGeometry.integral_rpow_sub_one`,
  `HTGeometry.intervalIntegrable_rpowSubOne`, Mathlib `sum_mul_eq_sub_sub_integral_mul`,
  `Chebyshev.theta_mono/theta_le_log4_mul_x/theta_nonneg`.

## NEXT BRICK (in progress): the prime window law
Master tool for the whole route-e analytic cluster (saddle barrier, euler-tilt, gibbs odd-cube):
  W_j(Y) := ∑_{2<p≤Y} p^(a-1) (log p) (log Y - log p)^j ,  Y^{-a} W_j(Y) → j!/a^(j+1).
Elementary proof plan (no substitution, no Gamma needed):
1. `windowRpowIntegral a j Y := ∫ u in 2..Y, u^(a-1) * (log Y - log u)^j`;
   integration by parts (u = (ℓ-log x)^j, v = x^a/a) gives
   `J_j = -(2^a ℓ^j)/a + (j/a) J_{j-1}`, `J_0 = (Y^a - 2^a)/a`;
   hence `J_j ≤ (j!/a^(j+1)) Y^a` and `Y^{-a} J_j → j!/a^(j+1)` by induction (ℓ^j/Y^a → 0).
2. window remainder: |thetaError| ≤ log 4 + 1 globally ⇒ head O(ℓ^j) = o(Y^a), tail ≤ δ J_j.
3. Abel identity with the Y-dependent weight f_Y(u) = u^(a-1)(log Y - log u)^j; boundary term at Y
   vanishes for j ≥ 1; the integral splits into (a-1)J_j - j J_{j-1} plus the remainder.
   Limit: -( (a-1) j!/a^(j+1) - j (j-1)!/a^j ) = j!/a^(j+1).
4. no-log-p version: ℓ·∑ p^(a-1) g(v_p) = ∑ p^(a-1) log p · g(v_p) + error, splitting at p = √Y
   (v ≤ ℓ/2 gives O(Y^a/ℓ); v > ℓ/2 gives O(ℓ^{k+1} Y^{a/2})).

## Card-by-card analytic debts (route-e cluster)
- route-e-physical-saddle-antiscale-coercivity-barrier: (15) = tendsto_primeRpowLogSumIoc ✓ built;
  (14) needs ∑_{p≤Y} p^{-2σ} log p ≤ ∑_{p≤Y} log p/p = O(log Y) (Mertens first, corpus
  Sieve/MertensFirst.lean); (3) Λ ~ (2/a)Y^a; (16) variance needs W_1; (21)/(23) antiscale sum
  needs the window law with h(v) = (π/a - πv)^2 and the sin²-expansion error control;
  (25)-(29) Euler deficit transport; then (5),(7),(10).
- route-e-source-faithful-euler-tilt-unit-shell-law: (9)-(14) need UNIFORM-in-δ sums
  ∑_{p≤Y} p^{-1-δ} log p = (1-e^{-δℓ})/δ + O(1), δ = O(log ℓ/ℓ²) — requires the L¹ bound
  ∫_2^∞ |θ(u)-u|/u² du < ∞ (finite because θ(u)-u = O(u exp(-c√log u))).
- route-e-gibbs-antiscale-determinant-mellin-odd-cube-law: four-field Mellin polarization + PNT
  terminal lower bounds.
- route-e-whole-anchor-bidirectional-harmonic-e3-law: Lean not started; its (6)/(10)/(13) packet is
  already covered by `MobiusWholeAnchorCapacityDisplacement.lean` (wholeAnchorE3_exact_packet,
  wholeAnchorReservoirBand_mul_eq, wholeAnchor_fullReservoirMass_eq_eulerProduct); remaining:
  (8) scale bounds, (16)-(18) harmonic mass ≥ exp(c₀L), (19)-(21) column bound — the last rests on
  the external sparse-forbidden all-interval E₃ supply theorem (9): check whether that is Lean or
  paper elsewhere in the corpus before claiming (7).

## Working discipline reminders
- Multiple concurrent peer sessions in this repo; check mtimes/git status before touching a module;
  never `cat >` over an existing Lean file.
- `lake build <module>` is authoritative; `lake env lean` is necessary not sufficient.
- Axiom audit via the session scratchpad (NOT /tmp). Baseline [propext, Classical.choice, Quot.sound].
- Bash cwd persists between calls — `grep` from the repo root silently misses `GaloisForLFunctions/`.
- `field_simp` frequently closes goals fully; a trailing `ring` then errors with "No goals".
