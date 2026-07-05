# Route B′ + Route A + phase-shift identity — ground to terminal state

**Goal (session 2026-07-05, seed 3253897643236190683).** Grind all three to
full formal Lean proof or detailed refutation (doc-82 grade, no partials):

1. **Route B′** (heir card 0-backlog/route-b-prime-normalized-kernel.md):
   (K-bdd-n-log) — normalized log-corrected kernel, N-uniform. Entrance exam:
   P-F5 saturation (runpod, N=2·10⁵ stage running; registered band 1.35–1.42
   ALREADY EXCEEDED at 10⁵ — level prediction failed; shape open, full-set
   rms per PREREG-4) + (SEED-GAP) re-typed (doc 85 §3″).
2. **Route A** (doc 55 §6.2–6.4, §7): GAF σ-profile universality. Engine:
   ρ(σ) = (1/4π)(log K)″(σ); ε(c) = L(c)/4π Langevin; Taylor tower =
   EGF of ζ(1−2k). Open core: Steinhaus-vs-Gaussian LOCAL universality of
   near-line zero statistics at leading order. Computable spine is
   formalizable now (profile limit, Langevin identity, Bernoulli tower);
   bridge = CLT-for-analytic-fields plan (Lindeberg ✓ shape) or refutation.
3. **Phase-shift identity** (doc 85 §3″, RouteBSeedGap.dpoly_shift_norm):
   boundary defect = seed re-phased. [CONJECTURE → derivation] The two-field
   factorization: in the Steinhaus model the carrier is
   P = Σ_{u z-smooth} u^{-1/2} X_u W_u(X_rough), W_u = Σ_r b_{ur} r^{-1/2}X_r,
   b_{ur} = Σ_{e|u, e≤z, ur≤Ne} λ_e, W_1 = 1 + S EXACTLY (rough locus ≤ N =
   {1} ∪ primes at z=√N). Smooth ⊥ rough coordinates ⟹ conditional
   decoupling is EXACT in the model; the kernel becomes a conditional
   smooth-packet density question with frozen rough coefficients — the typed
   analytic core of (K-bdd-n-log).

**Terminal admitted:** (a) kernels/bridges proven + full chain in Lean;
(b) refutation in all details (located false link / walled instrument class).

## Status
- OPEN. Lean substrate banked: RouteBSupport, RouteBSeedGap (8 endpoints),
  counting-layer wiring (DipKillsWiring etc.), dpoly/Compare surface.
- P-F5: N=200000 draw loop running on runpod.

## UPDATE (cycle 55, session close)

- **Front 3 (phase-shift identity): TERMINAL-POSITIVE.** Doc 86 §§1–3 exact;
  Lean RouteBTwoField.lean (7 endpoints) + RouteBSeedGap.dpoly_shift_norm.
  Nothing left open on this front as stated.
- **Front 1 (Route B′):** entrance exam P-F5 ADJUDICATED — SAT as
  registered (weak pass; prereg + doc 85 §7). Doc 86 (two-field
  architecture, (SPREAD)-diagonal derived, 1D-degeneration falsifier) +
  doc 87 (the O(1)-fluctuation law — Var(σ_W²) ≍ E²; the Branch-A
  hierarchy architecture; lemma ledger (L1)–(L4), (L1)/(L2)
  rigorous-shaped via Landau, (L3) hierarchical Esseen = technical core).
  The P-F5 plateau a ≈ 2.17 is now DERIVED (O(1) scale mixture), no longer
  an anomaly. NOT terminal: (L3)+(L4) write-out + Lean owed.
- **Front 2 (Route A):** doc 88 — bridge decomposed into (A1) conditional
  martingale CLT [provable-shaped] × (SCALAR-MIX) [true residue; the
  Steinhaus field is a variance-mixture of Gaussians, Δlog kills the
  scalar part exactly, P1 measures the identity holding]. Lean spine
  banked (RouteAProfile.lean, 6 endpoints: Langevin/coth chain, intensity
  ≥ 0, RouteAUniversality interface). NOT terminal: (A1) write-out +
  (SCALAR-MIX) resolution owed.
- **Unifying finding:** ONE object under both routes — the near-critical
  multiplicative field's conditional second-order data is an
  O(1)-fluctuation mixture (docs 87 §3 = 88 §2). (L3) and (SCALAR-MIX) are
  its small-ball and two-point faces.
- **Next Lean pole (confirmed feasible):** SteinhausModel.lean — the model
  probability space via Measure.infinitePi (EXISTS in toolchain), X_n
  orthonormality, model second-moment identity. Foundation for (L4)/(L3)
  skeleton and (A1). Multi-session; start next cycle.

## UPDATE (cycle 55, cont.)

- Lean banked this goal so far: 6 modules / 40 axiom-clean endpoints
  (RouteBSeedGap 8, RouteBTwoField 7, RouteAProfile 6, SteinhausModel 12,
  RouteBSublevel 7 incl. two_phase_sublevel). SteinhausModel COMPLETE
  (orthonormality + model second-moment identity — the lane's probability
  space is real). (L4)-seed + two-phase composition DONE; caustic factor
  isolated as (CAUSTIC).
- PNT/Mertens NOT in toolchain (probed): (L1)/(L2) Lean-native = own
  multi-session pole (build Möbius partial-sum decay); interim = typed
  interfaces + Landau-grade paper proofs (doc 87 App A).
- Remaining to terminal: (CAUSTIC) transversal bound → (L3)
  caustic-averaging induction (paper then Lean); (A1) martingale-CLT
  write-out; (SCALAR-MIX) resolution; PNT pole. No internal forks left
  anywhere; every remaining item is named, typed, and consumed by a
  machine-checked downstream chain.

## UPDATE (cycle 55, cont. 24–25) — (L3) block STEP + Mertens pole FORMALIZED

- **(L3) block anti-concentration STEP: Lean THEOREM.**
  `SteinhausModel.block_smallball_condition` + concrete `block_smallball_caustic`
  (RouteBBlockStep.lean, axiom-clean): the Steinhaus prime-block small-ball
  ≤ (2π)⁻⁴·fourPhaseConst, uniform in conditioning. Full plumbing formal:
  block marginal → lmarginal peel of 4 dominant phases → angle rescale
  (Jacobian (2π)⁻⁴) → the caustic four-phase engine → conditioning wrap.
  Supporting: prod-Fubini adapter (four_phase_prod_eq_nested), sum_phase_update4,
  rescale4, peel4, inner_block_le, block_pi_le, four_phase_nested_uniform.
- **(L1)/(L2) pole: Mertens' first theorem BUILT** (MertensFirst.lean):
  |∑_{d≤n} Λ(d)/d − log n| ≤ log 4 + 4, elementary, no PNT — the "PNT not in
  mathlib" pole is no longer a gap. Partial summation → the carrier log-derivative.
- Remaining to terminal: graded-ladder assembly (block STEP × (SPREAD)) →
  (K-bdd-n-log); partial-summation bridge Mertens → (L1)/(L2) carrier pole;
  (A1) martingale-CLT write-out (mathlib has only iid CLT); (SCALAR-MIX).
