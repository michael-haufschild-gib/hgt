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

## UPDATE (cycle 55, cont. 28) — codex batch reviewed; certificate side converges on (LOW)

- Codex batch (31 items, docs/drafts/rh-monodromy-weight-mismatch/
  lean_updates_codex.md) VERIFIED: formal lint green; six load-bearing
  endpoints axiom-checked [propext, Classical.choice, Quot.sound]
  (both local-window RH gates, the relative gate, the rough+boundary
  prime-packet identity, the zero-free-tower iff, the germ⟺circle-average
  equivalence).
- **Front 3 (phase-shift) STRENGTHENED model → actual carrier.**
  `seedGapCoeff` (RouteBSeedGap.lean) is the windowed-divisor coefficient of
  carrier − rough seed; exact identities: on singleton boundary packets
  seedGapCoeff = λ_d; with λ 1 = 1 the rough component vanishes and
  ∫‖dpoly(seedGapCoeff, P ∪ P·d)‖² = ∫‖dpoly(λ_d, P)‖² EXACTLY
  (`seedGap_rough_boundary_component_secondMoment_eq_prime_packet`);
  interval mass positive iff λ_d ≠ 0. Terminal-positive now holds on the
  real packet by equality, not by model comparison.
- **New terminal RH gates (SeamCongruence/RiemannTower):**
  `riemannHypothesis_of_local_online_windows`,
  `riemannHypothesis_of_emCarrier_close_floor_sign_local_windows`,
  `riemannHypothesis_of_relative_floor_sign_local_windows`. All seam/rung/
  sign endpoints consolidated onto the single `CarrierFloorOn` interface;
  RH is machine-checked-reduced to per-window finite certificates whose ONE
  analytic input is the (LOW) floor — the exact observable the (L3)
  small-ball theorem bounds in the Steinhaus model. Carrier zeros are
  budgeted (Σ m₂ ≤ s), not forbidden.
- New typed lane appended to doc 87 ((LOW) CONVERGENCE): (B1) Bohr transfer
  (model small-ball → t-density of floor failure; Kronecker–Weyl for the
  finite prime torus = next buildable gap if absent from mathlib), (B2)
  movable-shell pigeonhole (a.e.-height → every-window; obstruction migrates
  to the count face), (B3) count budget via the banked Rouché+EM counting
  island. The graded ladder and (B1)–(B2) consume the same per-level engine —
  the Route B′ remainder and the RH-gate residue are now one object.

## UPDATE (cycle 55, cont. 29) — Kronecker–Weyl equidistribution built; FloorFailureDensity

- **The named mathlib gap is now filled.** Probed: mathlib has NO linear-flow
  Weyl equidistribution / Weyl criterion / pointwise Birkhoff. Built
  `RHTower/WeylEquidistribution.lean` (axiom-clean, in-tree): `char_integral_eq`,
  `char_time_average_tendsto` (Weyl's criterion: (1/T)∫₀ᵀexp(iθt)→0 for θ≠0),
  `trig_time_average` ((1/T)∫₀ᵀ∑cᵢexp(iθᵢt)→∑_{θᵢ=0}cᵢ, the finite-torus
  equidistribution). Reusable, mathlib-grade.
- **FloorFailureDensity built (`RHTower/FloorFailureDensity.lean`, axiom-clean).**
  The indicator/small-ball transfer the L² Bohr method (already in-tree as
  `tendsto_secondMoment_average_steinhaus`) provably cannot reach. Chain:
  `cesaroUpperDensity` observable → `realTrig_time_average_tendsto` (Weyl
  density identity) → `cesaroUpperDensity_mono` → `cesaroUpperDensity_le_of_realTrigMajorant`
  (the transfer) → **`floorFailure_timeDensity_le`**, which GENUINELY CONSUMES
  `block_smallball_condition` for the ensemble measure and Weyl equidistribution
  for the transfer: Cesàro upper TIME density of the line failure-event
  ≤ (2π)⁻⁴·M + δ, carrier zeros budgeted not forbidden.
- **Sole remaining input, sharply typed:** the real trigonometric MAJORANT of
  the failure indicator with mean ≈ model measure (a Fejér/Jackson kernel on the
  finite prime torus). That is the next buildable gap — mathlib has
  `span_fourier_closure_eq_top` for one `AddCircle`; the product-torus version is
  the target. Everything else (equidistribution + block_smallball consumption) is
  proved. This is the (B1)/(B2) lane's analytic core, now isolated to one
  approximation-theory construction.

## UPDATE (cycle 55, cont. 30) — unconditional density bound (degree-1 majorant rung)

- The majorant is `q ∘ ‖F‖²` for a polynomial `q ≥ 1_{[0,t₀²]}` — cleaner than
  torus Stone–Weierstrass, and automatically a real trig poly with a computable
  (model-moment) mean.
- **`cesaroUpperDensity_secondMoment_le` (RHTower/FloorFailureDensity.lean,
  axiom-clean): UNCONDITIONAL.** Cesàro upper time density of any [0,1]-observable
  on the floor-failure set {‖F‖≤t₀} ≤ (B²−∑aₙ²)/(B²−t₀²). Degree-1 majorant
  `q(u)=(B²−u)/(B²−t₀²)`, mean fixed by the second-moment Bohr transfer. No
  hypothesis on the majorant — it is constructed. Plus `continuous_dpoly`.
- This is the base rung of the polynomial-majorant tower and a genuine
  Paley–Zygmund-grade unconditional density bound. The SHARP (2π)⁻⁴M version needs
  the degree-d tower: (BOHR-n) general moment identity (Weyl time-mean of q(‖F‖²)
  = model E[q(‖∑aX‖²)], all degrees) + (APPROX) polynomial step-majorant with
  model mean → floor-failure measure. Composing with block_smallball sends δ→0.
  NEXT: (BOHR-n) degree-2 (4-fold sum), the first non-linear rung.

## UPDATE (cycle 55, cont. 31) — degree-2 Bohr moment rung

- Project check: only the second moment existed anywhere (no higher moments in
  RHTower/BohrTransfer/SteinhausModel; SpurCumulant + theorem-m Moments unrelated).
- **BohrMoments.lean (axiom-clean, 8478 jobs):** the tower collapses via
  ‖F‖^{2k} = ‖F^k‖² + "a power of a Dirichlet poly is a Dirichlet poly". Keystone
  **`dpoly_sq`**: F² = dpoly(convSq)(sqSupport); `model_sq` its model twin via X_mul.
  Consequences: `tendsto_fourthMoment_average` (time ‖F‖⁴ → ∑convSq²),
  `integral_normSq_sq_dpoly` (model E‖·‖⁴ = ∑convSq²), and
  **`tendsto_fourthMoment_average_steinhaus`** — the degree-2 Bohr identity: time-avg
  ‖F‖⁴ = model fourth moment. Reuses the whole second-moment machinery on F².
- Unlocks the degree-2 majorant q(u)=α+βu+γu² with mean matched to the model,
  sharpening the density bound past the degree-1 rung. NEXT: dpoly_mul (general
  product) → F^k tower → (APPROX) step-majorant → sharp small-ball bound.

## UPDATE (cycle 55, cont. 32) — full even-moment tower + sharp δ→0 composition

- **BohrMoments.lean** rewritten as the GENERAL tower: dpoly_mul + model_mul (general product),
  powConv/powSupport + dpoly_pow/model_pow (Fᵏ by induction), **tendsto_evenMoment_average_steinhaus**
  (general 2k-moment Bohr identity, every k).
- **BohrMomentDensity.lean** (new): tendsto_polyMoment_average_steinhaus, cesaroUpperDensity_le_polyMoment,
  **floorFailure_timeDensity_le_sharp** — density ≤ B.toReal from a polynomial-majorant family + model bound B.
  δ→0 drive DONE; sharp bound reduced to EXACTLY (APPROX).
- Axiom-clean; lint green; 8496 jobs. SOLE remaining = (APPROX) Weierstrass step-majorant (on Ω; mathlib pieces present).

## UPDATE (cycle 55, cont. 33) — (APPROX) PROVEN; sharp density bound UNCONDITIONAL

- **WeierstrassMajorant.lean** (axiom-clean): exists_poly_majorant_expectation — the abstract
  Weierstrass step-majorant on a probability space (continuity-from-above + tent + Weierstrass).
  The hard analytic heart of (APPROX), standalone (Mathlib only).
- **FloorFailureUnconditional.lean** (axiom-clean): norm_modelSum_le/norm_dpoly_le,
  exists_poly_majorant_family (instantiates the majorant at Y=‖∑aX‖², produces the hApprox
  family), and **floorFailure_timeDensity_le_unconditional** — the sharp Cesàro upper
  time-density bound ≤ B.toReal with NO approximation hypothesis; block_smallball supplies
  B=(2π)⁻⁴M.
- The entire chain (Weyl equidistribution → tower → poly bridge → sharp δ→0 → APPROX) is now
  complete, unconditional, axiom-clean; 8498 jobs, lint green. The indicator/small-ball
  time↔model transfer is done.
