# Quiet-crossing rigidity for symmetric gammaless carriers

- **ID:** quiet-crossing-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `F` be entire, equal on `Re s ≥ c` (some `c ≥ ½`) to an absolutely
  convergent ordinary Dirichlet series `Σ aₙ n^{−s}`, with the exact reflection symmetry
  `F(s) = F(1−s)`. If ONE sequence of heights `T_k → ∞` exists along which
  `sup_{1−c ≤ σ ≤ c} ‖F(σ ± iT_k)‖ = o(T_k²)`, then `aₙ = 0` for every `n ≥ 2` and `F ≡ a₁`
  identically on ℂ. No order, growth-ceiling, integrality, or multiplicativity hypothesis: a
  single quiet crossing sequence replaces the finite-order standing axiom of the
  Hamburger/Kaczorowski–Perelli tradition (finite order ⟹ bounded strip via Phragmén–Lindelöf ⟹
  quiet, so the hypothesis is strictly weaker given the automatic flank bounds).
- **Lean:** `QuietCrossingRigidity.lean` — engine: `perronKernel_mellin`
  (`mellin (max(1−u,0)) = 1/(s(s+1))`), `perronKernel_inversion`, `smoothed_perron_sum`
  (`Σ aₙ max(x−n,0) = (1/2π)∫ L(c+it) x^{s+1}/(s(s+1)) dt`); theorem layer: `perronKink` (roots
  at both kernel poles: `perronKink_zero`, `perronKink_negOne`), `perronE` (entire via double
  `dslope`), `perronKink_second_difference` (kink = `aₙ/2`), `perronSecondDiff_integral`,
  `quiet_crossing_rigidity`, `quiet_crossing_rigidity_constant`. All
  `[propext, Classical.choice, Quot.sound]`; umbrella build green; lint green. Companion module
  `GammalessStripRigidity.lean` (P–L reduction, threshold `π/(2σ_a−1)`; edges-free lemma
  `lseries_bounded_on_halfplane`, consumed here).
- **Proof mechanism (residue-free):** the second difference of the smoothed count
  `A₁(x) = Σ aₙ max(x−n,0)` at knots `n, n±½` isolates `aₙ/2`; its Perron numerator
  `N(s) = (n+½)^{s+1} + (n−½)^{s+1} − 2n^{s+1}` vanishes at both kernel poles `s = 0, −1`, so the
  integrand `F·N/(s(s+1))` is ENTIRE and Cauchy's rectangle theorem shifts the line integral with
  no residue calculus; horizontal edges die along the quiet sequence (`(B+q_k)/T_k²`), the left
  edge is `O(B·(n−½)^{1−M})`, and `M → ∞` kills the coefficient. The kernel's two poles and the
  affine data `F(0)x − F(−1)` are the same two dimensions — second-differencing quotients both
  out, so the continuation's values at `{0, −1}` never enter.
- **Dual gate:** NOVEL — the quantifier flip (global growth ceiling → one quiet height sequence)
  is absent from the corpus; the gammaless symmetric infinite-order cell is unposed
  ([ABSENT]² verdicts), and the residue-free second-difference route is new even as proof
  architecture. × SIGNIFICANT — localizes the C-COC `σ_a ≥ 1/2` wall to growth PERSISTENCE (the
  seam-curtain object): a nonconstant member must be superpolynomially loud at EVERY height. With
  the small-abscissa classification (card `order-free-degree-zero-classification`) the two strata
  of the order-free program are now machine-checked to their exact residuals.

## Log
- 2026-07-09 — wave-1 paper proof; engine (A+B) and theorem (C) formalized; constancy corollary
  contributed by a parallel agent and verified in the same build; research program on card
  `goldilocks-divisor-rigidity.md`.
- 2026-07-09 (later) — conductor-datum form also formalized: `QuietCrossingConductor.lean`
  (`quiet_crossing_conductor_support`, `quiet_crossing_conductor_polynomial`) — quiet carriers
  under `F(s) = (Σ c_j Q_j^{1−2s})F(1−s)` have support ≤ Q₀²; axiom-clean, umbrella, lint green.
- 2026-07-09 (later) — Gaussian kernel escalation formalized: `QuietCrossingEscalation.lean`
  (`quiet_crossing_rigidity_gaussian`) — quiet budget weakened to `log q_k = o(T_k²)` (∀λ form;
  single-λ proven insufficient, quantifier corrected on the working card); axiom-clean, umbrella,
  lint green.
- 2026-07-09 (later) — path-quiet form formalized: `QuietPathRigidity.lean`
  (`quiet_path_rigidity`) — quiet C¹ paths through the strip replace straight crossings
  (budget q·L/T²); hexagonal-loop primitive-telescoping architecture; axiom-clean, umbrella,
  lint green.
