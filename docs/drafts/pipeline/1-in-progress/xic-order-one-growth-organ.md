# XiC order-one growth: the cornerstone of the explicit-formula organ

**Stage:** 1 — in progress
**Claim (exact):** [CONJECTURE → target theorem] There is `B ≥ 0` with
`∀ z : ℂ, ‖XiC z‖ ≤ Real.exp (B * (1 + ‖z‖) * Real.log (2 + ‖z‖))`
(equivalently the same bound for `xi` on `ℂ`), unconditional Lean.

**Why this card exists (the synergy audit conclusion, 2026-08-11):** four live lanes (C1/Gauss
deviation-mass, Route O restricted-Weil, Route U hard-edge boundary, Route T prime side) all
terminate against the missing Guinand–Weil explicit formula. The zero-side half of that organ is
the Hadamard product; the corpus already owns `xiHadamardQuotient * xiCanonicalProduct = XiC`
and the conditional constancy theorem `xiHadamardQuotient_constant_of_log_reBound`, whose ONLY
missing input is this growth bound (plus, for full constancy, a Cartan lower bound on the
canonical product — a separate later card). Mathlib meanwhile owns Jensen's formula
(`MeromorphicOn.circleAverage_log_norm`), so growth ⇒ zero-counting `N(r) ≪ r log r` is also
unlocked by this card.

**Immediate capstone reachable from this card alone (no Cartan needed):**
[CONJECTURE] `∃ ρ : ℂ, xi ρ = 0` — the first formal existence of a nontrivial zeta zero.
Proof route: if the divisor is empty, `XiZeroCopy` is empty, `xiCanonicalProduct ≡ 1`
(empty tprod), so `xiHadamardQuotient = XiC` by the corpus product identity; `XiC = exp g`
(`xiHadamardQuotient_has_log`), `Re g = log ‖XiC‖ ≤` growth bound, so
`xiHadamardQuotient_constant_of_log_reBound` forces `XiC` constant; but
`xi 0 = 1/2` and `xi 2 = π/6` (mathlib `riemannZeta_two`), and `π ≠ 3`
(`Real.pi_gt_three`), contradiction.

**Proof plan for the growth bound (no Stirling, no Phragmén–Lindelöf):**
1. `completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2` and
   `WeakFEPair.Λ₀ = mellin f_modif` (mathlib `AbstractFuncEq`). Hence
   `‖Λ₀(s)‖ ≤ ∫₀^∞ t^(Re s − 1) ‖f_modif t‖ dt`.
2. Majorant for `f_modif` (both ends rapid):
   - on `(1,∞)`: `f_modif = θ − 1 = 2Σ_{n≥1} e^{−πn²t} ≤ 2 e^{−πt}/(1−e^{−π})`;
   - on `(0,1)`: FE transport `hf_modif_FE`: `‖f_modif t‖ = t^(−1/2)·‖g_modif(1/t)‖ ≤
     C t^(−1/2) e^(−π/t)`; substitution `u = 1/t` folds this onto `∫₁^∞ u^(−σ−1/2) e^{−πu}`.
3. Elementary Gamma-type bound: `G a := ∫₁^∞ t^a e^{−πt} dt ≤ exp(K(1+a)·log(2+a))` by
   splitting at `M = 2a² + 9`: on `[1,M]` bound by `M^(a+1)`; on `[M,∞)` use
   `log t ≤ 2(√t − 1)` to get `t^a e^{−πt/2} ≤ 1`, leaving `∫ e^{−πt/2} = 2/π·e^{−π/2}`.
4. Assemble: `‖completedRiemannZeta₀ s‖ ≤ exp(K'(1+|Re s|)log(2+|Re s|))`; then
   `xi s = s(s−1)/2·Λ₀(s) + 1/2` gives the polynomial factor (absorbed), and
   `XiC z = xi(1/2 + z·I)` finishes.

**Downstream (later cards):** Cartan minimum-modulus for `xiCanonicalProduct` → Hadamard
constancy → partial fractions of `XiC'/XiC` over the divisor → glue with prime side
(mathlib/PNTPlus `−ζ'/ζ = Σ Λ(n) n^{−s}` on `Re > 1`) → the log-derivative explicit formula →
Weil-type formulas for band-limited tests → the producer sockets of C1/Gauss, O, U, T.

**Dead/closed context:** the O ↔ xiWeilPolarization "dictionary" splice is NOT definitional —
O's matrix is prime-side, the polarization is zero-side; their identification IS this organ.
Recorded 2026-08-11 after hostile check.

## Log
- 2026-08-11 — card opened after the frontier-map synergy audit. Mathlib interface points
  verified: `WeakFEPair.Λ₀ = mellin f_modif` (`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`),
  `hf_modif_FE`/`hf_modif_top`, `hurwitzEvenFEPair`, Jensen (`Mathlib/Analysis/Complex/
  JensenFormula.lean`), corpus receivers `xiHadamardQuotient_constant_of_log_reBound`,
  `entire_reBound_imp_affine`, `xiHadamardQuotient_has_log`,
  `xiHadamardQuotient_mul_canonicalProduct`. `riemannZeta_two` and `Real.pi_gt_three` confirm
  the nonconstancy witness needs no computation.
- 2026-08-11 — brick 1 [LEAN-PROVED]: `HTGeometry/MellinGrowthBounds.lean` (wired, HTGeometry
  umbrella green 18187 jobs, all 4 theorems `[propext, Classical.choice, Quot.sound]`):
  `rpow_mul_exp_neg_pi_le` (pointwise: `t^a·e^{−πt} ≤ (2a²+9)^a·e^{−πt} + e^{−πt/2}` for
  `t ≥ 1, a ≥ 0` — split at `2a²+9`; above it `log t ≤ 2√t` and `16a² ≤ π²t` via `π > 3`),
  `integrableOn_rpow_mul_exp_neg_pi`, `integral_rpow_mul_exp_neg_pi_le`
  (`∫₁^∞ t^a e^{−πt} ≤ (2a²+9)^a + 1`), `log_gammaTail_bound_le` (Hadamard shape:
  `log((2a²+9)^a+1) ≤ (1+a)(1+3·log(3+a))`).  No Stirling anywhere.  Next brick: the
  `f_modif` majorant for `hurwitzEvenFEPair 0` (BigO extraction from mathlib
  `isBigO_atTop_evenKernel_sub` + compact-interval sup + FE transport `hf_modif_FE` to (0,1)),
  then the Mellin-norm assembly `‖Λ₀(s)‖ ≤ C·G(|Re s|+…)`, then `xi`/`XiC` polynomial wrap,
  then the nonemptiness capstone.
- 2026-08-11 — **STATUS REWRITE after corpus-first audit (user directive)**: the card's
  cornerstone, capstone, and the full Hadamard product are ALREADY FORMAL in the corpus:
  `xi_growth_order_le_one` (`CompletedZetaGrowth.lean` — the exact target bound, via
  `modifiedEvenKernelDecay_holds` + `intbound_of_decay`); `xiHadamardQuotient_constant` and
  `XiC_eq_constant_mul_canonicalProduct` (`XiHadamardGrowth.lean` — unconditional Hadamard
  factorization via Nevanlinna proximity, no Cartan needed); `xiDivisorSupport_infinite`
  (`XiZerosInfinite.lean` — infinitely many zeros, superseding the planned nonemptiness
  capstone); `nonempty_xiZeroCopy` + instance and `finite_xiHeatShell`
  (`XiHeatShellMinimum.lean`).  Bricks 2–5 of the original plan are therefore CLOSED by
  existing corpus theorems; brick 1 (`MellinGrowthBounds.lean`) stays as public reusable API.
  **Reframed target (the genuine zero-side gap): the divisor partial fraction**
  `logDeriv XiC z = Σ'_q z/((α_q−z)·α_q)` for z off the divisor — assemble from mathlib
  `logDeriv_tprod_eq_tsum` + `canonicalProductE1Indexed_hasProdLocallyUniformlyOn`/`_ne_zero`/
  `_analytic` + `XiC_eq_constant_mul_canonicalProduct` (the multiplicative constant contributes
  zero log-derivative — evenness already killed the exponential factor upstream) +
  `XiC_zero_ne` (so every α_q ≠ 0) + summability from `xiSpectralPoint_inv_sq_summable` with a
  finite-ball split via `finite_xiHeatShell`.  Worked instantiation patterns:
  `neg_logDeriv_movingCanonicalProduct_eq`, `EllipticGammaProduct.lean:355`,
  `MovingCanonicalSurgery.lean:415`.  After that: the prime side (−ζ′/ζ = Σ Λ(n) n^{−s},
  mathlib/PNTPlus) and the Γ-factor glue through `xi`'s definition complete the log-derivative
  explicit formula on `Re s > 1`.
- 2026-08-11 — **second corpus-first sweep: the partial fraction ALSO already exists.**
  `XiRelativeResolventTrace.lean` owns the complete zero-side expansion:
  `logDeriv_weierstrassE1_div`, `summable_xiRelativeResolventTerm`,
  `logDeriv_xiCanonicalProduct_eq_relativeResolventTrace`,
  **`logDeriv_XiC_eq_relativeResolventTrace`** (the Hadamard partial fraction, sole hypothesis
  `XiC z ≠ 0`), the reciprocal-square resolvent form, and divisor power sums
  (`tsum_xiZeroCopyReciprocalSquare_pow`).  My drafted duplicate module was deleted unbuilt.
  Also present: `CompletedLogDerivStrip.lean` (`logDeriv_completed_split_strip` — arch/zeta
  additive split on the strip), `SeamFluxCompletion.lean` (`logDeriv_xi_reciprocity` — FE
  antisymmetry of `logDeriv xi`), `ArchEnvelope.lean` (archFactor derivative machinery).
  Mathlib owns the prime side: `LSeries_vonMangoldt_eq : L ↗Λ s = −ζ′(s)/ζ(s)` on `Re s > 1`
  (`Mathlib/NumberTheory/LSeries/Dirichlet.lean`).
  **The organ's ACTUAL remaining theorem — the glue** (next execution target): on `Re s > 1`,
  chain (i) `logDeriv XiC` at the spectral coordinate `z = (s−1/2)(−i)` to `logDeriv xi s`
  (affine chain rule), (ii) `logDeriv xi s = logDeriv (s(s−1)/2) + logDeriv Gammaℝ s +
  logDeriv ζ s` (factor split; all factors nonvanishing for `Re s > 1`), (iii) substitute the
  zero side (`logDeriv_XiC_eq_relativeResolventTrace`, coordinate-transported so terms become
  `1/(s − ρ_q)`-form) and the prime side (`LSeries_vonMangoldt_eq`), yielding the corpus's
  first unconditional zero-sum = prime-sum identity — the log-derivative Guinand–Weil fragment.
- 2026-08-11 — **THE GLUE THEOREM [LEAN-PROVED]: the log-derivative explicit formula.**
  `RHTower/XiExplicitFormulaLogDeriv.lean` (wired, umbrella green 18916 jobs, all 4 theorems
  `[propext, Classical.choice, Quot.sound]`):
  `xi_eq_XiC_comp` (coordinate identity `xi s = XiC((s−1/2)(−i))`),
  `logDeriv_xi_eq_partialFraction` (wherever `xi s ≠ 0`:
  `logDeriv xi s = Σ'_ρ (1/(ρ−1/2) + 1/(s−ρ))`, multiplicity-exact, absolutely convergent,
  no linear term — the classical Hadamard partial fraction in `s`-coordinates, transported by a
  hypothesis-free rotation lemma `resolvent_coordinate_transport`),
  `logDeriv_xi_split` (`Re s > 1`: `logDeriv xi = 1/s + 1/(s−1) + logDeriv Γℝ + logDeriv ζ`),
  and the capstone **`xi_explicitFormula_logDeriv`**: for `Re s > 1`
  `Σ'_ρ (1/(ρ−1/2) + 1/(s−ρ)) = 1/s + 1/(s−1) + logDeriv Γℝ s − Σ_n Λ(n) n^{−s}`
  — **the corpus's first unconditional zero-sum = prime-sum identity**, assembled from the
  corpus Hadamard partial fraction (zero side), the factor split, and mathlib's
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (prime side).  The Guinand–Weil organ now has
  its trunk: differentiating in `s`, pairing against tests, and moving the contour are the
  remaining limbs (each a separate later brick — contour motion is the analytically hard one).
