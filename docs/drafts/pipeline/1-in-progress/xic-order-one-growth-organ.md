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
- 2026-08-11 — **CORRECTION (third corpus sweep): the Guinand–Weil layer ALREADY EXISTS.**
  `XiGuinandWeilExplicitFormula.lean` owns the STRONGER statement:
  `xiGuinandWeilExplicitFormula` (finite superpositions of regularized Cauchy kernels; base
  points in the CONTINUED admissible region `0 < Re s`, `s ≠ 1`, `ζ s ≠ 0` — reaching inside
  the strip), `_primeSeries` (honest von Mangoldt Dirichlet-series source on `Re > 1`),
  `_single`.  It rests on `XiRelativeResolventFlux.lean`'s
  `continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace`.  My earlier log entry
  claiming "the corpus's first zero-sum = prime-sum identity" is WRONG; the new module
  `XiExplicitFormulaLogDeriv.lean` is honestly a [BRIDGE]: the classical textbook normal form
  (`logDeriv xi` partial fraction centered at 1/2, polar/arch/ζ split, mathlib `LSeries`
  vocabulary), now cross-referenced in its docstring.  Search lesson recorded: concept greps
  must be case-insensitive (`explicitFormula` missed `GuinandWeilExplicitFormula`).
  Additionally found already formal: `XiWeilResolventGram.lean`
  (`xiWeilPolarization_cauchyKernel_diagonal`, `xiSecondInverseMoment`) and
  `XiWeilCriterionConverse.lean` (`xiWeilPolarization_diagonal_eq_sub_two_re` — Weil diagonal
  = second inverse moment − 2·Re(coeff·logDeriv XiC), and
  `riemannHypothesis_of_weilDiagonal_nonneg` — RH from diagonal positivity on the regularized
  Cauchy kernel family alone).  **The organ and the Weil socket are therefore ALREADY FUSED in
  the corpus.**  The genuine open frontier of this card, after three sweeps: prove a
  POSITIVITY REGION — e.g., nonnegativity of
  `xiSecondInverseMoment − 2·Re(xiWeilDiagonalCoeff z · logDeriv XiC z)` for admissible base
  points in the PNTPlus zero-free region, using formalized `ζ'/ζ` bounds
  (`ZetaBounds` DerivUpperBnd/LogDerivZeta lemmas) — the first proven nontrivial positive
  region of the Weil diagonal, feeding `riemannHypothesis_of_weilDiagonal_nonneg`'s hypothesis
  on a quantified subfamily.
- 2026-08-11 — **the chart dictionary [LEAN-PROVED]: first strictly positive Weil diagonals,
  with arithmetic values.**  `RHTower/XiWeilResolventChartDictionary.lean` (wired, umbrella
  green 18921 jobs, all 6 theorems `[propext, Classical.choice, Quot.sound]`).  Fourth
  corpus-first sweep found `XiResolventTraceHankelCriterion.lean` already owning the resolvent
  chart (termwise `Re(α²+X)⁻¹ > 0` via the formalized height gap `xiZeroCopy_two_lt_im_sq`,
  the polynomial-weighted RH criterion `riemannHypothesis_of_forall_xiResolventTrace_re_nonneg`,
  and `xiResolventMoment_zero_eq_logDeriv`).  The new module identifies the two charts at base
  level: `xiWeilCauchyTest_pair_term_eq_resolventPoint` — at imaginary Cauchy parameter the
  Weil pair summand IS the resolvent coordinate `(α²+t²)⁻¹`; hence
  `xiWeilPolarization_cauchyTest_eq_resolventMoment` (diagonal = zeroth resolvent moment),
  **`xiWeilPolarization_cauchyTest_re_pos`** (the FIRST strictly positive family of Weil
  diagonals beyond the even sector — unconditional, consumes `nonempty_xiZeroCopy`),
  `xiWeilPolarization_cauchyTest_eq_logDeriv` (= Euler-ray response `logDeriv ξ(½+t)/t`),
  `logDeriv_xi_div_re_pos` (classical ray positivity, free corollary), and
  **`xiWeilPolarization_cauchyTest_eq_arithmetic`** (t > ½: the diagonal in explicit
  polar/Γℝ/von-Mangoldt terms — a strictly positive Weil diagonal evaluated in prime data).
  **Synthesis now visible across the corpus:** the Weil socket, the resolvent-Hankel
  criterion, Route U's shifted-Hankel tower, and the deviation mass are ONE arithmetic moment
  problem — positivity of the resolvent moment tower, whose entries are formally jets of
  `logDeriv ξ` on the Euler ray (arithmetic for `t > ½`).  Degree 0 is now proven positive in
  both charts; the wall is (exactly as the frontier map's Route U dossier records) all-degree
  positivity, where the corpus's Lean-closed crossing classification and the paper-level
  hard-edge theorems live.
- 2026-08-11 — **degrees 1 and 2 of the tower [LEAN-PROVED]:**
  `RHTower/XiResolventTowerLowDegreePositivity.lean` (wired, umbrella green 18924 jobs, all 9
  theorems `[propext, Classical.choice, Quot.sound]`).  The formalized height gap
  `2 < (Im ρ)²` beats the strip bound: **the 45° cone law**
  (`xiSpectralSq_add_abs_im_lt_re` — every shifted squared spectral point has `|Im| < Re` for
  all `X ≥ 0`) and the **30° cone inequality** at `X ≥ 3/4`.  Hence termwise strict positivity
  of the squared and cubed resolvent coordinates, and
  **`xiResolventMoment_one_re_pos`** (unconditional) and **`xiResolventMoment_two_re_pos`**
  (`X ≥ 3/4`).  The power-kernel dictionary (`xiWeilPolarization_powerKernel_eq_moment` — the
  diagonal Weil value of the `(n+1)`-power Cauchy test IS the `n`-th resolvent moment, all n)
  transfers these to two new strictly positive Weil-diagonal families (squared and cubed
  kernels).  Fifth sweep reuse: `XiResolventHankelLadder.lean` (pow-summability, Hankel form,
  its RH criterion, off-line pair negativity).  Frontier after this brick: degrees 0–2 of the
  arithmetic moment tower are strictly positive with explicit shift thresholds; the Hankel-form
  criterion needs all mixed `2×2` blocks (`M₀M₂ − M₁²`-type, Cauchy–Schwarz on the tower) —
  the first genuinely non-termwise question, where cancellation begins and Route U's crossing
  classification takes over.
- 2026-08-11 — **the resolvent-chart iff [LEAN-PROVED], and the sixth sweep's harvest.**
  Corpus-first (user prompt) found the Turán/Hankel programme far advanced: the HEAT chart
  already owns the full iff (`riemannHypothesis_iff_forall_xiHeatHankelForm_nonneg`,
  `XiGaussianHeatHankelLadder.lean`), ladder nesting (`HeatHankelLadderNesting.lean`), the
  Turán variance expansion with exact negative core in BOTH charts
  (`XiGaussianHeatTuranPairSum.lean`, `XiResolventHankelLadder.lean` —
  `two_mul_xiResolventTuranMinor_eq_tsum_pair`, `xiResolventPairTerm_lineConj` = −4‖u‖²(Im u)²)
  and bottom-shell detection (`XiHeatTuranBottomDetection.lean`: nonneg Turán defect at all
  times forces the bottom copy onto the line).  The resolvent chart lacked only its forward
  direction: new `RHTower/XiResolventHankelEquivalence.lean` (wired, umbrella green 18931
  jobs, all 5 theorems axiom-clean) supplies the Hamburger mechanism — under RH every
  resolvent coordinate is a strictly positive real (`exists_pos_ofReal_xiResolventPoint_of_rh`,
  via the height gap), every polynomial trace is a sum of nonnegative reals (junk-value
  convention absorbs non-summable weights: no norm bounds needed), hence
  **`riemannHypothesis_iff_forall_xiResolventHankelForm_re_nonneg`: for EVERY single shift
  `X ≥ 0`, RH ⟺ positive semidefiniteness of the resolvent Hankel matrix at that one shift**
  — whose entries at `X = x²`, `x > ½`, are the Euler-ray jets of `logDeriv ξ` (arithmetic).
  Plus `xiResolventTuranMinor_re_nonneg_of_riemannHypothesis` (order-two consequence).
  **Chart parity achieved**: heat and resolvent both carry complete iffs; resolvent
  additionally carries unconditional degrees 0–2 (cone laws) and the arithmetic entry
  evaluation; heat additionally carries bottom detection.  Frontier: the Turán minor's SIGN at
  low degree/small shift (negative cores −4‖u‖²(Im u)² vs positive bulk — the deviation-mass
  war at Hankel level); heat-chart bottom detection says its large-parameter sign is decided
  by the bottom copy alone.
- 2026-08-11 — **quantitative Turán control [LEAN-PROVED].**
  `RHTower/XiResolventTuranDeviationControl.lean` (wired, umbrella green 18938 jobs, all key
  theorems axiom-clean).  Mass functionals `S₀ = Σ‖u_q‖`, `S₁ = Σ|Im u_q|`, `M = Σ(Im u_q)²`
  (all unconditionally finite), the pointwise pair inequality `re_pair_ge_bulk_sub_err`
  (`Re(uv(u−v)²) ≥ Re u·Re v·(Re u−Re v)² − err(u,v)` with exact product-form error for
  unit-bounded u, v), exact factorization `tsum_xiResolventPairErr = 4S₁² + 4MS₀ + 8S₁S₀`,
  and the headline **`two_mul_xiResolventTuranMinor_re_ge`**:
  `Re(2·(M₀M₂−M₁²)) ≥ −(4S₁² + 4MS₀ + 8S₁S₀)` — the bulk is termwise nonnegative because
  every resolvent coordinate has positive real part (height gap), so the ENTIRE possible
  failure of the order-two Hankel inequality is explicitly carried by the imaginary masses.
  Plus `riemannHypothesis_iff_xiResolventImSqMass_eq_zero` (the mass in the bound is exactly
  the RH obstruction; converse via the height gap needs no norm cases).  This is the
  quantitative Hamburger direction at order two: Turán defect < −(mass expression) is
  impossible; contrapositively a certified negative Turán value would force explicit
  imaginary mass.  Next: (i) sharpen — the error's `S₁`-terms carry no decay pairing and can
  likely be improved to pure `M`-terms with weights, tightening toward the exact negative core
  `−4Σ‖u‖²(Im u)²`; (ii) the same control at general Hankel order via the polynomial trace;
  (iii) the heat-chart mirror.
- 2026-08-11 — **the quantitative Hamburger bound at EVERY order [LEAN-PROVED].**
  `RHTower/XiResolventTraceMassControl.lean` (wired, umbrella green 18940 jobs, all 6 theorems
  axiom-clean).  The 45° cone transfers to the resolvent coordinates themselves
  (`abs_im_lt_re_xiResolventPoint`: |Im u_q| < Re u_q — inversion preserves the cone); real
  polynomials are imaginary-Lipschitz on the unit disc
  (`abs_im_evalRealPolynomial_le`: |Im P(u)| ≤ L_p·|Im u| with L_p = Σ|coeff k|·k, via
  conj-reflection + the unit-disc power-difference bound `norm_pow_sub_pow_le_of_norm_le_one`);
  the cone gives the pointwise law `re_mul_sq_ge_of_cone`: Re(u·w²) ≥ −2(Im w)² for cone-u.
  Chained: **`xiResolventTrace_re_ge_neg_mass`:
  Re(xiResolventTrace X p) ≥ −2·L_p²·M for EVERY real polynomial p and every shift X ≥ 0**,
  and `xiResolventHankelForm_re_ge_neg_mass` for every Hankel order and coefficient vector —
  where M = Σ(Im u_q)² is the single ℓ² imaginary mass with M = 0 ⟺ RH.  This subsumes the
  step-24 Turán control (purely quadratic mass, no S₁ terms) and quantifies the entire Hankel
  criterion: **the failure of ANY instance of the RH-equivalent positivity is explicitly
  bounded by one deviation mass.**  Equivalently: RH is within `2L²·M` of being a theorem at
  every order simultaneously — the number M is the exact, unique, order-uniform obstruction.
- 2026-08-11 — **quadratic mass decay [LEAN-PROVED].**  `RHTower/XiResolventMassDecay.lean`
  (wired, umbrella green 18944 jobs, all 3 theorems axiom-clean).
  `im_sq_xiResolventPoint_le` — termwise `(Im u_q)² ≤ 2/(‖α_q‖²(X+1)²)` (height gap + strip:
  numerator 4γ²b² ≤ γ², denominator (γ²−b²+X)⁴ ≥ (7/8)⁴γ⁴(X+1)², rational constants close at
  2·(7/8)⁴ ≥ 9/8);  `xiResolventImSqMass_le` — **M(X) ≤ 2H/(X+1)²** with H the genus-one
  Hadamard sum;  `xiResolventTrace_re_ge_neg_div` — **every polynomial trace obeys the
  explicit decaying floor `Re(trace X p) ≥ −4L_p²H/(X+1)²`**.  The complete quantitative
  picture of the Hankel criterion is now: at every shift X ≥ 0 RH ⟺ all forms nonneg (iff);
  every form's failure ≤ 2L²M(X) (order-uniform control); and M(X) ≤ 2H/(X+1)² (decay) — so
  the RH-equivalent positivity holds asymptotically in the shift with explicit rate, uniformly
  over each polynomial, and the one number standing in the way at finite shift is M(X), with
  M = 0 ⟺ RH.  Route U's far-right chamber now has a formal trace-level quantitative
  counterpart with explicit constants.  Lean traps this brick: `div_le_div_iff` renamed
  `div_le_div_iff₀`; prefer `pow_le_pow_left₀` chains over nested nlinarith on fourth powers
  (heartbeat blowups); `set`-folded goals may need `rw [← hdef]` before closing.

## Step 27 (2026-08-11): the unconditional sector of the Hankel criterion — unbounded degree

**Assignment attacked**: close the gap between `M(X) ≤ 2H/(X+1)²` and `0` at one finite shift.
**Honest verdict first**: the gap IS RH — `M(X) = 0 ⟺ RH` (step 24), and any unconditional proof
of full Hankel positivity at one shift converts to RH through the corpus converse
(`riemannHypothesis_of_forall_xiResolventHankelForm_re_nonneg`), so no geometric/soft argument can
close it. What was closable — and is now closed — is the entire *linear and one-signed* sector of
the criterion, at every degree.

### New modules (both [LEAN-PROVED], axioms = [propext, Classical.choice, Quot.sound])

`RHTower/XiResolventUnconditionalSector.lean` (wired after XiResolventMassDecay):
- `sub_nat_mul_mul_pow_le` — Bernoulli induction `(a−nb)aⁿ ≤ (a−b)ⁿa`.
- `sector_pow_gap` — `(2n+1)b < a ⇒ (n+1)b(a+b)ⁿ < a^{n+1}` (AM-GM + Bernoulli, no trig/sqrt).
- `norm_pow_sub_re_pow_le`, `re_pow_ge_of_re_nonneg` — geometric-series drift bound
  `‖z^{n+1} − (Re z)^{n+1}‖ ≤ (n+1)|Im z|(Re z+|Im z|)ⁿ` via `geom_sum₂_mul`.
- `re_pow_pos_of_sector` — **closed-form sector power law**: `(2n+1)|Im z| < Re z ⇒ 0 < Re z^{n+1}`.
- `sector_xiSpectralSq_add` — divisor cone at shift: `X ≥ ((2n+1)²+1)/4` puts every `α²+X` in the
  `1/(2n+1)`-sector (height gap 2<γ² + strip |b|<1/2 + AM-GM `(2n+1)γ ≤ γ²+(2n+1)²/4`).
- `sector_xiResolventPoint` — cone survives inversion.
- `xiResolventMoment_re_pos` / `_of_add_one_sq_le` — **every moment `Rₙ(X)` strictly positive for
  `X ≥ (n+1)²`** — the diagonal of the Hankel criterion holds unconditionally at unbounded degree,
  quadratic shift law.
- `xiResolventHankelForm_re_nonneg_of_nonneg` / `_re_pos_of_nonneg` / `_of_sq_le` — the Hankel form
  is **unconditionally nonneg (strictly positive for nonzero weight) on the whole
  nonnegative-coefficient cone** for `X ≥ (2N+1)²`.
- `exists_coeff_neg_and_pos_of_xiResolventHankelForm_re_neg` — **any Hankel negativity witness at
  admissible shift must have coefficients of both strict signs** (the form is even in the weight).

`RHTower/XiSquaredCompleteMonotonicityFarRay.lean` (composition with the corpus CM module):
- `xiShiftedReciprocalSquare_eq_xiResolventPoint`, `xiShiftedReciprocalMoment_eq_xiResolventMoment`
  — the Möbius-translated reciprocal-square atom IS the resolvent coordinate.
- `xiResolventMoment_im_eq_zero` — every resolvent moment is a real number (conjugation transport).
- `alternating_iteratedDeriv_squaredXiRadialField_pos_of_sq_le` — **unbounded-order complete
  monotonicity on the quadratic far ray**: `(−1)ⁿ g⁽ⁿ⁾(y) > 0` for every `n` once `y ≥ (n+1)²`,
  `g y = ξ′(1/2+√y)/(2√y ξ(1/2+√y))`.
- `alternating_iteratedDeriv_squaredXiRadialField_pos_of_le_or_far` — the union domain
  `{n ≤ 18} ∪ {y ≥ (n+1)²}`; a CM failure (RH-forbidden) is confined to the wedge
  `n ≥ 19, y < (n+1)²`.

### Corpus-first findings (found AFTER writing module 1 — sweep was too narrow again)
- `HTGeometry/SectorPowerPositivity.lean` already owns the tangent-addition sector calculus
  (`re_mul_pos_and_abs_im_le`, budget chain `re_pow_pos_and_abs_im_le_of_chain`, 7 powers at c=1/5)
  — bounded explicit budgets only; my closed-form `(2n+1)`-aperture law is the unbounded-degree
  complement but LOSES a factor ≈ π versus the tangent chain (tan budget diverges at m ≈ (π/2)/c;
  closed form gives m ≈ 1/(2c)). Sharpening candidate: parametric tangent-chain budget would give
  threshold `X ≳ ((n+1)/π)²·4`.
- `RHTower/SquaredXiCompleteMonotonicity.lean` already owns: moment realness, the termwise
  derivative ladder `d/dv Rₙ = −(n+1)R_{n+1}` (`hasDerivAt_xiShiftedReciprocalMoment`),
  `iteratedDeriv_squaredXiRadialField`, CM through order 18 on ALL of y>0 (84-sector from the
  off-line quartet height gap 85 < v), and the arithmetic identification with `logDeriv ξ` on the
  ray. Also stronger height gaps than 2: `xiZeroCopy_fortyOne_div_two_lt_im_sq` (20.5 < γ² for all
  copies), off-line quartet gap 85.

### The wall, sharpened (why nothing further closes)
1. Full-Hankel positivity at large X unconditional ⇒ RH (corpus converse) ⇒ inaccessible to soft
   arguments; confirmed the Hankel matrix of decaying moments is never diagonally dominant.
2. Symmetry alone cannot sign the bilinear sector (step 13b insufficiency theorem).
3. `RH ⟺ Σ‖u‖² = R₁(X)` (the ℓ²-mass equals the arithmetic second moment); the missing object is a
   realization computing `Σ‖u‖²` arithmetically — the GNS socket, unchanged.
4. Degree-2 Turán minor at large X: positive bulk ~ (γ₂²−γ₁²)²/X⁶ vs hypothetical negative core
   ~ 16γ₀²b₀²/X⁶ — SAME decay rate, constants can favor the core; no unconditional sign at any X.

### External calibration
The unconditional sector is the resolvent-chart analogue of short-support Weil positivity
(Bombieri, "Remarks on Weil's quadratic functional…", 2000): support length ↔ degree, shift ↔
inverse support; both stop exactly at the bilinear sign-changing frontier.

### Recorded next candidates
- Heine k-tuple expansion of ALL Hankel determinants (generalizing the pair expansion
  `two_mul_xiResolventTuranMinor_eq_tsum_pair` to k×k minors: Σ over k-tuples of Πu·Vandermonde²)
  — the multilinear structure of the wedge.
- π-factor sharpening of the aperture via parametric tangent-chain budgets.
- Decay `S₁(X) ≤ C·H/√X` (termwise `|Im u| ≤ 1/(2γ²√X)`-type AM-GM) tightening step-24 constants.
- Quantitative detection floor (lower bound on the best negativity in terms of the largest
  single-copy deviation) — makes the defect two-sided.

### Session/tree note
Concurrent session active in this tree during the batch: RouteESignedInverseLoadFlux.lean (Route E
lane) currently fails to build with genuine proof errors and is umbrella-wired;
HTGeometry/CriticalSchurIdealInertiaTransport.lean times out under the working-tree state; both are
the other lane's in-flight work, left untouched. Unwired-but-green Suzuki modules
(MovableAnchorClarkCoherence, TwoPortProjectiveWedge) were wired into RHTower to fix the lint gate.

## Step 28 (2026-08-11): DISCOVERY — quartic shift rigidity of the deviation mass; RH as an escape law

**Claim** (exact): the deviation mass `M X = Σ'_q (Im u_q)²`, `u_q = (α_q²+X)⁻¹`, obeys the
differential law `M′(X) = −4·D(X)` with `D X = Σ' Re(u_q)(Im u_q)²`, and the strip+gap bound
`Re u_q ≤ 1/(X+1)` makes `(X+1)⁴·M(X)` MONOTONE NONDECREASING on `(0,∞)`. Consequences, all
unconditional: quartic floor `M(X) ≥ (X₀+1)⁴M(X₀)/(X+1)⁴` for `X ≥ X₀ > 0`; dichotomy (M ≡ 0 = RH,
or M everywhere positive in the corridor `c/(X+1)⁴ ≤ M(X) ≤ 2H/(X+1)²`); and the new equivalent
criterion **RH ⟺ (X+1)⁴M(X) → 0 as X → ∞ ⟺ (Xₙ+1)⁴M(Xₙ) → 0 along ONE sequence Xₙ → ∞**.
RH is thereby compressed into an exponent gap: unconditional ceiling `X⁻²` (step 26) versus
rigidity floor `X⁻⁴`; any arithmetic bound `M(X) = o(X⁻⁴)` proves RH.

**Module**: `RHTower/XiResolventMassRigidity.lean` (wired after XiSquaredCompleteMonotonicityFarRay).
9 theorems, all axioms [propext, Classical.choice, Quot.sound]:
`xiResolventDampedMass` (def) + nonneg + summable; `xiResolventPoint_re_le` (Re u ≤ 1/(X+1));
`xiResolventDampedMass_mul_le` ((X+1)D ≤ M); `hasDerivAt_im_sq_xiResolventPoint` (termwise
d/dX(Im u)² = −4Re u(Im u)²); `hasDerivAt_xiResolventImSqMass` (M′ = −4D, via
hasDerivAt_tsum_of_isPreconnected with majorant 8/‖α‖² from ‖u‖ ≤ 2/‖α‖², ‖α‖² > 2);
`monotoneOn_quartic_mul_xiResolventImSqMass`; `antitoneOn_xiResolventImSqMass`;
`xiResolventImSqMass_quartic_floor`; `_pos_of_pos`; `_corridor`;
`riemannHypothesis_iff_tendsto_quartic_mass_zero`; `riemannHypothesis_of_escape_sequence`;
`riemannHypothesis_iff_exists_escape_sequence`.

**Status**: [LEAN-PROVED]; [CANDIDATE NEW SCIENTIFIC KNOWLEDGE], provisional. Priority audit:
standard criterion families (Li, Weil, de Branges, Nyman–Beurling) have no shift-rigidity/escape
form; closest flavor relative is de Bruijn–Newman/Rodgers–Tao Lyapunov monotonicity — but that is
attraction of zeros of a heat-DEFORMED ξ, while here the divisor is FIXED, only the resolvent
chart moves, and the law is a persistence FLOOR (opposite direction). The functional M is
corpus-native. Keep provisional pending expert audit.

**Paper mechanism** (verified termwise, then Lean): d/dX u = −u²; Im(−u²) = −2Re u·Im u;
d/dX(Im u)² = −4Re u(Im u)². Termwise the renormalized density
`(X+1)⁴(Im w₀)²/|w₀+X|⁴ = (Im w₀)²((X+1)²/((X+p)²+s²))²` increases because `p = γ²−b² > 1`
(sign of derivative = (X+1)[(X+p)(p−1)+s²] > 0) — the quartic exponent is exactly critical
against the strip+gap constant `p > 7/4 > 1`; exponent 4+ε would break monotonicity.

**Lean traps hit**: pow_two must take its explicit argument or it rewrites the spectral square;
imCLM comp value needs an `rfl`-rewrite then `exact` (simpa mangles the Module instance path:
InnerProductSpace vs Semiring.toModule); id-wrapped derivative values need `simp only [id_eq]`
before value rewrites; there is no `HasDerivAt.im`.

**Next candidates from here**: (i) beat exponent 4 arithmetically — any `o(X⁻⁴)` ceiling on M is
RH; the unconditional ceiling stands at 2 (step 26); zero-density estimates would raise the
ceiling exponent but are not formalized; (ii) the same rigidity in the heat chart (t-derivative
of the heat-deviation mass — compare against genuine de Bruijn dynamics); (iii) D-mass ladder:
D′ computes similarly (all coefficients cone-signed) — a full CM-type hierarchy for M;
(iv) transfer the floor through the Turán defect bound: quantitative lower bounds on how negative
a Hankel form can get at large X if ¬RH.

## Step 29 (2026-08-11): the assignment "arithmetic bound M = o(X⁻⁴)" — collapse principle + exact open core

**Assignment**: find and prove an arithmetic bound `M(X) = o(X⁻⁴)` (which proves RH).
**Verdict, now a THEOREM**: no such bound exists short of RH itself. The quartic rigidity makes
the solution space of the assignment equal to the set of proofs of RH: any eventual majorant `g`
of `M` with `(X+1)⁴g(X) → 0` already implies RH (and then M ≡ 0, g was dominating zero). This is
formalized as `riemannHypothesis_of_mass_eventually_le` — the **collapse principle**. There is no
asymptotic/estimate route: "beating exponent 4" is not an inequality-improvement problem.

**Module**: `RHTower/XiResolventArithmeticTarget.lean` (6 theorems, axioms
[propext, Classical.choice, Quot.sound], wired after XiResolventMassRigidity):
- `norm_sq_xiResolventPoint_decomposition` + `tsum_norm_sq_xiResolventPoint_eq`:
  **ℓ²-mass decomposition** `Σ'‖u_q‖² = Re R₁(X) + 2M(X)` (termwise Pythagoras
  ‖u‖² = Re(u²) + 2(Im u)²).
- `moment_one_re_le_tsum_norm_sq`: geometry ≥ arithmetic, always (one-sided for free).
- `riemannHypothesis_iff_tsum_norm_sq_eq_moment_one_re`: **RH ⟺ Σ'‖u_q‖² = Re R₁(X)** at any
  one shift — RH as the exact equality of the ℓ²-mass (geometric/GNS side) with the arithmetic
  second moment.
- `hasDerivAt_xiResolventMoment_zero`: R₁ = −d/dX R₀ (and R₀(x²) = logDeriv ξ(1/2+x)/x is the
  corpus's Euler-ray identity) — certifying the arithmetic status of the target's right side.
- `riemannHypothesis_of_mass_eventually_le` (collapse principle).
- `riemannHypothesis_of_tsum_norm_sq_eventually_le`: **THE exact open core**: any eventual
  estimate `Σ'‖u_q‖² ≤ Re R₁(X) + g(X)` with `(X+1)⁴g → 0` proves RH.

**Best-shot analysis of every arithmetic route (recorded honestly, all quantitative)**:
1. Zero-free region (PNTPlus): shrinks |b| to ≤ 1/2 − A/log⁹γ — improves CONSTANTS in the
   ceiling only; the X-exponent comes from |α²+X|⁻⁴ termwise and is untouched.
2. Zero-density / b-decay hypotheses: even |b_q| ≤ C/γ_q^{1+δ} for ALL zeros gives only
   X⁴M(X) → Σ4γ²b² < ∞ — a finite limit, not 0. The monotone limit identity forces: o(X⁻⁴) ⟺
   the total deviation charge Σ4(γb)² = 0 ⟺ b ≡ 0. Only exact vanishing works (consistent with
   the collapse principle).
3. Bilinear arithmetic observables are σ-blind: for the conj-stable divisor, reindexing r ↦ σr
   turns every twisted double sum Σ_{q,r}f(A_q+Ā_r) into the plain Σ_{q,r}f(A_q+A_r); e.g. the
   vertical second moment (1/2π)∫|φ(X+it)|²dt = Σ_{q,r}1/(A_q+Ā_r+2X) equals the plain double
   sum — verified by residue computation + reindexing. The ℓ²-mass is a σ-DIAGONAL object;
   no product/second-moment of arithmetic functions reaches it.
4. Diagonal extraction via ordinate-separating exponential sums (Bohr mean of
   F_X(t) = Σu_q e^{iγ_q t}; Landau's formula links such sums to Λ at prime powers):
   4M(X) = BohrMean|F_X|² − 4R₁ modulo ordinate collisions. This is the pair-correlation /
   Route E correlations wall: unconditional error terms in Landau-type formulas are O(log)-scale,
   astronomically above o(X⁻⁴). Route stays open only through that wall.
5. Herglotz/Pick reformulation (φ Stieltjes ⟺ RH) = Lagarias's positivity criterion for ξ'/ξ —
   [REDISCOVERED], not a new opening.

**Net frontier statement (sharpest form to date)**: RH ⟺ the one-sided estimate
`Σ'‖(α_q²+X)⁻¹‖² ≤ −(d/dX)[logDeriv ξ(1/2+√X)/√X] + o(X⁻⁴)`; the reverse inequality is a
Lean theorem; every bilinear-arithmetic route to the left side is formally σ-blind; the two
candidate mechanisms that could see the diagonal are (i) ordinate-separation (pair-correlation
wall) and (ii) an operator/GNS realization computing the ℓ²-mass (the standing socket).

## Step 30 (2026-08-11): certificate ladder recorded in matrix form; J-fraction normal form; socket spec

**New module** `RHTower/XiResolventHankelMatrixLadder.lean` (axioms clean, wired after
XiResolventArithmeticTarget):
- `xiResolventHankelMatrix N X : Matrix (Fin N) (Fin N) ℝ`, entries `Re R_{i+j}(X)`;
  `_isHermitian`; quadratic-form bridge `dotProduct_xiResolventHankelMatrix_mulVec`.
- **`riemannHypothesis_iff_forall_xiResolventHankelMatrix_posSemidef`**: RH ⟺ ∀N,
  `(xiResolventHankelMatrix N X).PosSemidef` at any one shift X ≥ 0 — the certificate ladder as a
  formal object, connected to mathlib's PSD matrix theory.
- `xiResolventHankelMatrix_det_nonneg_of_riemannHypothesis`: the Hankel determinant ladder Δ_N ≥ 0
  under RH (converse direction of the rung ladder).
- Lean traps: `⬝ᵥ`/`*ᵥ` are scoped notations — need `open Matrix` (otherwise the parser falls
  into `subscriptTerm` errors); current `Matrix.PosSemidef` is Finsupp-based — use
  `Matrix.posSemidef_iff_dotProduct_mulVec` (Fintype bridge) and
  `Matrix.PosSemidef.dotProduct_mulVec_nonneg` (in the PosSemidef namespace).

**Reasoning results recorded (from the route analysis, chat 2026-08-11)**:
1. **J-fraction normal form**: rung-N certificate = first N three-term recurrence (Jacobi)
   coefficients of the zero measure Σu_qδ_{u_q} = coefficients of the Stieltjes continued
   fraction of the Euler-ray response logDeriv ξ(1/2+√X)/√X; obtained from prime data by FINITE
   RATIONAL operations (qd-algorithm). RH ⟺ all J-fraction coefficients positive.
2. **Closure analysis**: J-fraction positivity for all k is provable only via (i) an a priori
   positive-measure construction, or (ii) a combinatorial generating law for the coefficients.
   The FE is spent (chart variable is FE-invariant); multiplicativity lives in atom POSITIONS
   (log n) and does not transfer to qd-arrays. No (ii) found; all re-coordinatizations
   (Hankel dets ↔ Jacobi ↔ J-fraction ↔ OPs ↔ escape laws) are positivity-equivalent with no
   independent generating principle ⇒ certificate must be MANUFACTURED (GNS), not verified.
3. **Triangulation**: exactly three diagonal-seeing observable classes, each on a known wall:
   potential pairing (Littlewood lemma: Σ(β−1/2)⁺g(γ) = line integral of log|ζ| − smooth; wall =
   evaluation, killed by collapse principle), correlation separation (Bohr/Landau; wall =
   pair-correlation, killed by collapse principle), realization (GNS; construction — the only
   mechanism the collapse principle does not kill).
4. **Socket sign spec** (new constraint for the Gauss-lane GNS entry): the Euler-ray response
   splits exactly as [rank-one pole atom at −1/4, mass 2] + [c₀·X^{−1/2} continuum] − [manifestly
   positive Stieltjes: digamma cut density + ½-subordinated primes (atom c = log n, weight
   Λ(n)n^{−1/2}, stable-subordinator density — verified rep)]. The arithmetic enters NEGATIVELY:
   any GNS construction must realize the prime part by CONJUGATION (c†·c inside a CP map), not as
   a signed summand. This falsifies all "sum of positive place-states" ansätze immediately.
5. Empirical falsification test for the "certificate pattern" hope (pending compute access): if
   the Jacobi coefficients a_k at X=1 simply re-enumerate the resolvent points u_k = 1/(γ_k²+1)
   with small couplings, the pattern hypothesis dies (certificates = zeros in disguise),
   confirming the construction verdict; unexpected structure would redirect the program.
   BLOCKED: runpod ssh key ~/.ssh/id_ed25519 not present on this machine, agent has no
   identities.

## Step 31 (2026-08-11): runpod experiment — Jacobi certificate structure of the ladder at X = 1

Setup: moments R_0..R_20(1) from the arithmetic side (Cauchy circle, radius 0.3, 512 samples,
dps 450, 32-core); validation: |Im c_n| ≤ 1.2e-442; exact pole-part check 1.5e-201; zero-side
(1000 zeros, weight 2u) matches to 2e-10 (n=2, tail-limited), 1.3e-18 (n=4), 7e-35 (n=8);
Jacobi→moment reconstruction exact. Numbers are certified-quality.

**Data**: R_0(1) = 0.04613592806…, R_1 = 7.3772e-5, R_2 = 2.8441e-7, …, R_20 = 8.78e-49.
Hankel determinants: Δ_2 = 7.68e-9, Δ_3 = 1.68e-21, Δ_4 = 1.78e-40, Δ_6 = 4.6e-98,
Δ_8 = 3.4e-183, Δ_10 = 8.2e-297 (increments ≈ −13,−19,−26,−32,−39,−46,−53,−61 → Δ_N needs
~5N²/2-digit precision; rung-N interval certification cost grows quadratically in N).

**Finding 1 — the pattern hypothesis is DEAD, empirically**: the Gaussian-quadrature nodes of
J_9 lock onto the true resolvent points u_k = 1/(γ_k²+1) from the top: node/u ratios
1.0, 0.99999999, 0.99999, 0.992, 0.930, 0.797, 0.505, 0.204, 0.023 — with 9 rungs, ~4 zeros
resolved (≈ N/2 locking rate); the last node collapses toward the accumulation point 0. The
certificate's content at order N IS the location of the first ~N/2 zeros. No induction on N can
supply that without knowing the zeros: closed-form-certificate hopes are refuted by data, in
agreement with the closure analysis (step 30). Construction (GNS) verdict now confirmed both by
reasoning and experiment.

**Finding 2 — the equilibrium-bulk / edge-locking dichotomy (new, unanticipated)**: the coupling
ratios b_k²/(a_k a_{k+1}) = 0.65, 0.21, 0.22, 0.235, 0.266, 0.24, 0.226, 0.263 — after k=0 they
hover at ≈ 1/4, the CHEBYSHEV/EQUILIBRIUM value for a measure filling an interval [0,c]. The zero
measure at X=1 (atoms u_k accumulating at 0 with density from N(T)) behaves through its first
orthogonal polynomials like a continuum in equilibrium; individual atoms are resolved only at the
top edge, one at a time. So the certificate = [equilibrium bulk profile — governed by
zero-COUNTING, unconditional territory] + [edge-locking corrections — the RH content]. The RH
obstruction concentrates at the spectral EDGE: rung positivity is about the top node converging
to a real point, i.e., zero-by-zero reality, from the lowest zero downward. [CONJECTURE, bulk
part]: b_k²/(a_k a_{k+1}) → 1/4 for the Euler-ray Jacobi sequence, provable from unconditional
zero-counting while positivity persists. Recorded as a candidate unconditional theorem.

**Finding 3 — rung 2 is cheap**: Δ_2/(R_0R_2) ≈ 0.585 — the Turán minor at X=1 is 58% of the
product, NO delicate cancellation. Certifying D_2 ≻ 0 in Lean needs only ~1%-accurate bounds on
R_0, R_1, R_2 at X=1. Ingredients all classical/closed-form: pole parts exact rationals;
ψ(3/4) = −γ_E − 3 log 2 + π/2 and ψ′(3/4) = π² − 8G (Gauss/polygamma closed forms);
ζ(3/2), ζ′(3/2), ζ″(3/2) via partial sums + integral tail bounds. → NEXT FORMAL TARGET:
`D_2(1) ≻ 0` — the first unconditional rung of the ladder in Lean, beyond the sector theorems
(a sign-changing-test positivity at a concrete small shift, currently known only under RH).

Files on pod: /root/jacobi.py, /root/jacobi.out.

## Step 32 (2026-08-11): DIAGONAL EDGE DETECTION — moment positivity pins the lowest zero to the line

**The theorem** (formalizing step 31's empirical edge-locking as exact mathematics):
`RHTower/XiResolventDiagonalEdgeDetection.lean`, all axioms [propext, Classical.choice, Quot.sound]:
- `exists_criticalLine_copy_of_forall_moment_re_nonneg`: **if every resolvent moment Rₙ(X) at a
  single shift X ≥ 0 is nonnegative, then among the divisor copies of MAXIMAL resolvent modulus
  (the zeros minimizing ‖α²+X‖ — the lowest zeros of ξ) at least one lies ON THE CRITICAL LINE.**
- `exists_moment_re_neg_of_offline_edge` (contrapositive): if every maximal-modulus copy is
  off-critical, some diagonal moment is strictly negative — a single sign detects the edge.
- `exists_max_norm_xiResolventPoint`: the resolvent modulus attains its maximum (via
  finite_setOf_le_norm_xiResolventPoint).

**Generic engine** `HTGeometry/UnitPowerSumOscillation.lean` (reusable, axioms clean):
`unitPowerSum_no_decaying_lower_bound` — a nonempty finite family of unit-modulus points ≠ 1
cannot keep Re Σ vᵢ^(n+1) above −Cκⁿ (κ < 1). Finite second-moment proof: Cesàro sums bounded by
2/‖z−1‖ (`norm_geom_sum_le_of_norm_le_one`, `norm_sum_pow_succ_le`, `re_sum_pow_succ_ge`);
(Re A)² = (‖A‖² + Re A²)/2; pair expansion of ‖Aₙ‖² has diagonal +N per index ⇒ square sums grow
linearly; decaying floor ⇒ square sums bounded ⇒ contradiction. Fully effective (explicit
constants C₁, C₄, C₅; negativity threshold explicit in the data).

**Application mechanism**: normalize the finitely many max-modulus points to the unit circle;
"no critical-line copy at the edge" ⇒ all normalized points ≠ 1 (real positive max point ⇒
α²+X real ⇒ α real by height gap 2 < γ²); moments dominate the top power sums modulo a
geometric tail (S₀c·ρⁿ from the strictly smaller second level ρ < r built with the max(·, r/2)
trick — avoids needing Infinite XiZeroCopy); the oscillation engine finishes.

**Status and honest labels**: theorems [LEAN-PROVED]. Mechanism = classical power-sum/dominant-
singularity circle (Turán; Pringsheim flavor) — [LITERATURE] as a technique. The zeta statement —
partial (diagonal-only) positivity ⇒ partial (edge-only) zero reality in the shifted-resolvent
chart, at one shift, with the effective contrapositive — appears in no literature found (closest:
arXiv:1510.03420, full power-sum positivity ⟺ all zeros real for genus-0 with positive zeros —
an iff, not the localized partial implication; their setting also lacks the shift/height-gap
forcing). Label: [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] provisional — significance: FIRST theorem
in the corpus converting partial positivity into partial zero-location (all prior results were
full iff's), completing the arc: experiment saw edge-locking (step 31) → now a theorem (step 32).

**Composition targets recorded**: (i) iterate = deflation: diagonal positivity + 2×2 minors ⇒
two lowest zero classes on-line? (needs deflated-sequence positivity — open); (ii) hypothesis
supply: prove ∀n Rₙ(X₀) ≥ 0 at ONE X₀ unconditionally (weaker than RH; sector theorems give
n ≤ √X₀ only; the missing tail is the edge content again — the hypothesis is exactly
"diagonal-RH"); (iii) quantitative version with the explicit N-threshold from the engine.

**Lean traps**: split on a `set`-bound if-function needs `simp only [hdef]` (beta) before
`split`; targeted `Finset.add_sum_erase` needs the explicit function argument or it rewrites the
wrong Σ; `field_simp` can close goals fully (remove trailing `ring`); Complex division by a real:
rw-chain ofReal_pow/div_eq_mul_inv/ofReal_inv/mul_re/ofReal_re/ofReal_im, NOT bare simp.

## Step 33 (2026-08-12): TURÁN MINORS CLEANSE THE EDGE — the depth-graded criterion begins

**New theorem** `RHTower/XiResolventTuranEdgeCleansing.lean` (axioms [propext, Classical.choice,
Quot.sound], wired after XiResolventDiagonalEdgeDetection):
- `forall_edge_criticalLine_of_forall_turanMinor_re_nonneg`: **if every consecutive Turán minor
  `Rₙ·R_{n+2} − R_{n+1}²` at ONE shift X ≥ 0 is nonnegative, then EVERY divisor copy of maximal
  resolvent modulus — all the lowest zeros of ξ — lies on the critical line.** Strictly stronger
  conclusion than step 32 (∀ edge copies vs ∃ one), from the next Hankel layer.
- `two_mul_turanMinorAt_eq_tsum_pair`: the variance expansion at every level n —
  2(RₙR_{n+2} − R_{n+1}²) = Σ'_{(q,r)} (u_qu_r)^{n+1}(u_q−u_r)² (generalizes the corpus's n = 0
  pair expansion).
- `xiResolventPoint_im_ne_zero_of_spectral`: off-critical spectral points have off-real
  resolvent values (γ ≠ 0 from the height gap).
- `re_div_ofReal`: (z/↑a).re = z.re/a (reusable).

**Mechanism** (first-moment Cesàro only — simpler than step 32): normalize the edge pair points
u_qu_r (modulus r²) to the unit circle; the pair points EQUAL to r² are exactly the conjugate
pairs u_r = conj u_q, whose weights are the exact negative reals −4(Im u_q)² — the negative core
of the corpus's Turán ladder, now at every level n. Truncated at N: conjugate pairs contribute
−4(Im u_q)²·N per off-line edge copy (the witness pair (q, lineConj q) always exists by
conjugation stability); all other unit pair points contribute boundedly (geometric sums ≤
2/‖V−1‖, engine of step 32 reused); the sub-edge tail is a convergent geometric series
(4P₀/(1−ρ/r)). Minor nonnegativity ⇒ 4(Im u)²N bounded ∀N ⇒ Im u = 0 ⇒ (height gap) on the line.

**The emerging depth-graded picture** (steps 32–33): the Hankel criterion resolves the zero
spectrum from the edge downward — diagonal (rank 1) SEES the edge (∃ on-line copy); first minors
(rank 2) CLEAN the edge (∀ on-line). Conjectured continuation: rank-k data cleans/reaches the
k-th modulus level (deflation: subtract the now-known-real edge contributions and iterate —
needs positivity of deflated sequences, open). This grading is the theorem-form of the step-31
experimental structure (equilibrium bulk + edge locking).

**Novelty**: statement not found in literature (searched: Turán inequalities appear for ξ Taylor
coefficients (Csordas–Norfolk–Varga) and Li coefficients — never as zero-LOCALIZING hypotheses in
a resolvent chart at one shift; arXiv:1510.03420 remains the closest, a full iff without
localization). Mechanism classical-flavored (power sums + Cesàro). Label: [LEAN-PROVED] +
[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] provisional.

**Lean traps**: `Summable.of_norm_bounded` now takes (hg) before the bound; `rw [hdef]` on
set-bound lambdas needs `simp only [hdef]` (beta) — recurring; `rw` closes `r ≤ r` goals via
@[refl]-rfl (drop trailing exact le_rfl); `|>.trans_eq (by ring)` fails on metavariable targets —
use explicit calc; norm-rewrite chains must not mix `norm_pow` targets (first occurrence bites).

## Step 34 (2026-08-12): DEFLATION — the minors see the second level; the ladder descends

**New theorem** `RHTower/XiResolventDeflationSecondLevel.lean` (+ engine
`HTGeometry/WeightedUnitPowerSumOscillation.lean`), all axioms
[propext, Classical.choice, Quot.sound], both umbrellas wired:
- `exists_secondLevel_criticalLine_of_forall_turanMinor_re_nonneg`: **if every consecutive Turán
  minor at one shift is nonnegative, then among the divisor copies of maximal resolvent modulus
  STRICTLY BELOW the edge — the second level of lowest zeros — at least one lies on the critical
  line.** With step 33 (same hypothesis cleans the whole edge): rank-2 Hankel data cleans level 1
  and sees level 2. The deflation ladder takes its first step down the zero spectrum.
- Engine: `weightedUnitPowerSum_no_decaying_lower_bound` — oscillation for COMPLEX-weighted unit
  power sums under class-constancy (v i = v j → W i = W j) and conjugation-symmetry
  (v j = conj v i → W j = conj W i) with one nonzero weight; the two hypotheses are exactly what
  keeps the second-moment expansion sign-definite at resonant pairs (both resonance coefficients
  collapse to ‖W‖²). Reusable for all further deflation rungs.
- Helpers: `xiResolventPoint_im_eq_zero_of_spectral` (on-line ⇒ real value),
  `xiResolventPoint_eq_ofReal_of_im_eq_zero` (real max value = the atom).

**Mechanism** (the deflation step, exact): the cleansed edge collapses to the single atom r with
multiplicity m = |T|; substituting Rₖ = m·r^{k+1} + R'ₖ into the minor gives the identity
  minor_n = m·r^{n+1}·Dₙ + (R'ₙR'ₙ₊₂ − R'ₙ₊₁²),
  Dₙ = Σ'_q u^{n+1}(u − r)²  (FULL divisor sum: edge terms vanish identically — no
  subtype-of-subtype needed, the key formalization trick).
The deflated minor is O(ρ^{2n+2}); minor positivity therefore forces the decaying floor
Re Σ_{SF} (u−r)²·(u/ρ)^{n+1} ≥ −C₀κⁿ, κ = max(ρ/r, ρ₂/ρ) < 1, on the second-level system with
weights (u−r)² — class-constant, conj-symmetric, nonvanishing (‖u‖ = ρ < r) ⇒ engine ⇒ a real
point at the second level ⇒ height gap ⇒ critical line.

**The graded criterion after steps 32–34**:
  diagonal (rank 1) ⇒ ∃ on-line at level 1;
  minors (rank 2) ⇒ ∀ on-line at level 1 AND ∃ on-line at level 2.
Conjectured continuation (recorded): rank-k principal-minor data cleans levels < k and sees
level k; full PSD = all levels = RH (consistent with the corpus single-shift iff). Next rung
needs: 3×3-minor pair/triple expansions (Heine k=3) + iterated deflation (subtract TWO real
atoms; the weighted engine already covers the needed weight class). The cleansing of level 2
(∀ vs ∃) needs the step-33 argument on the deflated system — weights now (u−r)², conj-pair
points at 1 carry weight −4(Im u)²·|(u−r)²|-phase — CHECK: the level-2 cleansing needs the
pair-sum of the deflated minor: minor'' expansion — recorded as open.

**Lean traps**: `-(a)/b` vs `-(a/b)` are DIFFERENT linarith atoms — normalize with neg_div before
mixing; `set x : T := e` after a doc-comment: `set_option ... in` must precede the docstring;
stale oleans from `lake env lean` iterations can shadow a revised signature — `lake build +module`
after changing a dependency's statement; deprecated `push_neg` → `rw [not_le]`; conj-goals close
via rewriting the conj SIDE (map_pow, map_sub, conj_ofReal), not by conj-ifying the plain side.

## Step 35 (2026-08-12): LEVEL-2 CLEANSING — the deflated Turán minors; depth two complete

**New theorem** `RHTower/XiResolventDeflatedTuranCleansing.lean` (axioms clean, wired):
- `xiDeflatedMoment t k X := R_{k+2} − 2tR_{k+1} + t²R_k` — the t-deflated moments = moments of
  the divisor reweighted by (u−t)²; `xiDeflatedMoment_eq_tsum` (∀ t, unconditional).
- `two_mul_deflatedTuranMinorAt_eq_tsum_pair`: weighted variance expansion at every level n and
  every deflation point t.
- **`forall_secondLevel_criticalLine_of_forall_deflatedTuranMinor_re_nonneg`**: if all plain AND
  all t-deflated Turán minors at one shift are nonnegative (∀t — these are 2×2 minors of the
  CUBIC Hankel sections in the deflating basis {u−t, u(u−t)}, hence rank-3 positivity data),
  then EVERY copy of maximal resolvent modulus strictly below the edge is on the critical line.

**The graded criterion through depth two, all Lean-proved (steps 32–35)**:
  rank-1 (diagonal)          ⇒ ∃ on-line at level 1;
  rank-2 (plain minors)      ⇒ ∀ on-line at level 1, ∃ on-line at level 2;
  rank-3 (deflated minors)   ⇒ ∀ on-line at level 2.
The induction pattern is now fully exhibited: deflating at the cleansed level-k atom converts
rank-(k+1) determinant data into rank-2 data of the (u−r₁)²···(u−r_k)²-weighted system, whose
edge is level k+1; the cleansing and detection arguments repeat verbatim with the weighted
machinery (weighted oscillation engine + weighted pair expansions — both now in the corpus).
Conjectured general ladder [PAPER-level, recorded]: iterated-deflated Turán data of depth k
cleans the first k levels; RH = the full ladder = single-shift Hankel PSD (corpus iff).

**Mechanism of step 35**: plain minors cleanse the edge to the atom r (step 33/34 blocks);
the weight (u−r)² kills the edge identically, so the deflated pair expansion's maximal pair
points sit at ρ² (level-2 squared); pair points equal to ρ² are conjugate pairs with weights
−4(Im u)²·normSq((u−r)²) < 0 at an off-line witness; first-moment Cesàro + geometric tails
(third-level ρ₂; edge-coordinates give literally zero terms via by_cases q∈T) finish exactly as
in step 33 one level down.

**Lean traps**: same family as before; new: defeq-`show` rewrites for Prod-projections of
`set`-pairs ((qh, σqh).1 etc.); set-folded norms can close goals early (rw-rfl on ρ-folded
‖u qh‖ — remove dead tactics); cast: div_self on ↑(ρ²) needs ofReal_ne_zero, not pow_ne_zero
of (↑ρ)².

## Step 36 (2026-08-12): THE FULL LADDER — spectral descent equivalence [LEAN-PROVED]

**The capstone of the arc.** Two new modules (axioms [propext, Classical.choice, Quot.sound]):

`RHTower/XiResolventWeightedTuranMachine.lean` — **the universal level-cleansing machine**
`forall_level_criticalLine_of_weighted_turanMinors`: for ANY weight Wf on the divisor with
(a) uniform bound, (b) value-conjugation symmetry (u q' = conj u q → Wf q' = conj Wf q),
(c) vanishing above a level ℓ, (d) nonvanishing on it: nonnegativity of the Turán minors of the
Wf-weighted moments Σ'u^{k+1}Wf forces every copy at level ℓ onto the critical line. Subsumes
steps 33 and 35 as instances (Wf = 1 — vacuous kill above the top level — and Wf = (u−r)²).
Also `xiWeightedResolventMoment` (def).

`RHTower/XiResolventSpectralDescent.lean` — **RH as the polynomial Turán ladder**:
- `xiPolyMoment p k X` = Σ' u^{k+1}·(evalRealPolynomial p u)² — the p-weighted moments;
  polynomially weighted variance expansion `two_mul_polyTuranMinorAt_eq_tsum_pair`.
- `polyTuranMinor_re_nonneg_of_riemannHypothesis`: RH ⇒ all polynomial Turán minors ≥ 0.
- `forall_criticalLine_of_forall_polyTuranMinor_re_nonneg`: **SPECTRAL DESCENT** — polynomial
  Turán data at one shift places the ENTIRE divisor on the critical line. Proof: strong
  induction on ncard{q' : ‖u q'‖ ≥ ‖u q‖}: all strictly-higher copies are real atoms by IH;
  P := ∏_{r ∈ atoms}(X − C r) kills them as a weight; the machine at hpoly P cleanses q's level.
- **`riemannHypothesis_iff_forall_polyTuranMinor_re_nonneg`**: at any one shift X ≥ 0,
    RH ⟺ ∀ p : Polynomial ℝ, ∀ n, 0 ≤ Re(M_p n · M_p(n+2) − M_p(n+1)²).

**Significance.** (i) A new single-shift RH equivalence whose sufficient data is a THIN SLICE of
Hankel positivity: only the Turán (log-convexity) inequalities of polynomially reweighted moment
sequences — 2×2 minors — versus the corpus's previous criterion needing all N×N forms. For
general moment functionals this slice does NOT imply full positivity; the implication here runs
through the divisor's specific structure (finite modulus levels, conjugation stability, height
gap). (ii) The forward mechanism is INFINITE DESCENT DOWN THE ZERO SPECTRUM — the criterion
locates the zeros on the line level by level from the lowest upward; the ladder conjectured at
step 34 and built through steps 32–35 is now closed in full generality, in one induction.
(iii) In classical language: RH ⟺ the log-convexity of all sequences n ↦ Σ_ρ (ρ(1−ρ)+X)^{−n−1}
weighted by squared real polynomials in (ρ(1−ρ)+X)^{−1} — Turán inequalities appear in the zeta
literature only as NECESSARY conditions (Csordas–Norfolk–Varga; Li-coefficient variants); an
equivalence, localized, with a descent proof, is to our knowledge new. Label: [LEAN-PROVED] +
[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] provisional pending expert/priority audit.

**Arc summary (steps 32–36, five sessions of one program)**: diagonal ⇒ edge existence;
minors ⇒ edge cleansing + second-level existence; deflated minors ⇒ second-level cleansing;
universal machine + descent ⇒ the full ladder ⟺ RH. Everything rests on: the pair/variance
expansions, the conjugate-pair negative core −4(Im u)²·normSq(W), first/second-moment Cesàro
arguments, finite level sets, and the height gap. The open frontier moves to: SUPPLYING the
polynomial Turán data — for each fixed p a ONE-DIMENSIONAL family of inequalities on an
arithmetic-jet sequence (M_p is a finite combination of moments R_{k+i+j}, all arithmetic).
The GNS/certificate program now has a strictly easier target: realize positivity of the
p-weighted sequences one p at a time.

**Traps**: tabs from heredoc python strings break Lean (expand!); rw with a self-referential
equation (z = f(‖z‖)) rewrites inside the norm — use sub_eq_zero + exact; Set.ncard_lt_ncard has
autoParam finiteness; Nat.strong_induction_on names the IH `∀ m < N, ...`.

## Step 37 — the moment-index quantifier is redundant: RH as one Cauchy–Schwarz inequality per polynomial [LEAN-PROVED]

**Claim.** At any one shift `X ≥ 0`:

1. `RH ⟺ ∀ p : Polynomial ℝ, 0 ≤ Re(M_p(0)·M_p(2) − M_p(1)²)` — the single index-0 Turán
   minor per polynomial (`riemannHypothesis_iff_forall_polyTuranMinor_zero_re_nonneg`,
   `RHTower/XiResolventSingleMinorCriterion.lean`).
2. `RH ⟺ ∀ f g : Polynomial ℝ, 0 ≤ Re(L(f·f)·L(g·g) − L(f·g)²)` where
   `L p = Σ'_q u_q · p(u_q)` is the resolvent trace functional — RH is literally the
   Cauchy–Schwarz inequality of one explicit arithmetic functional at one point
   (`riemannHypothesis_iff_forall_polyCauchySchwarz`,
   `RHTower/XiResolventTraceCauchySchwarz.lean`).

**Mechanism.** Two new ingredients over step 36:

- *Index-shift identity* `xiPolyMoment_X_pow_mul`: `M_{X^m·p}(k) = M_p(k + 2m)` (from
  `u^{k+1}(u^m p(u))² = u^{k+2m+1}p(u)²`). The polynomial quantifier alone regenerates the
  whole EVEN-index minor ladder from the single index-0 minor.
- *Parity-robust machine* `forall_level_criticalLine_of_weighted_turanMinors_even`
  (`RHTower/XiResolventEvenTuranMachine.lean`): the level-cleansing Cesàro argument survives
  restriction to even minors. Key point: a normalized pair point `V` on the unit circle with
  `V² = 1, V ≠ 1` would force `u₂ = −conj u₁`, impossible since every resolvent point has
  strictly positive real part (`xiResolventPoint_re_pos`). Hence odd-power partial sums
  `Σ V^{2n+1} = V·Σ(V²)^n` stay bounded by `2/‖V²−1‖`, conjugate pairs still contribute the
  exact negative core `−4β·N` linearly, and the sub-level tail is geometric with ratio
  `(ρ₂/ℓ)²`. The descent then feeds the machine `hpoly (X^n · P)` instead of `hpoly P n`.
- The C-S packaging uses the Lagrange pair identity
  `2(L(f²)L(g²) − L(fg)²) = Σ'_{pairs} u₁u₂ (f₁g₂ − f₂g₁)²` and the specialization
  `g := X·f`, which recovers exactly `(M_p(0), M_p(1), M_p(2))`.

**Significance.**

- Strict sharpening of step 36: the `∀ n` quantifier is gone. The criterion is now *one real
  inequality per real polynomial* — the map `p ↦ Re(M_p(0)M_p(2) − M_p(1)²)` must be ≥ 0.
- The displayed C-S defects are abstractly invariant under negating a functional, but that does
  **not** make the literal Xi criterion sign-blind. Actual Xi has real `L` and an unconditional
  positive anchor `L(1)>0`; setting `g=1` forces `L(f²)>=0` for every `f`. Hence the all-pairs
  packaging is equivalent to Hamburger/Weil square positivity. The genuinely thin result is the
  diagonal family `g=Xf`, whose second vector depends on the first; its converse uses descent
  oscillation and does not assume square positivity. This correction is paper-proved on
  `route-u-positive-anchor-cauchy-schwarz-collapse.md`.
- Literature: Turán inequalities for ξ (Csordas–Norfolk–Varga etc.) are necessary conditions
  only; Li/Sekatskii single-point criteria are linear families. A quadratic 2×2-only
  equivalence at an arbitrary interior point with a descent-proof appears to be new.
  [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] provisional pending independent priority audit.

**Lean traps (new).** `field_simp` cannot reconcile `ℓ^(n*4)` with `ℓ⁻¹^(n*2)` under
symbolic exponents — pre-split all powers to matching atoms (`ℓ^(2n)`, `ℓ²`) via
`← pow_mul` / `← pow_add` before `field_simp` (which then closes fully — drop trailing
`ring`). `norm_num at h` on a minor inequality expands `Complex.mul_re` — use
`simpa only [Nat.zero_add] using h` to normalize Nat indices only.

**Next frontier.** (a) Supply the single inequality for concrete `p` (start `p = 1`:
`Re(R₀R₂ − R₁²) ≥ 0` at one shift — the pure edge case); (b) quantitative descent: replace
the infinitary Cesàro contradiction by Turán-power-sum effective bounds to get finite jet
certificates for partial RH; (c) the abstract masking no-go: plain minors (no polynomial
quantifier) provably cannot detect below the geometric mean of two higher real atoms —
worth a Lean counterexample to certify sharpness of the polynomial quantifier.

## Step 38 — the frontier pair: masking no-go + two-scale supply [LEAN-PROVED]

Attack on the three frontier items of step 37; outcome: (c) fully proved, (a) resolved by a
no-go analysis plus a bridge theorem, (b) scoped as the next program.

**(c) The masking no-go — the polynomial quantifier is not removable.**
`GaloisForLFunctions.HTGeometry.exists_nonreal_config_forall_turanMinor_re_nonneg`
(`HTGeometry/TuranMinorSubEdgeMasking.lean`): an explicit conjugation-symmetric
configuration — real atoms `12/25`, `5/12` with multiplicity 100, non-real pair
`w = (50 + 35i)/149` — in the open right unit half-disk with ALL moments ≥ 0 and ALL plain
Turán minors ≥ 0 at every index n, yet `Im w ≠ 0`. Mechanism: `|w| < 5/12`, so every pair
interaction involving `w` lives at scale ≤ `(1/5)^{n+1}` = the scale of the real-real pair
mass, and multiplicity 100² beats 100 uniformly in n (single rational bracket inequality,
n-free after scale comparison). The point w is numerically realizable as an actual resolvent
point (γ² = 1 + √149/10 ≈ 2.22 > 2, b = 7/(10γ) ≈ 0.47 < 1/2, X = 0), and its modulus
lies below the geometric mean √(1/5) of the two real atoms. CONSEQUENCE: the inference
"plain minors ⇒ all points real" is FALSE under every structural hypothesis the
level-cleansing machinery uses; detection below the geometric mean of two higher real atoms
REQUIRES a weight vanishing on the higher atoms. The polynomial quantifier in
`riemannHypothesis_iff_forall_polyTuranMinor_zero_re_nonneg` is essential, not an artifact.

**(a) Status resolved: the p = 1 datum is not abstractly winnable; it IS a bridge theorem.**
Analysis (recorded): an adversarial admissible configuration (one non-real pair + tiny tail)
makes `Re(R₀R₂ − R₁²) < 0`, so no proof from the resolvent-chart axioms alone can supply the
datum — it genuinely requires arithmetic knowledge of where zeta's zeros are. The winnable
form is the **two-scale supply theorem**
`RHTower.xiResolventTuranMinor_zero_re_nonneg_of_partial_line`
(`RHTower/XiResolventPartialLineSupply.lean`): if every copy with resolvent modulus ≥ δ lies
on the critical line, and `8εS ≤ 2r₁r₂(r₁−r₂)²` (ε = sub-δ norm-mass tail, S = total norm
mass, r₁ ≠ r₂ two above-δ moduli), then the index-0 plain minor at X is ≥ 0. Proof: split
the variance pair expansion at scale δ; above δ all atoms are positive reals (block ≥ the
separated witness pair 2r₁r₂(r₁−r₂)²); the complement pair mass is
S² − (S−ε)² ≤ 2εS, each pair term ≤ 4× its mass. Companion
`polyTuranMinor_one_zero_re_nonneg_of_partial_line` phrases it for the p = 1 instance of the
single-minor criterion via `xiPolyMoment_one : xiPolyMoment 1 k X = xiResolventMoment k X`.
So the first Turán datum = (partial RH at one scale) + (one checkable mass inequality) —
exactly the interface the effective program (b) must fill.

**(b) Scoped, not yet attacked**: effective Turán power-sum bounds → finite-n oscillation
windows → finite jet certificates for partial RH. Opens with formalizing a quantitative
version of the machine's Cesàro contradiction.

All four theorems audit to [propext, Classical.choice, Quot.sound]. Wired:
HTGeometry.lean (EOF append), RHTower.lean (after XiResolventTraceCauchySchwarz).

**Lean traps (new).** `rw [norm_mul, norm_pow, norm_mul, pow_one]` on ‖(uv)^{0+1}(u−v)²‖
normalizes only the FIRST power — state subsequent bounds against the actual residual form.
`set x := e` performed after the theorem's binders rewrites e inside hypotheses too — a later
`rw [← hx] at h` then fails with "pattern not found" because h already mentions x.
Multiplicity-4 configurations: prove `![a,b,w,w'] 2 = w` etc. as `rfl` facts and pass them to
`norm_num` — bare norm_num only reduces vecCons indices 0 and 1.

## Step 39 — effective descent, part I: the explicit detection window [PAPER-PROVED → Lean in progress]

Frontier item (b) of step 37, opening move. The even machine's master estimate
`0 ≤ −4βN + CP2 + CT` already uses minor nonnegativity only for `n < N`; re-quantifying it
turns the infinitary contradiction into an **explicit detection-index bound**.

**Theorem (effective even-minor detection).** Setup: `X ≥ 0`; weight `Wf` conj-symmetric,
`‖Wf‖ ≤ BW`, vanishing above level `ℓ > 0`; `ρ₂ ∈ [0, ℓ)` dominating all sub-level moduli;
`S ≥ Σ'‖u_q‖` (total resolvent mass); `g > 0` lower-bounding `‖V² − 1‖` over non-resonant
level pairs (`V = u₁u₂/ℓ²`); `qh` at level `ℓ` off-line with `Wf qh ≠ 0`. If the even
weighted minors `M(2n)M(2n+2) − M(2n+1)²` have nonnegative real part for all `n < N`, then

  N ≤ (2S²BW²/g + BW²S²/(ℓ² − ρ₂²)) / (Im(u_qh)²·|Wf qh|²).

**Paper proof.** Master estimate as in the even machine (its proof consumes minors only at
`n < N`): `0 ≤ −4βN + CP2 + CT` with `β = Im(u_qh)²|Wf qh|²`,
`CP2 = Σ_{non-resonant level pairs} ‖W₁W₂(u₁−u₂)²‖·2/‖V²−1‖`,
`CT = 4BW²P₀/ℓ² · 1/(1−(ρ₂/ℓ)²)`, `P₀` = complement pair mass. Three elementary bounds:
(i) level cardinality: `|SF|·ℓ = Σ_{SF}‖u‖ ≤ Σ'‖u‖ ≤ S`, so `|SF| ≤ S/ℓ`;
(ii) each CP2 term ≤ `(BW²·4ℓ²)·(2/g)`, count ≤ `|SF|²`, so `CP2 ≤ 8S²BW²/g`;
(iii) `P₀ ≤ Σ'_{all pairs}‖u₁‖‖u₂‖ = (Σ'‖u‖)² ≤ S²` and
`CT = 4BW²P₀/(ℓ²−ρ₂²) ≤ 4BW²S²/(ℓ²−ρ₂²)`. Combine: `4βN ≤ 8S²BW²/g + 4BW²S²/(ℓ²−ρ₂²)`;
divide by `4β`. ∎

Corollaries: detection form (`N > bound ⇒ ∃ n < N` with a negative even minor); certificate
form (finitely many even minors clean the level down to any defect threshold); top-level
plain-minor form (`Wf = 1`, `BW = 1`, level = maximal modulus — finitely many *plain* even
minors `R_{2n}R_{2n+2} − R_{2n+1}²` detect an off-line zero at the top level, window
`(2S²/g + S²/(ℓ²−ρ₂²))/Im(u_qh)²`).

Numerically pre-certified: 200 random two-scale configurations, first negative even minor
always within the bound (session scratch, 2026-08-12).

**Step 39 status: [LEAN-PROVED].** Module
`RHTower/XiResolventEffectiveTuranDetection.lean`, five theorems, all auditing to
[propext, Classical.choice, Quot.sound], olean-built, wired into RHTower.lean:

- `even_minor_truncation_le_of_offline_level` — the window bound: any truncation length `N`
  with all even weighted minors `n < N` nonnegative satisfies
  `N ≤ (2S²B²/g + B²S²/(ℓ²−ρ₂²)) / (Im(u_qh)²·|W qh|²)`.
- `exists_neg_even_minor_of_offline_level` — detection form (negative minor inside the window).
- `level_criticalLine_of_even_minors_window` — the finite jet certificate: minors on a finite
  window clean the level down to any defect threshold.
- `xiWeightedResolventMoment_one` — weight-1 bridge to the raw moments.
- `exists_neg_even_plain_minor_of_offline_top` — top level (maximal modulus): finitely many
  PLAIN even minors `R_{2n}R_{2n+2} − R_{2n+1}²` detect an off-line zero, window
  `(2S²/g + S²/(ℓ²−ρ₂²))/Im(u_qh)²`.

**Key structural point vs literature.** Classical Turán power-sum lower bounds
(Turán's main theorems, Tijdeman, Montgomery's lectures) give detection constants that decay
*exponentially* in the truncation length (`(N/(2e(m+N)))^N`-type); the minor family detects in a
window *polynomial* in the configuration data — the conjugate-pair term is linearly negative in
the truncation length while all oscillating pairs stay bounded (`2/g`) and the sub-level tail
sums geometrically. Hankel–Turán literature for special-function zeros (order-moment transport
arXiv:2606.31647; Rayleigh-sum Hankel determinants; ultraspherical Turán revisited) is
closed-form/qualitative, not detection-window quantitative. The effectivization is of OUR
criterion, so novelty rides on the criterion; label the window theorems [LEAN-PROVED], candidate
significance inherited from the step-36/37 arc.

**Lean traps (new).** linarith cannot connect division atoms across scalar multiples
(`8*S^2*BW^2/g` vs `2*S^2*BW^2/g`) inside a large local context — name the divided quantities
via `obtain ⟨A, hA⟩ : ∃ A, A = S^2*BW^2/g := ⟨_, rfl⟩` and rewrite the bounds to `8*A`, `2*A`
first; then linarith is purely linear. `push_neg` now emits a deprecation warning on this
toolchain (gate fails on warnings) — use `simp only [not_exists, not_and, not_lt]` instead.

**Next frontier (b, part II).** Effective descent iteration: compose the per-level window with
the killing-polynomial construction of the spectral descent (weight `P(u)²`, `P = ∏(X−r)` over
higher real atoms) to certify partial RH down to scale δ from finitely many polynomial-weighted
minors with explicit polynomials and windows; interface with the two-scale supply bridge
(step 38) closes the loop data-side. Also open: window optimality (is the `S²/g` shape tight?
the masking config of step 38 gives a lower-bound testbed).

## Step 40 — effective descent, part II: the polynomial descent step [PAPER-PROVED → Lean]

The window theorem instantiated at killing-polynomial weights, phrased so the finite
certificate consists of **single-minor data** (the step-37 criterion instances).

**Theorem (polynomial window).** Same two-scale setup; `P : ℝ[X]` with
`P(u_q) = 0` for every copy above level `ℓ` (a real polynomial can kill ANY conj-symmetric
finite set — non-real pairs via `(X−w)(X−w̄)` — so no descent induction is needed to state the
step); witness `qh` at level, off-line, `P(u_qh) ≠ 0`. If the even `P`-weighted minors are ≥ 0
for `n < N`, then `N ≤ (2S²b⁴/g + b⁴S²/(ℓ²−ρ₂²)) / (Im(u_qh)²·‖P(u_qh)‖⁴)` with
`b = evalRealPolynomialNormBound P 1`.

**Paper proof.** Instantiate the step-39 window with `Wf := P(u)²`, `BW := b²`:
`‖P(u)²‖ = ‖P(u)‖² ≤ b²` (norm bound on the unit disk); conj-symmetry from
`evalRealPolynomial_conj` and `map_pow`; kill from `P(u)² = 0`; defect
`normSq(P(u_qh)²) = ‖P(u_qh)‖⁴`; `(b²)² = b⁴`. ∎

**Single-minor phrasing.** By the index shift `M_{X^n·P}(k) = M_P(k+2n)` (step 37), the even
minor hypothesis at `n` equals the (0,2,1) single-minor datum at the polynomial `X^n·P`. So the
finite certificate reads: *the step-37 single-minor data at the `N` polynomials `X^n·P`,
`n < N`, clean level `ℓ`* — one real inequality per polynomial, `N` explicit. Certificate
corollary: any copy at the level not killed by `P` and with window below `N` is on the line.

Numeric pre-certification inherited from step 39 (the 200-config sweep used arbitrary bounded
weights, which covers polynomial weights).

## Step 40b — the nodal single-minor criterion: sharpening the RH endpoint [PAPER-PROVED → Lean]

Reading the spectral descent's proof shows it consumes polynomial Turán data ONLY at killing
products `∏(X − r)` over higher real atoms (nodes in `(0,1]` — norms of resolvent points), and
the step-37 single-minor reduction consumes only `X^m`-shifts of those. Hence the step-37
RH-equal endpoint strengthens:

**Theorem (nodal single-minor criterion).** For any shift `X ≥ 0`:
RH ⟺ for every finite set `R ⊂ (0,1]` of real nodes and every `m : ℕ`,
`0 ≤ Re(M_p(0)M_p(2) − M_p(1)²)` for `p = X^m·∏_{r∈R}(X − r)`.

The test family shrinks from all real polynomials (arbitrary coefficients) to *monic real-rooted
polynomials with roots in `[0,1]`* — squares of real-rooted multipliers suffice (echoes the
Laguerre–Pólya/Jensen hyperbolicity circle, but as a reweighting criterion, not a coefficient
condition).

**Paper proof.** Forward: RH ⇒ all polynomial data (step 36 forward), a fortiori nodal.
Backward: clone the descent's strong induction on the count of higher-modulus copies; at each
step the killing polynomial IS `nodalPolynomial atoms` with atoms = norms of strictly-higher
copies (real by the induction hypothesis, in `(0,1]` since `0 < ‖u q‖ < r = ‖u q'‖ ≤ 1`); the
even machine (step 37) needs only even-index minors of the `P`-reweighted moments, and the
`(2n, 2n+2, 2n+1)` minor of `P` is the `(0,2,1)` single minor of `X^n·P` by the index shift. ∎

**Steps 40 + 40b status: [LEAN-PROVED].** Two modules, all theorems auditing to
[propext, Classical.choice, Quot.sound], olean-built, wired into RHTower.lean.

`RHTower/XiResolventEffectivePolynomialDescent.lean`:
- `poly_minor_truncation_le_of_offline_level` — the polynomial detection window: for `P` real
  killing every copy above level `ℓ`, truncation `N` with all even `P`-weighted minors ≥ 0
  satisfies `N ≤ (2S²b⁴/g + b⁴S²/(ℓ²−ρ₂²))/(Im(u_qh)²‖P(u_qh)‖⁴)`, `b = normBound P 1`.
- `poly_single_minor_truncation_le_of_offline_level` — same window with data = the `(0,2,1)`
  single minors at the `N` polynomials `X^n·P` (one real inequality per polynomial).
- `level_criticalLine_of_poly_single_minors_window` — the finite polynomial jet certificate.

`RHTower/XiResolventNodalSingleMinorCriterion.lean`:
- `nodalPolynomial R = ∏_{r∈R}(X − C r)` + complex evaluation lemma.
- `forall_criticalLine_of_forall_nodal_single_minor` — nodal descent (strong induction; killing
  polynomial IS a nodal polynomial with nodes in `(0,1]`; even machine per level).
- `riemannHypothesis_of_forall_nodal_single_minor`.
- **`riemannHypothesis_iff_forall_nodal_single_minor`** — the sharpened endpoint: at any one
  shift `X ≥ 0`, RH ⟺ ∀ finite `R ⊂ (0,1]`, ∀ m, single `(0,2,1)` Turán minor of the
  `(X^m·∏_{r∈R}(X−r))²`-reweighted moments is ≥ 0. STRICT strengthening of the step-37
  capstone: the test family collapses from all real polynomials to monic real-rooted
  polynomials with roots in `[0,1]`.

**Audit notes.** In classical moment theory, restricting positivity tests to real-rooted squares
weakens a positive-definiteness condition; here the equivalence survives at the thin family
because detection is descent oscillation (the killing weights are constructed inside the
family), not square positivity — the criterion is NOT a Hamburger-type condition (route-u
correction stands). Literature echo: Laguerre–Pólya/Jensen hyperbolicity (Griffin–Ono–Rolen–
Zagier) is a coefficient-side statement about ξ; ours is a moment-reweighting test family.
[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] provisional for the nodal collapse, pending independent
priority audit; inherits the step 36-39 arc.

**Next frontier.** (i) Window optimality (masking config as lower-bound testbed); (ii) node
continuity: the nodal family is indexed by finite subsets of the compact `(0,1]` — quantify
stability of the datum in the nodes (Lipschitz in the node positions with the effective
constants), toward a countable dense sub-family criterion (rational nodes) — that would make
the RH endpoint a countable list of closed-form real inequalities; (iii) arithmetic supply of
the first nodal data via the two-scale bridge.

## Step 41 — rational nodes: RH as a countable list of real inequalities [PAPER-PROVED → Lean]

Densify the nodal criterion: the datum is Lipschitz in the node positions with explicit
constant, so rational nodes suffice — the RH endpoint becomes a countable family indexed by
`(j, m, c : Fin j → ℚ)`.

**Stability lemma.** For node tuples `c, c' ∈ [0,1]^j` with `|c_i − c'_i| ≤ ε`, shift `m`,
`p = X^m·∏(X−c_i)`, `S ≥ Σ'‖u‖`:
- eval bound: `‖p(u)‖ ≤ 2^j` on the closed unit disk (each factor ≤ 2);
- eval difference: `‖∏(u−c_i) − ∏(u−c'_i)‖ ≤ j·2^j·ε` (corpus `norm_prod_sub_prod_le`,
  factors bounded by 2, per-factor difference `|c_i − c'_i| ≤ ε`);
- squared difference: `‖p² − p'²‖ = ‖p−p'‖·‖p+p'‖ ≤ j·2^j·ε · 2^{j+1} = j·2^{2j+1}ε`;
- moment difference: `|M_c(k) − M_{c'}(k)| ≤ S·j·2^{2j+1}ε`; moment bound `|M(k)| ≤ S·4^j`;
- datum difference: `|Re(M0M2−M1²) − Re(M0'M2'−M1'²)| ≤ 4·(S4^j)·(Sj2^{2j+1}ε) = 8jS²16^j·ε`.

**Density.** Given real nodes `c ∈ (0,1]^j` and `δ > 0`: pick rationals
`q_i ∈ (max(c_i−ε, c_i/2), c_i)` (dense order), so `q_i ∈ (0,1] ∩ ℚ`, `|c_i − q_i| ≤ ε`;
with `ε := δ/(L+1)`, `L = 8jS²16^j`, the rational datum ≥ 0 forces the real datum ≥ −δ for
every δ, hence ≥ 0. Finset-nodal data follow by enumerating each node set as a tuple
(`orderIsoOfFin` + product transport), and RH follows from the step-40b nodal criterion. ∎

**Capstone.** RH ⟺ ∀ (j m : ℕ) (c : Fin j → ℚ ∩ (0,1]),
`0 ≤ Re(M_p(0)M_p(2) − M_p(1)²)`, `p = X^m·∏(X − c_i)` — a COUNTABLE family of real
inequalities at one shift. Note: countability per se is not new (Li's criterion is a countable
list); the content is the structure — single 2×2 minors of nodal reweightings at one point,
with the density argument powered by our own effective constants.

**Step 41 status: [LEAN-PROVED].** Module `RHTower/XiResolventRationalNodeCriterion.lean`,
eleven declarations, all auditing to [propext, Classical.choice, Quot.sound], olean-built,
wired. Key theorems:
- `norm_evalRealPolynomial_shiftedFinNodal_le` / `_sub_le` — `2^j` bound and `j·2^j·ε`
  node-displacement bound on the unit disk (via corpus `norm_prod_sub_prod_le`).
- `norm_xiPolyMoment_shiftedFinNodal_le` / `_sub_le` — moment bounds `S·4^j` and
  `S·j·2^(2j+1)·ε`.
- `abs_re_datum_shiftedFinNodal_sub_le` — datum Lipschitz constant `8j·S²·16^j`.
- `finNodal_datum_re_nonneg_of_rational` — rational density (approximation from below keeps
  nodes in `(0,1]`; `ε = δ/(L+1)`).
- **`riemannHypothesis_iff_forall_rational_nodal_single_minor`** — RH ⟺ the countable family
  of single (0,2,1) minors indexed by `(j, m, c : Fin j → ℚ)`, nodes in `(0,1] ∩ ℚ`.
- `rational_nodal_index_countable` — the index type is countable (instance-level).

Numerically pre-certified (300 random configs; worst observed ratio 5·10⁻³ of the Lipschitz
bound). Lean traps (new): a `have h := lemma args` without expected type cannot infer an
implicit that appears only inside a polynomial argument of the conclusion — pass `(m := m)`
explicitly; `calc` blocks with `‖_ + _‖` placeholder heads fail to parse — use
`refine le_trans (mul_le_mul ...) (le_of_eq ?_)` or plain `exact` on the rewritten goal.

**Next frontier.** (i) Window optimality (step-38 masking testbed); (ii) nodal supply: feed the
two-scale bridge into the FIRST rational-nodal data (R = ∅, j = 0 gives the plain single
minors; the bridge already supplies index 0) — chart the exact arithmetic content of the first
nontrivial rational instances; (iii) monotone structure of the rational family (does datum at
finer node sets dominate coarser ones? a lattice structure on the countable list would give a
canonical exhaustion).

## Step 42 — arithmetic content of the countable list + order-structure no-go [PAPER-PROVED → Lean]

Three-part attack on the recorded frontier: (A) universal supply, (C) refinement order, (B)
window optimality (assessed after A/C).

**(A) Universal nodal supply theorem.** Every entry of the countable rational-nodal list is
priced by the two-scale bridge. For ANY real polynomial `p` with `‖evalRealPolynomial p z‖ ≤ B`
on the unit disk, partial line placement above `δ` plus the mass inequality

  `8·B⁴·ε·S ≤ 2·(r₁r₂)^{2m+1}·(eval_{r₁} p)²·(eval_{r₂} p)²·(r₁−r₂)²`

(ε = sub-δ mass, S = total mass, r₁ ≠ r₂ two above-δ moduli) forces the `(0,2,1)` single-minor
datum of `X^m·p` to be nonnegative. Paper proof = step-38 two-scale split with weights: the
pair expansion of `p` at index `2m` (corpus `two_mul_polyTuranMinorAt_eq_tsum_pair`); above-δ
pair terms are `(r₁r₂)^{2m+1}·(eval p)²(eval p)²·(r₁−r₂)² ≥ 0` (atoms are positive reals by
line placement, weights are squares of real evaluations); the block dominates the separated
witness pair; complement pair terms ≤ `4B⁴ × pair mass ≤ 4B⁴·2εS`. Index transfer by
`xiPolyMoment_X_pow_mul`. Rational instances: `p = finNodalPolynomial c`, `B = 2^j`, witness
evaluations `∏(r_k − c_i)`. CHART: the cost of entry `(j, m, c)` degrades exponentially in `m`
(via `(r₁r₂)^{2m+1}`) and in `j` (via `16^j` and the node-witness distances) — the cheap prefix
of the list is small `j + m` with nodes away from the witness moduli. ∎ (mod Lean)

**(C) Refinement monotonicity is FALSE — explicit falsifier.** Config: real atom `1/2` with
multiplicity 6, conjugate pair `(3 ± 4i)/10` (norms ≤ 1, positive real parts, conj-symmetric).
Plain `(0,2,1)` datum: `M₀ = 18/5, M₁ = 34/25, M₂ = 129/250`, datum `= 1/125 > 0`. One-node
datum at the RATIONAL node `r = 1/2` (kills the real atom): only the pair survives,
`N_k = w^{k+1}W + conj`, `W = (w − 1/2)² = (−3−4i)/25`, and by the single-pair identity
`N₀N₂ − N₁² = |W|²|w|²(w − w̄)² = −4|W|²|w|²·Im(w)² = −4·(1/25)·(1/4)·(4/25) = −4/625 < 0`.
So passing a coarser instance does NOT imply passing a finer one: the rational family has no
refinement-monotone order; canonical exhaustion is by enumeration, not domination. Positive
salvage: the identity `(wW+w̄W̄)(w³W+w̄³W̄) − (w²W+w̄²W̄)² = WW̄·ww̄·(w−w̄)²` (pure ring) shows any
config reduced by a nodal weight to a single off-line pair has strictly negative datum — the
node mechanism of detection in closed form. ∎ (mod Lean)

**Step 42 status: (A) and (C) [LEAN-PROVED]; (B) scoped.** Two modules, all six declarations
auditing to [propext, Classical.choice, Quot.sound], olean-built, wired.

`RHTower/XiResolventNodalSupply.lean`:
- `polyTuranMinor_supply_of_partial_line` — THE UNIVERSAL SUPPLY THEOREM: for any real
  polynomial `p` with pointwise disk bound `B`, line placement above `δ` plus
  `8B⁴εS ≤ 2(r₁r₂)^{2m+1}(eval_{r₁}p)²(eval_{r₂}p)²(r₁−r₂)²` gives the `(0,2,1)` datum of
  `X^m·p`. Clone of the step-38 two-scale split with squared-real-evaluation weights.
- `rational_nodal_datum_of_partial_line` — the nodal pricing: disk bound `2^{4j}`, witness
  factors `∏(r_k − c_i)`. Chart: entry `(j, m, c)` costs `(r₁r₂)^{2m+1}` in the shift and
  `2^{4j}·∏(r_k − c_i)²`-degradation in the nodes — the cheap prefix of the countable list is
  small `j + m` with nodes away from the witness moduli.
- `eval_finNodalPolynomial` — real evaluation = product of node offsets.

`HTGeometry/TuranMinorNodeRefinementNonmonotone.lean`:
- `pair_minor_identity` — `(wW+w̄W̄)(w³W+w̄³W̄) − (w²W+w̄²W̄)² = WW̄·ww̄·(w−w̄)²` (pure ring).
- `pair_minor_re_neg` — single off-line pair datum `= −4|W|²|w|²Im(w)² < 0`.
- `exists_config_turanMinor_nonneg_nodal_refinement_neg` — REFINEMENT MONOTONICITY IS FALSE:
  explicit config (atom 1/2 ×6, pair (3±4i)/10) with plain datum `+1/125` and node-1/2 datum
  `−4/625`. The countable family has no refinement-monotone order; exhaustion is by
  enumeration. [FALSIFIED: refinement-domination conjecture; positive salvage = the pair
  identity + the explicit unmasking mechanism.]

**Lean traps (new).** `linear_combination e * Complex.I_sq` with polynomial coefficient
`e = α·I² + β` eliminates I-powers in explicit complex-number identities (compute α, β as the
x⁴/x²-coefficients of LHS−RHS as a polynomial in x = I); `push_cast` first. `norm_cast` closes
`(cast-built expression).re = real expression` goals after rewriting atoms to `ofReal` form.
Unused simp args (`Matrix.head_cons`) are now WARNINGS that fail the gate — trim simp lists.

**(B) window optimality — precise scope for next batch.** Target: a two-pair level family
parametrized by angle gap θ where the first negative even minor index grows like
`1/‖V²−1‖` — the Cesàro partial sums of `V^{2n+1}` remain above `−C` until `n ≈ 1/‖V²−1‖`,
so the master estimate's `CP2/g` term is attained up to constants. Would certify the `S²/g`
shape of the step-39 window as optimal. Numeric pre-certification first (runpod if needed).

## Step 43 — (B) window optimality: the delay dichotomy [PAPER-PROVED → Lean]

**Discovery 1 (no-delay for bare pairs — AM–GM obstruction).** For a level consisting of
conjugate pairs only, EVERY Turán minor index is negative: with two pairs at angles θ₁, θ₂ and
weights a, b the bracket is `a²sin²θ₁ + b²sin²θ₂ + 2ab sin²(η/2)cos(σ(n+2)+φ) +
2ab sin²(σ/2)cos(η(n+2)−φ)` and the resonant diagonal dominates every cross coefficient by
AM–GM (`a²sin²θ₁ + b²sin²θ₂ ≥ 2ab sin²((θ₁+θ₂)/2)` up to the η-corrections) — the bracket is
strictly positive at every index. Detection is immediate; oscillation between pairs can never
mask. In particular for a SINGLE pair, `M(n)M(n+2) − M(n+1)² = −4|W|²|w|^{2n+2}Im(w)² < 0` at
every n (substitute `W ↦ wⁿW` in the pair identity).

**Discovery 2 (delay ~ 1/g via a level REAL atom).** A real atom at the level carries no
resonant self-penalty, so its cross term with a phased pair can dominate: config = real atom
`ℓ = 1` (weight c) + pair `e^{±iθ}` (weights `be^{±iφ}`): bracket
`= b²sin²θ + 2cb sin²(θ/2)cos(θ(n+2)+φ)`; choosing `φ` to enter the favorable arc at `n = 0`,
minors stay ≥ 0 for all `n < N` with `N ≈ arccos-arc/θ ~ c₀/g` (`g = |e^{2iθ}−1| = 2 sinθ`).
NUMERICALLY CERTIFIED: `N·g ≈ 5.7` constant for `θ = π/8 … π/256` (three orders of magnitude)
— the `1/g` factor of the step-39 window is attained; the window shape is optimal in `g` at
fixed masses.

**Exact rational instance (for Lean).** Atoms `1` (weight 14), `(12±5i)/13` (weights `1±2i`) —
all at level 1, conj-symmetric, off-line pair present. Closed form: the pair expansion
collapses to `2·minor_n = (2c/169)·2Re(ζ·w^{n+1}) − 1000/169`, `ζ = (1+2i)(1−w)²·169 = −4−58i`;
the integer chain `z_k = ζ(12+5i)^k` satisfies `7·Re(z_{n+1}) ≥ 125·13^{n+1}` exactly for
`n = 0..6` and fails at `n = 7`: minors `0..6` are positive rationals
(`minor₀ = 3588/28561`, …), minor at `n = 7` is negative. DETECTION DELAY = 7 with an off-line
copy — a constant-size window is impossible; combined with Discovery 1, delay requires level
real atoms (the dichotomy).

**Step 43 status: [LEAN-PROVED].** Module `HTGeometry/TuranMinorDetectionDelay.lean`, both
theorems auditing to [propext, Classical.choice, Quot.sound], olean-built, wired
(HTGeometry.lean EOF append):
- `pair_minor_re_neg_at_index` — bare-pair zero delay: every index detects, via `W ↦ wⁿW` in
  the pair identity (`rw [map_mul, map_pow]; ring` shape bridge, then the fixed-index lemma).
- `exists_offline_config_minors_nonneg_below_seven` — the delay-7 instance: level = unit
  circle, real atom weight 14, pair `(12±5i)/13` weights `1±2i`; minors `n = 0..6`
  nonnegative (exact rationals, e.g. `minor₀ = 3588/28561`), off-line copy present with
  nonzero weight. Proof: Gaussian-rational moment chain `hy_k : Wp·vv^k = x_k + y_k·I`
  (recursion `pow_succ` + `linear_combination (5·y_k/13)·I_sq`), conj side by `map_pow/map_mul`,
  a uniform `hMof` assembler for the real moment values, then 7 `norm_num` minor checks
  (denominators up to 13⁹).

Together: the step-39 window's dependence on level data is NOT removable (no constant window),
its `1/g` factor is attained (numerically certified `N·g ≈ 5.7` across `θ = π/8..π/256`), and
the delay mechanism is classified — real atoms at the level are necessary and sufficient for
masking (AM–GM kills bare-pair oscillation). The asymptotic `1/g` family as an exact Lean
theorem (trig-arc formalization) remains open; recorded as a stretch item, not the frontier.

**Next frontier.** With the arc 36–43 closed (criterion sharpened to countable rational-nodal
form, effective windows, supply pricing, order no-go, delay dichotomy), the deepest open item
returns to arithmetic supply: prove the mass inequality of the supply theorem for the ACTUAL
ξ spectrum at a concrete shift `X` and scale `δ` from corpus-ownable inputs (zero-counting/
mass bounds for `Σ 1/|α_q² + X|`), turning the first rational-nodal data unconditional.

## Step 44 — unconditionalizing the supply's quantitative side [PAPER-PROVED → Lean]

Goal: make the supply's mass data unconditional for the ACTUAL ξ spectrum. Honest scoping
first: the two-scale tail ε(δ) encodes zero-density (its certification at the depth the actual
spectrum needs ≈ height 3·10¹⁰ at X = 1 is numerical-verification knowledge, not formalizable);
and hline IS partial RH. What IS unconditionalizable: the TOTAL mass S and the trace bridge.

**Theorem 1 (sector bound, tight at the certified floor).** For every shift `X ≥ 0` and copy:
`‖u_q(X)‖ ≤ (129/127)·Re(u_q(X))`. Proof: with `g = γ² > 32` (corpus certified floor
`xiSpectral_re_sq_gt_thirtytwo`), `s = b² < 1/4` (strip), `z = α² + X`:
`Im(z)² = 4gs ≤ g` and `512(g−1/4)² − 16129g = (g−32)(512g−1) ≥ 0`, so
`|z|² ≤ (129/127)²Re(z)²` — equality exactly at `g = 32`. Then `‖z⁻¹‖ ≤ (129/127)Re(z⁻¹)`.

**Theorem 2 (norm mass ≤ trace).** `Σ'‖u_q(X)‖ ≤ (129/127)·Re(M₀(X))`; at `X = x²` the
right side is `(129/127)·Re(logDeriv ξ(1/2+x)/x)` — prime–Gamma data
(`xiResolventMoment_zero_eq_logDeriv`).

**Theorem 3 (the unconditional numeric mass cap).** `‖u_q(X)‖ ≤ (132/127)·massAt(1/2)_q`
pointwise — `‖u‖ ≤ 1/(g−1/4)`, `massAt(1/2) ≥ 1/(g+1)` (both denominators from the strip),
and `127(g+1) ≤ 132(g−1/4) ⟺ g ≥ 32`, again equality at the floor (127·33 = 132·127/4 = 4191).
With the corpus budget `Σ massAt(1/2) ≤ 3/50`:  **`Σ'‖u_q(X)‖ ≤ 198/3175` for every `X ≥ 0`**
— a numeric unconditional cap on the total resolvent mass of ξ.

**Theorem 4 (supply with the mass budget discharged).** The universal supply theorem holds with
hypotheses: hline + sub-δ tail bound `ε ≤ E` + `8B⁴·E·(198/3175) ≤ 2(r₁r₂)^{2m+1}(...)(r₁−r₂)²`
— the total-mass input is GONE (replaced by the unconditional 198/3175). The remaining
arithmetic core of the first rational-nodal data is exactly: line placement above one scale +
one tail-mass (zero-density) bound. Also: every effective window of steps 39-40 can now be
instantiated with the numeric `S = 198/3175`.

**Step 44 status: [LEAN-PROVED].** Module `RHTower/XiResolventMassBudget.lean`, nine theorems,
all auditing to [propext, Classical.choice, Quot.sound], olean-built, wired:
- `xiSpectralPoint_im_sq_lt_quarter` — the open strip in spectral coordinates.
- `norm_xiResolventPoint_le_re_mul` — the sector bound `‖u‖ ≤ (129/127)·Re u`, tight at the
  certified floor `γ² > 32` (key algebra: `512(g−1/4)² − 16129g = (g−32)(512g−1)`).
- `tsum_norm_xiResolventPoint_le_re_moment` — norm mass ≤ (129/127)·Re(M₀(X)).
- `tsum_norm_xiResolventPoint_le_logDeriv` — the same on prime–Gamma data at `X = x²`:
  norm mass ≤ (129/127)·Re(logDeriv ξ(1/2+x)/x).
- `norm_xiResolventPoint_le_budgetMass` — `‖u‖ ≤ (132/127)·massAt(1/2)`, tight at the floor
  (`127·33 = 132·127/4 = 4191` at `γ² = 32`).
- **`tsum_norm_xiResolventPoint_le_budget`** — THE NUMERIC CAP: `Σ'‖u_q(X)‖ ≤ 198/3175`
  (≈ 0.0624) for EVERY shift `X ≥ 0`, unconditional (via the corpus budget
  `Σ massAt(1/2) ≤ 3/50`; consistency: true mass ≈ 0.046).
- `polyTuranMinor_supply_of_partial_line_budget` + `rational_nodal_datum_of_partial_line_budget`
  — the supply with the total-mass input DISCHARGED: hypotheses are now line placement, one
  sub-δ tail bound `ε ≤ E`, and `8B⁴·E·(198/3175) ≤ witness expression`. The arithmetic core
  of the first rational-nodal data = partial line placement + one zero-density bound. Honest
  scoping recorded: the tail bound at the depth the actual spectrum needs (height ≈ 3·10¹⁰ at
  X = 1) is numerical-verification territory; total mass is now a Lean number.
- `exists_neg_even_plain_minor_of_offline_top_budget` — the top-level detection window fully
  numeric: `(2·(198/3175)²/g + (198/3175)²/(ℓ²−ρ₂²))/Im(u)²`.

**Lean traps (new).** `div_add_div_same` no longer exists — use `← add_div`.
`ring` cannot verify `(c/d)·(1/B) = c/(d·B)` (inverse-of-product); use
`rw [mul_one_div, div_div]`. `Complex.hasSum_re h.hasSum |>.summable` for re-summability;
`Complex.re_tsum` needs the complex summability.

**Next frontier.** (i) The tail side: formalizable zero-density surrogates — the budget-probe
machinery at OTHER probe points `c` gives a FAMILY of mass identities; a probe at large `c`
weights high zeros more and could yield certified tail decay `ε(δ) ≤ E(δ)` without N(T);
(ii) numeric evaluation of `Re(logDeriv ξ(1/2+x)/x)` at a rational `x` from the prime–Gamma
expansion with certified error (corpus `xiSquaredEulerFullResponse` monotonicity) — would make
the trace-form mass bound concrete and sharpen 198/3175 toward the true ≈ 0.046.
