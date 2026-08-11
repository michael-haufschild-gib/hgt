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
