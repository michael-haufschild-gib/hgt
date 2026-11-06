# Arithmetic Inner-Function Theory (AIF)

Namespace `GaloisForLFunctions.ArithmeticInnerFunctionTheory`; umbrella
`ArithmeticInnerFunctionTheory.lean`; 23 modules. Every theorem is unconditional. A statement about RH is an
equivalence with RH, and no theorem has RH as a premise.

## 1. Motivation

On `Re s > ½` the function `E(s) = (s − 1)ζ(s)/s` factors as an inner function times an outer function, and
its inner factor is the Blaschke product of the right zeros. RH says this inner factor is trivial. Every route
in the corpus reads this one object: Balazard–Saias–Yor reads its mass at `1`, the camera reads it at a zero,
the Krein–Langer index reads its degree, Schur parameters and the anchor reflection peel it, Carleson separation
is its regularity.

Every available tool stops for a proved reason: size, positivity preservation, sieve data, barriers, short
mollifiers, finite computation, tensor amplification, integrality, parabolic monotonicity, unitarity, torus-uniform
Euler positivity. Each route has a one-sided sign proved, and the opposite sign is RH. What is missing is not a
sharper estimate of the first expression but a second expression.

AIF asks why a function with an Euler product and a functional equation has trivial inner factor on the half-plane
right of its symmetry line, while its critical passive system stays passive at zero slack. De Branges theory, Krein
systems, Hardy spaces and critical Hardy inequalities are not new. What AIF adds is arithmetic forcing: which inputs
can make an inner factor trivial, what positivity survives frustration, and what the incommensurability of `log p`
does and does not buy.

The field gives the second expression, exact certificates, classifications and walls. It produces no sign for `ζ`.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Half-plane datum, centre | `IsHalfPlaneDatum`, `IsCentre` | entire `E` of polynomial growth on `Re s ≥ ½`; a point where the Poisson–Jensen identity applies |
| Green kernel | `greenKernel` | `G(w, ρ) = log(|w + ρ̄ − 1|/|w − ρ|) = log 1/ϱ(w, ρ)` |
| Inner field of a datum | `innerOf` | `I_E(w) = ∫ log|E| P_w − log|E(w)|` |
| Inner field of `ζ` | `innerField`, `ZetaRightZero`, `zeroMult` | `I(w) = Σ_ρ m_ρ G(w, ρ)` over the right zeros |
| Budget | `budget`, `polyMollifier` | `∫ |ζ e^{Q∘φ_w}|² P_w`, the mollified Poisson second moment |
| Curve inner mass | `innerMass`, `lPoly` | `Σ log⁺|β_i|`, the Mahler measure of the normalized `L`-polynomial |
| Euler column | `column` | `1 − c p^{−s}`; reflection threshold `|c| = √p` |
| Crowd geometry | `InBox`, `shadow`, `crowd` | box of ratio `θ` at `w`; the shadow `[γ − b, γ + b]`; the shadow count |
| Passive layered medium | `IsAnchorFlow`, `IsAnchorTraces`, `kickFlow`, `logClock` | flow `κ′ = q − sinh 2κ`, `r = tanh κ`; cooling with kicks at `½ log n` |
| Echo train | `echoSymbol`, `columnSum`, `echoChain`, `echoSeq` | base `1`, echoes `c_i` at `ℓ_i`; the medium with prescribed reflection data |
| Outer predictor | `predPoly`, `predRev`, `paraPoly`, `stepDown` | `A = 1 + Σ a_k z^{k+1}`, `A^* = zⁿA(1/z)`, `A ∓ zA^*`, the inverse Levinson step |
| Prime insertion | `insertion`, `insertAll`, `cosSum` | `T_{θ,ℓ}f(x) = Σ_k U_k(cos θ) f(x + kℓ)` |
| Torus sum, characters | `torusSum`, `chiProd`, `ampl`, `heckeOne`, `satoTate` | sum of `n` insertions at free phases; the Hecke form of level one |
| Exponentially convex cone | `IsExpConvexFrom` | Hermitian Hankel forms `Σ c_i c̄_j f(x₀ + t_i + t_j) ≥ 0` |
| Locked phases | `IsKroneckerFamily`, `isKroneckerFamily_log_primes` | `θ_i = bℓ_i`, dense in the torus for `ℓ_i = log p_i` |
| Slack | `withSlack` | `κ_s(d) = κ(d) + sδ_{d,0}`: an absolutely continuous density `s` |

Lattice data `κ = weilSeq φ h`, margins, predictors and reflection coefficients are those of `GrowingWindowsOfSpecZ`;
the datum plane `datumCone β s c` is that of `CriticalHardyTheoryOfTheWindowCone`.

## 3. Language

**Budget instead of exact sign.** A statement is a bound on `I(w)`, and `e^{2I}` is an infimum of second moments, so every
mollifier is an upper bound and a family of them is a proof.

**Hyperbolic geometry of zeros.** `Re s > ½` is hyperbolic: a zero has depth `b`, a shadow `[γ − b, γ + b]`, and a box. The Green
kernel is hyperbolic distance. The inner field is the potential of the configuration, and it is what every local statement sums to.

**The width axis.** The depth `x = Re w − ½` of a centre is the scale at which the field is read: at `x ≍ 1/log T` it sees isolated zeros,
at `x → ∞` it reads the mean mass per unit height. A theorem has to say at which width it holds.

**Duality of prime weights and blind states.** The window form reads a weight only through the autocorrelation of the test at `log n`
(`weilSeqW_single_kick`; CHT `coneForm_ofReal`). A test whose autocorrelation vanishes at `log n` is blind to that weight, and a test that
sees exactly one weight reads it exactly (`weilSeqW_one_sub`).

**The Laguerre form as common observable.** The first reflector is the Born term `κ₁/κ₀` and the second is
`(κ₀κ₂ − κ₁²)/(κ₀² − κ₁²)` (`reflCoeff_one_eq`). The same form is the wall of log-concavity (`sum_sq_le_of_logConcave`), the sign of the Turán test of the
aperture, and the obstruction to an alternating predictor.

**Multiplicative vectors.** A torus sum is the Hankel form `Σ_{a,b} f(x + log ab) χ(a) χ̄(b)` evaluated on one completely multiplicative unimodular vector `χ`
(`ofReal_insertion_eq_tsum_pairs`, `torusSum_cons`). So torus positivity is positivity of a Hankel form on multiplicative vectors only, and the Bernstein theorem says when that is enough.

## 4. Mechanisms

1. **A second expression with opposite sign.** The first expression of the inner mass is the zero sum, manifestly `≥ 0`. The second is
   Szegő's: `e^{2I(w)} (|E(w)|/|w|)² = inf_Q ∫ |ζ e^{Q∘φ_w}|² P_w` (`isGLB_budget_innerField`). Its members are manifest upper bounds, and it is an
   equality, so no information is lost by mollifying. The proof uses no boundary limits of outer functions, only exponentials of polynomials in the Blaschke coordinate
   (`isGLB_circle`).
2. **Causality replaces positivity.** A frustrated form has no positive ground state in any gauge. Its causal solution, the predictor, exists anyway. Positivity of the
   solution is replaced by zero-freeness in the closed disc, and the mechanism is Schur's: `A^*/A` is holomorphic and unimodular on the circle, so contractive
   (`norm_predRev_le`).
3. **Phase locking is torus positivity.** For a fixed summable amplitude, Kronecker makes locked and free phases equivalent (`torusSum_nonneg_iff_locked`). Locking
   adds nothing at a fixed amplitude. What it can give has to come from the correlation of the amplitude with the height.
4. **Columns add.** On independent reflectors the infimum over the height of a sum of columns is the sum of their minima (`le_columnSum_iff_min`). Cancellation lives inside one column, among the powers of one prime.
5. **Passivity from arithmetic initial data.** The form starts positive on short tests (GWZ `weilQuad_pos_of_short`), each new echo has a Schur band (`passive_iff_each_echo_in_band`), and each prime
   enters as one Schur parameter (GWZ `schurParam_single_kick`). The medium forgets its past at rate `2` (`abs_le_of_isAnchorFlow`), so contact is local.
6. **Recurrence replaces decoupling.** Far translates of a bubble never separate in energy (`not_tendsto_weilOrbitCorr`). The orbit returns.

## 5. Pillar theorems

### The inner field

| Theorem | Statement |
|---|---|
| `hasSum_poissonJensen` | For every datum and centre, `Σ_ρ m_ρ G(w, ρ) = ∫ log|E| P_w − log|E(w)|`: no singular inner factor |
| `riemannHypothesis_iff_innerField_eq_zero` | RH iff `I(w₀) = 0` at one point where `E(w₀) ≠ 0` |
| `isGLB_circle`, `isGLB_budget_innerField` | Helson–Lowdenslager–Szegő without boundary limits; the second expression |
| `riemannHypothesis_iff_exists_budget_lt` | RH iff for every `ε > 0` some mollifier has budget below `1 + ε` at `1` |
| `hasSum_and_normalDerivative_eq` | `N(ρ) = exp(−Σ_{a≠ρ} m_a G(ρ, a))`: the camera bound is an equality over all other zeros |
| `curve_inner_tfae`, `innerMass_goldenDatum` | Curves: inner mass `0` ⇔ unitary ⇔ Castelnuovo ⇔ reflectors in `(−1, 1)`; golden mass `log φ` |
| `innerOf_column`, `tendsto_innerOf_column` | Columns: closed form; inner mass at infinity is `log⁺(|c|/√p)`, the Mahler measure |
| `mult_sum_box_le_log_budget`, `card_mul_exp_le` | Box budget for every mollifier; crowds of size `k` are rare at rate `e^{−4θk/5}` |
| `zero_free_or_infinite_of_recurrent`, `dirichletPoly_zero_free_or_infinite` | Recurrence: zeros in a strip are absent or infinite |
| `riemannHypothesis_iff_tendsto_innerField_and_recurrent` | RH ⇔ field vanishing at infinity on each vertical line ∧ weak recurrence |

### Forms, cones and media

| Theorem | Statement |
|---|---|
| `toeplitzPosDef_iff_exists_outer_predictor` | For every sign pattern, a window is positive definite iff it has a predictor with positive margin and no zero in the closed disc |
| `paraPoly_zero_on_circle` | A Riemann hypothesis in every positive window: `A ∓ zA^*` have all zeros on the circle |
| `riemannHypothesis_iff_exists_outer_predictor` | RH is the existence of outer predictors for all windows of all lattices |
| `lattice_trichotomy`, `riemannHypothesis_iff_every_lattice_is_at_threshold` | `s > 0` Szegő, `s < 0` empty, `s = 0` threshold; every lattice at threshold iff RH |
| `torusPositive_iff_hankel_nonneg` | **Arithmetic Bernstein.** For left exponent `κ < ½`, torus positivity at all prime sets and base points is exponential convexity |
| `torusSum_nonneg_iff_locked` | Locking is torus positivity at a fixed summable amplitude |
| `hecke_level_one`, `sum_sq_le_of_logConcave`, `torusSum_ge_of_geometric` | Hecke–Bessel; the log-concavity wall; the size floor |
| `echoSymbol_nonneg_iff`, `exists_passive_commensurable_train` | Independent reflectors: passive iff `2Σ|c_i| ≤ 1`. Commensurable: passive with mass `N` for every `N` |
| `passive_iff_each_echo_in_band`, `exists_evenSeq_of_reflCoeff` | Schur bands; reflection data are free coordinates |
| `weight_eq_of_reflCoeff_eq`, `vonMangoldt_eq_of_reflCoeff` | The first reflector reads the prime weight, exactly |
| `abs_le_of_isAnchorFlow`, `abs_kickFlow_logClock` | A priori bounds free of `1/μ`: `|κ_n| ≤ ¼ log n + ½ log(2 log n) + 5A` for kicks `≤ A log n/√n` |
| `not_tendsto_weilOrbitCorr`, `not_tendsto_dipole` | Unconditional: no nonzero bubble decouples from its far translate |
| `tendsto_weilQuad_of_dominated` | Unconditional: on dominated sequences the form loses no energy at spectral infinity |
| `riemannHypothesis_iff_orbit_recurs` | RH ⇔ strict orbit Cauchy–Schwarz plus dipoles of fixed mass with arbitrarily small energy at arbitrarily large separation |

## 6. Questions and answers

Each question has a theorem in `TheQuestionsOfTheField.lean`.

| # | Question | Answer |
|---|---|---|
| Q1 | When is a frustrated form nonnegative at zero slack? | Iff at every positive slack each window has an outer predictor with positive margin (`question_one`). For `Spec ℤ`: RH iff all windows have outer predictors, the reflection data are not square-summable, and negative slack is empty (`question_one_specZ`) |
| Q2 | What replaces Allegretto–Piepenbrink? | The causal solution: outer instead of positive. It carries a Riemann hypothesis in every window, and on nonpositive couplings it is the positive supersolution (`question_two`, `toeplitzForm_eq_doob`, `toeplitzForm_nonneg_of_supersolution`). In the aperture variable the passive state itself gives a Darboux pair of positive Schrödinger solutions (`IsAnchorTraces.darboux`) |
| Q3 | Which cones are invariant under prime insertion with locked phases? | The exponentially convex cone is invariant (`IsExpConvexFrom.torusSum`). Among amplitudes of left exponent below `½` it is the only one with nonnegative insertions at all prime sets, base points and locked phases (`question_three`). On a fixed prime set the cone is strictly larger (`gaussian_torus_positive`, `not_isExpConvexFrom_gaussian`) |
| Q4 | When is an echo train passive? | When each echo lies in its Schur band; the bands are free coordinates. On independent reflectors only size counts; on commensurable ones the mass is unbounded (`question_four`) |
| Q5 | Why is `(β, s) = (1, 0)` critical? | `s` is an absolutely continuous density over a measure with none. `s > 0` is Szegő, `s < 0` is empty, `s = 0` is the threshold. At `β = 0` the weights are not pinned (`question_five`) |
| Q6 | Can an arithmetic inner factor be finite and nontrivial? | Without arithmetic, yes (`innerOf_linear`). For Dirichlet polynomials and periodic data, never. For positive generalized primes with small reciprocal mass, yes (`exists_small_reciprocalMass_zero_off_line`). For `ζ` it is open, and RH splits as field vanishing plus recurrence (`question_six`) |

## 7. Tools

| Tool | Status | Lean |
|---|---|---|
| T1. Exact certificates for frustrated forms | Developed: exact for every sign pattern on lattices | `toeplitzPosDef_iff_exists_outer_predictor`, `exists_sum_sq_certificate`, `stepDown`, `abs_last_lt_one` |
| T2. A priori estimates for Krein systems with soft kicks, free of `1/μ` | Developed, for continuous potentials and for atomic kicks of arithmetic size | `abs_le_of_isAnchorFlow`, `integral_sq_eq`, `abs_kickFlow_le`, `abs_kickFlow_logClock`, `one_sub_tanh_sq_kickFlow_ge` |
| T3. Concentration-compactness for arithmetic forms | The principle is settled: decoupling fails on every bubble, no energy is lost at spectral infinity, and recurrence replaces decoupling. A profile decomposition is open | `eq_zero_of_tendsto_cos_sum`, `not_tendsto_weilOrbitCorr`, `tendsto_weilQuad_of_dominated`, `riemannHypothesis_iff_orbit_recurs` |
| T4. Carleson embedding at the critical scale with arithmetic coefficients | Developed as an exact budget, valid at every centre and for every mollifier | `greenKernel_ge`, `mult_sum_box_le_log_budget`, `exp_mul_sum_box_le`, `card_mul_exp_le`, `volume_shadows_le`, `isGLB_budget_innerField` |
| T5. Inverse scattering with prime data | Developed: free coordinates, uniqueness, exact reading of a weight | `exists_evenSeq_of_reflCoeff`, `evenSeq_eq_of_reflCoeff_eq`, `reflCoeff_zero_sub`, `weight_eq_of_reflCoeff_eq`; GWZ `levinson_weilSeqW_congr`, `schurParam_single_kick` |

## 8. Test cases

**The function-field chain.** The sign is known and `r, q` compute (`TheCurveChainOfTheInnerFactor`, GWZ `TheCanonicalFlowOfACurve`). The inner mass is the Mahler measure, and Castelnuovo, Carathéodory and trivial inner factor coincide.

**The `{2, 3}` rung.** Steep amplitudes are torus positive on `{2, 3}` (`torusSum_two_three_nonneg`), and the Gaussian lies in this cone without being exponentially convex. Only all primes, with the base
point moved to the left, force the Laplace cone.

**One critical ratio.** Handled by AHD: `exists_larger_window_with_all_critical_pencils_positive`, `windowPencil_pos_of_le_successor`. A fixed ratio is a finite rung and decides nothing about RH.

## 9. Selectivity

The statement "trivial inner factor" is false on each corpus fake, so a proof must use what the fake lacks.

| Fake | What it has | Why it fails | Reference |
|---|---|---|---|
| Euler column, `|c| > √p` | Euler factor, periodic zeros | Inner mass `log(|c|/√p)`; no functional equation | `exists_column_zero`, `tendsto_innerOf_column` |
| Golden curve | Integral zeta, Beurling system with nonnegative counts, functional equation | Inner mass `log φ`: not pure | `innerMass_goldenDatum`, AOG `golden_orbitCorr_rate_iff` |
| FE twins | Functional equation, finite coefficient prefix | Right zeros placed at will | `SelbergClass.exists_cubic_twin_with_many_right_hand_zeros` |
| Beurling one-off | Euler product with positive primes of small reciprocal mass | One off-line pair: a finite nontrivial inner factor | `exists_small_reciprocalMass_zero_off_line` |
| Shifted products | Shifted configuration | Not pure | AOG `curveShiftedPair_not_pure`, `shiftedPairConfig` |
| Heated kernels | Parabolic monotonicity | Blind to `t = 0` | SRT, `RHTower/Heat` |
| Polynomial `s − ρ` | Nothing arithmetic | Inner field `G(·, ρ)`, finite and nontrivial | `innerOf_linear` |

Periodic data admit finite impurity per period. The theory sees this: for a column, the mass at infinity is positive with infinitely many right zeros, and independent reflectors leave only size (`echoSymbol_nonneg_iff`).

## 10. Traps

| Trap | Truth |
|---|---|
| A mollifier loses information about the zeros | The infimum over mollifiers is exactly `e^{2I}` |
| `N(ρ) ≤ Πϱ` is lossy | It is an equality over all other zeros |
| Phase locking is a free extra source of positivity | At a fixed summable amplitude it is torus positivity. It can act only through amplitude–height correlation |
| A positive supersolution exists at zero slack, in some gauge | Frustration survives every gauge (`exists_wrong_edge`, FADF). The certificate must be causal |
| An outer predictor is RH | It certifies one window; the content is all windows of all lattices |
| Zero slack means vanishing innovation | Not in general: a density may vanish at a point with `E_∞ > 0`. For `Spec ℤ` under RH, `E_n → 0`: the spectral measure is singular |
| The Laplace cone is forced on small prime sets | Only by all primes together with base points to the left. The Gaussian is in the `{2, 3}` cone |
| The Bernstein theorem kills the theta amplitude | It needs base points to the left and left exponent below `½`, where the diagonal `Σ_p p^{−2s}` converges. `S` reads the amplitude only from `x = 0`, where it decays doubly exponentially, and its formula continued to `x < 0` has left exponent `½ + a` |
| Reflectors sit on `½ log n` | Only to first order. The second reflector is the Laguerre form and is present at an echo-free site |
| Far bubbles decouple, as in the Euclidean case | Never, for any nonzero test: the orbit correlation does not tend to `0` |
| Size bounds are lossy on Euler trains | On independent reflectors size is exact. Cancellation lives inside one column |
| Finite inner degree is a small perturbation | It forces the field to vanish at infinity, and a recurrent datum cannot have it |

## 11. Open research topics

1. **The opposite sign.** A family of mollifiers with budget tending to `1` at one centre (`riemannHypothesis_iff_exists_budget_lt`). This is RH, and it is the form in which a construction would have to arrive.
2. **Amplitude–height correlation.** `S(a, b) = Σ_N τ_b(N) A(N; a, b)` has an amplitude depending on the same `b` as the phases, so `torusSum_nonneg_iff_locked` does not apply. This is the only place left for phase locking as a source of positivity.
3. **The Bernstein theorem at a fixed base point.** Is the exponent `½` sharp? What does torus positivity at all prime sets force when the base point is fixed at `x = 0`, the form in which `S` reads its amplitude? There the Hecke form sees only primes up to `e^{y/2}`, and the diagonal does not vanish.
4. **The zero–one law for `ζ`.** A lower bound on returns around an off-line zero (`ZetaZeroDiscWeaklyRecurrent`). Corpus: return shifts have density zero, no lower bound.
5. **Inner mass at infinity of `ζ`.** For a column `I(σ + it)` tends to the Mahler measure as `σ → ∞`. For `ζ` the same limit measures the depth `Σ_ρ b_ρ` per unit height. Its vanishing is implied by RH and would be weaker. Not yet formalized.
6. **Profile decomposition on the Bohr compactification.** Given that bubbles do not decouple, what replaces Lions' lemma for sequences at translation infinity?
7. **Mid-range clusters.** Crowds of size `k` obey `e^{−4θk/5}`. The range `εα ≲ k ≲ α/θ` stays at rate `2θ`, and a joint event law is needed.
8. **Roots of predictors of `Spec ℤ`.** Under RH the zeros of `A ∓ zA^*` should approximate the atoms `e^{iγ_ρ h}`. Quantify the distance of the roots of `A` from the circle by the margins.
9. **The literal flow.** Bounds for the literal Weil chain in the form of `abs_kickFlow_logClock`, and sharpness of `¼ log n + ½ log log n` under coherent kicks. Contact itself is RH-strength.
10. **The height cost of locking.** Over `𝔽_q` the pole recurs with the echoes. Over `ℤ` it does not, and alignment at large height is paid by the archimedean base. Compare the height of simultaneous alignment (ADO, Baker) with `log |b|`.

## 12. Place in the research

AIF is on the receiver side of the sign block. The production side, square-root precision, is not obviously part of the field, and the corpus proves no bridge beyond shared RH endpoints.

| Programme | Interface |
|---|---|
| MZF | Derivative law and camera: `MultiscaleMollifiedZetaField.normalDerivative` becomes an equality; second moments enter through `integrable_and_log_norm_le_poisson` |
| BSY/CTF | `I(1)` is the Balazard–Saias–Yor mass; `isGLB_budget_one` is its variational form |
| GWZ | Lattice Schur–Levinson system: predictors, margins, causality, kicks. AIF adds outer predictors, free coordinates, the weight dictionary and the Szegő threshold |
| CSTW | The literal Weil chain (`TheWeilChainIsOneScalarFlow`, `TheWeilTracesHaveTheirSoftKick`); `TheAnchorFlow` is its abstract layered-medium form |
| CHT | Datum plane and window cone (`datum_classification`); AIF reads the datum as an absolutely continuous density |
| CompletedArithmeticForms | `eulerPartial`, `S = Π T_p A`, `thetaApertureAmplitude_not_laplaceMixture`; AIF gives the cone, the walls and the classification |
| FADF, ACT | Frustration past `log ρ` in every sign gauge, Doob gauges, Hardy weights; AIF gives the causal certificate that survives frustration |
| AKL | The Krein–Langer index reads the inner degree; the zero–one law says when finite degree is possible |
| ACS, AOG | Curve data and orientation; T3 rests on `blindAbove_of_orbitCorr_le` |
| ZCG | Blindness density (`eq_zero_of_blind_of_unbounded_density`) and the camera; ZCG is sign-free, and AIF's budgets are the same zeros read through second moments |
| AHD | Critical ratios of windows, the third test case |
| ADO | Baker repulsion for Euler carriers, the height of locking |
| HT | Kronecker density, simultaneous Dirichlet approximation |

## 13. Success criteria

The field succeeds when its main statement is proved for `ζ`: a second expression with the opposite sign that forces trivial inner factor. A proof must be:

* false on every fake of §9;
* parity-breaking, locally pure, and at unbounded aperture;
* able to recover Weil's proof over `𝔽_q`, including Castelnuovo: the curve chain is the model;
* sensitive to the incommensurability of `log p`, since periodic data admit finite impurity;
* consistent with the walls: no route through a fixed-amplitude locked positivity, a positive supersolution, decoupling of far bubbles, or a bounded prime set.

Below that level, the field succeeds by exact statements: each named tool developed, each question answered by a theorem, and each mechanism either certified or killed with its survivor.

## 14. What a contribution must be

A contribution is an exact identity, an equivalence, a classification, a sharp law, or a no-go with its strongest positive survivor. It is unconditional, it says which data it reads, it says at which width it holds, and it is tested on the fakes. A bound that holds equally on a fake is a statement about the fake's class, and it has to say so. An equivalence with RH counts when it moves the question to a form with a new tool; it does not count as progress on the sign.

## 15. Big picture

There is one object, the inner field. It has two expressions: a sum over zeros, nonnegative, and an infimum over mollifiers, an upper bound. RH is their meeting at `0`.

On the side of forms, the exact certificate for frustrated positivity exists: a causal solution that is outer. Each positive window carries its own Riemann hypothesis, for the same reason as Hermite–Biehler. Positivity of all windows of all lattices is RH, and it sits exactly at the threshold of Szegő's regime, with no absolutely continuous density to spare.

On the side of arithmetic, locking gives nothing at a fixed amplitude, the cone of all primes is the Laplace cone, independent reflectors leave only size, and far bubbles never decouple. So what remains is narrow: the correlation of amplitude with height, recurrence around a zero, and the construction of mollifiers. The reflection data read every prime exactly, so nothing about the primes is hidden from the system. What is missing is the reason for its sign.
