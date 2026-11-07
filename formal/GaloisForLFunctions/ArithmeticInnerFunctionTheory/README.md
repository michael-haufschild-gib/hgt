# Arithmetic Inner-Function Theory (AIF)

Namespace `GaloisForLFunctions.ArithmeticInnerFunctionTheory`; umbrella
`ArithmeticInnerFunctionTheory.lean`; 37 modules. Every theorem is unconditional. A statement about RH is an
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

The field gives the second expression, exact certificates, classifications, tangents and walls. It produces no sign for `ζ`.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Half-plane datum, centre | `IsHalfPlaneDatum`, `IsCentre` | entire `E` of polynomial growth on `Re s ≥ ½`; a point where the Poisson–Jensen identity applies |
| Green kernel | `greenKernel` | `G(w, ρ) = log(|w + ρ̄ − 1|/|w − ρ|) = log 1/ϱ(w, ρ)` |
| Inner field of a datum | `innerOf` | `I_E(w) = ∫ log|E| P_w − log|E(w)|` |
| Inner field of `ζ` | `innerField`, `ZetaRightZero`, `zeroMult` | `I(w) = Σ_ρ m_ρ G(w, ρ)` over the right zeros |
| Budget | `budget`, `polyMollifier` | `∫ |ζ e^{Q∘φ_w}|² P_w`, the mollified Poisson second moment |
| Hardy functions of the disc | `IsHardyDisc`, `taylorCoeff`, `mollified` | functions with `|Φ| ≤ A/|1 − w|²` and bounded means, with Parseval and no boundary limit theory; `E M_Q` in the coordinate `u = (s − 1)/s` |
| Curve inner mass | `innerMass`, `lPoly` | `Σ log⁺|β_i|`, the Mahler measure of the normalized `L`-polynomial |
| Abel mollifier of a curve | `frobTrace`, `abelPoly`, `abelBudget`, `abelRatio` | `Q = Σ_{k≤N} ρ^k a_k v^k/k`, the Euler logarithm damped and truncated; the dilation quotient `|P(v)/P(ρv)|²` |
| Euler column | `column`, `colShape`, `colRadius`, `signedMin` | `1 − c p^{−s}`; `log p · Re(x/(1 − x))`, `|x| = p^{−½−a}`, with its extreme values `r/(1 − r)` and `−r/(1 + r)` |
| Gamma base and current | `columnMass`, `columnsAt`, `columnCurrent`, `alignedMass` | `½ log(b/2π)` against the columns of a prime set |
| Crowd geometry | `InBox`, `shadow`, `crowd` | box of ratio `θ` at `w`; the shadow `[γ − b, γ + b]`; the shadow count |
| Arithmetic Carleson measure | `depth`, `centre`, `InCarlesonBox`, `shiftedCrowd` | `μ = Σ m_ρ b_ρ δ_ρ`; the boxes at width `x`; the weight `ν_x` of the embedding |
| Local onset field | `onsetTest`, `onsetEnergy` | `Re W(f, f)` for `f(u) = ψ(u/a) e^{iXu}`: the form on aperture `a` localized at height `X` |
| Passive layered medium | `IsAnchorFlow`, `IsAnchorTraces`, `kickFlow`, `logClock` | flow `κ′ = q − sinh 2κ`, `r = tanh κ`; cooling with kicks at `½ log n` |
| Lattice potential | `latticeKick`, `vacuum`, `predMass` | `q_n = −artanh γ_n`; the free medium; the mass of the predictor |
| Echo train | `echoSymbol`, `columnSum`, `echoChain`, `echoSeq` | base `1`, echoes `c_i` at `ℓ_i`; the medium with prescribed reflection data |
| Outer predictor | `predPoly`, `predRev`, `paraPoly`, `stepDown` | `A = 1 + Σ a_k z^{k+1}`, `A^* = zⁿA(1/z)`, `A ∓ zA^*`, the inverse Levinson step |
| Forward map | `tiltSeq`, `primeEcho`, `collarVec`, `autocorr` | the line `κ + tη`; the echo of one prime power; the minimizers of the collar; the autocorrelation of the predictor test |
| Certified window | `certifiedAperture`, `pencilMatrix` | total length `2·successorWeilFloorAperture`; the window pencil at a critical ratio on a lattice |
| Energy space | `energy`, `spectralVector`, `bubbleTest` | `ℓ²` of the zeros, on which translation acts by `e^{iγt}`; the moving bubbles |
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

**Excess.** The excess of a mollifier is `B(Q) − 1`. It controls the distance of `E M_Q` to `1` at every point, so a statement about a mollifier is a statement about its excess.

**Hyperbolic geometry of zeros.** `Re s > ½` is hyperbolic: a zero has depth `b`, a shadow `[γ − b, γ + b]`, and a box. The Green
kernel is hyperbolic distance. The inner field is the potential of the configuration, and it is what every local statement sums to.

**The width axis.** The depth `x = Re w − ½` of a centre is the scale at which the field is read: at `x ≍ 1/log T` it sees isolated zeros,
at `x → ∞` it reads the mean depth per unit height. A theorem has to say at which width it holds.

**Duality of prime weights and blind states.** The window form reads a weight only through the autocorrelation of the test at `log n`
(`weilSeqW_single_kick`; CHT `coneForm_ofReal`). A test whose autocorrelation vanishes at `log n` is blind to that weight, and a test that
sees exactly one weight reads it exactly (`weilSeqW_one_sub`).

**The Laguerre form as common observable.** The first reflector is the Born term `κ₁/κ₀` and the second is
`(κ₀κ₂ − κ₁²)/(κ₀² − κ₁²)` (`reflCoeff_one_eq`). The same form is the wall of log-concavity (`sum_sq_le_of_logConcave`), the sign of the Turán test of the
aperture, and the obstruction to an alternating predictor.

**Multiplicative vectors.** A torus sum is the Hankel form `Σ_{a,b} f(x + log ab) χ(a) χ̄(b)` evaluated on one completely multiplicative unimodular vector `χ`
(`ofReal_insertion_eq_tsum_pairs`, `torusSum_cons`). So torus positivity is positivity of a Hankel form on multiplicative vectors only, and the Bernstein theorem says when that is enough.

**The calculus of signed echoes.** Across independent reflectors the three operations are exact. Sums: the infimum over the height of a signed sum of columns is the sum of the signed minima (`le_signedColumns_iff`). Products: a product of columns, each positive somewhere, is nonnegative at all heights iff each factor is (`prod_nonneg_iff`). Pairings: `∫ S_a S_b = Σ_k a_k b_k` (`integral_torusSum_mul_torusSum`). So a sign cannot be moved between independent columns.

**Born and past Born.** The Born regime is the range where each reflector reads only its own echo. It is measured by the accumulated reflection `Π_{k<n}(1 + |γ_k|) − 1`.

## 4. Mechanisms

1. **A second expression with opposite sign.** The first expression of the inner mass is the zero sum, manifestly `≥ 0`. The second is
   Szegő's: `e^{2I(w)} (|E(w)|/|w|)² = inf_Q ∫ |ζ e^{Q∘φ_w}|² P_w` (`isGLB_budget_innerField`). Its members are manifest upper bounds, and it is an
   equality, so no information is lost by mollifying. The proof uses no boundary limits of outer functions, only exponentials of polynomials in the Blaschke coordinate
   (`isGLB_circle`).
2. **Near-extremal mollifiers are rigid.** In the disc coordinate `E M_Q` is a Hardy function with value `1` at the origin, so Parseval bounds its distance to `1` by the excess (`norm_sub_one_sq_le`). There is one target, `1/E`.
3. **Castelnuovo supplies holomorphic convergence and domination.** Purity makes the damped Euler-log series converge to `1/P(ρv)` and bounds each quotient factor by two. Boundary quotient convergence alone is nonselective: every finite datum has quotient mean tending to one (`tendsto_circleAverage_abelRatio_unconditional`), while the golden Abel budgets stay uniformly separated from that mean (`eventually_golden_budget_sub_quotient_ge`).
4. **Causality replaces positivity.** A frustrated form has no positive ground state in any gauge. Its causal solution, the predictor, exists anyway. Positivity of the
   solution is replaced by zero-freeness in the closed disc, and the mechanism is Schur's: `A^*/A` is holomorphic and unimodular on the circle, so contractive
   (`norm_predRev_le`). Off Toeplitz forms the certificate survives as a triangular sum of squares (`exists_causal_certificate`).
5. **Passivity from arithmetic data.** The form is positive on windows of total length up to `2·successorWeilFloorAperture`, past `log 2` (`weilQuad_pos_of_certified`). On these windows the certificate is a theorem about `Spec ℤ`, with primes in it (`exists_outer_predictor_of_certified`, `abs_schurParam_lt_of_certified`).
6. **The envelope theorem computes the forward map.** Margins and Schur parameters are minima of quadratic forms, the sequence is affine in each prime weight, and so the tangent is the form of the perturbation on the minimizer (`hasDerivAt_levinsonErr`, `hasDerivAt_reflCoeff`). The same minimum shows that the margin is concave in the weights (`levinsonErr_le_add`).
7. **Phase locking is torus positivity.** For a fixed summable amplitude, Kronecker makes locked and free phases equivalent (`torusSum_nonneg_iff_locked`). An amplitude with a limit at height infinity gains nothing either (`torusSum_nonneg_of_locked_of_tendsto`). What locking can give has to come from an amplitude that keeps oscillating with the height (`exists_correlated_train`).
8. **Columns add.** On independent reflectors the infimum over the height of a sum of columns is the sum of their minima (`le_columnSum_iff_min`). Cancellation lives inside one column, among the powers of one prime.
9. **The base grows, and alignment has a height.** The Gamma base pays a prime set by size once `log(b/2π)` passes twice its mass (`columnCurrent_pos_of_mass_lt`), and Dirichlet aligns the set somewhere in every range `[B, BQ^{|S|}]` (`exists_height_aligned`).
10. **The medium forgets.** The flow restores at rate `2` (`abs_le_of_isAnchorFlow`), and in integrated form this needs no derivative of the potential (`abs_artanh_anchorReflection_le_osc`), so contact is local.
11. **Recurrence replaces decoupling.** Far translates of a bubble never separate in energy (`not_tendsto_weilOrbitCorr`). Translation is compact on the energy space, through the Bohr compactification, and the interference of bubbles is read by characters (`tendsto_energy_bubbles`).

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
| `sum_depth_box_le`, `carleson_embedding` | `μ(box at x) ≤ (5/2) x I(½ + x + it)`; a large sieve for zeros with the inner field as constant |
| `tendsto_innerField_iff_depthDensity`, `bounded_innerField_iff_depthDensity` | `I → 0` at infinite width iff the depth density is `o(T)`; `I` bounded iff it is `O(T)` |
| `tendsto_poisson_log_iff_depthDensity` | The Abel log-mean of `ζ` on the line tends to `0` iff the depth density is `o(T)` |
| `exists_innerField_le_loglog`, `exists_sum_depth_le` | Unconditionally, `I(½ + x + it) ≤ log(1 + log 5x) + C` and `Σ_{|γ−t|≤T} m_ρ b_ρ ≤ (5/2) T (log(1 + log 5T) + C)` |
| `zero_free_or_infinite_of_recurrent`, `dirichletPoly_zero_free_or_infinite` | Recurrence: zeros in a strip are absent or infinite |
| `riemannHypothesis_iff_tendsto_innerField_and_recurrent` | RH ⇔ field vanishing at infinity on each vertical line ∧ weak recurrence |

### Mollifiers

| Theorem | Statement |
|---|---|
| `norm_sub_one_sq_le` | `|E(s) M_Q(s) − 1|² ≤ (B(Q) − 1) |s − 1|²/(2 Re s − 1)` for every `Q` and every `Re s > ½` |
| `riemannHypothesis_iff_exists_near_extremal`, `tendsto_of_tendsto_budget` | RH is a family with `B → 1`, and along any such family `E M_Q → 1` pointwise |
| `norm_coeff_one_add_le`, `sum_taylorCoeff_le` | `|q₁ − (1 − γ)|² ≤ B(Q) − 1`, and all Taylor coefficients are bounded by the excess |
| `le_budget_of_zero` | A zero costs at least `|ρ|²/|ρ − 1|²` in every budget |
| `integral_abs_flatten_le` | Near-extremal mollifiers flatten: `∫ | |ζM|²/B − 1 | P₁ ≤ 2√(log B − 2I(1))` |
| `hodgeIndex_iff_abelMollifiers` | Castelnuovo on the Frobenius span holds iff the Abel mollifiers reach budget `1` |
| `sq_goldenRatio_le_abelBudget` | The golden curve has budget at least `φ²` for every Abel mollifier |

### Forms, cones and media

| Theorem | Statement |
|---|---|
| `toeplitzPosDef_iff_exists_outer_predictor` | For every sign pattern, a window is positive definite iff it has a predictor with positive margin and no zero in the closed disc |
| `paraPoly_zero_on_circle` | A Riemann hypothesis in every positive window: `A ∓ zA^*` have all zeros on the circle |
| `riemannHypothesis_iff_exists_outer_predictor` | RH is the existence of outer predictors for all windows of all lattices |
| `exists_outer_predictor_of_certified`, `paraPoly_zero_on_circle_of_certified`, `abs_schurParam_lt_of_certified` | Unconditional for `Spec ℤ` on certified windows, including the echoes that carry `Λ(2)` |
| `exists_certificate_at_critical_ratio` | At a ratio below the threshold of a window the pencil has a triangular certificate, with no Toeplitz structure |
| `lattice_trichotomy`, `riemannHypothesis_iff_every_lattice_is_at_threshold` | `s > 0` Szegő, `s < 0` empty, `s = 0` threshold; every lattice at threshold iff RH |
| `torusPositive_iff_hankel_nonneg` | **Arithmetic Bernstein.** For left exponent `κ < ½`, torus positivity at all prime sets and base points is exponential convexity |
| `torusSum_nonneg_iff_locked`, `torusSum_nonneg_of_locked_of_tendsto` | Locking is torus positivity at a fixed amplitude, and at an amplitude with a limit at height infinity |
| `exists_correlated_train` | An amplitude oscillating with the height has nonnegative locked sums and negative torus values |
| `hecke_level_one`, `sum_sq_le_of_logConcave`, `torusSum_ge_of_geometric` | Hecke–Bessel; the log-concavity wall; the size floor |
| `tsum_mul_nonneg_of_torusPositive` | The torus-positive cone lies in its own dual under the Sato–Tate pairing |
| `echoSymbol_nonneg_iff`, `exists_passive_commensurable_train` | Independent reflectors: passive iff `2Σ|c_i| ≤ 1`. Commensurable: passive with mass `N` for every `N` |
| `le_signedColumns_iff`, `prod_nonneg_iff` | Signed sums of Euler columns have the sum of the minima; products are rigid |
| `columnCurrent_pos_of_mass_lt`, `columnMass_le`, `exists_columnCurrent_neg` | The base pays by size, for `S ⊆ [2, P]` once `log(b/2π) > 14√P log P`; alignment below the base fails the current |
| `passive_iff_each_echo_in_band`, `exists_evenSeq_of_reflCoeff` | Schur bands; reflection data are free coordinates |
| `weight_eq_of_reflCoeff_eq`, `vonMangoldt_eq_of_reflCoeff` | The first reflector reads the prime weight, exactly |
| `hasDerivAt_levinsonErr_autocorr`, `hasDerivAt_reflCoeff_weight` | `∂E_n/∂λ(n₀) = −(2/√n₀) A_n(log n₀)`, and the exact tangent of each reflector in each prime weight |
| `hasDerivAt_reflCoeff_vacuum`, `abs_schurParam_sub_le`, `hasDerivAt_latticeKick` | Born at the vacuum; the defect by the accumulated reflection; the tangent of `q_n` at every positive stage |
| `ae_canonicalPotential_eq_born_add` | Before contact `Ψ′ = (r′ + 2r) + (r′ + 2r) r²/(1 − r²)` almost everywhere |
| `abs_le_of_isAnchorFlow`, `abs_kickFlow_logClock` | A priori bounds free of `1/μ`: `|κ_n| ≤ ¼ log n + ½ log(2 log n) + 5A` for kicks `≤ A log n/√n` |
| `abs_artanh_anchorReflection_le_osc` | The actual chain: `|artanh r(x)| ≤ artanh e^{−2(x−c)} + 2ω`, with `ω` the oscillation of `Ψ` on `[c, x]` |
| `exists_profile_decomposition` | Bounded energy and any translations give a weak profile, a Bohr character and a Brezis–Lieb splitting |
| `tendsto_configEnergy_bubbles`, `riemannHypothesis_iff_bubbles_relativelyCompact` | On-line configurations: moving bubbles converge to the Bohr energy; for `Spec ℤ` this relative compactness is RH |
| `not_tendsto_weilOrbitCorr`, `not_tendsto_dipole` | Unconditional: no nonzero bubble decouples from its far translate |
| `tendsto_weilQuad_of_dominated` | Unconditional: on dominated sequences the form loses no energy at spectral infinity |
| `riemannHypothesis_iff_orbit_recurs` | RH ⇔ strict orbit Cauchy–Schwarz plus dipoles of fixed mass with arbitrarily small energy at arbitrarily large separation |
| `hasSum_onsetEnergy`, `onsetSummand_of_onLine` | The onset field is a sum over zeros seen at scale `1/a`; on-line terms are nonnegative |
| `re_onsetPair_ge_of_small`, `two_thirds_le_pairEnergy`, `pairEnergy_le` | A pair at depth `δ` costs at most `(16/9)δ²a⁴‖ψ‖²` for `δa ≤ ½`, at every height; `S(δ, a) ≍ δ²a³` |
| `onsetEnergy_nonneg_of_le`, `riemannHypothesis_iff_onsetEnergy_nonneg` | Bounded apertures are positive at every height; RH is positivity at all apertures |

## 6. Questions and answers

Each question has a theorem in `TheQuestionsOfTheField.lean`. Answers that are RH-strength are stated as equivalences: the field locates these, and it does not settle them.

| # | Question | Answer |
|---|---|---|
| Q1 | When is a frustrated form nonnegative at zero slack? | Iff at every positive slack each window has an outer predictor with positive margin (`question_one`). For `Spec ℤ`: RH iff all windows have outer predictors, the reflection data are not square-summable, and negative slack is empty (`question_one_specZ`). The form of the answer is proved. Its producer is unconditional only on certified windows and at critical ratios |
| Q2 | What replaces Allegretto–Piepenbrink? | The causal solution: outer instead of positive. It carries a Riemann hypothesis in every window, and on nonpositive couplings it is the positive supersolution (`question_two`, `toeplitzForm_eq_doob`, `toeplitzForm_nonneg_of_supersolution`). In the aperture variable the passive state itself gives a Darboux pair of positive Schrödinger solutions (`IsAnchorTraces.darboux`) |
| Q3 | Which cones are invariant under prime insertion with locked phases? | The exponentially convex cone is invariant (`IsExpConvexFrom.torusSum`). Among amplitudes of left exponent below `½` it is the only one with nonnegative insertions at all prime sets, base points and locked phases (`question_three`). On a fixed prime set the cone is strictly larger (`gaussian_torus_positive`, `not_isExpConvexFrom_gaussian`) |
| Q4 | When is an echo train passive? | When each echo lies in its Schur band; the bands are free coordinates. On independent reflectors only size counts; on commensurable ones the mass is unbounded (`question_four`) |
| Q5 | Why is `(β, s) = (1, 0)` critical? | `s` is an absolutely continuous density over a measure with none. `s > 0` is Szegő, `s < 0` is empty, `s = 0` is the threshold. At `β = 0` the weights are not pinned (`question_five`) |
| Q6 | Can an arithmetic inner factor be finite and nontrivial? | Without arithmetic, yes (`innerOf_linear`). For Dirichlet polynomials and periodic data, never. For positive generalized primes with small reciprocal mass, yes (`exists_small_reciprocalMass_zero_off_line`). For `ζ` it is open, and RH splits as field vanishing plus recurrence (`question_six`) |
| Q7 | How do reflectors depend on primes past the first echo? | Through the autocorrelation of the predictor test at `log n₀`, exactly, at every stage; the margin is concave in the weights (`question_seven`, `hasDerivAt_reflCoeff_weight`, `levinsonErr_le_add`) |
| Q8 | What plays the role of Castelnuovo? | The target is forced: `1/E`, with first coefficient `1 − γ` (`question_eight`). Over a curve purity gives holomorphic Euler-log convergence and quotient domination (`question_eight_curve`). Over `ℤ` near-unit holomorphic budgets remain open; boundary quotient limits alone do not control them |
| Q9 | How does the Gamma base pay the columns? | By size once `log(b/2π)` passes twice the mass, which is at most `14√P log P` for `S ⊆ [2, P]`. In each range `[B, BQ^{|S|}]` there is a height where the set aligns, and there the base has to exceed the aligned mass (`question_nine`). The true height of alignment is the open part |
| Q10 | How does `q` depend on the data past the Born regime? | On a lattice `q_n = −artanh γ_n`. At the vacuum each reflector reads its own echo. In general the defect is at most `K(Π(1 + |γ_k|) − 1)`, and the tangent is exact at every positive stage (`question_ten`). The first correction is `κ₁²(κ₂ − κ₀)/(κ₀(κ₀² − κ₁²))` (`reflCoeff_one_sub_born`). Before contact `Ψ′` is an exact rational function of `r` and `r′` (`ae_canonicalPotential_eq_born_add`) |

## 7. Tools

| Tool | State | Lean |
|---|---|---|
| T1. Exact certificates for frustrated forms | Exact for every sign pattern on lattices, and for general symmetric forms as triangular squares | `toeplitzPosDef_iff_exists_outer_predictor`, `exists_sum_sq_certificate`, `exists_causal_certificate`, `stepDown`, `abs_last_lt_one` |
| T2. A priori estimates free of `1/μ` | For continuous potentials, for atomic kicks of arithmetic size, and for the actual Weil chain by the oscillation of `Ψ` | `abs_le_of_isAnchorFlow`, `integral_sq_eq`, `abs_kickFlow_le`, `abs_kickFlow_logClock`, `abs_artanh_anchorReflection_le_osc` |
| T3. Profile decomposition over Bohr space | On the energy space, for every bounded sequence and all translations; for on-line tempered configurations through moving bubbles; for `Spec ℤ` the passage to tests is RH. Tilted tails are tight on critical ratios | `exists_profile_decomposition`, `tendsto_energy_bubbles`, `tendsto_configEnergy_bubbles`, `riemannHypothesis_iff_bubbles_relativelyCompact`, `integral_tail_le_exponentialMass`, `tendsto_weilQuad_of_dominated` |
| T4. Carleson embedding at the critical scale with arithmetic coefficients | At every scale and for every entire coefficient of quadratic growth, with the inner field as constant | `carleson_embedding`, `shiftedCrowd_le_innerField`, `sum_depth_box_le`, `greenKernel_ge`, `mult_sum_box_le_log_budget`, `card_mul_exp_le` |
| T5. Inverse scattering and the forward map | Free coordinates, uniqueness, exact reading of a weight, exact tangent in every direction | `exists_evenSeq_of_reflCoeff`, `evenSeq_eq_of_reflCoeff_eq`, `reflCoeff_zero_sub`, `weight_eq_of_reflCoeff_eq`, `hasDerivAt_reflCoeff`, `hasDerivAt_latticeKick` |
| T6. Hardy calculus of the disc | Mean value, Parseval and the reproducing bound with no boundary limits | `IsHardyDisc`, `IsHardyDisc.circleAverage_norm_sq_eq`, `IsHardyDisc.norm_sub_sq_le` |
| T7. Calculus of signed Euler columns | Sums, products and pairings across independent columns | `le_signedColumns_iff`, `prod_nonneg_iff`, `integral_torusSum_mul_torusSum`, `exists_height_aligned` |

## 8. Test cases

**The function-field chain.** The sign is known and `r, q` compute (`TheCurveChainOfTheInnerFactor`, GWZ `TheCanonicalFlowOfACurve`). The inner mass is the Mahler measure, and Castelnuovo, Carathéodory and trivial inner factor coincide. The near-extremal family is explicit (`CastelnuovoConstructsTheMollifierOfACurve`), and the golden fake keeps a floor `φ²`.

**The `{2, 3}` rung.** Steep amplitudes are torus positive on `{2, 3}` (`torusSum_two_three_nonneg`), and the Gaussian lies in this cone without being exponentially convex. Only all primes, with the base
point moved to the left, force the Laplace cone.

**One critical ratio.** At a ratio below the threshold the window pencil `a_φ Q(H) + (7J(1)/R) M₈(H)` is positive, with an exponentially tilted slack that breaks translation invariance. The causal certificate survives as a triangular sum of squares (`exists_certificate_at_critical_ratio`, `exists_certificate_below_floor`), and the tilt makes the left tail tight (`integral_tail_le_exponentialMass`). A fixed ratio is a finite rung and decides nothing about RH.

**One certified window.** On windows up to `2·successorWeilFloorAperture` the predictor of `Spec ℤ` is outer, its Riemann hypothesis holds, and the echoes carrying `Λ(2)` lie in their Schur bands (`PassivityCertifiedFromArithmeticData`).

## 9. Selectivity

The statement "trivial inner factor" is false on each corpus fake, so a proof must use what the fake lacks.

| Fake | What it has | Why it fails | Reference |
|---|---|---|---|
| Euler column, `|c| > √p` | Euler factor, periodic zeros | Inner mass `log(|c|/√p)`; no functional equation | `exists_column_zero`, `tendsto_innerOf_column` |
| Golden curve | Integral zeta, Beurling system with nonnegative counts, functional equation | Inner mass `log φ`: not pure; Abel budgets stay above `φ²` | `innerMass_goldenDatum`, `sq_goldenRatio_le_abelBudget`, AOG `golden_orbitCorr_rate_iff` |
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
| Boundary dilation quotients control holomorphic mollifiers | Every finite datum has quotient mean tending to one; the golden datum still has Abel budgets at least `φ²`. Euler-log convergence must be justified separately |
| A rigidity law makes a mollifier | It holds for every `Q`, with the excess on the right. It produces no family with small excess |
| `N(ρ) ≤ Πϱ` is lossy | It is an equality over all other zeros |
| Phase locking is a free extra source of positivity | At a fixed amplitude, and at an amplitude with a limit at height infinity, it is torus positivity. It can act only through an amplitude oscillating with the height |
| A positive supersolution exists at zero slack, in some gauge | Frustration survives every gauge (`exists_wrong_edge`, FADF). The certificate must be causal |
| An outer predictor is RH | It certifies one window; the content is all windows of all lattices |
| Zero slack means vanishing innovation | Not in general: a density may vanish at a point with `E_∞ > 0`. For `Spec ℤ` under RH, `E_n → 0`: the spectral measure is singular |
| The Laplace cone is forced on small prime sets | Only by all primes together with base points to the left. The Gaussian is in the `{2, 3}` cone |
| The Bernstein theorem kills the theta amplitude | It needs base points to the left and left exponent below `½`, where the diagonal `Σ_p p^{−2s}` converges. `S` reads the amplitude only from `x = 0`, where it decays doubly exponentially, and its formula continued to `x < 0` has left exponent `½ + a` |
| Reflectors sit on `½ log n` | Only to first order. The second reflector is the Laguerre form and is present at an echo-free site |
| The Born approximation holds at large `n` | It holds while `Π(1 + |γ_k|) − 1` is small. For `Spec ℤ` under RH the reflection data are not square-summable (`question_one_specZ`), so this quantity is unbounded and the defect bound says nothing at large `n` |
| Far bubbles decouple, as in the Euclidean case | Never, for any nonzero test: the orbit correlation does not tend to `0` |
| A profile decomposition on the energy space is a theorem about tests | The energy space has it unconditionally. The energy is the Weil form only on the line, and the transfer to tests for `Spec ℤ` is RH |
| Size bounds are lossy on Euler trains | On independent reflectors size is exact. Cancellation lives inside one column |
| Finite inner degree is a small perturbation | It forces the field to vanish at infinity, and a recurrent datum cannot have it |
| Dirichlet gives the height of alignment | It gives an upper bound on the first aligned height, not a lower bound. The aligned height may be much smaller than `BQ^{|S|}` |

## 11. Open research topics

1. **The opposite sign.** A holomorphic mollifier family with budget tending to `1` at one centre (`riemannHypothesis_iff_exists_budget_lt`). This is RH. Over a curve, purity gives Euler-log convergence as well as quotient domination. Over `ℤ` both the holomorphic family and its budget must be controlled.
2. **Oscillating amplitudes.** `S(a, b) = Σ_N τ_b(N) A(N; a, b)` has an amplitude depending on the same `b` as the phases. Amplitudes with a limit gain nothing, and oscillating ones can. Does `A` oscillate at the rate tied to the phases?
3. **The Bernstein theorem at a fixed base point.** Is the exponent `½` sharp? What does torus positivity at all prime sets force when the base point is fixed at `x = 0`, the form in which `S` reads its amplitude? There the Hecke form sees only primes up to `e^{y/2}`, and the diagonal does not vanish.
4. **The zero–one law for `ζ`.** A lower bound on returns around an off-line zero (`ZetaZeroDiscWeaklyRecurrent`). Corpus: return shifts have density zero, no lower bound.
5. **Inner mass at infinity of `ζ`.** It tends to `0` iff the depth density is `o(T)` iff the Abel log-mean of `ζ` on the line tends to `0`. Moment data give `log log x` (`exists_innerField_le_loglog`). Boundedness is the depth density `O(T)`, and vanishing is below RH.
6. **The profile decomposition at atomic tests.** For `R > R₀`, does every sequence of atomic tests with bounded complete energy split as a strong physical `L¹` limit plus profiles over Bohr space, with nonnegative asymptotic energy? The energy-space theorem and the tail tightness are in place, and the nonnegative energy at infinity is the gap.
7. **Mid-range clusters.** Crowds of size `k` obey `e^{−4θk/5}`. The range `εα ≲ k ≲ α/θ` stays at rate `2θ`, and a joint event law is needed.
8. **Roots of predictors of `Spec ℤ`.** Under RH the zeros of `A ∓ zA^*` should approximate the atoms `e^{iγ_ρ h}`. Quantify the distance of the roots of `A` from the circle by the margins.
9. **The literal flow.** `q` as a function inside the precontact set, and the sharpness of `¼ log n + ½ log log n` under coherent kicks. Contact itself is RH-strength.
10. **The height of alignment.** A lower bound on the first aligned height of a prime set closes the bracket of Q9. Dirichlet is an upper bound and Baker gives polynomial repulsion (ADO). Moment methods do not reach it, because their off-diagonal needs length at least `P^K`.
11. **The onset field at fixed `λ`.** A first sign at unbounded aperture for all tests, on density-one heights. A fixed `λ` on density-one heights is a statement below RH.
12. **The second variation of the forward map.** The tangent is exact. Its curvature decides how far a known window extends, and it has not been computed.

## 12. Place in the research

AIF is on the receiver side of the sign block. The production side, square-root precision, is not obviously part of the field, and the corpus proves no bridge beyond shared RH endpoints.

| Programme | Interface |
|---|---|
| MZF (`MultiscaleMollifiedZetaField`) | Derivative law and camera: `MultiscaleMollifiedZetaField.normalDerivative` becomes an equality; second moments enter through `integrable_and_log_norm_le_poisson` |
| BSY/CTF | `I(1)` is the Balazard–Saias–Yor mass; `isGLB_budget_one` is its variational form |
| GWZ (`GrowingWindowsOfSpecZ`) | Lattice Schur–Levinson system: predictors, margins, causality, kicks. AIF adds outer predictors, free coordinates, the forward map, the weight dictionary and the Szegő threshold |
| CSTW (`CanonicalSystemOfTheWindowTower`) | The literal Weil chain (`TheWeilChainIsOneScalarFlow`, `TheWeilTracesHaveTheirSoftKick`); `TheAnchorFlow` is its abstract layered-medium form, and `abs_artanh_anchorReflection_le_osc` is its restoring bound |
| CHT (`CriticalHardyTheoryOfTheWindowCone`) | Datum plane and window cone (`datum_classification`); AIF reads the datum as an absolutely continuous density |
| CompletedArithmeticForms | `eulerPartial`, `S = Π T_p A`, `thetaApertureAmplitude_not_laplaceMixture`; AIF gives the cone, the walls and the classification |
| FADF (`FrustratedArithmeticDirichletForms`), ACT (`ArithmeticCriticalityTheory`) | Frustration past `log ρ` in every sign gauge, Doob gauges, Hardy weights; AIF gives the causal certificate that survives frustration |
| AKL (`ArithmeticKreinLangerTheory`) | The Krein–Langer index reads the inner degree; the zero–one law says when finite degree is possible |
| ACS (`ArithmeticCastelnuovoSeveri`), AOG (`ArithmeticOrientationGeometry`) | Curve data and orientation; the Abel family is the mollifier reading of `hodgeIndexOnSpan_iff_unitary`, and T3 rests on `blindAbove_of_orbitCorr_le` |
| ZCG (`ZeroConfigurationGeometry`) | Blindness density (`eq_zero_of_blind_of_unbounded_density`) and the camera; ZCG is sign-free, and AIF's budgets are the same zeros read through second moments |
| AHD (`ArithmeticHodgeTheoryOfDegenerations`) | Critical ratios of windows and the pencil on which the triangular certificate is built |
| WVL (`WindowVisibilityLaw`), SRT (`SquareRootThreshold`) | The certified aperture and the pair energy of the onset field |
| ADO (`ArithmeticDiscreteness`) | Baker repulsion for Euler carriers, the height of locking |
| HT (`HTGeometry`) | Kronecker density, simultaneous Dirichlet approximation |

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

On the side of mollifiers, the target is forced and the excess controls everything. Over a curve the family is the damped Euler logarithm; Castelnuovo supplies its holomorphic convergence and boundary domination. Quotient limits alone forget the inner mass.

On the side of forms, the exact certificate for frustrated positivity exists: a causal solution that is outer. Each positive window carries its own Riemann hypothesis, for the same reason as Hermite–Biehler. Positivity of all windows of all lattices is RH, and it sits exactly at the threshold of Szegő's regime, with no absolutely continuous density to spare. On certified windows and at critical ratios the certificate is a theorem.

On the side of arithmetic, locking gives nothing at a fixed or convergent amplitude, the cone of all primes is the Laplace cone, independent reflectors leave only size, the base pays by size, and far bubbles never decouple. So what remains is narrow: oscillation of the amplitude with the height, recurrence around a zero, and the bound on the mollifier family. The reflection data read every prime exactly, and the forward map has an exact tangent, so nothing about the primes is hidden from the system. What is missing is the reason for its sign.
