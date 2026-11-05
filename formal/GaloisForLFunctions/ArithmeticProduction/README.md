# Arithmetic Production at Square-Root Precision (APR)

Namespace `GaloisForLFunctions.ArithmeticProduction`; umbrella `ArithmeticProduction.lean`; 18 modules.

## 1. Motivation

Every route to RH reduces to one inequality, the count `ψ(x) − x = O(√x log²x)`, read in some coordinate. A *receiver*
states what must be delivered. A *producer* delivers an inequality. The corpus has many receivers and no producer: the
prime number theorem, Guth–Maynard and every error law weaker than square root hold for weights that fail the count,
finite windows are blind to every width, and exact identities determine `Λ` without giving an inequality.

APR is the theory of production. It asks which unconditional statements about `Λ` and `ζ` inside the strip can carry
square-root precision, what each classical tool provably can and cannot produce, and where precision is lost between
`ζ` and `Λ`. Its answers are mostly exact limits: for each classical tool, the theorem that says how far it reaches and
the weight on which it stops.

The central finding reorganizes the question. Parity is not the hard part: the only parity seen by any known input is
the sign of one residue, and a corrected twin carries the same count as `Λ`. Precision-faithfulness is not the hard
part either: pinning one linear functional achieves it. The hard part is the stabilizer, together with the proof that a
statement implies the count.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Weight, count | `Count`, `partialSum` (ASRP) | `a : ℕ → ℝ`; `A(x) − x = O(√x log²x)` |
| Square-root class, stabilizer | `sqrtClass` (ASRP) | `𝒬`: partial sums `O(√x log²x)`; the perturbations a statement survives |
| Twin, corrected twin, reflection | `liouvilleWeight`, `poleCorrectedTwin`, `countReflection` | `λΛ`; `λΛ + 2`; `2 − a` |
| Impure factor | `impureFactor`, `impureWeight`, `impureCoeff` | `1 − c p^{−s}`, `c > √p`; weight and integer coefficients of `ζ(s)(1 − c p^{−s})` |
| Type II form | `bilinearForm`, `bilinearConstants`, `IsBilinearStatement` | `Σ α_m β_n a(mn)` on a box; admissible constants; statements seeing only those |
| Type I datum | `divisorSum`, `sum_lam_mul_divisorSum` | `W(n) = Σ_{d|n} c_d` of level `D` |
| Mollifier | `edPoly b (Icc 1 N)`; `linearCoeff`, `sharpCoeff` | `M(s) = Σ_{n≤N} b_n n^{−s}`, `b₁ = 1`, `|b_n| ≤ 1`, real |
| Length exponent | `N ≤ T ^ θ` | `θ = log N / log T` |
| Mollifier defect, sawtooth form | `mollifierDefect`, `sawtoothDefect` | `(2π)⁻¹∫|1 − ζM(½+it)|²dt/(¼+t²)`; `∫₀^∞|1_{x≥1} + Σ b_d {x/d}|²dx/x²` |
| Second-moment profile | `lineFun`, `StripDecay` | `Φ(x) = ∫|F(½+x+it)|²dt`, a Laplace transform in `x` |
| Mollified window | `gaussWindow`, `mollifiedWindow`, `windowBody`, `gaussKernel`, `linePower` | `ζM` times `(s−1)/(s+1)`, localized by a Gaussian of width `w` at height `t₀` |
| Line polynomial, resonance | `linePoly`, `resonantWeight` | `P_a(t) = Σ_{n≤N} a(n) n^{−½−it}`; `εn^{−η+iγ}`, the explicit-formula term of a zero `1 − η + iγ` |
| Second-moment law, rate | `MollifiedSecondMomentLaw`, `SecondMomentRate` | excess `→ 0` at length `exp(o(T))`; excess `K/log T` |
| Mertens law, proximity | `MertensLaw`, `mertensInvisible`, `Proximity` | `Σ a(n)/n = log N − γ + o(1)`; its invisible perturbation; `a − Λ ∈ 𝒬` |
| Shifted width | `shiftedWidth` | width of `ξ(s+a)ξ(s−a)` |

## 3. Language

- **Producer / receiver.** A receiver implies the count from a hypothesis. A producer is an unconditional inequality.
- **Entry tests.** Necessary properties of a statement `S` with `S ⇒ Count` (`deciding_input_necessary_properties`): twin, precision, aperture, stabilizer.
- **Filter / certificate.** A filter rejects statements. A certificate would establish `S ⇒ Count`. No list of necessary properties is a certificate (`proximity_passes_entry_criteria`).
- **Blind.** A statement is blind to a perturbation if it holds for both `a` and `a + δ`; a tool is blind to a class if its output cannot separate its members.
- **Pole parity.** Separating `Λ` from a weight through the residue at `s = 1` only.
- **Locally pure.** Sensitive to the size of the Euler factor at every single prime.
- **Excess.** `(1/T)∫_T^{2T}|ζM|² − 1`.
- **Window.** Length `≤ T` is below the window, length `T^θ` with `θ > 1` is above it.

## 4. Mechanisms

**A. Conjugation.** A completely multiplicative sign conjugates a Type II form, `B_{ga}(α,β) = B_a(gα, gβ)`, and preserves `ℓ²`. A relabeling of the primes does the same. So norms know neither parity nor where the primes are.

**B. Cancellation of `λ` at Type I level.** `Σ λ(n)W(n) = Σ c_d λ(d) L(N/d)` is small for every Type I weight of level `N^{1−δ}`, while `Λ` has mass `N`. Type I weights cannot approximate `Λ` in `L¹`.

**C. Sawtooth dictionary.** Mellin–Plancherel turns the mollifier defect into a sawtooth form with no constraint at `s = 1`. For the linear Möbius mollifier the form equals `xD(1) − ψ(x)/log y` on `[1, y]`. The defect is the Chebyshev error, so a bounded defect is RH. The sharp Möbius mollifier gives `F = x m(y)`, whose defect never tends to `0` because `M(x) = Ω(√x)`.

**D. Laplace rigidity.** `Φ(x) = ∫e^{−2xu}|Y(u)|²du` with `Y` supported on a band of width `L = log(T²N^{3/2})` up to negligible tails. So `e^{La}Φ(a) + e^{−La}Φ(−a) ≤ 2cosh(aL)Φ(0)`. The floors `Φ(a) ≳ T` (first moment) and `Φ(−a) ≳ e^{2a log T}T` (zero count) form a kink at `0`, and the interpolation at `aL ≈ log 2` forbids it unless `Φ(0)` has an excess of order `1/θ`.

**E. Resonance.** At length `N`, the polynomial of `εn^{−η+iγ}` has no cancellation on a window of length `1/log N` around `γ`, so it contributes `ε²N^{1−2η}/log N` to the second moment. The sharp mean value bounds every `|a_n| ≤ εn^{−η}` by `ε²(T log N + N^{1−2η}/(1−2η))`. The two meet at `θ(1−2η) = 1`.

**F. Reflection.** `2 − a` reflects the error term, so it preserves every error law, and `λΛ + 2` is the reflection of `Λ` up to `𝒬`.

**G. Concavity against purity.** The log-mean of an impure factor is exactly `log(c/√p)` and the log-means of `ζ` and `M` are at least `−o(1)`. Concavity then gives a second-moment floor of `c²/p`, while upper bounds change only by a constant.

## 5. Foundational pillars

Each theorem is unconditional unless the statement is an equivalence with RH or an implication from a named law.

| # | Theorem | Lean | Module |
|---|---|---|---|
| 1 | Type II statements fail at `Λ` if they imply the count; constants invariant under twists and relabelings; prime-power locality | `not_bilinearStatement_vonMangoldt`, `bilinearConstants_twist`, `allBilinearConstants_comp`, `bilinearForm_eq_zero_of_coprime` | `BilinearFormsAreParityBlind` |
| 2 | Type I weights of level `N^{1−δ}` stay at `L¹` distance `(1−ε)N` from `Λ` | `typeI_parity_barrier`, `exists_abs_liouvilleCount_le` | `TypeIInformationIsParityBlind` |
| 3 | Mollifier defect = sawtooth form | `mollifierDefect_eq`, `mollifierDefect_ge_band` | `TheMollifierDefectIsASawtoothForm` |
| 4 | Linear mollifier = Chebyshev error; bounded or subpolynomial defect ⇒ RH; sharp mollifier does not close | `sawtoothDefect_linear`, `riemannHypothesis_of_linearDefect_bounded`, `riemannHypothesis_of_linearDefect_subpolynomial`, `exists_frequently_le_sharpDefect` | `TheLinearMollifierIsTheChebyshevError` |
| 5 | Every off-line zero pins a floor, at any length: `(2β−1)|1−ρ|²/|ρ|⁴` | `mollifierDefect_floor` | `EveryOffLineZeroPinsAFloor` |
| 6 | Cosh interpolation of the profile | `cosh_interpolation` | `TheSecondMomentIsALaplaceTransform` |
| 7 | **Necessary length**: `∫_T^{2T}|ζM|² ≥ (1 + 1/(8+6θ))T` at `N ≤ T^θ`; second moment `→ 1` forces every exponent | `necessary_length`, `length_exponent_tendsto_of_second_moment_tendsto_one` | `TheNecessaryLengthOfAMollifier` |
| 8 | Second moment `→ 1` ⇒ `100%` clustering; excess `K/log T` ⇒ `D_zero`; both false at every fixed exponent | `logMean_tendsto_zero_of_mollifiedSecondMomentLaw`, `criticalClustering_of_mollifiedSecondMomentLaw`, `logFreeNearLineZeroDensity_of_secondMomentRate`, `not_secondMomentLaw_of_bounded_exponent`, `not_secondMomentRate_of_bounded_exponent` | `LongMollifiersImplyCriticalClustering` |
| 9 | **Length–precision law**: the second moment at `T^θ` sees `εn^{−η}` iff `η < ½ − 1/(2θ)`; below the window only moduli are seen | `length_precision_law`, `below_the_window_every_power_is_blind`, `abs_integral_twist_sub_le` | `TheLengthPrecisionLaw` |
| 10 | **Corrected twin**: `λΛ + 2` shares every error law, the count and PNT with `Λ`; prime polynomials of `λΛ`, `−Λ` agree in mean square through `T²` | `errorLaw_poleCorrectedTwin_iff`, `count_poleCorrectedTwin_iff`, `primeNumberLaw_poleCorrectedTwin`, `twist_polynomial_second_moment_le` | `TheLiouvilleTwinOnlySeesThePole` |
| 11 | **Impure mimic**: exact integer count, all upper bounds, failed count, lattice of zeros at any width, log-mean `log(c/√p)` | `abs_sum_impureCoeff_sub_le`, `integral_norm_sq_mimic_le`, `not_count_impureWeight`, `impureFactor_rpow_eq_zero`, `exists_lattice_zero_near`, `tendsto_logMean_impureFactor` | `ImpureEulerFactorsPassEveryUpperBound` |
| 12 | **Second moment sees purity**: floor `(1−ε)c²/p` at every length `exp(δT)` | `impure_second_moment_floor`, `not_secondMomentLaw_impure` | `TheMollifiedSecondMomentSeesPurity` |
| 13 | **Self-improvement** on the shifted family is `Θ = 1`; corrected width invariant; shifted coefficients non-Ramanujan | `selfImprovement_on_shifts_iff`, `shiftedWidth_eq`, `shiftedWidth_sub_eq`, `coefficient_exponent_lower_bound` | `SelfImprovementFailsOnShiftedProducts` |
| 14 | **Filters are not certificates**: the Mertens law passes three tests and fails the fourth; proximity passes all four and implies the count iff RH | `mertensLaw_vonMangoldt`, `not_mertensLaw_liouvilleWeight`, `not_mertensLaw_and_add_smul_powerWeight`, `exists_extension_not_mertensLaw`, `exists_mertensLaw_not_count`, `proximity_passes_entry_criteria`, `proximity_implies_count_iff` | `AFaithfulInputNeedNotDecide` |

Infrastructure modules: `TheMollifiedZetaFunctionIsBandLimited` (`exists_stripDecay_mollifiedWindow`), `TheFloorsOfTheMollifiedSecondMoment` (`right_floor`, `exists_left_floor`), `TheGaussianAveragingOfTheWindow` (`integrated_gauss_inequality`, `exists_window_inequality`), `TheInterpolationAtALargeHeight` (`eventually_remainder_le`, `eventually_left_floor`).

## 6. Questions and their status

| Question | Status | Exact content |
|---|---|---|
| **Q1. `100%` critical-scale clustering (B20)** | Open. Reduced to Q3 | Q3 implies it at length `exp(o(T))`; no statement at a fixed exponent can carry the reduction |
| **Q2. `D_win`, `D_zero` (B21)** | Open. Reduced to a rate | Excess `K/log T` at length `exp(T/log T)` implies `D_zero`, hence `D_win`. Excess is at least a constant at every polynomial length. `D_win` fails on the impure mimic, which keeps all upper bounds, so an input must be locally pure |
| **Q3. Second moment at `T^θ`, `θ → ∞`** | Lower side settled in form, upper side open | Floor `1 + 1/(8+6θ)`; the law needs unbounded `θ` and local purity; for the linear mollifier a bounded defect is RH. The corpus has an upper bound at `θ = 21/50` (`eventually_offLineMoment_le_selberg_upper`). Classical prediction for the floor: `1 + 1/θ` |
| **Q4. Self-improvement (B57)** | False as a class theorem | On Euler products with functional equation (shifted family) the class law is `Θ = 1`. Without functional equation one factor realizes any width. A proof must use the Ramanujan bound and the functional equation together, on which no mechanism exists |
| **Q5. Parity-breaking bilinear input at square-root precision** | No such input exists among norm statements, and the question is restated | Type II norms, Type I weights and prime-polynomial mean values are parity-blind. Parity in every known input is pole parity. The real content is a provable statement with stabilizer inside `𝒬`, other than proximity |

**The restated question.** Find an unconditional statement `S`, not defined through `Λ`, with `S(Λ)` provable and `S(a) ∧ S(a+δ) ⇒ δ ∈ 𝒬`, together with a proof of `S ⇒ Count`. None is known. The formal obstruction list is sections 5.1, 5.2, 5.9, 5.10, 5.14; no theorem excludes its existence.

## 7. Tools

**Developed.**
- Mean-value normal form on the critical line and the threshold law (`abs_integral_norm_sq_linePoly_sub_le`, `integral_linePoly_le_of_power_bound`, `resonant_second_moment_ge`).
- Laplace profile with decay (`StripDecay`, `cosh_interpolation`) and Gaussian localization at height (`gaussWindow`, `integrated_gauss_inequality`, `exists_center_tail`).
- Floors uniform in the mollifier (`right_floor`, `exists_left_floor`, `eventually_left_floor`) and slices avoiding all zeros (`exists_admissible_slices`).
- Log-integral ceiling from a second moment (`exists_logIntegral_le_of_secondMoment`) and folding of off-line multiplicity (`sum_order_filter_abs_le`).
- Mimic battery: `liouvilleWeight`, `poleCorrectedTwin`, `impureWeight`, `mertensInvisible`, power perturbations, `shiftedWidth`.
- Sawtooth dictionary and dyadic elimination of the offset (`sawtoothDefect`, `band_of_dyadic`).

**Used from the corpus.** Littlewood budget and sandwich (`exists_zetaLine_logMean_sandwich`, `exists_zetaLine_littlewood_edge_budget_all_heights`), sharp mean value (`Sieve.dirichlet_meanValue_sharp_window`), mollifier floors (`exists_edPoly_line_logMean_floor`), zero count (`exists_xiZeroCount_close`), Gallagher's identity (`Sieve.gallagher_identity`), which is the bridge from long polynomials to short-interval variance.

**To build.** Uniform version of `necessary_length` in `θ ≤ c log T`, which would turn the statement "the rate needs `N ≥ exp(c log²T)`" into a theorem. A mimic battery test harness stating any new input against all weights above.

## 8. Traps

1. **Twin failure is not a parity break.** PNT already fails for the twin. Test against `poleCorrectedTwin`.
2. **Precision-faithfulness is cheap.** One pinned functional achieves it at every power (`not_mertensLaw_and_add_smul_powerWeight`). Test the stabilizer.
3. **True + all necessary tests proves nothing.** `Proximity` is the counterexample.
4. **Upper bounds cannot see purity.** Any argument with only upper bounds for `ζ` on lines also proves itself for the mimic. It cannot imply the count, `D_win` or Q3.
5. **Length is not parity.** Lengthening raises precision by the law `η < ½ − 1/(2θ)` and leaves parity where it was: prime polynomials of `λΛ` and `−Λ` agree in mean square through `T²`.
6. **A fixed exponent cannot close anything.** Q1 and Q2 by second moment need `θ → ∞`.
7. **Bounded coefficients matter.** Floors use `|b_n| ≤ 1`. Finite windows with unbounded coefficients have no floor, so they answer a different question.
8. **Class theorems.** A self-improvement statement must exclude shifted products and impure factors explicitly. If its proof does not use the Ramanujan bound, it proves `Θ = 1`.
9. **`∫` body in Lean.** `∫ t in a..b, f t - c` integrates `f − c`. Parenthesize integrals.

## 9. Open research topics

1. The upper side of Q3 at `θ > 21/50`, and any statement at growing `θ`.
2. The constant of the floor: `1/(8+6θ)` proved, `1/θ` predicted. The loss sits in the left floor, which uses only the zero count and not pair correlation.
3. Uniformity of the necessary-length law in `θ`, and the exact length required by the rate `K/log T`.
4. A Blaschke form of the floor at several zeros (conjectured `1 − |I(0)|² − |I'(0)|²`).
5. Which statements other than proximity have stabilizer inside `𝒬`. Classifying finite systems of linear laws would settle whether any such system can.
6. Self-improvement inside the Ramanujan class with functional equation: find any mechanism, or a mimic in that class.
7. Second moments of integer polynomials above the window, which see the kernel `1` and do not reduce to prime polynomials. This is the one place in the mean-value world where parity is not yet shown to be blind away from the pole.

## 10. Context

**Uses.** ASRP (classes, count, entry tests, twin), RHTower (mollifier log-mean floors, Littlewood budgets, Selberg upper bound, mean value, Gallagher), CDG (clustering TFAE, `D_zero`, `D_win`, shells), HTGeometry (Plancherel, line shifts).

**Relation to other programmes.**
- ASRP names the precision classes and the tests. APR decides what can enter them.
- CDG states the near-line questions. APR gives the second-moment route to them and its limits.
- ZCG and the heat routes are sign-free readers. They read a configuration; they do not produce an inequality.
- AOG, ACS and the Hodge-type programmes are Programme A: they supply sign once given production. The two programmes meet at the count.
- FFP and WTZ work at finite level, where every width is consistent. APR's aperture statement is why they cannot close alone.

**Place in the whole.** Programme B alone can close RH, because the count at square-root precision is RH. APR establishes that the classical tools cannot do so by themselves and locates the missing content in one sentence: a provable non-tautological statement with stabilizer inside `𝒬`.

## 11. Success and contribution criteria

**The programme succeeds if** it proves any of: a non-tautological statement with stabilizer in `𝒬` that implies the count; Q1 or Q2; the second-moment law at growing exponent. It also succeeds in part with a theorem showing that no statement in a named class can have stabilizer in `𝒬`.

**A contribution must:**
1. be unconditional, with every analytic input proved. An implication from a named law must state that law and must be shown not to be an equivalence with RH in disguise, unless it is labeled one;
2. state the outcome on the mimic battery: twin, corrected twin, `Λ + εn^{−η}`, `Λ + mertensInvisible`, impure weight, shifted width;
3. say which entry tests it passes and name its stabilizer, or a perturbation in it;
4. for a limit theorem, name the weight or configuration at which the tool stops, and extract the sharp positive statement;
5. improve a pillar, answer a question of section 6, or add a tool used by another module. A restatement of a corpus equivalence is not a contribution.
