# Arithmetic Production at Square-Root Precision (APR)

Namespace `GaloisForLFunctions.ArithmeticProduction`; umbrella `ArithmeticProduction.lean`; 22 modules. Every theorem is
unconditional unless it is an equivalence with RH or an implication from a named law. APR is the producer programme of
the Riemann Hypothesis work in this corpus. Its partner, Critical Hardy Theory of the Window Cone
(`CriticalHardyTheoryOfTheWindowCone/README.md`), is the receiver programme: what any input must deliver on a window.

## 1. The field

Every route to RH reduces to one inequality, the count `ψ(x) − x = O(√x log²x)`, read in some coordinate: a sign on a
window, a Krein form, a squared gap, a Jensen count, a mollified mean square. A *receiver* states what must be
delivered. A *producer* delivers an unconditional inequality. The corpus holds many receivers and no producer: the prime
number theorem, Guth–Maynard and every error law weaker than square root hold for weights that fail the count, finite
windows are blind to every width, exact identities determine `Λ` without giving an inequality, and polynomial-length
mollifiers stop at a constant excess.

APR is the theory of production. It asks which unconditional statements about `Λ` and about `ζ` inside the critical
strip can carry square-root precision, what each classical tool provably can and cannot produce, where precision is lost
between `ζ` and `Λ`, and on which receivers a producer would land. Its answers are mostly exact limits: for each tool,
the theorem that says how far it reaches and the weight on which it stops.

The field has four parts.

1. **Precision classes and entry filters.** The square-root class `𝒬`, the stabilizer of a statement, and the five
   properties every count-implying statement must have: parity-breaking (false for the Liouville twin), locally pure
   (false for `ζ(s)(1 − cp^{−s})`, `c > √p`), precision-faithful (never true for both `a` and `a + εn^{−η}`, `η < ½`), of
   unbounded aperture and length, and with stabilizer inside `𝒬`. The filters are necessary conditions; no list of them
   is a certificate.
2. **Limits of the classical tools.** Type I information at level `N^{1−δ}` and Type II norms are parity-blind; finite
   systems of convergent linear laws (Mertens among them) admit a common perturbation outside `𝒬`; every upper bound on
   `Re s ≥ ½` that survives an impure Euler factor is purity-blind; the Liouville twin corrected at the pole shares every
   error law with `Λ`; prime polynomials of `λΛ` and `−Λ` agree in mean square to `O(T log T)` through length `T²`.
3. **Mollifier theory.** The mollified second moment `∫_T^{2T}|ζM(½+it)|²dt` as the mean-value form of the count: its
   sawtooth dictionary, its floors (first moment on the right, zero count on the left), its Laplace rigidity in the
   abscissa, its exact necessary-length laws (floor `1 + 1/(8+6θ)` at length `T^θ`; the `exp(c log²T)` threshold for an
   excess `K₀/log T`; `log N/log T → ∞` for a moment tending to `1`), its length–precision law (`η < ½ − 1/(2θ)`), and
   the Gram floors pinned by off-line zeros.
4. **Landings.** The receivers a producer would reach, with exact thresholds: moment `→ 1` at length `exp(o(T))` gives
   `100%` critical-scale clustering; excess `K₀/log T` at length `exp(T/log T)` gives `D_zero` and `D_win`; a dyadic
   bound with prefix cancellation to `T^{θ₁}`, `θ₁ > ½`, gives eventual quasi-RH; a cofinal bound for arbitrarily large
   length exponents gives RH; a bounded linear Möbius defect gives RH. On the density side, `D_win` is reached by any
   holomorphic actual-zero detector with shifted `L²` defect at scale `V/log V`, that scale is sharp, and no critical-line
   proportion and no exponential depth-tail rate reaches `D_win`.

The central finding reorganizes the question. Parity is not the hard part: the twin test sees only the sign of one
residue, a corrected twin carries the same count as `Λ`, and away from the pole parity is visible to long integer
polynomials, as the difference between a zero of `ζ` and a pole of `1/ζ`. Precision-faithfulness is not the hard part
either: pinning one linear functional achieves it. Length is necessary and quantified: every landing needs
superpolynomial mollifier length, and the thresholds are exact. The hard part is the stabilizer, together with the
proof that a statement implies the count; in mean-value form, an upper bound for a long mollified second moment.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Weight, count | `Count`, `partialSum` (ASRP) | `a : ℕ → ℝ`; `A(x) − x = O(√x log²x)` |
| Square-root class, stabilizer | `sqrtClass` (ASRP) | `𝒬`: partial sums `O(√x log²x)`; the perturbations a statement survives |
| Twin, corrected twin, reflection | `liouvilleWeight`, `poleCorrectedTwin`, `countReflection` | `λΛ`; `λΛ + 2`; `2 − a` |
| Impure factor | `impureFactor`, `impureWeight`, `impureCoeff` | `1 − c p^{−s}`, `c > √p`; weight and integer coefficients of `ζ(s)(1 − c p^{−s})` |
| Type II form | `bilinearForm`, `bilinearConstants`, `IsBilinearStatement` | `Σ α_m β_n a(mn)` on a box; admissible constants; statements seeing only those |
| Type I datum | `divisorSum`, `sum_lam_mul_divisorSum` | `W(n) = Σ_{d|n} c_d` of level `D` |
| Mollifier | `edPoly b (Icc 1 N)`; `linearCoeff`, `sharpCoeff` | `M(s) = Σ_{n≤N} b_n n^{−s}`, `b₁ = 1`, `|b_n| ≤ 1`, real or complex |
| Hermitian trace | `edPolyHermitianTrace` (CDG) | `(Ψ(z + iT) + Ψ*(z − iT))/2`, the holomorphic extension of `x ↦ Re Ψ(x + iT)` for complex coefficients |
| Length exponent | `N ≤ T ^ θ` | `θ = log N / log T` |
| Mollifier defect, sawtooth form | `mollifierDefect`, `sawtoothDefect` | `(2π)⁻¹∫|1 − ζM(½+it)|²dt/(¼+t²)`; `∫₀^∞|1_{x≥1} + Σ b_d {x/d}|²dx/x²` |
| Second-moment profile | `lineFun`, `StripDecay` | `Φ(x) = ∫|F(½+x+it)|²dt`, a Laplace transform in `x` |
| Mollified window | `gaussWindow`, `mollifiedWindow`, `windowBody`, `gaussKernel`, `linePower` | `ζM` times `(s−1)/(s+1)`, localized by a Gaussian of width `w` at height `t₀` |
| Line polynomial, resonance | `linePoly`, `resonantWeight` | `P_a(t) = Σ_{n≤N} a(n) n^{−½−it}`; `εn^{−η+iγ}`, the explicit-formula term of a zero `1 − η + iγ` |
| Second-moment law, rate | `MollifiedSecondMomentLaw`, `SecondMomentRate`; `ComplexMollifiedSecondMomentLaw`, `ComplexSecondMomentRate` (CDG) | excess `→ 0` at length `exp(o(T))`; excess `K/log T` at length `exp(T/log T)` |
| Credited Jensen budget | `flowCreditedJensenBudget` (CDG) | `½log(T⁻¹∫_T^{2T}|ζΨ(½+it)|²) − T⁻¹∫_T^{2T}log|Ψ(½+it)|` |
| Mertens law, proximity | `MertensLaw`, `mertensInvisible`, `Proximity` | `Σ a(n)/n = log N − γ + o(1)`; its invisible perturbation; `a − Λ ∈ 𝒬` |
| Shifted width | `shiftedWidth` | width of `ξ(s+a)ξ(s−a)` |
| Gram form | `gramForm`, `gramTest` | `Σ x(ρ) x̄(σ)/(ρ+σ̄−1)`: the Szegő kernel of `Re s > ½` at off-line zeros |
| Selberg integral | `selbergIntegral` | `∫|Σ_{u<log n≤u+δ} a(n) n^{−½}|²du` |
| Linear law | `LinearLaw`, `LinearLaw.Holds`, `LinearLaw.Convergent` | the limit of `Σ_{n≤N} a(n)w(n) − ℓ(N)`; `w` converges against every `n^{−t}`, `¼ ≤ t < ½` |
| Near-line receivers | `LogFreeNearLineZeroDensity`, `LogFreeNearLineWindowOccupancy`, `criticalClustering_logMean_mollifier_hecke_tfae` (CDG) | `D_zero`, `D_win`, and the eight forms of `100%` critical-scale clustering |
| Burnol window, detector | `burnolUnitXiZeros`, `fejerDirichletDetector` (CDG) | the unit windows of the near-line ladder; the Fejér–Dirichlet polynomial that occupies them at scale `V/log V` |
| Root model | `rootModel` (CDG) | a unit-window zero model with critical proportion `→ 1`, every exponential depth-tail rate, clustering, and no window occupancy |

## 3. Language

- **Producer / receiver / landing.** A receiver implies the count, or a weaker target, from a hypothesis. A producer is
  an unconditional inequality. A landing is the receiver a given producer shape reaches, with its threshold.
- **Entry tests.** Necessary properties of a statement `S` with `S ⇒ Count` (`deciding_input_necessary_properties`,
  ASRP): twin, precision, aperture, stabilizer; purity and length are the two further filters proved here.
- **Filter / certificate.** A filter rejects statements. A certificate would establish `S ⇒ Count`. No list of
  necessary properties is a certificate (`proximity_passes_entry_criteria`).
- **Blind.** A statement is blind to a perturbation if it holds for both `a` and `a + δ`; a tool is blind to a class if
  its output cannot separate its members.
- **Pole parity.** Separating `Λ` from a weight through the residue at `s = 1` only.
- **Locally pure.** Sensitive to the size of the Euler factor at every single prime.
- **Excess.** `(1/T)∫_T^{2T}|ζM|² − 1`.
- **Window.** Length `≤ T` is below the window, length `T^θ` with `θ > 1` is above it.
- **Prefix cancellation.** `ζM` has vanishing Dirichlet coefficients for `2 ≤ n ≤ X₁`.
- **Detector scale.** The size of the shifted `L²` defect of an actual-zero detector, measured against `V` and `V/log V`.

## 4. Mechanisms

**A. Conjugation.** A completely multiplicative sign conjugates a Type II form, `B_{ga}(α,β) = B_a(gα, gβ)`, and preserves `ℓ²`. A relabeling of the primes does the same. So norms know neither parity nor where the primes are. The same holds on any test class stable under the sign, so a parity-breaking bilinear input has to name test vectors outside such a class. Classical parity breaks on thin sequences (Friedlander–Iwaniec, Heath-Brown) have this shape; none is known at square-root precision for `Λ` itself.

**B. Cancellation of `λ` at Type I level.** `Σ λ(n)W(n) = Σ c_d λ(d) L(N/d)` is small for every Type I weight of level `N^{1−δ}`, while `Λ` has mass `N`. Type I weights cannot approximate `Λ` in `L¹`.

**C. Sawtooth dictionary.** Mellin–Plancherel turns the mollifier defect into a sawtooth form with no constraint at `s = 1`. For the linear Möbius mollifier the form equals `xD(1) − ψ(x)/log y` on `[1, y]`. The defect is the Chebyshev error, so a bounded defect is RH. The sharp Möbius mollifier gives `F = x m(y)`, whose defect never tends to `0` because `M(x) = Ω(√x)`.

**D. Laplace rigidity.** `Φ(x) = ∫e^{−2xu}|Y(u)|²du` with `Y` supported on a band of width `L = log(T²N^{3/2})` up to negligible tails. So `e^{La}Φ(a) + e^{−La}Φ(−a) ≤ 2cosh(aL)Φ(0)`. The floors `Φ(a) ≳ T` (first moment) and `Φ(−a) ≳ e^{2a log T}T` (zero count) form a kink at `0`, and the interpolation at `aL ≈ log 2` forbids it unless `Φ(0)` has an excess of order `1/θ`. Taking the ratio `a²/w²` directly against the excess removes the polynomial-length bottleneck and makes the law uniform up to `log N ≤ T^{1/60}`.

**E. Resonance.** At length `N`, the polynomial of `εn^{−η+iγ}` has no cancellation on a window of length `1/log N` around `γ`, so it contributes `ε²N^{1−2η}/log N` to the second moment. The sharp mean value bounds every `|a_n| ≤ εn^{−η}` by `ε²(T log N + N^{1−2η}/(1−2η))`. The two meet at `θ(1−2η) = 1`.

**F. Reflection.** `2 − a` reflects the error term, so it preserves every error law, and `λΛ + 2` is the reflection of `Λ` up to `𝒬`.

**G. Concavity against purity.** The log-mean of an impure factor is exactly `log(c/√p)` and the log-means of `ζ` and `M` are at least `−o(1)`. Concavity then gives a second-moment floor of `c²/p`, while upper bounds change only by a constant.

**H. Holomorphy at a zero.** A bound for `∫_T^{2T}|P_{a,N}|²` uniform in `N` passes by partial summation to every line `Re s = ½ + x`, becomes pointwise of size `√(B/x)` by the Sobolev inequality, and travels from `Re s > 1` to `Re s > ½` by three circles. So `|A| ≤ |E| √(10B + 26B/x)` whenever `E Σ a(n) n^{−s} = A`. With `E = (s−1)ζ` this forbids a zero of `ζ` in the window unless `A` vanishes there. It holds for `a = 1` after the pole term is removed and fails for `a = λ`, `μ`.

**I. Hermitian analytic trace.** For complex coefficients, `(Ψ(z + iT) + Ψ*(z − iT))/2` with `Ψ*(w) = Σ conj(a_n)n^{−w}` extends `Re Ψ(x + iT)` holomorphically and keeps the `5/16` head dominance at `z = 4` and the half-plane `ℓ¹` bound. Backlund's horizontal-edge bound, Littlewood's budget, the log-integral ceiling and every landing then hold for complex mollifiers.

**J. Prefix cancellation and spikes.** Around an off-line zero `ρ₀ = ½ + δ₀ + iγ₀`, the divided difference of `ζ(ρ₀+w)Ψ(ρ₀+w)exp(αw² + w log Y)` at `w = 0` is holomorphic; a Gaussian Cahen–Mellin contour on `Re s = 2` evaluates it, and prefix cancellation through `X₁` removes the main term. A critical-line spike `≥ (3/4)δ₀e^{−2αδ₀²}Y^{2δ₀}` on `[γ₀ − R, γ₀ + R]` results, and colouring occupied windows modulo `⌈2R + 7⌉` superposes the spikes. Dyadic boundedness therefore forces eventual quasi-RH, and cofinal boundedness at arbitrarily large exponents forces RH.

**K. Disc-corridor counting.** A holomorphic detector vanishing at the right-half zeros of occupied windows has an `L²` defect on a disc around each zero bounded below by its own size; summing disjoint discs over a corridor and comparing with the shifted defect bounds the number of occupied windows. With defect `Ce^{−r(σ−½)log V}·V/log V` the bound is `(32C/(πr))e^{−rA/2}V/A²`, hence `D_win`. The Fejér–Dirichlet polynomial has every `L^p` and `log⁺` defect of that size and occupies `≥ V/12` windows, so the `V/log V` scale cannot be improved by any norm, and every subcritical polynomial mollifier has defect `≥ c_{θ,A}V`.

**L. Prime-log and rough floors.** Keeping `n = 1` and the primes in `(y, M]` with sharp Mertens gives `∫_T^{2T}|ζΨ(½ + a/log T + it)|² ≥ (1 + e^{−2a}log(1/θ) − ε)T` for length `y ≤ T^θ`; splitting every `m ≤ M` into `y`-smooth and `y`-rough parts gives the `1/θ` blow-up floor. Möbius inversion on `[1, y]` produces an index `e* ≤ y` with `c_{e*v} = c_{e*}` for all `y`-rough `v`, so the credited Jensen budget diverges for `y ≤ (log T)^{1/8}`.

## 5. Foundational pillars

Each theorem is unconditional unless the statement is an equivalence with RH or an implication from a named law.

| # | Theorem | Lean | Module |
|---|---|---|---|
| 1 | Type II statements fail at `Λ` if they imply the count; constants invariant under twists, stable test classes and relabelings; prime-power locality | `not_bilinearStatement_vonMangoldt`, `bilinearConstants_twist`, `classConstants_twist`, `allBilinearConstants_comp`, `bilinearForm_eq_zero_of_coprime` | `BilinearFormsAreParityBlind` |
| 2 | Type I weights of level `N^{1−δ}` stay at `L¹` distance `(1−ε)N` from `Λ` | `typeI_parity_barrier`, `exists_abs_liouvilleCount_le` | `TypeIInformationIsParityBlind` |
| 3 | Mollifier defect = sawtooth form | `mollifierDefect_eq`, `mollifierDefect_ge_band` | `TheMollifierDefectIsASawtoothForm` |
| 4 | Linear mollifier = Chebyshev error; bounded or subpolynomial defect ⇒ RH; sharp mollifier does not close | `sawtoothDefect_linear`, `riemannHypothesis_of_linearDefect_bounded`, `riemannHypothesis_of_linearDefect_subpolynomial`, `exists_frequently_le_sharpDefect` | `TheLinearMollifierIsTheChebyshevError` |
| 5 | Every off-line zero pins a floor, at any length: `(2β−1)|1−ρ|²/|ρ|⁴` | `mollifierDefect_floor` | `EveryOffLineZeroPinsAFloor` |
| 5′ | **Gram floor**: defect `≥ v*G⁻¹v`, `v(ρ) = (1−ρ)/ρ²`, `G` the Szegő kernel on any finite set of off-line zeros; floors add up to interference | `mollifierDefect_gram_floor`, `mollifierDefect_gram_floor_singleton`, `mollifierDefect_floor_sum` | `FiniteSetsOfZerosPinAGramFloor` |
| 6 | Cosh interpolation of the profile | `cosh_interpolation` | `TheSecondMomentIsALaplaceTransform` |
| 7 | **Necessary length**: `∫_T^{2T}|ζM|² ≥ (1 + 1/(8+6θ))T` at `N ≤ T^θ`, uniformly for `θ ≤ (log T)/24`; an excess `κ` forces `log N ≥ min(log²T/24, log T/(14κ))`; second moment `→ 1` forces every exponent | `necessary_length_uniform`, `necessary_length`, `log_length_ge_of_excess`, `length_exponent_tendsto_of_second_moment_tendsto_one` | `TheNecessaryLengthOfAMollifier` |
| 8 | Second moment `→ 1` ⇒ `100%` clustering; excess `K/log T` ⇒ `D_zero`; both false at every fixed exponent; the excess `K/log T` needs `log N ≥ min(1/24, 1/(14K)) log²T` | `logMean_tendsto_zero_of_mollifiedSecondMomentLaw`, `criticalClustering_of_mollifiedSecondMomentLaw`, `logFreeNearLineZeroDensity_of_secondMomentRate`, `not_secondMomentLaw_of_bounded_exponent`, `not_secondMomentRate_of_bounded_exponent`, `log_length_ge_of_secondMomentRate` | `LongMollifiersImplyCriticalClustering` |
| 9 | **Length–precision law**: the second moment at `T^θ` sees `εn^{−η}` iff `η < ½ − 1/(2θ)`; below the window only moduli are seen | `length_precision_law`, `below_the_window_every_power_is_blind`, `abs_integral_twist_sub_le` | `TheLengthPrecisionLaw` |
| 9′ | Selberg integral dictionary: `∫_{−T}^{T}|P_a|² ≤ (5π/2)T² S_a(N, 1/T)`, and the resonance in short intervals | `integral_norm_sq_linePoly_le_selbergIntegral`, `le_selbergIntegral_resonant` | `TheSelbergIntegralDictionary` |
| 10 | **Corrected twin**: `λΛ + 2` shares every error law, the count and PNT with `Λ`; prime polynomials of `λΛ`, `−Λ` agree in mean square through `T²` | `errorLaw_poleCorrectedTwin_iff`, `count_poleCorrectedTwin_iff`, `primeNumberLaw_poleCorrectedTwin`, `twist_polynomial_second_moment_le` | `TheLiouvilleTwinOnlySeesThePole` |
| 11 | **Impure mimic**: exact integer count, all upper bounds, failed count, lattice of zeros at any width, log-mean `log(c/√p)` | `abs_sum_impureCoeff_sub_le`, `integral_norm_sq_mimic_le`, `not_count_impureWeight`, `impureFactor_rpow_eq_zero`, `exists_lattice_zero_near`, `tendsto_logMean_impureFactor` | `ImpureEulerFactorsPassEveryUpperBound` |
| 12 | **Second moment sees purity**: floor `(1−ε)c²/p` at every length `exp(δT)` | `impure_second_moment_floor`, `not_secondMomentLaw_impure` | `TheMollifiedSecondMomentSeesPurity` |
| 13 | **Self-improvement** on the shifted family is `Θ = 1`; corrected width invariant; shifted coefficients non-Ramanujan | `selfImprovement_on_shifts_iff`, `shiftedWidth_eq`, `shiftedWidth_sub_eq`, `coefficient_exponent_lower_bound` | `SelfImprovementFailsOnShiftedProducts` |
| 14 | **Filters are not certificates**: the Mertens law passes three tests and fails the fourth; proximity passes all four and implies the count iff RH | `mertensLaw_vonMangoldt`, `not_mertensLaw_liouvilleWeight`, `not_mertensLaw_and_add_smul_powerWeight`, `exists_extension_not_mertensLaw`, `exists_mertensLaw_not_count`, `proximity_passes_entry_criteria`, `proximity_implies_count_iff` | `AFaithfulInputNeedNotDecide` |
| 15 | **No finite system of convergent linear laws decides**: any such system has a stabilizer outside `𝒬` | `exists_stabilizer_outside_sqrtClass`, `finite_linear_system_cannot_decide`, `sum_powerWeight_not_mem_sqrtClass` | `NoFiniteSystemOfLinearLawsDecides` |
| 16 | **Long integer polynomials see parity**: at each height the integer polynomial stays bounded in `N` after removing the pole term; at every large height those of `λ` and `μ` are unbounded in `N` | `integral_norm_sq_integer_polynomial_le`, `eventually_not_uniform_liouville`, `eventually_not_uniform_moebius`, `norm_le_of_uniform_second_moment`, `not_uniform_second_moment_of_zero` | `LongIntegerPolynomialsSeeParity` |

Infrastructure modules: `TheMollifiedZetaFunctionIsBandLimited` (`exists_stripDecay_mollifiedWindow`), `TheFloorsOfTheMollifiedSecondMoment` (`right_floor`, `exists_left_floor`), `TheGaussianAveragingOfTheWindow` (`integrated_gauss_inequality`, `exists_window_inequality`), `TheInterpolationAtALargeHeight` (`remainder_le_of_small`, `center_remainder_le_of_small`, `right_floor_error_le_of_small`, `exists_left_floor_of_small`).

Pillars of the field proved in its neighbour modules (`ConjugateDiagonalGeometry/NearLineLogMean`,
`ArithmeticOfSquareRootPrecision`), on which the landings and filters rest.

| Theorem | Lean | Module |
|---|---|---|
| Entry tests: twin, precision, aperture, stabilizer; precision-blindness of PNT and weaker error laws | `deciding_input_necessary_properties`, `producers_are_precision_blind`, `errorLaw_cannot_decide`, `not_of_finite_window` | ASRP |
| Complex necessary length, uniform to `log N ≤ T^{1/60}`; excess `E` forces `log N ≥ min(T^{1/60}, log T/(6E) − (4/3)log T)`; excess `K₀/log T` forces `log N ≥ log²T/(6K₀) − (4/3)log T`; moment `→ 1` forces `log N/log T → ∞` | `eventually_uniform_complex_necessary_length`, `eventually_log_mollifier_length_ge_of_excess`, `complexSecondMomentRate_forces_exp_logSq_length`, `not_complexSecondMomentRate_below_exp_logSq`, `tendsto_log_length_div_log_atTop_of_complex_second_moment_tendsto_one` | `SubexponentialMollifierLengthAndWindowSpikes` |
| Complex landings: moment `→ 1` ⇒ (L) and clustering; `ComplexSecondMomentRate` ⇒ `D_zero ∧ D_win`; multi-window spikes; occupied windows `≤ (4/3)⌈2R+7⌉e^{2αδ²}δ⁻¹Y^{−2δ}Msq` | `logMean_tendsto_zero_of_complexMollifiedSecondMomentLaw`, `criticalClustering_of_complexMollifiedSecondMomentLaw`, `logFreeNearLineWindowOccupancy_of_complexSecondMomentRate`, `occupiedBurnolWindows_criticalLine_spike_ge`, `occupiedBurnolWindows_le_of_prefixCancelling_secondMoment` | `SubexponentialMollifierLengthAndWindowSpikes` |
| Prime-log and rough floors on and right of the line; credited Jensen budget diverges; single-zero spike; dyadic boundedness ⇒ eventual quasi-RH; cofinal boundedness ⇒ RH | `eventually_integral_normSq_zetaMollified_ge_one_add_log_inv_theta`, `eventually_integral_normSq_zetaMollified_ge_roughConst_div_theta`, `eventually_flowCreditedJensenBudget_ge`, `integral_normSq_zetaMollified_criticalLine_spike_of_zero`, `finite_offLineZeros_beyond_of_dyadic_long_mollifier`, `riemannHypothesis_of_cofinal_long_mollifier` | `TwoSidedThetaMollifierTrap` |
| `D_win` from `V/log V` detection; `L^p` and `log⁺` impossibility at that scale; Barban–Vehov two-length defect at scale `V`; universal subcritical floor and `V log V` disc divergence; Gallagher's `log N` sharp | `logFreeNearLineWindowOccupancy_of_shiftedDefect_div_log`, `fejerDirichletDetector_Lp_defect_le_div_log`, `exists_twoLength_defect_normSq_arbitrary_rate`, `eventually_integral_normSq_zetaMollified_sub_one_ge`, `eventually_discCorridorBound_zetaMollified_ge_mul_log`, `exists_separated_dirPoly_sum_normSq_ge_mul_log` | `DiscCorridorDivergenceAndDetectorSharpness` |
| Proportion one ⇒ clustering and (L); the root model has proportion one, every exponential depth rate, clustering, and no occupancy | `criticalClustering_of_tendsto_xiCriticalRatio_one`, `logMean_tendsto_zero_of_tendsto_xiCriticalRatio_one`, `exists_proportionOne_allRates_model_not_windowOccupancy` | `ProportionHierarchyOfNearLineQuestions` |

## 6. Questions and their status

| Question | Status | Exact content |
|---|---|---|
| **Q1. `100%` critical-scale clustering** | Open. Reduced to Q3 | Q3 implies it at length `exp(o(T))`; no statement at a fixed exponent can carry the reduction; the critical-line proportion `→ 1` implies it |
| **Q2. `D_win`, `D_zero`** | Open. Reduced to a rate or a detector | Excess `K₀/log T` at length `exp(T/log T)` implies `D_zero`, hence `D_win`; that rate needs `log N ≥ log²T/(6K₀) − (4/3)log T`. A holomorphic actual-zero detector with shifted defect `≤ Ce^{−r(σ−½)log V}V/log V` implies `D_win`; the scale is sharp and no polynomial mollifier reaches it. No critical-line proportion and no exponential depth-tail rate implies `D_win`; depth must decay at rate `≍ log log V`. `D_win` fails on the impure mimic, so an input must be locally pure |
| **Q3. Second moment at `T^θ`, `θ → ∞`** | Lower side settled in form; upper side open | Floor `1 + 1/(8+6θ)`, real to `θ ≤ log T/24`, complex to `log N ≤ T^{1/60}`; moment `→ 1` forces `log N/log T → ∞`; local purity necessary; for the linear mollifier a bounded defect is RH. The corpus has a bounded mollified second moment at `θ = 21/50` near the line (`zetaMollifiedMeanSquareGateFrom_selberg_upper`), which gives the off-line moment bound `eventually_offLineMoment_le_selberg_upper`. Classical prediction for the floor: `1 + 1/θ` |
| **Q4. Self-improvement** | False as a class theorem | On Euler products with functional equation (shifted family) the class law is `Θ = 1`. Without functional equation one factor realizes any width. A proof must use the Ramanujan bound and the functional equation together, on which no mechanism exists |
| **Q5. Parity-breaking bilinear input at square-root precision** | None exists among norm statements on sign-stable test classes; the question is restated | Type II norms, Type I weights and prime-polynomial mean values are parity-blind. The parity seen by PNT, the Mertens law and every error law is pole parity. Away from the pole, parity is visible to long integer polynomials (pillar 16), which do not imply the count. The real content is a provable statement with stabilizer inside `𝒬`, other than proximity |
| **Q6. A complex mollifier at length `exp(c log²T)`** | Open; a construction problem | Any normalized complex family with excess `≤ K₀/log T` at length `exp(c log²T)`, `c ≥ 1/(6K₀)`, lands on `D_zero ∧ D_win`. Every polynomial-length and every sub-threshold family is excluded; the Levinson–Conrey optimum is a main-term computation at polynomial length |
| **Q7. Long-mollifier boundedness** | Open; RH-hard in its cofinal form | Dyadic `∫_T^{2T}|ζM|² ≤ CT` with prefix cancellation to `T^{θ₁}`, `θ₁ > ½`, gives depth `< 1/(2θ₁) + ε` for all but finitely many zeros; cofinal `∫_1^T|ζM|² ≤ C_θT^K` for arbitrarily large `θ` gives RH |

**The restated question.** Find an unconditional statement `S`, not defined through `Λ`, with `S(Λ)` provable and
`S(a) ∧ S(a+δ) ⇒ δ ∈ 𝒬`, together with a proof of `S ⇒ Count`; or, in mean-value form, an upper bound for the mollified
second moment at superpolynomial length with the excess the landings require. None is known. The formal obstructions
are pillars 1, 2, 9, 10, 14 and 15 and the necessary-length laws; pillar 16 shows that parity away from the pole does
not supply it; no theorem excludes its existence. By pillar 15 such a statement cannot be a finite system of convergent
linear laws; by the length laws it cannot be a mean value at polynomial length.

## 7. Tools

**Developed.**
- Mean-value normal form on the critical line and the threshold law (`abs_integral_norm_sq_linePoly_sub_le`, `integral_linePoly_le_of_power_bound`, `resonant_second_moment_ge`).
- Laplace profile with decay (`StripDecay`, `cosh_interpolation`) and Gaussian localization at height (`gaussWindow`, `integrated_gauss_inequality`, `exists_center_tail`).
- Floors uniform in the mollifier (`right_floor`, `exists_left_floor`, `eventually_left_floor`) and slices avoiding all zeros (`exists_admissible_slices`).
- Log-integral ceiling from a second moment (`exists_logIntegral_le_of_secondMoment`) and folding of off-line multiplicity (`sum_order_filter_abs_le`).
- Mimic battery: `liouvilleWeight`, `poleCorrectedTwin`, `impureWeight`, `mertensInvisible`, power perturbations, `shiftedWidth`; in the neighbour modules the `rootModel` and the Fejér–Dirichlet detector.
- Sawtooth dictionary and dyadic elimination of the offset (`sawtoothDefect`, `band_of_dyadic`).
- Explicit smallness conditions for the interpolation, so that the exponent may grow with `T` (`LengthSmall`, `eventually_lengthSmall`); their stretched-exponential form for complex coefficients (`le_integral_window_right_of_sq_le`, CDG).
- Partial summation with monotone weights on critical-line polynomials and pointwise bounds on shifted lines (`weightedPoly_eq_abel`, `integral_norm_sq_weightedPoly_le`, `norm_sq_edPoly_shift_le`).
- Selberg integral of a weight and its bridge from the second moment (`selbergIntegral`, `linePoly_eq_logPoly`), resting on `Sieve.integral_Icc_normSq_logPoly_le_window`.
- Gram interpolation at off-line zeros (`gramTest`, `gramForm`, `norm_sq_sum_le_defect_mul`).
- Hermitian analytic trace, Gaussian Cahen–Mellin kernel, divided difference at a zero, disc-corridor superadditivity, `y`-smooth/rough splitting with sharp Mertens (CDG `NearLineLogMean`).

**Used from the corpus.** Littlewood budget and sandwich (`exists_zetaLine_logMean_sandwich`, `exists_zetaLine_littlewood_edge_budget_all_heights`), sharp mean value (`Sieve.dirichlet_meanValue_sharp_window`), mollifier floors (`exists_edPoly_line_logMean_floor`), zero count (`exists_xiZeroCount_close`), Gallagher's identity (`Sieve.gallagher_identity`), the Sobolev bound (`sobolev_pointwise`), three circles (`HTGeometry.norm_le_of_three_circles_center`), Barban–Vehov tails and Mertens' second theorem (`RHTower.Sieve`). Nair integrals and the integrality halves stay in ASRP (`nairIntegral`, `TheIntegralityExponentIsTheZeroWidth`), where square-root integrality in each half is RH, so they are receivers in this language.

**To build.** A mimic battery test harness stating any new input against all weights above; an explicit evaluation of the constants in the complex length laws.

## 8. Traps

1. **Twin failure is not a parity break.** PNT already fails for the twin. Test against `poleCorrectedTwin`.
2. **Precision-faithfulness is cheap.** One pinned functional achieves it at every power (`not_mertensLaw_and_add_smul_powerWeight`). Test the stabilizer.
3. **True + all necessary tests proves nothing.** `Proximity` is the counterexample.
4. **Upper bounds cannot see purity.** Any argument with only upper bounds for `ζ` on lines also proves itself for the mimic. It cannot imply the count, `D_win` or Q3.
5. **Length alone is not parity.** Lengthening raises precision by the law `η < ½ − 1/(2θ)` and leaves prime polynomials parity-blind: those of `λΛ` and `−Λ` agree in mean square through `T²`. Parity away from the pole appears for integer polynomials, in a bound uniform in `N`.
6. **A fixed exponent cannot close anything.** Q1, Q2 and Q6 by second moment need superpolynomial length; the thresholds are exact.
7. **Bounded coefficients matter.** Floors use `|b_n| ≤ 1`. With unbounded coefficients finite windows have no floor (Müntz–Szász, classical), so they answer a different question.
8. **Class theorems.** A self-improvement statement must exclude shifted products and impure factors explicitly. If its proof does not use the Ramanujan bound, it proves `Θ = 1`.
9. **Proportion is not occupancy.** A critical-line proportion tending to one, or any fixed exponential depth-tail rate, gives clustering and not `D_win`: the root model satisfies both and fails occupancy.
10. **Norms do not detect windows.** At scale `V/log V` every `L^p` and `log⁺` defect is attained by a detector occupying `≥ V/12` windows; only the shifted `L²` defect of an actual-zero detector counts.
11. **`∫` body in Lean.** `∫ t in a..b, f t - c` integrates `f − c`. Parenthesize integrals.

## 9. Open research topics

1. The upper side of Q3 at `θ > 21/50`, and any statement at growing `θ`; a complex family at length `exp(c log²T)` with excess `K₀/log T` (Q6).
2. The constant of the floor: `1/(8+6θ)` proved, `1/θ` predicted. The left floor uses only the zero count; the two floors alone, optimized over `a`, stop near `1/(eθ)` by a paper estimate, so reaching `1/θ` needs pair correlation.
3. The exact constant in the length `exp(c log²T)` required by the rate `K₀/log T` (`1/(6K₀)` is necessary), and the law for `log N` beyond `T^{1/60}`.
4. Exactness of the Gram floor: whether the infimum of the defect over all mollifiers equals `sup v*G⁻¹v`, which would identify the closure of the mollified span as a Blaschke multiple.
5. Which statements other than proximity have stabilizer inside `𝒬`. Finite convergent linear systems cannot (pillar 15); the next class is countable systems with a decay condition, or nonlinear laws.
6. Self-improvement inside the Ramanujan class with functional equation: find any mechanism, or a mimic in that class.
7. The rate of growth in `N` of the second moment of the Liouville polynomial at a fixed height, and whether any statement built on holomorphy at zeros can have stabilizer inside `𝒬`.
8. Detectors between scale `V` (Barban–Vehov) and `V/log V` with uniform depth decay: structured, non-polynomial detectors.
9. The depth-tail rate `≍ log log V` as a statement about `ζ`: any unconditional bound of that shape, or a model showing that the near-line ladder admits no further intermediate statement.

## 10. Context

**Uses.** ASRP (classes, count, entry tests, twin), RHTower (mollifier log-mean floors, Littlewood budgets, Selberg upper bound, mean value, Gallagher, Mertens, Barban–Vehov), CDG (clustering TFAE, `D_zero`, `D_win`, shells, Burnol windows, complex length laws, detectors, long-mollifier receivers), HTGeometry (Plancherel, line shifts).

**Relation to other programmes.**
- ASRP names the precision classes and the tests. APR decides what can enter them.
- CDG states the near-line questions and holds the landings and the complex-coefficient laws. APR gives the second-moment route to them and its limits.
- ZCG and the heat routes are sign-free readers: they read a configuration and produce no inequality. The sharp-location theorem of ZCG converts window positivity into location and needs positivity as input.
- ADO (Diophantine repulsion) is an amplifier: finite Euler carriers, integral pure carriers and almost every value of `ζ` repel polynomially, and uniform repulsion along a real path transports reality; it produces no inequality for `Λ`, and polynomial repulsion of `ζ`'s zeros bears on no real part.
- CHT, FADF, SWC, CSTW and the Hodge-type programmes are the receiver programme: they state the exact target on each window and supply sign once given production. The two programmes meet at the count.
- FFP and WTZ work at finite level, where every width is consistent. APR's aperture and length statements are why they cannot close alone.

**Place in the whole.** The producer programme alone can close RH, because the count at square-root precision is RH and a cofinal long-mollifier bound is RH. APR establishes that the classical tools cannot do so by themselves, quantifies the length every landing needs, and locates the missing content in one sentence: a provable non-tautological statement with stabilizer inside `𝒬`, or an upper bound for a long mollified second moment.

## 11. Success and contribution criteria

**The programme succeeds if** it proves any of: a non-tautological statement with stabilizer in `𝒬` that implies the count; Q1, Q2 or Q6; the second-moment law at growing exponent; a detector at scale `V/log V`. It also succeeds in part with a theorem showing that no statement in a named class can have stabilizer in `𝒬`, or that no family in a named class reaches a landing.

**A contribution must:**
1. be unconditional, with every analytic input proved. An implication from a named law must state that law and must be shown not to be an equivalence with RH in disguise, unless it is labeled one;
2. state the outcome on the mimic battery: twin, corrected twin, `Λ + εn^{−η}`, `Λ + mertensInvisible`, impure weight, shifted width, root model;
3. say which entry tests it passes and name its stabilizer, or a perturbation in it; for a mean value, state its length and compare it with the necessary-length laws;
4. for a limit theorem, name the weight, configuration or detector at which the tool stops, and extract the sharp positive statement;
5. improve a pillar, answer a question of section 6, or add a tool used by another module. A restatement of a corpus equivalence is not a contribution.
