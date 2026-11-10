# Missed opportunities: exact outstanding statements

- **Stage:** 1-in-progress
- **Source:** `docs/reports/review-0911/fable.md`, §11.
- **Scope:** solve and unconditionally formalize every mathematical task in §11;
  existing criteria alone do not discharge their analytic inputs.

## Required results

| Item | Required result | Status |
|---|---|---|
| 11.6 | Width and two-sided log-square prime-window criteria; signed-deletion proof | Complete: `signed-deletion-for-log-square-windows.md` in `3-formalized`; all signed helpers and prime transfers passed direct and axiom audits. Width, absolute, and quasi-RH criteria in `PrimeLogSquareWindows.lean` also audited |
| 11.6 | Quasi-RH ∨ AAL; quasi-RH iff tail abscissa < 1; consequences under ¬AAL | Complete: `quasi-rh-is-a-tail-law.md` and `arithmetic-bounds-without-the-abscissa-law.md`; includes the stronger tail-based heavy-return exponent |
| 11.6 | Exact simple near-line census alternatives at 70%, 75%, 80% | Complete: `near-line-census-at-seventy-seventy-five-eighty-percent.md`; existing 70% and 75%, new 80%, all audited |
| 11.1 | Halving descent connected to one-eigenform detection; precise remaining Shimura nonvanishing; static 2/3 boundary | Complete assembly: `halving-descent-and-shimura-obstruction.md`. Sharp decay alone still requires the stated Shimura nonvanishing |
| 11.1 | Shimura nonvanishing for one eigenform at every relevant nonhalving zero | Open; one eigenform for each zero does not give one eigenform for all zeros |
| 11.2 | Precise fixed-part/isolation obstruction for twists and covers, with positive survivor | Revised report marks paper/source theorem; scope and Lean audit still require verification |
| 11.3 | Compact-surface Selberg calibration with finitely many exceptional real zeros | Open; distinguish nontrivial zeros from other Selberg zeros |
| 11.3 | Lagarias–Suzuki line law as a calibration for sign routes | Complete: `lagarias-suzuki-sign-calibration.md` in `3-formalized`; exact non-real line law and index-one real exception in both ledgers; direct and axiom audits passed |
| 11.3 | Exceptional-character filter for sign-free producers | Open assembly from upper/lower Dirichlet trace laws |
| 11.4 | Short-interval multiplicative cancellation and averaged correlations | Open; published statements and proof dependencies require audit |
| 11.4 | Carlitz–Goss RH | Open; `carlitz-goss-rh-from-greedy-compositions.md` states the target over `𝔽_p((T⁻¹))` for every prime power and every `p`-adic parameter, with exact combinatorial and analytic dependencies |
| 11.4 | Bilinear mollified-moment bounds past length T^(1/2) | Open; precise theorem and range require audit |
| 11.4 | Stepanov bounds for Heilbronn sums and Fermat quotients | Open published input |
| 11.4 | Effective lower bounds for linear forms in three logarithms | Complete for `log(-1), log p, log q`: `three-logarithms-minus-one-and-two-primes.md` in `3-formalized`, direct and axiom audits passed. The affine real form needed by the upper-side construction remains open |
| 11.5 | Audit recommended route closures, retain exact positive survivors | In progress; audited `frobenius-order-at-an-integer-point.md` in `3-formalized` refutes unrestricted descent of evaluated δ-jets and proves the exact compatibility law. Ideal-power restriction remains valid. The exact multinomial carry identity and `carryTerm(N)/N → 2 log 2−1>0` passed direct and transitive axiom audits; broader family closure remains open |
| 11.6 | Logarithmic prime-window criterion at radius `32 log(T+2)` | Complete existing criterion: `PrimeLogarithmicWindows.lean`, formalized card `b130-logarithmic-windows-by-positive-source-repair.md`; independent direct audit passed, all twelve axiom checks standard only |
| 11.6 | Coupled-orbit density row `4 regularMean = −2 gammaHardyPhaseRate(0)−(log(4π)+γ)` | Complete existing theorem `ArchimedeanConstantBridge.four_mul_regularMean_eq`; owning module directly checked, standard axioms only |
| 11.6 | Census covariance ceiling `4π(1−0.67250071)` | Complete: `Census/SourceCovarianceBaseline.lean`; direct and axiom audits passed |
| 11.6 | Exchange rates `H*(4)=7/10`, `λ*=10/9`, Frobenius constant `13/10` at `4/3` | Complete: `TransThresholdPairCorrelation/SeventyPercentExchangeRates.lean`; direct and axiom audits passed. See formalized card `census-covariance-and-seventy-percent-exchange.md` |
| 11.6 | Graded recurrence from Guth–Maynard zero density | Complete: `graded-self-recurrence-from-zero-density.md` in `3-formalized`; separated-return bound on `[0,T]`, direct and transitive axiom audits passed |
| 11.6 | Upper side at degrees `p^a q^b` without attainment | Open; `two-prime-upper-bound-and-inhomogeneous-frequency.md` identifies the actual frequencies `(1, log p, log q)`. The reported replacement by `log(-1)` needs justification |
| 11.6 | A65 two-prime local criterion | Complete: `two-prime-local-window-criterion.md` in `3-formalized`; direct and transitive axiom audits passed |
| 11.6 | A67 dominant-ordinate divergence | Complete: `dominant-ordinate-forces-current-divergence.md` in `3-formalized`; grouped Gamma mass handles multiplicities, full divergence limit; direct and axiom audits passed |
| 11.6 | A50 finite-stratum laws | Shifted Jensen implication and cosine RH ⇔ ZAL under its finite-stratum law are audited; `finite-stratum-laws-for-cosine-and-shifted-jensen.md` in `3-formalized`. The stronger cosine implication still lacks finiteness near zero |

## Existing anchors

- `SurfaceOfSpecZ/ScaleLocality/PrimeLogSquareWindows.lean`:
  `riemannHypothesis_iff_prime_logSquare_windows`.
- `RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean`:
  `critical_proportion_or_simple_offLine_near_line`.
- `RHTower/Zeta23SimpleOffLineNearLine.lean`:
  `three_quarters_or_simple_offLine_near_line`.
- `ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean`:
  `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`.

The new `ArithmeticWeightTheory/TheZeroMotiveIsTheFixedPartOfEveryArithmeticFamily`
packages null-fibre moments, vanishing masses, a product-positivity
counterexample, and an RH-equivalent gauge-cover moment condition. Its
statement does not quantify over every arithmetic family or every derived
inequality. These precise results do not yet justify the universal route
closure in §11.2; its module-level description is stronger than its theorem.

No item is complete until its exact statement has a dependency-closed Lean proof,
direct `lake --old env lean` audit, and transitive axiom audit.

## Published inputs: precise targets

- [Matomäki–Radziwiłł, Theorem 1](https://arxiv.org/html/1501.04585):
  uniform comparison of short and long averages of real multiplicative
  functions bounded by one, for `2 ≤ h ≤ X`, with an explicit exceptional-set
  bound. The revised report identifies a balanced-fibre Möbius theorem for
  every `h→∞`, `h≤√x`. Its precise Lean range requires verification;
  ordinary integer-start intervals for general bounded multiplicative
  functions remain distinct. The fibre theorem does not discharge §11.4.
- [Matomäki–Radziwiłł–Tao](https://arxiv.org/abs/1503.05121):
  the correlation target includes the absolute values:
  `Σ_{h≤H}|Σ_{n≤X} λ(n)λ(n+h)| = o(HX)` for `H→∞`, `H≤X`.
  Unmodulated short-interval cancellation alone does not supply this;
  the published argument also proves uniform additive Fourier cancellation.
- [Sheats](https://arxiv.org/abs/math/9801158): Goss zeta for `𝔽_q[T]`,
  for every prime power `q`; not the complex Hasse–Weil zeta of a curve.
- [Bettin–Chandee–Radziwiłł, Theorem 1](https://www.math.mcgill.ca/radziwill/BCR.pdf):
  the smoothed twisted second moment for arbitrary divisor-subpower
  coefficients of length `N = T^θ`, `θ < 17/33`, with error
  `O(T^(3/20+ε) N^(33/20) + T^(1/3+ε))`. Its Kloosterman-fraction estimate
  must be proved, not supplied as an assumption. Applicability to the fourth
  Gram moment is a further theorem, not a consequence of the shared word “bilinear”.
- [Selberg spectral zeros](https://www.cambridge.org/core/journals/nagoya-mathematical-journal/article/on-the-distribution-of-zeros-of-the-derivative-of-selbergs-zeta-function-associated-to-finite-volume-riemann-surfaces/D00CFAABD97A4F9082CF43296184B4DF):
  for a compact hyperbolic surface, strip zeros satisfy `s(1−s)=λ`.
  The corpus's `SelbergSpectralParameter` proves the parameter algebra;
  `SelbergExceptionalCompactModel` realizes a complementary-series
  representation, not a compact surface with its geodesic Euler product.
  The geometric realization and Selberg-zeta identity remain necessary.
