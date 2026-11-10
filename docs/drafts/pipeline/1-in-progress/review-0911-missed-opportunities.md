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
| 11.3 | Lagarias–Suzuki line law as a calibration for sign routes | Existing theorem; calibration audit open |
| 11.3 | Exceptional-character filter for sign-free producers | Open assembly from upper/lower Dirichlet trace laws |
| 11.4 | Short-interval multiplicative cancellation and averaged correlations | Open; published statements and proof dependencies require audit |
| 11.4 | Carlitz–Goss RH | Open; exact field and zeta statement require audit |
| 11.4 | Bilinear mollified-moment bounds past length T^(1/2) | Open; precise theorem and range require audit |
| 11.4 | Stepanov bounds for Heilbronn sums and Fermat quotients | Open published input |
| 11.4 | Effective lower bounds for linear forms in three logarithms | Open published input; distinguish homogeneous and inhomogeneous bounds |
| 11.5 | Audit recommended route closures, retain exact positive survivors | Open; recommendations are not mathematical proofs |
| 11.6 | Logarithmic prime-window criterion at radius `32 log(T+2)` | Other active work supplies kernel/filter infrastructure; criterion requires audit |
| 11.6 | Coupled-orbit density row `4 regularMean = −2 gammaHardyPhaseRate(0)−(log(4π)+γ)` | Open assembly |
| 11.6 | Census covariance ceiling `4π(1−0.67250071)` | Open assembly; existing ceiling `4π/3` |
| 11.6 | Exchange rates `H*(4)=7/10`, `λ*=10/9`, Frobenius constant `13/10` at `4/3` | Open assembly |
| 11.6 | Graded recurrence from Guth–Maynard zero density | Open assembly; returns must be one-separated and numerous enough |
| 11.6 | Upper side at degrees `p^a q^b` without attainment | Open; effective inhomogeneous three-logarithm input |
| 11.6 | A65 two-prime local criterion, A67 dominant-ordinate divergence, A50 finite-stratum laws | Open assemblies |

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
