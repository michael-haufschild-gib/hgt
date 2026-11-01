# Finite-field approximation of ξ: exact failure and surviving problem

- **ID:** finite-field-euler-approximation-route-audit
- **Stage:** 5-failed, **literal Euler-product branch only**.
- **Type:** FALSIFIED branch; BRIDGE for centered numerators.
- **Source:** [obstacles summary, §2.4](../../../reports/review-0111/obstacles-summary.md#24-a-wildly-different-route).
- **Verdict:** no direct Euler-product transport of Deligne by a vanishing mesh. Approximation by explicitly centered curve numerators remains open; no arithmetic producer was found in the audited sources.

## Exact killing mechanism

For a smooth projective geometrically connected curve over `𝔽_q`, write
`Z_C(t)=P_C(t)/((1-t)(1-qt))`. Its nontrivial reciprocal roots have modulus `√q`, and its ordinary Euler product has abscissa one in `u`, where `t=q^{-u}`. These geometric inputs are classical, not newly formalized here. For general smooth projective varieties Deligne gives weight-dependent lines, not a single common zero line. See [Deligne, Theorem 1.6 and §1.5](https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf).

For real `a>0`, put `u=as+b`. Centering the curve's zero line gives `a/2+b=1/2`, hence

`σ_E=(1-b)/a=(1+a)/(2a)`, and `(σ_E-1/2)(a log q)=(log q)/2`.

Thus `a log q → 0`, with `q≥2`, forces `σ_E→∞`. An explicit version: for `M>1/2`,

`a log q < (log 2)/(2M-1)  ⇒  M < σ_E`.

Keeping `σ_E≤1` instead forces `a≥1`. For dimension `d` and a centered weight `w`, the exact identity is
`(σ_E-1/2)(a log q)=(d-w/2)log q`.

**Scope:** ordinary positive Euler products of the rescaled curves cannot supply convergence on a fixed right half-plane. Clearing poles or taking pure factors changes the analytic object and survives this obstruction. This is not a no-go for all geometric limits.

## Strongest positive survivor

Let `h>0`, and pair the unitarized curve eigenvalues as `e^{±iθ_j}`. Fix `x₀=3/2`. The explicit normalization

`F(z)=exp(gh(z-x₀)) P_C(q^{-1/2}exp(-hz))/P_C(q^{-1/2}exp(-hx₀))`

equals

`∏_{j=1}^g (cosh(hz)-cos θ_j)/(cosh(hx₀)-cos θ_j)`.

The denominators are strictly positive. Each numerator factor has nonnegative even Taylor coefficients because `1-cos θ_j≥0`. Consequently `|F(z)|≤F(R)` for `|z|≤R`. For any sequence of such products, pointwise convergence for every real `R>1/2` bounds their values at a larger real radius, hence bounds the sequence on each complex disk. No genus bound or separate zero-count estimate is needed.

The geometric pairing uses classical Weil theory. The following analytic statements are proved for explicit finite products, with no geometric realization assumption:

- `norm_centeredWeilProduct_le`: exact radial bound, independent of degree.
- `centeredWeilProduct_bounded_disks_of_real_convergence`: real-half-line convergence bounds every disk.
- `centeredWeilProduct_locally_bounded_of_real_convergence`: local boundedness in Vitali's form.

Their paper proof is the triangle inequality applied to the cosh power series, multiplication of the resulting bounds, and boundedness of each convergent real sequence. Lean follows exactly that proof.

**New insight for this proposal:** after canonical centering, real-axis approximation alone is the remaining analytic target. Strip boundedness is automatic. This is an elementary application of positive coefficients, not a claim of new scientific knowledge.

## Open core and attacks

**[OPEN CORE]** Construct curves, `h_n→0`, and the explicit normalizations above from arithmetic, and prove
`F_n(R)→ξ(1/2+R)/ξ(2)` for every real `R>1/2`. The radial bound, Vitali and Hurwitz would then imply RH. No theorem here proves this convergence or constructs these curves.

- Matching Euler factors and matching analytically continued numerators are different requirements. The former is killed above; the latter is not supplied by Deligne.
- The original “effective dimension tends to zero” argument is not a proof: the shift reweights the point contributions, and point-count errors depend on genus. Fixed-curve asymptotics cannot be used uniformly over an arbitrary growing-genus family.
- Frobenius equidistribution supplies spectral flexibility, not selection of ξ. [Katz–Sarnak, §3](https://web.math.princeton.edu/~nmk/old/katzsarnakarticle.pdf) studies limits of Frobenius conjugacy classes. It gives no ζ-specific convergence theorem of the required form; fitting a target's zero list would not produce an independent RH proof.
- The `𝔽₁` theme is established: [Connes–Consani, §2](https://arxiv.org/html/0903.2024) recovers completed zeta through a counting distribution and a formal `q→1` construction. That is not a sequence of ordinary finite-field varieties inheriting Deligne's zero constraint.
- [Zykin, §§3–6](https://arxiv.org/html/1310.6107) studies normalized logarithmic limits and zero distributions in families. Such limits do not identify the entire ξ function by compact-open convergence.
- [Ax, Theorems 8–9](https://people.maths.ox.ac.uk/bays/mtpsf/Ax68.pdf) gives first-order transfer to pseudofinite fields. Analytic convergence and identification with ξ require additional arguments; “only bounded genus transfers” is not the precise model-theoretic statement.
- Vitali needs a common connected open domain and an interior uniqueness set. Bounds inside the open critical strip alone do not join it to `Re s>1`. The centered entire products avoid this domain defect.
- Uniform zero counts do not control normalization: `exp(nz²)` is zero-free, even, and one at zero, yet locally unbounded. The explicit radial bound is what resolves this for the stated products.

## Corpus and Lean status

Searches covered normal/real-zero approximants, finite-field spectra, exact finite realizations, prime-length rigidity, and nonnegative Taylor bounds. Statements were read in source.

- `RHTower/XiCRealZeroVitaliBlowup.lean`: `riemannHypothesis_of_XiC_vitali_realZero_approximants` and `exists_local_norm_blowup_of_not_riemannHypothesis_of_XiC_pointwise_realZero`. The receiver and its obstruction already exist.
- `ArithmeticResonanceTheory/OverFiniteFieldsTheOddPartIsSpectral.lean`: matrix/eigenvalue, period and purity calibration. It does not formalize Deligne or construct curves.
- `ArithmeticResonanceTheory/TheArchimedeanPlaceForbidsFiniteVirtualRealizations.lean`: `riemannZeta_ne_virtualRealization` excludes exact equality with a finite virtual realization, not limits.
- `ArithmeticResonanceTheory/ARealizationOfZetaIsPrimeLength.lean`: `isPrimeLength_of_realization` assumes exact equality on a half-plane; it cannot be applied separately to merely approximating functions.
- New leaf `ArithmeticResonanceTheory/TheEulerDomainOfACenteredApproximation.lean`: four exact parameter theorems, including the explicit mesh threshold. No unproved geometric hypothesis is represented as a formalized theorem.
- New leaf `ArithmeticResonanceTheory/CenteredWeilProductsAreBoundedByTheirRealValues.lean`: the radial bound and automatic local boundedness for the displayed finite products. Both leaves pass direct Lean checks. Their audited results, and the existing Vitali receiver/blow-up theorem, depend only on `propext`, `Classical.choice`, `Quot.sound`.

The literal branch is retired. Its positive survivor is formalized analytic control; arithmetic production and ξ-selection remain open. This audit moves no RH frontier and establishes no novel result beyond the cited theories.
