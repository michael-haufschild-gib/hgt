# Cleared theta Hankel kernel versus the raw odd Gram matrix

**Exploratory diagnostic, not a proof certificate.** All matrix calculations ran on the authorized Runpod. No computed number is used in Lean. Inputs retain finite shell and integration cutoffs; the six-shell result is not an infinite-source theorem.

## Question and outcome

Can the logarithmic Hankel form, after clearing its two Xi denominators, be a positive contraction relative to the literal odd-monomial theta Gram form?

Write `μ_j=m_j/m_0` for the normalized raw even moments. The compared matrices are

`B⁺_ij=2Σ_(k≤min(i,j))(i+j+1-2k)μ_(i+j+1-k)μ_k/((2(i+j+1-k))!(2k)!)`,

`D⁺_ij=μ_(i+j+1)/((2i+1)!(2j+1)!)`.

`D⁺` is a positive raw-source Gram matrix. The first rows of both matrices agree, giving an exact generalized eigenvector of eigenvalue one. The question concerns the other eigenvalues, particularly their lower signs.

| Shell cutoff | Degree | Least generalized eigenvalue of `B⁺/D⁺` | Greatest |
|---|---:|---:|---:|
| 1 | 3 | −7.0071790896e−8 | 1 |
| 1 | 12 | −1.6891604865e−5 | 1 |
| 2 | 12 | −6.0907585891e−19 | 1 |
| 3 | 12 | +1.2447072251e−19 | 1 |
| 6 | 12 | +1.2447072263e−19 | 1 |

The six-shell approximation has all tested generalized eigenvalues in `(0,1]` through degree 12. The one- and two-shell counterexamples to the lower sign retain the tested upper bound. Therefore upper domination alone supplies no positivity producer. No positive lower constant uniform in degree is established.

## Method and independent verification

`gram_comparison.py` reuses the archived `raw_atoms` arrays in [the earlier source computation](../theta-all-degree-source-2026-09-06/REPORT.md). It performs no new quadrature. Four shell cutoffs are analyzed in separate processes, with one native math thread per worker.

For every block, it independently generates logarithmic moments from the scalar recurrence and verifies `B⁺=S T H Tᵀ S`, where `T` is the lower triangular coefficient matrix of `F(q)=Σ(-1)^j μ_j q^j/(2j)!` and `S_ii=(-1)^i`. Positive diagonal scaling and Cholesky whitening of `D⁺` yield a symmetric eigenproblem. Witness vectors and their separate `B⁺` and `D⁺` values are retained in the JSON outputs.

- `gram-comparison-results.json`: 130-digit matrix arithmetic, archived 160-digit direct-density input, shell cutoffs 1, 2, 3, 6.
- `gram-comparison-ward-results.json`: 190-digit matrix arithmetic, independent archived 220-digit Ward input, shell cutoffs 1, 2, 3.
- `gram-comparison-validation.json`: all stored 60-digit eigenvalues agree for shared cutoffs and degrees 1–12. Maximum congruence residuals are approximately `4.213e−136` and `3.028e−196`, respectively.

Reproduction on the Runpod, from the directory containing the earlier raw data:

```sh
python3 gram_comparison.py direct-density-results.json
python3 gram_comparison.py ward-high-precision-results.json --precision 190 --output gram-comparison-ward-results.json
```

## Mathematical consequence and limitations

Literal equality `B⁺=D⁺` is independently ruled out by a symbolic complete-source proof: consecutive raw theta moment ratios tend to infinity, and consequently `D⁺_(1,n+1)>B⁺_(1,n+1)` eventually. See [the precise failed candidate and positive survivor](../../../5-failed/theta-literal-odd-gram-identity.md). That proof uses no calculation in this folder.

The positive-contraction candidate survives these finite diagnostics. Constructing its positive operator from the complete arithmetic density, or deriving the lower quadratic-form bound by another mechanism, remains the missing mathematical producer. The recorded spectra prove neither RH nor its negation.
