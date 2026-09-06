# Recovery gaps: a concrete obstruction candidate

**Outcome, 6 September 2026:** the stronger positive-moment conjecture now has a reproducible numerical counterexample candidate, expressed by a canonical degree-17 polynomial. The sign is not proved exactly. All numerical work ran on the authorized Runpod, `/root/chronological-recovery-gaps`, with up to 24 workers and one BLAS/OpenMP thread per worker. Scripts and JSON outputs are downloaded here. No result is a Lean proof certificate.

The actual gaps δ_k come from the weighted polynomial problem in [the compact research card](../../../1-in-progress/chronological-recovery-moment-problem.md). The questions are whether δ_(k+1)²≤δ_kδ_(k+2) for all k and whether γ_k=(δ_k/δ_0)² is a positive moment sequence. The second would imply the first, but its numerical obstruction does not refute the first.

## Exact witness formula; exploratory evaluation

Set s=3/10000 and

`p(x)=Σ_(j=0)^17 c_j x^j`, `c_j=(-1)^j binom(17,j) binom(18+j,j)/(j+1)`.

This is P_17^(1,0)(1−2x)/18, the normalized Jacobi polynomial; the coefficient identity follows from [DLMF 18.5.7](https://dlmf.nist.gov/18.5.E7). Its selection requires no numerically fitted polynomial coefficients.

The computed functional value is

`Σ_(i,j=0)^17 c_i c_j s^(−i−j) γ_(i+j) ≈ −0.000243400090218270819`.

Without normalization by δ_0², it is approximately −0.00000398195275827065. If the exact value is negative, γ cannot have any positive representing measure: this sum would equal the integral of p(x/s)². Only gaps δ_0,…,δ_34 are involved. The rational scale removes dependence on the numerical evaluation of the potential-theory constant ρ.

`witness_probe.py` independently recomputes the first 35 gaps at 230 decimal digits using monomial coefficients and contact points, rather than the factor/logarithm equations used to discover them. Contact heights are fixed to alternating ±1. Maximum relative disagreement with the earlier 140-digit gaps was about 6.9×10^−135. All coefficient-coordinate equation residuals were below 10^−180. The displayed negative value is stable across these two coordinate systems. These are numerical consistency checks, not certified error bounds for the exact minimizers.

## Why the earlier positivity tests missed it

For the scaled sequence γ_k/ρ^(2k), the 17×17 unshifted Hankel matrix is numerically positive, while the 18×18 matrix has smallest eigenvalue approximately −9.57×10^−26. The first-entry Schur complement is about −0.00041287; its larger magnitude helps expose the conditioning issue. Once-shifted matrices remain positive through the tested size 32.

All 2080 available Hausdorff finite differences of the 64 scaled moments are positive. There is no contradiction: checking Bernstein-basis positivity only through that finite degree is weaker than checking every nonnegative polynomial of that degree. A nonzero square with interior zeros cannot itself have all nonnegative Bernstein coefficients, since each Bernstein basis polynomial is positive in the interior. The full infinite Hausdorff criterion gives positivity on squares through approximation, for example by strictly positive perturbations. The earlier finite triangles alone gave misleadingly favorable evidence.

The unsquared scaled gaps already have a negative 10×10 unshifted Hankel test; their once-shifted sequence also fails at larger size. Thus the evidence does not support a model whose sole defect is a negative atom at zero. Logarithmic differences first become negative at order 24, excluding the tested route through infinite divisibility at a numerical level.

## Retained calculations

| Script → output | Purpose and scope |
|---|---|
| minimax_probe.py → minimax-results.json | Degrees 1–8 on 1001/4001/12001 grids; Chebyshev-coordinate linear programs and contact refinement. |
| refine_probe.py → refined-results.json | 70-digit contact solve and potential-theory constant. Corrected a failed double-precision degree-eight refinement. |
| moment_tests.py → moment-tests.json | Initial eight-moment Hausdorff triangle. |
| factor_probe.py → factor-results.json | Degrees 1–32, 110-digit factor-coordinate Newton solve; full tested moment-matrix spectra. |
| structure_probe.py → structure-results.json | Unsquared, logarithmic and Bernstein-function routes. |
| extension_probe.py → extension-results.json | Degrees 1–64 at 140 digits, with analytic block elimination in Newton's method; moment tests through matrix size 32. |
| witness_probe.py → witness-results.json | Independent coefficient-coordinate verification and exact-form degree-17 square witness. |
| diagnostics_probe.py → diagnostics-results.json | The size-17/18 sign transition, all 2080 finite differences, and all 63 successive gap ratios (increasing in this range). |

The host reported 32 CPUs, NumPy 1.24.4 and SciPy 1.10.1. Small postprocessing jobs were serial; expensive independent minimax solves used 24 workers. Runs completed; no worker is intentionally left running.

The factor-coordinate method uses physical roots 0<d_1<⋯<d_m<1 and

`F(c)=c^m ∏_j(c−d_j)(2−c−d_j)`.

On each zero-free interval, `(log|F|)''=−m/c²−Σ_j[(c−d_j)^−2+(2−c−d_j)^−2]<0`. There is exactly one peak in every interval before the last root; after the last root the derivative remains positive up to c=1. Hence interlacing, equal contact heights and the endpoint account for the global minimax shape in the exact equations. This avoids relying on a dense grid, but approximate solutions are still not exact certificates.

## Mathematical consequences and next step

The independent [exponential-rate proof](../../chronological-recovery-exponential-rate.md) gives lim δ_k^(1/k)=ρ≈0.017360042099820883. Its equilibrium measure describes approximation roots, not the sought gap moments. The old JSON field `physical_contact_limit` only records 1−cos θ; the initial computation did not prove contact convergence.

Investigating the obstruction also produced a [paper proof of uniform block growth and the exact spectral disc](../../chronological-recovery-uniform-spectrum.md). It uses a correction of the forbidden penultimate coefficient of extremal polynomials to obtain δ_(k+d)≤[t_d+(d/4)t_(d−1)]δ_k for every k,d. Consequently the actual multiplier's complex spectrum is the closed disc of radius ρ, independently of moment positivity. This result is not yet formalized.

**Next hard step:** prove the exact sign of the displayed finite square functional, or find a structural proof of the same obstruction. The global log-convexity question remains open. Do not turn the decimals or contact residuals into Lean assumptions, claim a proved no-go, or return to scanning more degrees without a new mathematical reason.
