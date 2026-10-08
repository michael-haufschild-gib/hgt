# WP06: uniform cheap strong Xi-profile transfer

- **ID:** WP06-C8
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** [WP06 proof register](../../../reports/weil-work/results/06-deficit/PROOF.md)
- **Statement attacked:** At fixed physical aperture, every spectral shift of Xi can be approximated with coefficient variation at most exp N and squared L² error o(1/log N).

## Goal

Transfer the anchored spectral cancellation witnesses into actual Xi-divisible physical-translate packets with affordable coefficients. The uniform strong-norm shortcut fails. The finite-moment construction and transfer of the particular moving witnesses remain open.

## Gates

- [x] Exact packet class, aperture, coefficient variation and physical L² error specified.
- [x] Dependency-closed paper proof of the full stability law and explicit cost inversion.
- [x] Target-only build and final unchanged direct Lean audit passed.
- [x] Four public theorem axiom/API audits passed; umbrella wired.

## No-go closure

- **Killing mechanism:** Every finite physical translate preserves each real Xi zero. Modulation by a real Xi zero fills that zero with the nonzero central value. A finite-interval L² estimate plus the actual theta tail turns this mismatch into a cost barrier.
- **Strongest positive survivor:** Uniform cutoff stability `h≤sqrt(2L)E+2B(V+1)exp(−exp(2(L−a)))` for every L>0. Consequently `h²≤8(a+log(N+K))E²` when V≤exp N, and every packet satisfies E>0 and `exp(exp(h²/(8E²)−a)−K)≤V+1`. Here h=|XiC(0)|; B>0 and K>1 are universal. Both aperture and complete coefficient variation remain explicit.
- **New insight:** Density without a quantitative cost cannot justify this uniform transfer. Zero preservation must be retained when designing an affordable witness. Finite quadratic moment transfer may avoid the strong-norm mismatch; derivative packets already preserve the zeros exactly.
- **Status:** CLOSED for the stated uniform shortcut. Four exact Lean theorems in namespace `RHTower.WeilWorkDeficitApproximation`: `paperFT_error_at_zero`, `zero_approximation_cutoff_bound`, `exponential_budget_error_bound`, `double_exponential_variation_bound`. Module `WeilWorkDeficitXiApproximationCost`; target build, final direct audit, and public axiom/API audit all exit0. Only `propext`, `Classical.choice`, `Quot.sound`. The spectral Plancherel restatement is paper-only.
- **Limits:** No simplicity assumption, no matching upper bound, no sharpness claim. This does not prove a quantitative mismatch for the particular M-dependent Bernoulli shifts and does not refute C7, C9 or C10. The actual real-zero domain is nonempty by the corpus's unconditional Hardy theorem.
- **Novelty:** Classical cutoff mechanism specialized to the actual kernel. External scientific novelty is not established.

## Log

- 2026-10-07 — Full positive stability law formally closed before retiring the uniform shortcut. Main spectral-deficit goal remains ACTIVE and UNSOLVED.
