# Infinite decomposition of the mixed Euler-deletion source

- **ID:** EDQ-INFINITE-DECOMPOSITION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), [BRIDGE]
- **Source:** [fixed statement and paper derivation](../1-in-progress/euler-deletion-growing-modulus-decomposition.md)
- **Statement:** For `1/2 <= Re(s) < 1` and every positive integer `p`, the actual ordered mixed sum equals the full quadratic/amplitude/boundary/remainder decomposition.

## Exact statement

Write `sigma=Re(s)`, `Z=zeta(s)`, `c_p=p^(1-s)`, and `S_N=sum_(n=1..N)n^(-s)`. Define

`T_p=lim_(N->infinity) sum_(k<N)[S_k-c_p S_floor(k/p)-(1-c_p)Z](k+1)^(-conj(s))`,

`R_s(n)=S_n-zeta(s)-n^(1-s)/(1-s)-(1/2)n^(-s)`,

`W_p=c_p sum_(n>=1)n^(-s)R_conj(s)(pn)`.

Then

`T_p=(c_p-1)|Z|² + zeta(2 sigma-1)/(1-conj(s)) (p^(2-2 sigma)-1)`

`    + B_sigma(p) + W_p-W_1`,

where `B_sigma(p)=(1/2)(p^(1-2 sigma)-1)zeta(2 sigma)` for `sigma>1/2`, and `B_(1/2)(p)=-(1/2)log p`.

The ordered limit exists at every ordinary cutoff. The `W_p` series is absolutely convergent. These are proved conclusions, not assumed analytic inputs. Unit deletion gives `T_1=0` exactly. No primality or zeta-zero assumption is required.

## Lean certificate

Namespace: `RHTower.DeletionMixedRefinement`.

| Claim | Module | Theorem |
|---|---|---|
| Actual remainder bound | `EulerDeletionPowerSumRemainder` | `norm_powerSumRemainder_le` |
| Weighted remainder decay | same | `tendsto_powerSumRemainder_mul_cpow` |
| Absolute remainder convergence | same | `summable_norm_remainder` |
| Exact finite cancellation | `EulerDeletionMixedDecompositionFinite` | `mixedPrefix_decomposition_with_error` |
| Endpoint error decomposition | same | `endpointError_decomposition` |
| All ordinary cutoffs converge | `EulerDeletionInfiniteDecomposition` | `tendsto_mixedPrefix` |
| Full infinite equality | same | `infiniteMixed_eq_decomposition` |
| Strict-right / critical branches | same | `infiniteMixed_eq_strict`, `infiniteMixed_eq_critical` |
| Literal conjugate-exponent series | same | `infiniteRemainder_eq_conjugate_exponent` |
| Unit-deletion boundary case | same | `infiniteMixed_one` |

The main analytic estimate is `|R_s(N)| <= |s(s+1)|/(Re(s)+1) N^(-Re(s)-1)` for `Re(s)>-1`, `s!=1`, and `N>=1`. It comes from the actual centered Bernoulli-tail representation. Subtracting unit deletion isolates two power-sum differences and a terminal error. Retaining the half endpoints cancels the otherwise persistent critical-line constant. The harmonic dilation limit supplies the logarithm; finitely many residue classes control incomplete cells.

## Verification

Scratch checks and the published main source passed `lake env lean`. Each of the three leaf modules passed its serialized final `LEAN_NUM_THREADS=1 lake build --old <module>` audit. All three are imported by `GaloisForLFunctions.RHTower`; no full or umbrella build was run.

A scratch `#print axioms` audit of all 55 public declarations reports only `propext`, `Classical.choice`, and `Quot.sound`. No new axiom, proof placeholder, or computational certificate is used. No numerical experiment was needed. The corpus index was refreshed and retrieves the final theorem.

Global `scripts/formal_tools.py lint --check-generated` detected an unrelated new shared-tree module, `GaloisForLFunctions.HTGeometry.DigammaMittagLeffler`, missing from its own umbrella, plus existing large-file warnings. The decomposition's three modules are reachable; this unrelated module was not edited. Global lint success is not claimed.

## Scope for further research

This closes the frozen infinite-decomposition [BRIDGE]. It does not establish an arithmetic identity forcing its remainder to vanish, nor an RH implication. The sharper `1/12` remainder expansion, the separate formula for `Re W_1`, and the growing-modulus/bounded-correction consequences remain paper results in the source card. They must not be inferred from the Lean certificate without formalizing their further estimates.
