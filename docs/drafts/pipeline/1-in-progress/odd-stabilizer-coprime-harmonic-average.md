# Uniform coprime-harmonic error averaged over odd conductors

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](parity-stabilizer-logarithmic-coalescent-calibration.md).

## Target

Let `A(q)=μ²(q)/φ(q)²` and `H_q(N)=Σ_{n≤N,(n,q)=1}1/n`.
For every cutoff Q and every choice of positive integer horizons N(q), prove

`Σ_{q≤Q,odd} q A(q)|H_q(N(q))−(φ(q)/q)log N(q)|`
`≤73728(2+log Q)`.

Uniformity in the horizons allows the primitive Poisson samples to use
`N(q)=floor(qt/π)` throughout the height window. This would make the
coprime-harmonic contribution `O(T log²T)`, below the proposed model main
term `T log³T`.

## Mechanism

Möbius decomposition and floor-harmonic bounds should give

`|H_q(N)−(φ(q)/q)log N|≤Σ_{d|q}(1+log d)/d`, for N≥1.

The proved conductor estimate `Σ_{q≤Q,odd}A(q)σ₂(q)≤64Q` should imply

- `Σ_{q≤Q,odd}qA(q)≤64(2+log Q)` by reciprocal Abel summation;
- `Σ_{q odd}A(q)sqrt(q)≤384` by the existing Dirichlet-weight bound;
- `Σ_{q odd}A(q)(1+log q)≤1152`, since `1+log q≤3sqrt(q)`.

Finally `A(dk)≤A(d)A(k)`: a squarefree product has coprime factors, and
otherwise the left side vanishes. Divisor swapping reduces the averaged
error to the product of the first and third bounds.

## Existing inputs

`sum_odd_sqfree_sigma2_totient_sq_le`,
`RHTower.Sieve.abs_sum_div_le_of_partial_bound`,
`RHTower.summable_and_mul_tsum_weightedDirichlet_le`,
`RHTower.Sieve.coprimeHarmonic_sub_totient_mul`, and
`GaloisForLFunctions.RHTower.log_le_rpow_div` supply the respective conductor,
Abel, Dirichlet, Möbius and logarithm-versus-power steps.

The displayed new bounds and constants remain to be formalized. No estimate
for the actual prime-minus-model discrepancy follows from this arithmetic
model calculation alone.
