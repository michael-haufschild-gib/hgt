# Báez-Duarte distances: the unconditional 1/log N floor

**Status:** formalized (Lean, axiom-clean), 2026-10-05. STATUS MUST-779.

## Statement
∃ c > 0 such that for every N ≥ 2, `d_N² ≥ c / log N`, where `d_N = bdDistDiscrete N` is the distance from
`1_{(0,1]}` to the span of the first N Báez-Duarte functions `({u/n} − {u}/n)/u`.
Explicitly, for every zero ρ of ζ with Re ρ = ½:
`1 ≤ d_N² (4|ρ|²(1 + 7 log N) + 4 + 576(12|ρ| + 4)²)`.

Lean: `RHTower.exists_div_log_le_bdDistDiscrete_sq`, `RHTower.one_le_bdDistDiscrete_sq_mul_of_zero`.

## Proof
1. **Dual sequences** (BaezDuarteDualSequence). In the discrete carrier the target is the constant 1 and the
   generators are e_m(k) = (k mod m)/m with weights 1/(k(k+1)). For finitely supported A, the step vector of
   W_k = k(k+1)(A_k − A_{k+1}) pairs with the target to A_1, with e_m to (1/m)ΣA − Σ_{m|k}A_k (summation by parts,
   e_m(k) − e_m(k−1) = 1/m − [m|k]), and has squared norm Σk(k+1)(A_k − A_{k+1})². So exact annihilation plus
   A_1 = 1 gives `1 ≤ d_N² · energy`.
2. **Zero dual** (BaezDuarteDistanceLogLowerBound). a_k = k^{−ρ}(Y − k + 1)/Y = (1/Y)Σ_{k≤j≤Y}k^{−ρ}. Its defect
   against m is (1/Y)Σ_j(m^{−ρ}S(⌊j/m⌋) − S(j)/m) with S(M) = Σ_{k≤M}k^{−ρ} = M^{1−ρ}/(1−ρ) + O(|ρ|M^{−1/2})
   (truncated ζ representation and ζ(ρ) = 0). Main terms cancel exactly; each defect is ≤ (12|ρ|+4)/√Y.
   Energy ≤ 2|ρ|²(1 + log Y) + 2 via k(k+1)(k^{−1/2} − (k+1)^{−1/2})² ≤ 1/(4k).
3. **Exact correction.** For a prime P ∈ (N, 2N], the sequences δ_d − δ_P (2 ≤ d ≤ N) have defect [m|d];
   Möbius inversion over the divisor lattice gives coefficients |x_d| ≤ Σ|v|. With Y = N⁷ the correction costs
   O(1) energy. Real parts preserve the (real-coefficient) constraints.

## Position
- With MUST-778 (RH ⟺ d_N → 0) this is the rate cap: d_N ≫ 1/√log N always.
- Off-line zeros give a constant floor (corpus `bdDist_floor_of_zero`); critical zeros give this 1/log N floor.
- Sharp constant (Burnol: liminf d_N² log N ≥ Σ m_ρ²/|ρ|²) is not claimed; the method gives constant
  1/(28|ρ|²) for one zero with Y = N⁷ (Y = N^{1+ε} with a smooth taper would approach 1/(2|ρ|²)… the factor 2
  comes from k(k+1) ≤ 2k² and (x+y)² ≤ 2x²+2y²).
- Not formalized: summing several zeros (orthogonal dual sequences) for the Σ 1/|ρ|² constant.
