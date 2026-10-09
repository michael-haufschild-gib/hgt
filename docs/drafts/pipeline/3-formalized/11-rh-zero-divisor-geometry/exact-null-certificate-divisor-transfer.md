# Exact-null certificates: blindness at log ℕ is a ζ-free condition

- **ID:** exact-null-certificate-divisor-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** loop rows 586–587 (`rh-goal-loop-opus-2026-09-29.md`); big-picture card §5 (C556, the positivity question for the uniqueness half of template (d)); step-phase loop S41–S46.
- **Statement:** For `R` holomorphic on `½ ≤ Re s ≤ 3` with `ξ²R` and `G²R` decaying (`G(s) = s(s−1)Γ_ℝ(s)/2`), the test `ĝ(t) = Ξ(t)²R(½+it)` vanishes at every `log n`, `n ≥ 2`, iff `Ψ_R = 𝓜^{−1}[G²R]` vanishes at every integer `n ≥ 2`. Then `∫Ξ²R = 2πΨ_R(1)`, and under the critical logarithmic room for `G²R` blindness forces `∫Ξ²R = 0`.

## Goal
U, the uniqueness half of template (d) (`W ⊆ {Λ}`), would follow from a positive exact-null certificate: `R ≥ 0` with `ĝ = Ξ²R` blind at `log ℕ_{≥2}`. The corpus says growth is exhausted for U and only positivity (C556) can decide. This card removes `ζ` from that question. Blindness becomes a vanishing condition for a kernel built from the archimedean factor alone, and the remaining question is purely about `Γ_ℝ`, integers and positivity.

## Proof
1. **Transfer.** `ξ = Gζ` on `Re s > 1`. Shift the line integral of `ξ(s)²R(s)n^{−s}` from `Re s = ½` to `Re s = 3`; `ξ` is entire, so there is no residue. Expand `ζ² = Σd(m)m^{−s}` (`LSeries_convolution'` with `1 ⍟ 1 = d`) and exchange sum and integral (`Σd(m)(mn)^{−3} < ∞`). Result: `∫Ξ²R(½+it)n^{−(½+it)}dt = 2πΣ_m d(m)Ψ_R(mn)`.
2. **Inversion.** `(μ⋆μ)⋆(ζ⋆ζ) = (μ⋆ζ)² = δ₁`. For `Ψ(N) = O(N^{−3})` the double series `Σ_kΣ_m(μ⋆μ)(k)d(m)Ψ(kmn)` converges absolutely, using `|μ⋆μ| ≤ d ≤ id`. The fibre sums over `km = N` give `Ψ(n)`. If `Σ_m d(m)Ψ(mj) = 0` for all `j ≥ 2`, every inner sum with `k ≥ 1` vanishes, so `Ψ(n) = 0` for `n ≥ 2`. The converse is immediate.
3. **Growth law.** On `Re s = ½`, `Ψ_R(n)√n` is the Dirichlet moment of `w(t) = G(½+it)²R(½+it)`. The critical log-room Carlson theorem (`fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom_critical`, nodes `n ≥ 2`, `Σ1/(n log n) = ∞`) gives `∫w = 0`, i.e. `Ψ_R(1) = 0`, hence `∫Ξ²R = 0`.

## Lean
- `RHTower/ExactNullCertificateDivisorTransfer.lean`, namespace `RHTower.ExactNullDivisorTransfer`. Key declarations:
  - `tsum_tsum_mul_comp_mul` (dilation convolution);
  - `moebiusSq_convolution_divisorCard`;
  - `eq_zero_of_divisorDilation_eq_zero`;
  - `riemannZeta_sq_eq_tsum`, `xi_eq_archXi_mul_zeta`;
  - `integral_xi_sq_mul_cpow_eq_tsum` (transfer);
  - `logNode_blind_iff_certKernel_vanishes` (iff);
  - `integral_xi_sq_eq_certKernel_one`.
- `RHTower/ExactNullCertificateLogRoomGrowth.lean`: `certKernel_eq_mellinInv_half`, `integral_xi_sq_eq_zero_of_logNode_blind_of_logRoom`.
- Both modules built with `lake build --old` and audited clean with `lake env lean`; `#print axioms` gives `propext, Classical.choice, Quot.sound`; wired in `RHTower.lean` after `StretchedBoseCriticalLogRoomDensity`.

## Reading
- **ζ-free C556.** A positive exact-null certificate exists iff some even `R ≥ 0` has `∫R(t)|G(½+it)|²cos(2θ(t) − t log n)dt = 0` for all `n ≥ 2` and `≠ 0` at `n = 1`, with `θ` the Riemann–Siegel theta. These are the first-AFE-term phases of `Z(t)²`. For even `R`, `Ψ_R` is a fixed point of the Voronoi involution of `ζ²`, so the uniqueness certificate is a degree-2 object.
- **Growth.** MUST-830 needed `∫|t|^{7/2}|ζ(½+it)|²|ĥ|e^{−K|t|/log} = ∞`. The ζ-free form needs `∫|t|^{7/2}|R|e^{−(π/2)|t|/log(|t|+3)} = ∞` (critical constant included). It is a condition on `R` alone and does not depend on the size of `ζ` on the line.
- **Farkas side [P].** With finitely many constraints the cone of the vectors `(cos(2θ(t) − t log n))_{n≤N}` is all of `ℝ^N`. A dual Dirichlet polynomial with `a₁ = 1` and `Re(e^{2iθ}D) ≤ 0` cannot exist, because `e^{2iθ}` rotates at speed `log(t/2π) → ∞` while `D` is almost periodic. So finite-level ζ-free certificates exist at every level. Exact certificates can fail only through singular duals; the S45 twin rosettes are candidates.

## Log
- 2026-10-09 — paper reformulation (row 586) and Lean (row 587), stage 3.
- 2026-10-09 — supercritical half of the order/degree dictionary in Lean (row 590):
  - module `RHTower/GammaRPowSupercriticalUniqueness.lean`;
  - `exists_sym_uniqueness_mod_finite`, `exists_anti_uniqueness_mod_finite`: for `d ≥ 3`, a fixed or anti-fixed point of ζ^d's Voronoi involution (chart space) vanishing at every integer node `n^{1/d}`, `n ≥ 2`, and at finitely many auxiliary points near 0, vanishes on `(0,∞)`;
  - `exists_card_le_of_sym_vanishing`: such fixed points span at most `m + 1` dimensions;
  - standard axioms.
- 2026-10-09 — every order in Lean (row 592), module `RHTower/ExactNullCertificateOrderTransfer.lean`:
  - `integral_xi_pow_mul_cpow_eq_tsum`: `ζ^k = Σ d_k(m) m^{−s}` and `μ^{⋆k}` inversion, with `|μ^{⋆k}| ≤ d_k ≤ n^{k−1}`;
  - `logNode_blind_iff_certKernelPow_vanishes`;
  - `integral_xi_pow_eq_zero_of_logNode_blind_of_logRoom`: the order-`k` growth law. For `k ≥ 3` it kills every `R` below `e^{(k−2)π|t|/4}`, up to sub-exponential factors.
