# Burnol's sharp lower bound for the Báez-Duarte distances

**Target.** Unconditionally, `liminf_{N→∞} d_N² log N ≥ Σ_{ζ(ρ)=0, Re ρ=½} m_ρ²/|ρ|²`
(Burnol 2002; BDBLS 2000 had c/log N). Corpus has `d_N² ≥ c/log N` (MUST-779, constant 1/(28|ρ|²) from one zero,
Y = N⁷ forced by the crude correction).

**Why it matters.** Sharp rate law of the NB route: with RH ⟺ d_N → 0 (MUST-778) and the off-line floor
(`bdDist_floor_of_zero`), the distances are pinned between the critical-zero floor (this card) and 1 − Π|1−1/ρ|².
Under RH Burnol conjectures equality; any NB proof of RH must match this rate.

## Plan
- B1 Smooth taper ψ ∈ C^∞, ψ = 1 on [0,1], 0 on [2,∞) (mathlib `ContDiffBump`). Mellin ψ̃(z) = 1/z + entire,
  |ψ̃(z)| ≪_K |z|^{−K} on vertical strips (integrate by parts K times; ψ^{(j)} supported in [1,2]).
- B2 Smoothed partial sums at a zero: Φ_ρ(y) = Σ_m m^{−ρ}ψ(m/y) = y^{1−ρ}ψ̃(1−ρ) + O_A(y^{−A}).
  Mellin inversion + interchange on Re z = 1, shift to Re z = −A past z = 1−ρ (main term) and z = 0
  (residue ζ(ρ) = 0); left-half-plane growth of ζ via the functional equation; horizontal edges die by ψ̃ decay.
- B3 Dual a_k = Re(k^{−ρ})ψ(k/Y) (pairs ρ, ρ̄): defects O(N^{1/2}Y^{−A}); energy (|ρ|²/2) log Y + O(1)
  (cross term Σ cos(2γ log k + φ)/k bounded).
- B4 Correction (MUST-779 Möbius) with Y = N^{1+ε}: energy O(N⁶Y^{−2A}) → 0 once A > 3/(1+ε).
- B5 Several zeros: Gram of duals ≈ diag(|ρ|²log Y/2) + O(1) ⇒ d² log Y ≥ Σ_{ρ∈Z} 2/|ρ|² − o(1) (pairs).
- B6 Multiplicities: duals k^{−ρ}(log k)^j, j < m (ζ^{(j)}(ρ) = 0); m² factor from the optimal combination.

## Status
- 2026-10-05: card opened. Start with B1–B2 (the analytic core); B3–B5 reuse BaezDuarteDualSequence.
- 2026-10-05: B1–B2 formalized (ZetaZeroSmoothedPartialSums): `exists_norm_mellin_le_rpow_of_bump` (all-order
  Mellin decay), `exists_norm_tsum_smooth1_zeroCoeff_sub_le` (Σ n^{−ρ}ψ(n/X) = ν̃(ε(1−ρ))X^{1−ρ}/(1−ρ) + O(X^{−A})
  for every zero 0<Re ρ<1, every A). Refined plan for B3: only an UPPER bound E(Re a) ≤ (|ρ|²/2)log Y + K is
  needed; main term via cos² = (1+cos 2θ)/2 and bounded oscillatory sums Σ cos(α log k + c)ψ(k/Y)²/k (α ≠ 0,
  ψ nonincreasing ⇒ Abel summation). Multi-zero: cross terms are the same oscillatory sums with α = γ ± γ'.
- 2026-10-05: B3–B5 formalized; card at stage 3 (MUST-782). Modules: BaezDuarteSmoothZeroDual (cutoff monotone/Lipschitz,
  bounded partial sums on Re z = 1 + Abel, second-order Taylor bound, bilinear pair energy, diagonal (|ρ|²/2)log Y + O(1),
  off-diagonal O(1) for distinct zeros in Im > 0, defects O(m^A Y^{−A})) and BaezDuarteDistanceBurnolLowerBound
  (`eventually_le_bdDistDiscrete_sq_mul_log_of_zeros`: liminf d_N² log N ≥ Σ_{ρ∈Z} 2/|ρ|²; single-zero corollary).
  Weights λ_ρ = |ρ|^{−2}/S; Y = N^{1+η}, A = 4/η; energy split (1+η)E(a) + (1+1/η)E(b). B6 (multiplicities) not done:
  needs duals k^{−ρ}(log k)^j and ζ^{(j)}(ρ) = 0 in the smoothed partial-sum asymptotics.
- Open (frontier): the matching upper bound under RH (Burnol's conjecture: d_N² log N → Σ m_ρ²/|ρ|² under RH), i.e. that
  these duals are asymptotically extremal. Lean has only d_N → 0 under RH (MUST-778, no rate).
- 2026-10-09: B6 (multiplicities) formalized; see card `3-formalized/baez-duarte-burnol-multiplicity.md` (MUST-872, MUST-874). The full target `liminf d_N² log N ≥ Σ_{Re ρ=½} m_ρ²/|ρ|²` is now in Lean as `eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum_order` (sum over `Im ρ > 0` of `2m_ρ²/|ρ|²`, in `[0, ∞]`). The duals are `p_m(log k/log Y)k^{−ρ}ψ(k/Y)`, where `p_m` is the Legendre endpoint extremal. Only the matching upper bound under RH stays open.
