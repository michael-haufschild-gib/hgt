# Franel–Landau Farey criterion

**Statement.** Let `f_1 < ⋯ < f_L` be the Farey fractions `a/q`, `1 ≤ a ≤ q ≤ n`, `(a,q) = 1`.
RH ⟺ `Σ_ν |f_ν − ν/L| = O(n^{1/2+δ})` for every `δ > 0`.

**Status.** Stage 3 (Lean, unconditional, axioms `propext, Classical.choice, Quot.sound`).
`RHTower.riemannHypothesis_iff_fareyL1Discrepancy_le` (MUST-756 receiver, MUST-757 forward).

**Proof.**
- Receiver: Ramanujan sums give `Σ e(f_ν) = M(n)`, `Σ e(ν/L) = 0`, Lipschitz bound, Littlewood.
- Forward:
  1. Hermite: `Σ_{a<N} ψ(y + a/N) = ψ(Ny)`; autocorrelation `∫ψ(y)ψ(y+c) = c²/2 − c/2 + 1/12`;
     coprime reduction ⇒ `∫_0^1 ψ(mx)ψ(m'x) = gcd²/(12mm')`.
  2. `N_n(x) = Σ_k ⌊kx⌋ M(n/k)` (Dirichlet convolution `μ * ⌊·x⌋`, regrouped by
     `sum_Ioc_mul_eq_sum_sum`); `Σ_k M(n/k) = 1`; defect `Lx − N_n(x) = ½ + S_n(x)`.
  3. RH ⇒ `|M(n/k)| k^a ≤ B n^a` (`a = ½ + δ`); `gcd ≤ (kk')^a`; Gauss identity
     ⇒ `∫S_n² ≤ (B²/12) n^{2a}(1 + log n)³`.
  4. Separation `≥ 1/n²` ⇒ `N_n` constant on `[f, f + 1/n²)`; average over these disjoint intervals
     ⇒ `Σ|δ_ν| ≤ (n²/L)∫_0^1|S_n| + 3/2`; AM–GM with `T = n^a(1 + log n)²`.
  5. `L = Σφ(q)`, `Σ_k Φ(n/k) = n(n+1)/2`, `Σ_{k≥2} 1/k² ≤ 3/4` ⇒ `L ≥ n²/16` (`n ≥ 256`).

**Modules.** `FareyDiscrepancyLandauCriterion`, `CenteredFractCorrelation`,
`FareyCountMertensIdentity`, `FareySawtoothMeanSquare`, `FareyDiscrepancyFranelCriterion`.

**Insight.** The Farey ℓ¹ discrepancy is a receiver of the same Mertens ceiling as Littlewood's
criterion; its forward half costs only the ℓ² gcd structure of sawtooth correlations, so the
criterion is equivalent to, not stronger than, `M(x) = O(x^{1/2+ε})`.

**Exponent law (MUST-758).** Unconditionally `Θ = inf {b ≥ 0 : Σ_ν |f_ν − ν/L| = O(n^b)}`
(`RHTower.zetaZeroAbscissa_eq_sInf_fareyL1Discrepancy_exponents`, FareyDiscrepancyExponentLaw).
The transfer works from any Mertens exponent `a ∈ [½, 1]`
(`fareyL1Discrepancy_le_of_mertens_rpow_bound`).

**Franel's square form (MUST-765).** RH ⟺ `Σ_ν δ_ν² = O(n^{−1+δ})` ∀δ>0, with exponent law
`Σ δ_ν² = O(n^{2b−2})` ⟺ (for b>Θ / forces Θ ≤ b)
(`RHTower.riemannHypothesis_iff_fareyL2Discrepancy_le`, FareyDiscrepancyFranelSquareLaw).
