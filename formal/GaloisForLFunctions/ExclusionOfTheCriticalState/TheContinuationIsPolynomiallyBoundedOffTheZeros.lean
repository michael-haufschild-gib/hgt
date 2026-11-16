import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes

/-!
# The continuation is polynomially bounded off the zeros

The explicit formula bounds the pairing of a profile with a probe in the whole plane: at distance
`δ` from the zeros,

  `|B F(p)| ≤ |B F(1)| + 3 m S (1 + |p|)(1 + |p|/δ)`,

with `m` the mass of the profile at `-½` and `S = Σ_z |z|⁻²`. In particular `B F` is holomorphic and
`O(|p|²)` on every closed half-plane right of the zeros, and the continuation of the state's transform
is `O(|w|²)` on `Re w ≥ κ - 8 + δ` when every zero has `Re z ≤ κ`. These are the bounds on vertical
lines for the series (★); they come from the zero side, with no estimate of `ζ'/ζ`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

theorem xi_ne_zero_of_dist {p : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hq : ∀ q : XiZeroCopy, δ ≤ ‖p - centredZero q‖) : xi (1 / 2 + p) ≠ 0 := by
  intro h0
  obtain ⟨q, hq'⟩ := exists_xiZeroCopy_of_xi_eq_zero h0
  have hz : centredZero q = p := by
    unfold centredZero
    rw [hq']
    ring
  have := hq q
  rw [hz, sub_self, norm_zero] at this
  linarith

/-- `Z F(p) = O((1 + |p|)(1 + |p|/δ))` at distance `δ` from the zeros. -/
theorem norm_zeroSum_le_of_dist {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hq : ∀ q : XiZeroCopy, δ ≤ ‖p - centredZero q‖) :
    ‖zeroSum F p‖ ≤ 3 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) *
      ((1 + ‖p‖) * (1 + ‖p‖ / δ)) := by
  have hs := (summable_inv_sq_centredZero.mul_left
    (halfPoleMass F * (1 + ‖p‖) * (1 + ‖p‖ / δ) * 3)).hasSum
  unfold zeroSum
  refine (tsum_of_norm_bounded hs fun q => norm_zeroSum_term_le hF hδ le_rfl (hq q)).trans ?_
  rw [tsum_mul_left]
  exact le_of_eq (by ring)

/-- **The pairing with a probe is bounded off the zeros**, in the whole plane. -/
theorem norm_globalRemainder_le_of_dist {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    {δ : ℝ} (hδ : 0 < δ) (hq : ∀ q : XiZeroCopy, δ ≤ ‖p - centredZero q‖) :
    ‖globalRemainder F p‖ ≤ ‖globalRemainder F 1‖ +
      3 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) *
        ((1 + ‖p‖) * (1 + ‖p‖ / δ)) := by
  have h := globalRemainder_sub_eq_zeroSum hF (xi_ne_zero_of_dist hδ hq)
  have e : globalRemainder F p = globalRemainder F 1 + zeroSum F p := by
    rw [← h]
    ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_zeroSum_le_of_dist hF hδ hq))

/-- The pairing with a probe is holomorphic off the zeros. -/
theorem differentiableAt_globalRemainder_of_xi_ne_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} (hxi : xi (1 / 2 + p) ≠ 0) :
    DifferentiableAt ℂ (globalRemainder F) p := by
  refine differentiableAt_globalRemainder hF fun hp hz => hxi ?_
  rw [xi_eq_half_mul_Gammaℝ_mul_zetaEntire (by rw [re_one_half_add]; linarith), hz]
  ring

/-! ### Half-planes right of the zeros -/

/-- A point of `Re p ≥ κ + δ` is at distance `δ` from every zero with `Re z ≤ κ`. -/
theorem le_norm_sub_centredZero_of_re {κ δ : ℝ} (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ)
    {p : ℂ} (hp : κ + δ ≤ p.re) (q : XiZeroCopy) : δ ≤ ‖p - centredZero q‖ := by
  have h := Complex.abs_re_le_norm (p - centredZero q)
  have h2 := le_abs_self (p - centredZero q).re
  rw [Complex.sub_re] at h h2
  have := hκ q
  linarith

/-- **Bounds on vertical lines.** If every zero has `Re z ≤ κ`, the pairing is holomorphic and
`O(|p|²)` on `Re p ≥ κ + δ`. -/
theorem norm_globalRemainder_le_of_re {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {κ δ : ℝ} (hδ : 0 < δ) (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {p : ℂ}
    (hp : κ + δ ≤ p.re) :
    ‖globalRemainder F p‖ ≤ ‖globalRemainder F 1‖ +
      3 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) *
        ((1 + ‖p‖) * (1 + ‖p‖ / δ)) :=
  norm_globalRemainder_le_of_dist hF hδ (le_norm_sub_centredZero_of_re hκ hp)

theorem differentiableAt_globalRemainder_of_re {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {κ : ℝ} (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {p : ℂ} (hp : κ < p.re) :
    DifferentiableAt ℂ (globalRemainder F) p :=
  differentiableAt_globalRemainder_of_xi_ne_zero hF
    (xi_ne_zero_of_dist (sub_pos.mpr hp)
      (le_norm_sub_centredZero_of_re hκ (by linarith : κ + (p.re - κ) ≤ p.re)))

/-- **The continuation of the state's transform on vertical lines.** If every zero has `Re z ≤ κ`,
then on `Re w ≥ κ - 8 + δ` the continuation is bounded by a quadratic polynomial in `|w + 8|`. -/
theorem norm_stateMeromorphic_le_of_re {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {κ δ : ℝ} (hδ : 0 < δ)
    (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {w : ℂ} (hw : κ - 8 + δ ≤ w.re) :
    ‖stateMeromorphic W₀ F w‖ ≤ (‖globalRemainder F 1‖ +
      3 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) *
        ((1 + ‖w + 8‖) * (1 + ‖w + 8‖ / δ))) / criticalAliasCoefficient W₀ := by
  have ha := criticalAliasCoefficient_positive hW
  have h8 : (w + 8).re = w.re + 8 := by simp
  have h := norm_globalRemainder_le_of_re hF hδ hκ (p := w + 8) (by rw [h8]; linarith)
  unfold stateMeromorphic
  rw [norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha.le]
  exact div_le_div_of_nonneg_right h ha.le

end GaloisForLFunctions.ExclusionOfTheCriticalState
