import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSideIsNormalisedAtTheLeftEnd
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheContinuationIsPolynomiallyBoundedOffTheZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TwoVerticalLinesWeighTheZerosOfAFunctionOfOrderOne

/-!
# Two vertical lines cut out the zero series of the state

Let `F` be a profile of the energy domain, `B F(p)` its pairing with the probe `e_p`, and `H` entire
with `|H(σ + it)| ≤ D (1 + t²)⁻²` on `a ≤ σ ≤ b`, where `a ≤ -1` and `1 ≤ b`. Then

  `Σ_z L F(z) H(z) = (1/2π) (∫ H(b + it) B F(b + it) dt − ∫ H(a + it) B F(a + it) dt)`,

the sum over the centred zeros with multiplicity. For the critical state `B F(p) = −a L F(p − 8)`,
with the transform itself right of `Re p = 4` and its continuation left of the zeros:

  `Σ_z L F(z) H(z) = −(a/2π) (∫ H(b + it) L F(b − 8 + it) dt − ∫ H(a + it) L F(a − 8 + it) dt)`.

This is (★) summed against `H`: the zero series of the state as a distribution on both sides of the
wall, in transform form. The right line carries the state on `u < 0`; the left line carries its
continuation beyond the zero strip, which is the head term, the prime heads and the two charges.

Mechanism. Off the zeros `B F(p) − B F(1) = Σ_z L F(z) (1/(p − z) − 1/(1 − z))`. On a line at distance
`½` from the zeros the terms are at most a multiple of `|z|⁻² (1 + t²)`, so against `H` the series
integrates term by term. For one zero the two lines cut out the residue `H(z)`; the constants drop
out because the two line integrals of `H` agree.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Growth on a line against fourth-order decay -/

/-- On the line `Re p = σ`: `(1 + |p|)(1 + 2|p|) ≤ 4 (1 + |σ|)² (1 + t²)`. -/
private theorem line_growth_le (σ t : ℝ) :
    (1 + ‖(σ : ℂ) + t * I‖) * (1 + ‖(σ : ℂ) + t * I‖ / (1 / 2)) ≤
      4 * (1 + |σ|) ^ 2 * (1 + t ^ 2) := by
  have hn : ‖(σ : ℂ) + t * I‖ ≤ |σ| + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + t * I)
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have him : ((σ : ℂ) + t * I).im = t := by simp
    rwa [hre, him] at h
  have h0 := norm_nonneg ((σ : ℂ) + t * I)
  have hσ := abs_nonneg σ
  have ht := abs_nonneg t
  have hsq : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (1 - |t|), sq_abs t]
  have e : ‖(σ : ℂ) + t * I‖ / (1 / 2) = 2 * ‖(σ : ℂ) + t * I‖ := by ring
  rw [e]
  have h1 : (1 + ‖(σ : ℂ) + t * I‖) * (1 + 2 * ‖(σ : ℂ) + t * I‖) ≤
      2 * (1 + ‖(σ : ℂ) + t * I‖) ^ 2 := by nlinarith
  have h2 : (1 + ‖(σ : ℂ) + t * I‖) ^ 2 ≤ ((1 + |σ|) * (1 + |t|)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by nlinarith [mul_nonneg hσ ht]) 2
  have h3 : ((1 + |σ|) * (1 + |t|)) ^ 2 = (1 + |σ|) ^ 2 * (1 + |t|) ^ 2 := mul_pow _ _ _
  have h4 := mul_le_mul_of_nonneg_left hsq (sq_nonneg (1 + |σ|))
  linarith

/-- Decay `D/Q²` against growth `K · 4SQ` leaves `4DKS/Q`. -/
private theorem mul_le_of_decay_of_growth {x y D K G S Q : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ D / Q ^ 2) (hy0 : 0 ≤ y) (hy : y ≤ K * G) (hK : 0 ≤ K) (hG : G ≤ 4 * S * Q)
    (hQ : 0 < Q) : x * y ≤ 4 * D * K * S * Q⁻¹ := by
  have h1 : y ≤ K * (4 * S * Q) := hy.trans (mul_le_mul_of_nonneg_left hG hK)
  have h2 := mul_le_mul hx h1 hy0 (hx0.trans hx)
  have e : (Q ^ 2)⁻¹ * Q = Q⁻¹ := by
    rw [pow_two, mul_inv, inv_mul_cancel_right₀ hQ.ne']
  calc x * y ≤ D / Q ^ 2 * (K * (4 * S * Q)) := h2
    _ = 4 * D * K * S * Q⁻¹ := by linear_combination (4 * D * K * S) * e

private theorem nonneg_of_le_div_sq {x D t : ℝ} (hx : 0 ≤ x) (h : x ≤ D / (1 + t ^ 2) ^ 2) :
    0 ≤ D := by
  have hq : (0 : ℝ) < (1 + t ^ 2) ^ 2 := by positivity
  have h2 := hx.trans h
  rwa [le_div_iff₀ hq, zero_mul] at h2

private theorem div_sq_le_div {D : ℝ} (hD : 0 ≤ D) (t : ℝ) :
    D / (1 + t ^ 2) ^ 2 ≤ D / (1 + t ^ 2) := by
  have hq : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hq2 : 1 + t ^ 2 ≤ (1 + t ^ 2) ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_left hD (by linarith) hq2

/-! ### One line -/

/-- The term of one zero on a line at distance `½` from the zeros, against the decay of `H`. -/
theorem norm_mul_zeroSum_term_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {H : ℂ → ℂ}
    {D σ : ℝ} (hσ : 1 ≤ |σ|) (hD : ∀ t : ℝ, ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2)
    (q : XiZeroCopy) (t : ℝ) :
    ‖H (σ + t * I) * (negativeHalfLineLaplace (cx F) (centredZero q) *
        (((σ : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹))‖ ≤
      4 * D * (3 * halfPoleMass F * ‖centredZero q‖⁻¹ ^ 2) * (1 + |σ|) ^ 2 * (1 + t ^ 2)⁻¹ := by
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have hdist := half_le_norm_sub_centredZero (p := (σ : ℂ) + t * I) (by rw [hre]; exact hσ) q
  have hterm := norm_zeroSum_term_le hF (by norm_num : (0 : ℝ) < 1 / 2) le_rfl hdist
  have hK : 0 ≤ 3 * halfPoleMass F * ‖centredZero q‖⁻¹ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (halfPoleMass_nonneg F)) (sq_nonneg _)
  rw [norm_mul]
  exact mul_le_of_decay_of_growth (norm_nonneg _) (hD t) (norm_nonneg _)
    (hterm.trans (le_of_eq (by ring))) hK (line_growth_le σ t) (by positivity)

theorem integrable_mul_zeroSum_term {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) {D σ : ℝ} (hσ : 1 ≤ |σ|)
    (hD : ∀ t : ℝ, ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2) (q : XiZeroCopy) :
    Integrable (fun t : ℝ => H (σ + t * I) * (negativeHalfLineLaplace (cx F) (centredZero q) *
      (((σ : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹))) := by
  have hmaj : Integrable (fun t : ℝ =>
      4 * D * (3 * halfPoleMass F * ‖centredZero q‖⁻¹ ^ 2) * (1 + |σ|) ^ 2 * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hmaj.mono' ?_ (Eventually.of_forall fun t => norm_mul_zeroSum_term_le hF hσ hD q t)
  refine (continuous_iff_continuousAt.mpr fun t => ?_).aestronglyMeasurable
  have hl : ContinuousAt (fun t : ℝ => (σ : ℂ) + t * I) t := by fun_prop
  have hne : (σ : ℂ) + t * I - centredZero q ≠ 0 := by
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have hdist := half_le_norm_sub_centredZero (p := (σ : ℂ) + t * I) (by rw [hre]; exact hσ) q
    exact norm_pos_iff.mp (by linarith)
  exact ((hH _).continuousAt.comp hl).mul
    (continuousAt_const.mul (((hl.sub continuousAt_const).inv₀ hne).sub continuousAt_const))

/-- **Termwise integration on a line.** On a line `Re p = σ`, `|σ| ≥ 1`, a test of fourth-order
decay integrates the zero sum term by term. -/
theorem hasSum_line_integral_zeroSum {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) {D σ : ℝ} (hσ : 1 ≤ |σ|)
    (hD : ∀ t : ℝ, ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2) :
    HasSum (fun q : XiZeroCopy => ∫ t : ℝ, H (σ + t * I) *
        (negativeHalfLineLaplace (cx F) (centredZero q) *
          (((σ : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹)))
      (∫ t : ℝ, H (σ + t * I) * zeroSum F (σ + t * I)) := by
  have hint := fun q : XiZeroCopy => integrable_mul_zeroSum_term hF hH hσ hD q
  have hsum : Summable fun q : XiZeroCopy => ∫ t : ℝ, ‖H (σ + t * I) *
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        (((σ : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹))‖ := by
    refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun t => norm_nonneg _) (fun q => ?_)
      (summable_inv_sq_centredZero.mul_left
        (4 * D * 3 * halfPoleMass F * (1 + |σ|) ^ 2 * Real.pi))
    calc (∫ t : ℝ, ‖H (σ + t * I) * (negativeHalfLineLaplace (cx F) (centredZero q) *
            (((σ : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹))‖)
        ≤ ∫ t : ℝ, 4 * D * (3 * halfPoleMass F * ‖centredZero q‖⁻¹ ^ 2) * (1 + |σ|) ^ 2 *
            (1 + t ^ 2)⁻¹ :=
          integral_mono (hint q).norm (integrable_inv_one_add_sq.const_mul _)
            (fun t => norm_mul_zeroSum_term_le hF hσ hD q t)
      _ = 4 * D * 3 * halfPoleMass F * (1 + |σ|) ^ 2 * Real.pi * ‖centredZero q‖⁻¹ ^ 2 := by
          rw [integral_const_mul, integral_univ_inv_one_add_sq]
          ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have e : (∫ t : ℝ, H (σ + t * I) * zeroSum F (σ + t * I)) =
      ∫ t : ℝ, ∑' q : XiZeroCopy, H (σ + t * I) *
        (negativeHalfLineLaplace (cx F) (centredZero q) *
          (((σ : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹)) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show H (σ + t * I) * zeroSum F (σ + t * I) = ∑' q : XiZeroCopy, H (σ + t * I) *
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        (((σ : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹))
    rw [tsum_mul_left]
    rfl
  rw [e]
  exact h

/-- On a line `Re p = σ`, `|σ| ≥ 1`, the pairing is its value at `1` plus the zero sum. -/
theorem globalRemainder_line_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {σ : ℝ}
    (hσ : 1 ≤ |σ|) (t : ℝ) :
    globalRemainder F (σ + t * I) = globalRemainder F 1 + zeroSum F (σ + t * I) := by
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have hxi : xi (1 / 2 + ((σ : ℂ) + t * I)) ≠ 0 :=
    xi_ne_zero_of_half_le_abs_re (by rw [hre]; linarith)
  have h := globalRemainder_sub_eq_zeroSum hF hxi
  rw [← h]
  ring

theorem integrable_mul_zeroSum_line {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) {D σ : ℝ} (hσ : 1 ≤ |σ|)
    (hD : ∀ t : ℝ, ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2) :
    Integrable (fun t : ℝ => H (σ + t * I) * zeroSum F (σ + t * I)) := by
  have hmaj : Integrable (fun t : ℝ =>
      4 * D * (3 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2)) *
        (1 + |σ|) ^ 2 * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hline : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t => by simp
  refine hmaj.mono' ?_ (Eventually.of_forall fun t => ?_)
  · refine (continuous_iff_continuousAt.mpr fun t => ?_).aestronglyMeasurable
    have hl : ContinuousAt (fun t : ℝ => (σ : ℂ) + t * I) t := by fun_prop
    have hxi : xi (1 / 2 + ((σ : ℂ) + t * I)) ≠ 0 :=
      xi_ne_zero_of_half_le_abs_re (by rw [hline]; linarith)
    have hz : ContinuousAt (zeroSum F ∘ fun t : ℝ => (σ : ℂ) + t * I) t :=
      ContinuousAt.comp (g := zeroSum F) (f := fun t : ℝ => (σ : ℂ) + t * I) (x := t)
        (differentiableAt_zeroSum hF hxi).continuousAt hl
    have hh : ContinuousAt (H ∘ fun t : ℝ => (σ : ℂ) + t * I) t :=
      ContinuousAt.comp (g := H) (f := fun t : ℝ => (σ : ℂ) + t * I) (x := t)
        (hH _).continuousAt hl
    exact hh.mul hz
  · show ‖H (σ + t * I) * zeroSum F (σ + t * I)‖ ≤
      4 * D * (3 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2)) *
        (1 + |σ|) ^ 2 * (1 + t ^ 2)⁻¹
    have hdist : ∀ q : XiZeroCopy, 1 / 2 ≤ ‖(σ : ℂ) + t * I - centredZero q‖ :=
      half_le_norm_sub_centredZero (by rw [hline]; exact hσ)
    have hZ := norm_zeroSum_le_of_dist hF (by norm_num : (0 : ℝ) < 1 / 2) hdist
    have hK : 0 ≤ 3 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (halfPoleMass_nonneg F))
        (tsum_nonneg fun q => sq_nonneg _)
    rw [norm_mul]
    exact mul_le_of_decay_of_growth (norm_nonneg _) (hD t) (norm_nonneg _) hZ hK
      (line_growth_le σ t) (by positivity)

/-- The line integral of `H · B F` splits into the constant and the zero sum. -/
theorem integral_mul_globalRemainder_line {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) {D σ : ℝ} (hσ : 1 ≤ |σ|)
    (hD : ∀ t : ℝ, ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2) :
    (∫ t : ℝ, H (σ + t * I) * globalRemainder F (σ + t * I)) =
      globalRemainder F 1 * (∫ t : ℝ, H (σ + t * I)) +
        ∫ t : ℝ, H (σ + t * I) * zeroSum F (σ + t * I) := by
  have hD0 : 0 ≤ D := nonneg_of_le_div_sq (norm_nonneg _) (hD 0)
  have hHint : Integrable (fun t : ℝ => H (σ + t * I)) :=
    AbsoluteGeometryOfSpecZ.integrable_line_of_bound hH (C := D)
      (fun t => (hD t).trans (div_sq_le_div hD0 t))
  have hZint := integrable_mul_zeroSum_line hF hH hσ hD
  rw [← integral_const_mul, ← integral_add (hHint.const_mul _) hZint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show H (σ + t * I) * globalRemainder F (σ + t * I) =
    globalRemainder F 1 * H (σ + t * I) + H (σ + t * I) * zeroSum F (σ + t * I)
  rw [globalRemainder_line_eq hF hσ t]
  ring

/-! ### Two lines -/

/-- **Two vertical lines cut out the zero series of a profile.** For `F` in the energy domain and
`H` entire of fourth-order decay on `a ≤ Re p ≤ b`, `a ≤ -1`, `1 ≤ b`:
`Σ_z L F(z) H(z) = (1/2π)(∫ H(b + it) B F(b + it) dt − ∫ H(a + it) B F(a + it) dt)`. -/
theorem hasSum_zeroValues_two_lines {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) {D a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b)
    (hD : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * H (centredZero q))
      ((1 / (2 * Real.pi) : ℂ) * ((∫ t : ℝ, H (b + t * I) * globalRemainder F (b + t * I)) -
        ∫ t : ℝ, H (a + t * I) * globalRemainder F (a + t * I))) := by
  have hab : a ≤ b := by linarith
  have hD0 : 0 ≤ D := nonneg_of_le_div_sq (norm_nonneg _) (hD a 0 le_rfl hab)
  have hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) := fun σ t h1 h2 =>
    (hD σ t h1 h2).trans (div_sq_le_div hD0 t)
  have hσa : 1 ≤ |a| := by
    rw [abs_of_nonpos (show a ≤ 0 by linarith)]
    linarith
  have hσb : 1 ≤ |b| := by
    rw [abs_of_nonneg (show (0 : ℝ) ≤ b by linarith)]
    exact hb
  have hDa : ∀ t : ℝ, ‖H (a + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2 := fun t => hD a t le_rfl hab
  have hDb : ∀ t : ℝ, ‖H (b + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2 := fun t => hD b t hab le_rfl
  -- the two lines, term by term
  have hS := (hasSum_line_integral_zeroSum hF hH hσb hDb).sub
    (hasSum_line_integral_zeroSum hF hH hσa hDa)
  -- one zero: the residue, the constant dropping out
  have hterm : ∀ q : XiZeroCopy,
      (2 * Real.pi : ℂ) * (negativeHalfLineLaplace (cx F) (centredZero q) * H (centredZero q)) =
      (∫ t : ℝ, H (b + t * I) * (negativeHalfLineLaplace (cx F) (centredZero q) *
          (((b : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹))) -
      (∫ t : ℝ, H (a + t * I) * (negativeHalfLineLaplace (cx F) (centredZero q) *
          (((a : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹))) := by
    intro q
    have hz := abs_lt.mp (abs_re_centredZero_lt q)
    have h2 := AbsoluteGeometryOfSpecZ.two_line_simple_pole_add_const hH hC
      (p := centredZero q) (by linarith [hz.1]) (by linarith [hz.2]) (-(1 - centredZero q)⁻¹)
    have eb : ∀ σ : ℝ, (∫ t : ℝ, H (σ + t * I) *
          (negativeHalfLineLaplace (cx F) (centredZero q) *
            (((σ : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹))) =
        negativeHalfLineLaplace (cx F) (centredZero q) * ∫ t : ℝ, H (σ + t * I) *
          (((σ : ℂ) + t * I - centredZero q)⁻¹ + -(1 - centredZero q)⁻¹) := by
      intro σ
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      show H (σ + t * I) * (negativeHalfLineLaplace (cx F) (centredZero q) *
          (((σ : ℂ) + t * I - centredZero q)⁻¹ - (1 - centredZero q)⁻¹)) =
        negativeHalfLineLaplace (cx F) (centredZero q) * (H (σ + t * I) *
          (((σ : ℂ) + t * I - centredZero q)⁻¹ + -(1 - centredZero q)⁻¹))
      ring
    rw [eb b, eb a, ← mul_sub, h2]
    ring
  have hS' : HasSum (fun q : XiZeroCopy =>
        (2 * Real.pi : ℂ) * (negativeHalfLineLaplace (cx F) (centredZero q) * H (centredZero q)))
      ((∫ t : ℝ, H (b + t * I) * zeroSum F (b + t * I)) -
        ∫ t : ℝ, H (a + t * I) * zeroSum F (a + t * I)) := by
    rw [funext hterm]
    exact hS
  -- the constant of the explicit formula drops out
  have hline := AbsoluteGeometryOfSpecZ.integral_line_eq hH hab hC
  have hval : (∫ t : ℝ, H (b + t * I) * globalRemainder F (b + t * I)) -
        ∫ t : ℝ, H (a + t * I) * globalRemainder F (a + t * I) =
      (∫ t : ℝ, H (b + t * I) * zeroSum F (b + t * I)) -
        ∫ t : ℝ, H (a + t * I) * zeroSum F (a + t * I) := by
    rw [integral_mul_globalRemainder_line hF hH hσb hDb,
      integral_mul_globalRemainder_line hF hH hσa hDa, hline]
    ring
  rw [hval]
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero hpi
  have h3 := hS'.mul_left (1 / (2 * Real.pi) : ℂ)
  have hfun : (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * H (centredZero q)) =
      fun q => (1 / (2 * Real.pi) : ℂ) * ((2 * Real.pi : ℂ) *
        (negativeHalfLineLaplace (cx F) (centredZero q) * H (centredZero q))) := by
    funext q
    rw [← mul_assoc, one_div, inv_mul_cancel₀ h2pi, one_mul]
  rw [hfun]
  exact h3

/-- **(★) summed against an entire test.** For the critical state, `a ≤ -1` and `4 < b`:
`Σ_z L F(z) H(z) = −(a/2π)(∫ H(b + it) L F(b − 8 + it) dt − ∫ H(a + it) L F(a − 8 + it) dt)`,
with the transform itself on the right line and its continuation on the left line. -/
theorem criticalState_hasSum_zeroValues_two_lines {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {D a b : ℝ} (ha : a ≤ -1) (hb : 4 < b)
    (hD : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * H (centredZero q))
      (-((criticalAliasCoefficient W₀ : ℂ) / (2 * Real.pi)) *
        ((∫ t : ℝ, H (b + t * I) * negativeHalfLineLaplace (cx F) (b + t * I - 8)) -
          ∫ t : ℝ, H (a + t * I) * stateMeromorphic W₀ F (a + t * I - 8))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hA := hasSum_zeroValues_two_lines hd hH ha (by linarith) hD
  have ha0 : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  -- the right line: the transform of the state
  have e1 : ∀ t : ℝ, globalRemainder F (b + t * I) =
      -((criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) (b + t * I - 8)) := by
    intro t
    have hre : ((b : ℂ) + t * I - 8).re = b - 8 := by simp
    have h := criticalState_alias_mul_laplace hW hthreshold hF
      (u := (b : ℂ) + t * I - 8) (by rw [hre]; linarith)
    rw [h, neg_neg]
    congr 1
    ring
  -- the left line: the continuation
  have e2 : ∀ t : ℝ, globalRemainder F (a + t * I) =
      -((criticalAliasCoefficient W₀ : ℂ) * stateMeromorphic W₀ F (a + t * I - 8)) := by
    intro t
    unfold stateMeromorphic
    rw [mul_div_assoc', mul_div_cancel_left₀ _ ha0, neg_neg]
    congr 1
    ring
  have i1 : (∫ t : ℝ, H (b + t * I) * globalRemainder F (b + t * I)) =
      -(criticalAliasCoefficient W₀ : ℂ) *
        ∫ t : ℝ, H (b + t * I) * negativeHalfLineLaplace (cx F) (b + t * I - 8) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show H (b + t * I) * globalRemainder F (b + t * I) = -(criticalAliasCoefficient W₀ : ℂ) *
      (H (b + t * I) * negativeHalfLineLaplace (cx F) (b + t * I - 8))
    rw [e1 t]
    ring
  have i2 : (∫ t : ℝ, H (a + t * I) * globalRemainder F (a + t * I)) =
      -(criticalAliasCoefficient W₀ : ℂ) *
        ∫ t : ℝ, H (a + t * I) * stateMeromorphic W₀ F (a + t * I - 8) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show H (a + t * I) * globalRemainder F (a + t * I) = -(criticalAliasCoefficient W₀ : ℂ) *
      (H (a + t * I) * stateMeromorphic W₀ F (a + t * I - 8))
    rw [e2 t]
    ring
  rw [i1, i2] at hA
  convert hA using 1
  ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
