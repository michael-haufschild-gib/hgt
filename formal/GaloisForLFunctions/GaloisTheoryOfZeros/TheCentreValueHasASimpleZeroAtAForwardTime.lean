import GaloisForLFunctions.GaloisTheoryOfZeros.ForEachSignALoopOfSaddlesTurnsTheRatioOfTheTwoTerms
import GaloisForLFunctions.GaloisTheoryOfZeros.TheCentreValueIsTheEquationOfTheSignBranchPoints
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Liouville

/-!
# The centre value has a simple zero at a forward time

The centre value `c(τ) = H_τ(0)` is the equation of the sign branch points: a zero of order `k`
of `c` is a collision of `2k` zeros at the centre.

**Theorem** (`exists_centreValue_simple_zero`). For every `T` there is a time `τ₀` with
`Re τ₀ > T`, `c(τ₀) = 0` and `c'(τ₀) ≠ 0`. There `H_{τ₀}` has a zero of order exactly two at the
centre (`exists_isCollision_center_two`): one pair `±z` collides.

Proof. At the saddle time `τ(a)` the centre value is `B₀(a) + 2S₀(a)` up to a small relative
error, and `(2S₀)² = Q B₀²`. Around a base point `a₁` the family

`a(v) = a₁ + (−Log Q(a₁) + v)/(2D₁) + t·πi/D₁`, `D₁ = P₁(2a₁ − 1)`, `|v| ≤ 1`,

has `Q(a(v)) = e^{v + 2πit}` up to `1/4096` (`centreSaddle_spec`). The sign of the square root is
constant along paths, and the half period `t = 1` reverses it, so for `t = 0` or `t = 1` the
ratio is `2S₀ = −e^{v/2}B₀` on the whole disc (`exists_centre_family`). Then
`Φ(v) = c(τ(a(v)))/B₀(a(v))` is holomorphic near the disc and within `1/1024` of `1 − e^{v/2}`
(`norm_centreValue_div_bulkTerm_sub_le`). On the circle `|v| = 1/2` it stays `1/8` away from
`Φ(0)`, and `|Φ(0)| ≤ 1/1024`: by the open mapping theorem `Φ` has a zero `v*` in the disc. The
derivative of `Φ − (1 − e^{v/2})` at `v*` is at most `1/512` by the Cauchy estimate, while a
double zero of `c` would make it `e^{v*/2}/2`.
-/

open Complex MeasureTheory Filter Topology Set Metric
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The family of saddles around a central collision of the model -/

/-- The shift at which the squared ratio is `e^v` to first order:
`h(v) = (−Log Q(a₁) + v)/(2D₁)`, `D₁ = P₁(2a₁ − 1)`. -/
def ratioShift (a₁ v : ℂ) : ℂ :=
  (-Complex.log (saddleRatioSq a₁) + v) / (2 * (saddleP a₁ * (2 * a₁ - 1)))

/-- The family of saddles `a(v) = a₁ + h(v) + t·πi/D₁`. -/
def centreSaddle (a₁ : ℂ) (t : ℝ) (v : ℂ) : ℂ := a₁ + (ratioShift a₁ v + t * halfPeriod a₁)

/-- The amplitude `A = 2S₀ e^{−v/2} e^{−iπt}` of the family: `A² = B₀²` up to `|B₀|²/4096`. -/
def centreAmp (a₁ : ℂ) (t : ℝ) (v : ℂ) : ℂ :=
  2 * saddleTerm (centreSaddle a₁ t v) * cexp (-(v / 2)) * cexp (-(π * t * I))

/-- The centre value over the bulk term on the family. -/
def centreRatio (a₁ : ℂ) (t : ℝ) (v : ℂ) : ℂ :=
  centreValue (saddleTime (centreSaddle a₁ t v)) / bulkTerm (centreSaddle a₁ t v)

/-- The shift is of size `M e^{−2σ}`. -/
theorem norm_ratioShift_le {a₁ : ℂ} (hσ : 51 ≤ a₁.re) (him0 : 0 ≤ a₁.im) (him1 : a₁.im ≤ 1)
    (hf : (saddlePhaseValue a₁).re = 0) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    ‖ratioShift a₁ v‖ ≤ loopConst * Real.exp (-(2 * a₁.re)) := by
  have hπ3 := Real.pi_gt_d2
  have hπ0 := Real.pi_pos
  have hM12 := twelve_le_loopConst
  have hM0 : 0 ≤ loopConst := by linarith
  obtain ⟨hn_lo, -⟩ := norm_two_mul_sub_one_bounds (by linarith : 1 ≤ a₁.re) him0 him1
  have hn0 : 0 < ‖2 * a₁ - 1‖ := lt_of_lt_of_le (by linarith) hn_lo
  have hlogQn := (norm_log_saddleRatioSq_le (by linarith : 1 ≤ a₁.re) him0 him1 hf).2
  have hD : ‖2 * (saddleP a₁ * (2 * a₁ - 1))‖ =
      2 * (π * Real.exp (2 * a₁.re) * ‖2 * a₁ - 1‖) := by
    rw [norm_mul, norm_mul, norm_saddleP, Complex.norm_ofNat]
  have hDpos : 0 < 2 * (π * Real.exp (2 * a₁.re) * ‖2 * a₁ - 1‖) :=
    mul_pos two_pos (mul_pos (mul_pos hπ0 (Real.exp_pos _)) hn0)
  have hnum : ‖-Complex.log (saddleRatioSq a₁) + v‖ ≤ loopConst * a₁.re := by
    have h2 := mul_nonneg (sub_nonneg.mpr hM12) (by linarith : (0 : ℝ) ≤ a₁.re - 1)
    calc ‖-Complex.log (saddleRatioSq a₁) + v‖
        ≤ ‖-Complex.log (saddleRatioSq a₁)‖ + ‖v‖ := norm_add_le _ _
      _ ≤ (loopConst - 12 + 11 * a₁.re + π) + 1 := by
          rw [norm_neg]
          linarith
      _ ≤ loopConst * a₁.re := by linarith [Real.pi_lt_d2]
  rw [ratioShift, norm_div, hD, div_le_iff₀ hDpos]
  have e : loopConst * Real.exp (-(2 * a₁.re)) *
      (2 * (π * Real.exp (2 * a₁.re) * ‖2 * a₁ - 1‖)) =
      2 * π * loopConst * ‖2 * a₁ - 1‖ *
        (Real.exp (-(2 * a₁.re)) * Real.exp (2 * a₁.re)) := by ring
  rw [e, SaddleRegion.exp_neg_two_mul_exp, mul_one]
  refine hnum.trans ?_
  have h1 : loopConst * a₁.re ≤ loopConst * ‖2 * a₁ - 1‖ :=
    mul_le_mul_of_nonneg_left (by linarith) hM0
  have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * π - 1) (mul_nonneg hM0 hn0.le)
  linarith

/-- **The family at a base point.** If `Re a₁ = σ ≥ 51`, `Re f(a₁) = 0`,
`3/10 ≤ (π/4 − Im a₁)σ ≤ 7/10` and `(2 + M)²σ⁴e^{−σ} ≤ 1/300000`, then for `|v| ≤ 1` and
`0 ≤ t ≤ 1` the saddle `a(v)` is in the saddle region, within `1` of `a₁`, and
`|Q(a(v)) e^{−v} e^{−2πit} − 1| ≤ 1/4096`. -/
theorem centreSaddle_spec {a₁ : ℂ} (hσ : 51 ≤ a₁.re) (hf : (saddlePhaseValue a₁).re = 0)
    (hlo : 3 / 10 ≤ (π / 4 - a₁.im) * a₁.re) (hhi : (π / 4 - a₁.im) * a₁.re ≤ 7 / 10)
    (hK : (1 + (loopConst + 1)) ^ 2 * a₁.re ^ 4 * Real.exp (-a₁.re) ≤ 1 / 300000)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    SaddleRegion (centreSaddle a₁ t v) ∧ a₁.re - 1 ≤ (centreSaddle a₁ t v).re ∧
      ‖saddleRatioSq (centreSaddle a₁ t v) * cexp (-v) * cexp (-(2 * π * t * I)) - 1‖ ≤
        1 / 4096 := by
  have hπ3 := Real.pi_gt_d2
  have hπ4 := Real.pi_lt_d2
  have hσ0 : 0 < a₁.re := by linarith
  have hM0 : 0 ≤ loopConst + 1 := by linarith [twelve_le_loopConst]
  -- the imaginary part of the base point
  have him1 : a₁.im ≤ 1 := by
    by_contra hc
    push Not at hc
    have h1 := mul_nonpos_of_nonpos_of_nonneg (by linarith : π / 4 - a₁.im ≤ 0) hσ0.le
    linarith
  have him0 : 0 ≤ a₁.im := by
    by_contra hc
    push Not at hc
    have h1 := mul_lt_mul_of_pos_right (by linarith : (1 / 50 : ℝ) < π / 4 - a₁.im) hσ0
    linarith
  -- the size of the shift
  have hhn : ‖ratioShift a₁ v + t * halfPeriod a₁‖ ≤
      (loopConst + 1) * Real.exp (-(2 * a₁.re)) := by
    have h1 := norm_ratioShift_le hσ him0 him1 hf hv
    have h2 := norm_halfPeriod_le (by linarith : 1 ≤ a₁.re) him0 him1
    have h3 : ‖(t : ℂ) * halfPeriod a₁‖ ≤ Real.exp (-(2 * a₁.re)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      calc t * ‖halfPeriod a₁‖ ≤ 1 * ‖halfPeriod a₁‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ ≤ Real.exp (-(2 * a₁.re)) := by rw [one_mul]; exact h2
    have h4 := norm_add_le (ratioShift a₁ v) ((t : ℂ) * halfPeriod a₁)
    linarith
  obtain ⟨hk1, hk2⟩ := loop_smallness hM0 hσ (norm_nonneg _) hhn
  have hhK : ‖ratioShift a₁ v + t * halfPeriod a₁‖ ≤
      (1 + (loopConst + 1)) ^ 2 * a₁.re ^ 4 * Real.exp (-a₁.re) := by
    have h1 : ‖ratioShift a₁ v + t * halfPeriod a₁‖ * 1 ≤
        ‖ratioShift a₁ v + t * halfPeriod a₁‖ * a₁.re :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    linarith
  obtain ⟨hreg, hre⟩ := saddleRegion_add (h := ratioShift a₁ v + t * halfPeriod a₁) hσ hlo hhi
    (hk1.trans hK)
  refine ⟨hreg, hre, ?_⟩
  -- the squared ratio on the family
  obtain ⟨hn_lo, -⟩ := norm_two_mul_sub_one_bounds (by linarith : 1 ≤ a₁.re) him0 him1
  have h2a : 2 * a₁ - 1 ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * a₁.re - 1) hn_lo)
  have hQne := (norm_log_saddleRatioSq_le (by linarith : 1 ≤ a₁.re) him0 him1 hf).1
  have h2h : 2 * a₁ - 1 + 2 * (ratioShift a₁ v + t * halfPeriod a₁) ≠ 0 := by
    intro h0
    have hre' : (2 * a₁ - 1 + 2 * (ratioShift a₁ v + t * halfPeriod a₁)).re =
        2 * a₁.re - 1 + 2 * (ratioShift a₁ v + t * halfPeriod a₁).re := by simp
    rw [h0, Complex.zero_re] at hre'
    have h3 := (abs_le.mp ((Complex.abs_re_le_norm
      (ratioShift a₁ v + t * halfPeriod a₁)).trans hhK)).1
    linarith
  have hP0 := saddleP_ne_zero a₁
  have hD0 : 2 * (saddleP a₁ * (2 * a₁ - 1)) ≠ 0 :=
    mul_ne_zero two_ne_zero (mul_ne_zero hP0 h2a)
  have hexp : cexp (2 * (saddleP a₁ * (2 * a₁ - 1)) * (ratioShift a₁ v + t * halfPeriod a₁)) =
      (saddleRatioSq a₁)⁻¹ * cexp v * cexp (2 * π * t * I) := by
    have e1 : 2 * (saddleP a₁ * (2 * a₁ - 1)) * ratioShift a₁ v =
        -Complex.log (saddleRatioSq a₁) + v := by
      rw [ratioShift, mul_div_cancel₀ _ hD0]
    have e2 : 2 * (saddleP a₁ * (2 * a₁ - 1)) * ((t : ℂ) * halfPeriod a₁) = 2 * π * t * I := by
      rw [halfPeriod]
      field_simp
    rw [mul_add, e1, e2, Complex.exp_add, Complex.exp_add, Complex.exp_neg,
      Complex.exp_log hQne]
  have hX := norm_remainder_sub_one_le (a₁ := a₁) (h := ratioShift a₁ v + t * halfPeriod a₁)
    (by linarith) him0 him1
    (by linarith : (1 + (loopConst + 1)) ^ 2 * a₁.re ^ 4 * Real.exp (-a₁.re) ≤ 1 / 17) hhK hk2
  have key : ∀ Q X E F : ℂ, Q ≠ 0 → E ≠ 0 → F ≠ 0 →
      Q * (Q⁻¹ * E * F) * X * E⁻¹ * F⁻¹ = X := by
    intro Q X E F hQ hE hF
    field_simp
  rw [centreSaddle, saddleRatioSq_add h2a h2h, hexp, Complex.exp_neg, Complex.exp_neg,
    key _ _ _ _ hQne (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)]
  linarith

/-! ## The sign of the ratio on the family -/

/-- **The sign is constant along a path of the family.** Along a path `(v(r), t(r))` on which
the saddles are in the region and `|Q e^{−v} e^{−2πit} − 1| ≤ 1/4096`: if `A = ηB₀` up to
`|B₀|/4096` at one parameter, `η = ±1`, then at all. -/
theorem norm_centreAmp_sub_le_of_path {a₁ : ℂ} {vp : ℝ → ℂ} {tp : ℝ → ℝ} (hvp : Continuous vp)
    (htp : Continuous tp) (hR : ∀ r, SaddleRegion (centreSaddle a₁ (tp r) (vp r)))
    (hQ : ∀ r, ‖saddleRatioSq (centreSaddle a₁ (tp r) (vp r)) * cexp (-vp r) *
      cexp (-(2 * π * tp r * I)) - 1‖ ≤ 1 / 4096)
    {η : ℂ} (hη : η = 1 ∨ η = -1) {r₀ : ℝ} (hr₀ : r₀ ∈ Icc (0 : ℝ) 1)
    (h0 : ‖centreAmp a₁ (tp r₀) (vp r₀) - η * bulkTerm (centreSaddle a₁ (tp r₀) (vp r₀))‖ ≤
      1 / 4096 * ‖bulkTerm (centreSaddle a₁ (tp r₀) (vp r₀))‖) :
    ∀ r ∈ Icc (0 : ℝ) 1,
      ‖centreAmp a₁ (tp r) (vp r) - η * bulkTerm (centreSaddle a₁ (tp r) (vp r))‖ ≤
        1 / 4096 * ‖bulkTerm (centreSaddle a₁ (tp r) (vp r))‖ := by
  have ha : Continuous fun r => centreSaddle a₁ (tp r) (vp r) := by
    unfold centreSaddle ratioShift
    exact continuous_const.add (((continuous_const.add hvp).div_const _).add
      ((Complex.continuous_ofReal.comp htp).mul continuous_const))
  have hA : Continuous fun r => centreAmp a₁ (tp r) (vp r) := by
    have h1 : Continuous fun r => cexp (-(vp r / 2)) :=
      Complex.continuous_exp.comp (hvp.div_const _).neg
    have h2 : Continuous fun r => cexp (-(π * tp r * I)) :=
      Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.comp htp)).mul continuous_const).neg
    exact ((continuous_const.mul (continuous_saddleTerm_comp ha hR)).mul h1).mul h2
  have hB := continuous_bulkTerm_comp ha hR
  have hsq : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖centreAmp a₁ (tp r) (vp r) ^ 2 - bulkTerm (centreSaddle a₁ (tp r) (vp r)) ^ 2‖ ≤
        1 / 4096 * ‖bulkTerm (centreSaddle a₁ (tp r) (vp r))‖ ^ 2 := by
    intro r _
    refine norm_sq_sub_sq_le (hR r) ?_
    have e1 : cexp (-(vp r / 2)) ^ 2 = cexp (-vp r) := by
      rw [sq, ← Complex.exp_add]
      congr 1
      ring
    have e2 : cexp (-(π * tp r * I)) ^ 2 = cexp (-(2 * π * tp r * I)) := by
      rw [sq, ← Complex.exp_add]
      congr 1
      ring
    rw [e1, e2]
    exact hQ r
  have hdich := norm_sub_le_or_norm_add_le hA.continuousOn hB.continuousOn
    (fun r _ => (hR r).bulkTerm_ne_zero) (by norm_num : (1 / 4096 : ℝ) ≤ 1 / 2) hsq
  rcases hη with rfl | rfl
  · simp only [one_mul] at h0 ⊢
    rcases hdich with hd | hd
    · exact hd
    · exact (not_norm_sub_le_and_norm_add_le (hR r₀).bulkTerm_ne_zero h0 (hd r₀ hr₀)).elim
  · simp only [neg_mul, one_mul, sub_neg_eq_add] at h0 ⊢
    rcases hdich with hd | hd
    · exact (not_norm_sub_le_and_norm_add_le (hR r₀).bulkTerm_ne_zero (hd r₀ hr₀) h0).elim
    · exact hd

/-- **A family with the sign of the central collision.** As far out as wanted there are a base
point and `t ∈ {0, 1}` such that for all `|v| ≤ 1` the saddle `a(v)` is in the saddle region and
`2S₀ e^{−v/2} = −B₀` up to `|B₀|/4096`: the model `B₀ + 2S₀ cos ζ` has the zeros `ζ ≈ ±√v`. -/
theorem exists_centre_family (σ₀ : ℝ) : ∃ (a₁ : ℂ) (t : ℝ), ∀ v : ℂ, ‖v‖ ≤ 1 →
    SaddleRegion (centreSaddle a₁ t v) ∧ σ₀ ≤ (centreSaddle a₁ t v).re ∧
      ‖2 * saddleTerm (centreSaddle a₁ t v) * cexp (-(v / 2)) +
        bulkTerm (centreSaddle a₁ t v)‖ ≤ 1 / 4096 * ‖bulkTerm (centreSaddle a₁ t v)‖ := by
  obtain ⟨σ₂, h51, hthr⟩ := exists_sign_threshold
  obtain ⟨a₁, ha, hf, hlo, hhi⟩ := exists_basePoint (max σ₂ (σ₀ + 1))
  have h1 : σ₂ ≤ a₁.re := (le_max_left _ _).trans ha
  have h2 : σ₀ + 1 ≤ a₁.re := (le_max_right _ _).trans ha
  have hspec : ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → ∀ {v : ℂ}, ‖v‖ ≤ 1 →
      SaddleRegion (centreSaddle a₁ t v) ∧ a₁.re - 1 ≤ (centreSaddle a₁ t v).re ∧
        ‖saddleRatioSq (centreSaddle a₁ t v) * cexp (-v) * cexp (-(2 * π * t * I)) - 1‖ ≤
          1 / 4096 :=
    fun ht0 ht1 _ hv => centreSaddle_spec (h51.trans h1) hf hlo hhi (hthr _ h1) ht0 ht1 hv
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hclamp : Continuous fun r : ℝ => max 0 (min r 1) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hc0 : ∀ r : ℝ, 0 ≤ max 0 (min r 1) := fun r => le_max_left _ _
  have hc1 : ∀ r : ℝ, max 0 (min r 1) ≤ 1 := fun r => max_le zero_le_one (min_le_right _ _)
  have hz : ‖(0 : ℂ)‖ ≤ 1 := by rw [norm_zero]; exact zero_le_one
  -- the sign at `v = 0`, `t = 0`
  obtain ⟨η, hη, hbase⟩ : ∃ η : ℂ, (η = 1 ∨ η = -1) ∧
      ‖centreAmp a₁ 0 0 - η * bulkTerm (centreSaddle a₁ 0 0)‖ ≤
        1 / 4096 * ‖bulkTerm (centreSaddle a₁ 0 0)‖ := by
    have hR0 := (hspec le_rfl zero_le_one hz).1
    have hsq : ‖centreAmp a₁ 0 0 ^ 2 - bulkTerm (centreSaddle a₁ 0 0) ^ 2‖ ≤
        1 / 4096 * ‖bulkTerm (centreSaddle a₁ 0 0)‖ ^ 2 := by
      refine norm_sq_sub_sq_le hR0 ?_
      have e1 : cexp (-((0 : ℂ) / 2)) ^ 2 = cexp (-(0 : ℂ)) := by simp
      have e2 : cexp (-(π * ((0 : ℝ) : ℂ) * I)) ^ 2 = cexp (-(2 * π * ((0 : ℝ) : ℂ) * I)) := by
        simp
      rw [e1, e2]
      exact (hspec le_rfl zero_le_one hz).2.2
    rcases norm_sub_le_or_norm_add_le (A := fun _ : ℝ => centreAmp a₁ 0 0)
      (B := fun _ : ℝ => bulkTerm (centreSaddle a₁ 0 0)) continuousOn_const continuousOn_const
      (fun _ _ => hR0.bulkTerm_ne_zero) (by norm_num : (1 / 4096 : ℝ) ≤ 1 / 2)
      (fun _ _ => hsq) with hd | hd
    · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using hd 0 h00⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_mul, one_mul, sub_neg_eq_add] using hd 0 h00⟩
  -- along the segment from `0` to `v` at a fixed `t`
  have hseg : ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → ∀ {η : ℂ}, (η = 1 ∨ η = -1) →
      ‖centreAmp a₁ t 0 - η * bulkTerm (centreSaddle a₁ t 0)‖ ≤
        1 / 4096 * ‖bulkTerm (centreSaddle a₁ t 0)‖ →
      ∀ v : ℂ, ‖v‖ ≤ 1 → ‖centreAmp a₁ t v - η * bulkTerm (centreSaddle a₁ t v)‖ ≤
        1 / 4096 * ‖bulkTerm (centreSaddle a₁ t v)‖ := by
    intro t ht0 ht1 η hη h0 v hv
    have hn : ∀ r : ℝ, ‖((max 0 (min r 1) : ℝ) : ℂ) * v‖ ≤ 1 := fun r => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 r)]
      calc max 0 (min r 1) * ‖v‖ ≤ 1 * 1 :=
            mul_le_mul (hc1 r) hv (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h := norm_centreAmp_sub_le_of_path (a₁ := a₁)
      (vp := fun r => ((max 0 (min r 1) : ℝ) : ℂ) * v) (tp := fun _ => t)
      ((Complex.continuous_ofReal.comp hclamp).mul continuous_const) continuous_const
      (fun r => (hspec ht0 ht1 (hn r)).1) (fun r => (hspec ht0 ht1 (hn r)).2.2) hη h00
      (by simpa only [min_eq_left zero_le_one, max_self, Complex.ofReal_zero, zero_mul] using h0)
      1 h11
    simpa only [min_self, max_eq_right zero_le_one, Complex.ofReal_one, one_mul] using h
  -- the bridge from `t = 0` to `t = 1` at `v = 0`
  have hbr := norm_centreAmp_sub_le_of_path (a₁ := a₁) (vp := fun _ => (0 : ℂ))
    (tp := fun r => max 0 (min r 1)) continuous_const hclamp
    (fun r => (hspec (hc0 r) (hc1 r) hz).1) (fun r => (hspec (hc0 r) (hc1 r) hz).2.2) hη h00
    (by simpa only [min_eq_left zero_le_one, max_self] using hbase) 1 h11
  simp only [min_self, max_eq_right zero_le_one] at hbr
  rcases hη with rfl | rfl
  · -- the sign `+1` at `t = 0`: take `t = 1`
    refine ⟨a₁, 1, fun v hv => ?_⟩
    obtain ⟨hreg, hre, -⟩ := hspec zero_le_one le_rfl hv
    refine ⟨hreg, by linarith, ?_⟩
    have h := hseg zero_le_one le_rfl (Or.inl rfl) hbr v hv
    have e : centreAmp a₁ 1 v - 1 * bulkTerm (centreSaddle a₁ 1 v) =
        -(2 * saddleTerm (centreSaddle a₁ 1 v) * cexp (-(v / 2)) +
          bulkTerm (centreSaddle a₁ 1 v)) := by
      have eπ : cexp (-((π : ℂ) * I)) = -1 := by
        rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
      rw [centreAmp, Complex.ofReal_one, mul_one, eπ]
      ring
    rwa [e, norm_neg] at h
  · -- the sign `−1` at `t = 0`
    refine ⟨a₁, 0, fun v hv => ?_⟩
    obtain ⟨hreg, hre, -⟩ := hspec le_rfl zero_le_one hv
    refine ⟨hreg, by linarith, ?_⟩
    have h := hseg le_rfl zero_le_one (Or.inr rfl) hbase v hv
    have e : centreAmp a₁ 0 v - -1 * bulkTerm (centreSaddle a₁ 0 v) =
        2 * saddleTerm (centreSaddle a₁ 0 v) * cexp (-(v / 2)) +
          bulkTerm (centreSaddle a₁ 0 v) := by
      rw [centreAmp, Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero]
      ring
    rwa [e] at h

/-! ## The centre value on the family -/

theorem differentiableAt_saddleTime {a : ℂ} (ha : a ≠ 0) : DifferentiableAt ℂ saddleTime a := by
  have h : DifferentiableAt ℂ (fun a : ℂ => (π : ℂ) * cexp (2 * a) / a) a :=
    ((differentiableAt_const _).mul ((differentiableAt_id.const_mul 2).cexp)).div
      differentiableAt_id ha
  exact h

theorem differentiableAt_bulkTerm {a : ℂ} (h : SaddleRegion a) :
    DifferentiableAt ℂ bulkTerm a := by
  have hτ := differentiableAt_saddleTime h.ne_zero
  have hτ0 : saddleTime a ≠ 0 := fun h0 => by
    have h1 := h.time_re_pos
    rw [h0, Complex.zero_re] at h1
    exact lt_irrefl _ h1
  have h1 : DifferentiableAt ℂ (fun a => ((π : ℂ) / saddleTime a) ^ (1 / 2 : ℂ)) a :=
    ((differentiableAt_const _).div hτ hτ0).cpow (differentiableAt_const _)
      (pi_div_mem_slitPlane h.time_re_pos)
  exact (differentiableAt_const _).mul h1

/-- **The centre value over the bulk term is `1 − e^{v/2}` up to `1/1024`** at a saddle of the
region with the model at the centre and `2S₀ e^{−v/2} = −B₀` up to `|B₀|/4096`, `|v| ≤ 1`. -/
theorem norm_centreValue_div_bulkTerm_sub_le {a v : ℂ} (hR : SaddleRegion a) (hv : ‖v‖ ≤ 1)
    (hmodel : ‖centreValue (saddleTime a) - bulkTerm a - 2 * saddleTerm a‖ ≤
      1 / 16384 * (‖bulkTerm a‖ + ‖saddleTerm a‖))
    (hsign : ‖2 * saddleTerm a * cexp (-(v / 2)) + bulkTerm a‖ ≤ 1 / 4096 * ‖bulkTerm a‖) :
    ‖centreValue (saddleTime a) / bulkTerm a - (1 - cexp (v / 2))‖ ≤ 1 / 1024 := by
  have hB0 := hR.bulkTerm_ne_zero
  have hBn : 0 < ‖bulkTerm a‖ := norm_pos_iff.mpr hB0
  -- `|e^{v/2}| ≤ 2`
  have hE : ‖cexp (v / 2)‖ ≤ 2 := by
    have h1 : (v / 2).re ≤ 1 / 2 := by
      have h2 := Complex.re_le_norm (v / 2)
      have h3 : ‖v / 2‖ = ‖v‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
      linarith
    have h4 : Real.exp (1 / 2) ≤ 2 := by
      have h5 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      have h6 := Real.exp_one_lt_d9
      nlinarith [Real.exp_pos (1 / 2)]
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr h1).trans h4
  have hEE : cexp (v / 2) * cexp (-(v / 2)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  -- `2S₀ = e^{v/2}(δ − B₀)` with `δ = 2S₀e^{−v/2} + B₀`
  obtain ⟨δ, hδ⟩ : ∃ δ : ℂ, δ = 2 * saddleTerm a * cexp (-(v / 2)) + bulkTerm a := ⟨_, rfl⟩
  have hδn : ‖δ‖ ≤ 1 / 4096 * ‖bulkTerm a‖ := by rw [hδ]; exact hsign
  have h2S : 2 * saddleTerm a = cexp (v / 2) * (δ - bulkTerm a) := by
    rw [hδ]
    linear_combination (-2 * saddleTerm a) * hEE
  have hSn : ‖saddleTerm a‖ ≤ 2 * ‖bulkTerm a‖ := by
    have h1 : ‖2 * saddleTerm a‖ ≤ 2 * (1 / 4096 * ‖bulkTerm a‖ + ‖bulkTerm a‖) := by
      rw [h2S, norm_mul]
      exact mul_le_mul hE ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _) (by norm_num)
    rw [norm_mul, Complex.norm_ofNat] at h1
    linarith
  -- the error of the model
  obtain ⟨e, he⟩ : ∃ e : ℂ, e = centreValue (saddleTime a) - bulkTerm a - 2 * saddleTerm a :=
    ⟨_, rfl⟩
  have hen : ‖e‖ ≤ 3 / 16384 * ‖bulkTerm a‖ := by
    rw [he]
    linarith
  have key : centreValue (saddleTime a) / bulkTerm a - (1 - cexp (v / 2)) =
      (e + cexp (v / 2) * δ) / bulkTerm a := by
    have h1 : centreValue (saddleTime a) =
        e + bulkTerm a + cexp (v / 2) * (δ - bulkTerm a) := by
      rw [he, ← h2S]
      ring
    rw [h1]
    field_simp
    ring
  rw [key, norm_div, div_le_iff₀ hBn]
  calc ‖e + cexp (v / 2) * δ‖ ≤ ‖e‖ + ‖cexp (v / 2)‖ * ‖δ‖ := by
        rw [← norm_mul]
        exact norm_add_le _ _
    _ ≤ 3 / 16384 * ‖bulkTerm a‖ + 2 * (1 / 4096 * ‖bulkTerm a‖) :=
        add_le_add hen (mul_le_mul hE hδn (norm_nonneg _) (by norm_num))
    _ ≤ 1 / 1024 * ‖bulkTerm a‖ := by linarith

/-! ## The simple zero -/

/-- **The centre value has a simple zero at forward times of arbitrarily large real part.** -/
theorem exists_centreValue_simple_zero (T : ℝ) :
    ∃ τ₀ : ℂ, T < τ₀.re ∧ centreValue τ₀ = 0 ∧ deriv centreValue τ₀ ≠ 0 := by
  obtain ⟨σm, hmodel⟩ :=
    exists_forall_norm_complexHeat_sub_model_le (ε := 1 / 16384) (by norm_num)
  obtain ⟨a₁, t, hfam⟩ := exists_centre_family (max σm (T + 1))
  have hR : ∀ v : ℂ, ‖v‖ ≤ 1 → SaddleRegion (centreSaddle a₁ t v) := fun v hv => (hfam v hv).1
  -- the ratio is `1 − e^{v/2}` up to `1/1024` on the closed unit disc
  have hest : ∀ v : ℂ, ‖v‖ ≤ 1 → ‖centreRatio a₁ t v - (1 - cexp (v / 2))‖ ≤ 1 / 1024 := by
    intro v hv
    obtain ⟨hreg, hre, hsign⟩ := hfam v hv
    have hm := hmodel _ hreg ((le_max_left _ _).trans hre) 0 (by rw [norm_zero]; norm_num)
    rw [zero_div, Complex.cos_zero, mul_one] at hm
    exact norm_centreValue_div_bulkTerm_sub_le hreg hv hm hsign
  -- the ratio is holomorphic at the points of the closed unit disc
  have hsad : Differentiable ℂ fun v : ℂ => centreSaddle a₁ t v := by
    simp only [centreSaddle, ratioShift]
    fun_prop
  have hdiff : ∀ v : ℂ, ‖v‖ ≤ 1 → DifferentiableAt ℂ (centreRatio a₁ t) v := by
    intro v hv
    have hreg := hR v hv
    have hτ : DifferentiableAt ℂ (fun v => saddleTime (centreSaddle a₁ t v)) v :=
      (differentiableAt_saddleTime hreg.ne_zero).comp v (hsad v)
    have hN : DifferentiableAt ℂ (fun v => centreValue (saddleTime (centreSaddle a₁ t v))) v :=
      (differentiable_centreValue _).comp v hτ
    have hD : DifferentiableAt ℂ (fun v => bulkTerm (centreSaddle a₁ t v)) v :=
      (differentiableAt_bulkTerm hreg).comp v (hsad v)
    exact hN.div hD hreg.bulkTerm_ne_zero
  have hDon : DifferentiableOn ℂ (centreRatio a₁ t) (closedBall (0 : ℂ) 1) := fun v hv =>
    (hdiff v (mem_closedBall_zero_iff.mp hv)).differentiableWithinAt
  -- the value at the centre and on the circle of radius `1/2`
  have h0 : ‖centreRatio a₁ t 0‖ ≤ 1 / 1024 := by
    have h := hest 0 (by rw [norm_zero]; exact zero_le_one)
    rwa [zero_div, Complex.exp_zero, sub_self, sub_zero] at h
  have hsph : ∀ v ∈ sphere (0 : ℂ) (1 / 2),
      1 / 8 ≤ ‖centreRatio a₁ t v - centreRatio a₁ t 0‖ := by
    intro v hv
    have hvn : ‖v‖ = 1 / 2 := mem_sphere_zero_iff_norm.mp hv
    have hw : ‖v / 2‖ = 1 / 4 := by
      rw [norm_div, Complex.norm_ofNat, hvn]
      norm_num
    have h1 := Complex.norm_exp_sub_one_sub_id_le (x := v / 2) (by rw [hw]; norm_num)
    rw [hw] at h1
    have h2 := hest v (by rw [hvn]; norm_num)
    have h3 : ‖v / 2‖ ≤ ‖1 - cexp (v / 2)‖ + ‖cexp (v / 2) - 1 - v / 2‖ := by
      have e : v / 2 = -(1 - cexp (v / 2)) - (cexp (v / 2) - 1 - v / 2) := by ring
      calc ‖v / 2‖ = ‖-(1 - cexp (v / 2)) - (cexp (v / 2) - 1 - v / 2)‖ := congrArg norm e
        _ ≤ ‖-(1 - cexp (v / 2))‖ + ‖cexp (v / 2) - 1 - v / 2‖ := norm_sub_le _ _
        _ = ‖1 - cexp (v / 2)‖ + ‖cexp (v / 2) - 1 - v / 2‖ := by rw [norm_neg]
    have h4 : ‖1 - cexp (v / 2)‖ ≤ ‖centreRatio a₁ t v - centreRatio a₁ t 0‖ +
        ‖centreRatio a₁ t v - (1 - cexp (v / 2))‖ + ‖centreRatio a₁ t 0‖ := by
      have e : 1 - cexp (v / 2) = (centreRatio a₁ t v - centreRatio a₁ t 0) -
          (centreRatio a₁ t v - (1 - cexp (v / 2))) + centreRatio a₁ t 0 := by ring
      calc ‖1 - cexp (v / 2)‖ = ‖(centreRatio a₁ t v - centreRatio a₁ t 0) -
            (centreRatio a₁ t v - (1 - cexp (v / 2))) + centreRatio a₁ t 0‖ := congrArg norm e
        _ ≤ ‖(centreRatio a₁ t v - centreRatio a₁ t 0) -
            (centreRatio a₁ t v - (1 - cexp (v / 2)))‖ + ‖centreRatio a₁ t 0‖ :=
          norm_add_le _ _
        _ ≤ ‖centreRatio a₁ t v - centreRatio a₁ t 0‖ +
            ‖centreRatio a₁ t v - (1 - cexp (v / 2))‖ + ‖centreRatio a₁ t 0‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
    rw [hw] at h3
    norm_num at h1
    linarith
  -- the ratio is not constant near the centre
  have hfreq : ∃ᶠ z in 𝓝 (0 : ℂ), centreRatio a₁ t z ≠ centreRatio a₁ t 0 := by
    by_contra hcon
    rw [not_frequently] at hcon
    have hcon' : ∀ᶠ z in 𝓝 (0 : ℂ), centreRatio a₁ t z = centreRatio a₁ t 0 :=
      hcon.mono fun z hz => not_not.mp hz
    have han : AnalyticOnNhd ℂ (centreRatio a₁ t) (ball 0 1) :=
      DifferentiableOn.analyticOnNhd (fun v hv =>
        (hdiff v (mem_ball_zero_iff.mp hv).le).differentiableWithinAt) isOpen_ball
    have heq := han.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_const (v := centreRatio a₁ t 0)) (convex_ball (0 : ℂ) 1).isPreconnected
      (mem_ball_self one_pos) hcon'
    have hmem : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      norm_num
    have h2 : centreRatio a₁ t (1 / 2) = centreRatio a₁ t 0 := heq hmem
    have h1 := hsph (1 / 2) (by rw [mem_sphere_zero_iff_norm]; norm_num)
    rw [h2, sub_self, norm_zero] at h1
    norm_num at h1
  -- a zero of the ratio in the disc of radius `1/2`
  have hdcl : DiffContOnCl ℂ (centreRatio a₁ t) (ball 0 (1 / 2)) :=
    hDon.diffContOnCl_ball (closedBall_subset_closedBall (by norm_num))
  have himg := hdcl.ball_subset_image_closedBall (by norm_num : (0 : ℝ) < 1 / 2) hsph hfreq
  obtain ⟨vs, hvs, hzero⟩ := himg (show (0 : ℂ) ∈ ball (centreRatio a₁ t 0) (1 / 8 / 2) by
    rw [mem_ball, dist_eq_norm, zero_sub, norm_neg]
    linarith)
  have hvs' : ‖vs‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hvs
  have hreg := hR vs (by linarith)
  have hB0 := hreg.bulkTerm_ne_zero
  have hc0 : centreValue (saddleTime (centreSaddle a₁ t vs)) = 0 := by
    have h := hzero
    rw [centreRatio, div_eq_zero_iff] at h
    exact h.resolve_right hB0
  refine ⟨saddleTime (centreSaddle a₁ t vs), ?_, hc0, fun hd => ?_⟩
  · have h1 := re_le_saddleTime_re hreg
    have h2 := (le_max_right σm (T + 1)).trans (hfam vs (by linarith)).2.1
    linarith
  · -- a double zero of the centre value is a critical point of the ratio
    have hcd : HasDerivAt centreValue 0 (saddleTime (centreSaddle a₁ t vs)) := by
      have h := (differentiable_centreValue (saddleTime (centreSaddle a₁ t vs))).hasDerivAt
      rwa [hd] at h
    have hτd : DifferentiableAt ℂ (fun v => saddleTime (centreSaddle a₁ t v)) vs :=
      (differentiableAt_saddleTime hreg.ne_zero).comp vs (hsad vs)
    have hN : HasDerivAt (fun v => centreValue (saddleTime (centreSaddle a₁ t v))) 0 vs := by
      have h := hcd.comp vs hτd.hasDerivAt
      rwa [zero_mul] at h
    have hDd : DifferentiableAt ℂ (fun v => bulkTerm (centreSaddle a₁ t v)) vs :=
      (differentiableAt_bulkTerm hreg).comp vs (hsad vs)
    have hΦ : HasDerivAt (centreRatio a₁ t) 0 vs := by
      have h := hN.div hDd.hasDerivAt hB0
      simp only [hc0, zero_mul, sub_zero, zero_div] at h
      exact h
    have hexp : HasDerivAt (fun v : ℂ => 1 - cexp (v / 2)) (-(cexp (vs / 2) * (1 / 2))) vs :=
      (((hasDerivAt_id vs).div_const 2).cexp).const_sub 1
    have hg : HasDerivAt (fun v => centreRatio a₁ t v - (1 - cexp (v / 2)))
        (0 - -(cexp (vs / 2) * (1 / 2))) vs := hΦ.sub hexp
    -- the circle of radius `1/2` around the zero lies in the closed unit disc
    have hsub : ∀ v : ℂ, ‖v - vs‖ ≤ 1 / 2 → ‖v‖ ≤ 1 := fun v hv => by
      have h2 := norm_add_le (v - vs) vs
      rw [sub_add_cancel] at h2
      linarith
    have hgd : DiffContOnCl ℂ (fun v => centreRatio a₁ t v - (1 - cexp (v / 2)))
        (ball vs (1 / 2)) := by
      have hD2 : DifferentiableOn ℂ (fun v => centreRatio a₁ t v - (1 - cexp (v / 2)))
          (closedBall (0 : ℂ) 1) := hDon.sub (by fun_prop)
      exact hD2.diffContOnCl_ball fun v hv =>
        mem_closedBall_zero_iff.mpr (hsub v (by rwa [mem_closedBall, dist_eq_norm] at hv))
    have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by norm_num : (0 : ℝ) < 1 / 2) hgd (C := 1 / 1024) fun v hv =>
        hest v (hsub v (by rw [mem_sphere, dist_eq_norm] at hv; exact hv.le))
    rw [hg.deriv] at hbound
    have hlow : 3 / 8 ≤ ‖(0 : ℂ) - -(cexp (vs / 2) * (1 / 2))‖ := by
      rw [zero_sub, neg_neg, norm_mul, Complex.norm_exp]
      have h1 : -(1 / 4 : ℝ) ≤ (vs / 2).re := by
        have h2 := (abs_le.mp (Complex.abs_re_le_norm (vs / 2))).1
        have h3 : ‖vs / 2‖ = ‖vs‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
        linarith
      have h4 : (3 / 4 : ℝ) ≤ Real.exp ((vs / 2).re) :=
        le_trans (by linarith) (Real.add_one_le_exp _)
      have h5 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [h5]
      linarith
    have h6 : (1 / 1024 : ℝ) / (1 / 2) = 1 / 512 := by norm_num
    rw [h6] at hbound
    linarith

/-- **A collision of exactly one pair at the centre** exists at forward times of arbitrarily
large real part: `H_{τ₀}` has a zero of order two at `0`. -/
theorem exists_isCollision_center_two (T : ℝ) : ∃ τ₀ : ℂ, T < τ₀.re ∧ IsCollision τ₀ 0 2 := by
  obtain ⟨τ₀, hT, h0, hd⟩ := exists_centreValue_simple_zero T
  refine ⟨τ₀, hT, fun i hi => ?_, fun h2 => hd ?_⟩
  · interval_cases i
    · rw [iteratedDeriv_zero]
      exact h0
    · exact iteratedDeriv_complexHeat_center_odd τ₀ odd_one
  · have h := iteratedDeriv_centreValue 1 τ₀
    rw [iteratedDeriv_one, mul_one, h2, mul_zero] at h
    exact h

end

end GaloisForLFunctions.GaloisTheoryOfZeros
