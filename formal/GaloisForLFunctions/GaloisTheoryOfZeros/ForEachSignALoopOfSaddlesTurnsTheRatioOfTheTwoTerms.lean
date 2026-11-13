import GaloisForLFunctions.GaloisTheoryOfZeros.ACollisionAwayFromTheCentreExistsAtAForwardTime

/-!
# For each sign a loop of saddles turns the ratio of the two terms

On the loop of saddles of a base point `a₁` the squared ratio `Q = (2S₀/B₀)²` follows
`1/cos² ξ₀(s)`, so `2S₀ cos ξ₀(s) = ±B₀` up to `|B₀|/4096` with a sign that is constant on the
loop but not determined by the construction. The sign decides which zeros of the model
`B₀ + 2S₀ cos ζ` are exchanged: those near `2πk` or those near `π + 2πk`.

**Theorem** (`exists_isSignedLoop`). For each of the two signs there is a loop of saddles, as far
out as wanted, on which `2S₀ cos ξ₀(s) = εB₀` up to `|B₀|/4096`.

Proof. `Q(a₁ + h) ≈ Q(a₁)e^{2D₁h}`, `D₁ = P₁(2a₁ − 1)`: moving the loop by the half period
`πi/D₁` leaves `Q` unchanged and reverses the sign of the ratio. Precisely, on the family
`a₁ + h(s) + t·πi/D₁` the function `A = 2S₀ cos ξ₀(s) e^{−iπt}` has `A² ≈ B₀²`, so along a path
`A ≈ B₀` throughout or `A ≈ −B₀` throughout (`norm_sub_le_or_norm_add_le`). The loops `t = 0` and
`t = 1` are joined by the bridge `s = 0`, `0 ≤ t ≤ 1`, and `e^{−iπ} = −1`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The family of saddles -/

/-- The half period of the squared ratio at the base point: `πi/D₁`, `D₁ = P₁(2a₁ − 1)`. -/
def halfPeriod (a₁ : ℂ) : ℂ := π * I / (saddleP a₁ * (2 * a₁ - 1))

/-- The family of saddles: the loop of `a₁` moved by `t` half periods. -/
def signSaddle (a₁ : ℂ) (s t : ℝ) : ℂ := a₁ + (loopShift a₁ s + t * halfPeriod a₁)

theorem signSaddle_eq (a₁ : ℂ) (s t : ℝ) :
    signSaddle a₁ s t = loopSaddle a₁ s + t * halfPeriod a₁ := by
  rw [signSaddle, loopSaddle]
  ring

theorem continuous_signSaddle_left (a₁ : ℂ) (t : ℝ) : Continuous fun s => signSaddle a₁ s t := by
  simp only [signSaddle_eq]
  exact (continuous_loopSaddle a₁).add continuous_const

theorem continuous_signSaddle_right (a₁ : ℂ) (s : ℝ) : Continuous fun t => signSaddle a₁ s t := by
  simp only [signSaddle_eq]
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

theorem signSaddle_one_left (a₁ : ℂ) (t : ℝ) : signSaddle a₁ 1 t = signSaddle a₁ 0 t := by
  rw [signSaddle_eq, signSaddle_eq, loopSaddle_one]

theorem norm_halfPeriod_le {a₁ : ℂ} (hσ : 1 ≤ a₁.re) (him0 : 0 ≤ a₁.im) (him1 : a₁.im ≤ 1) :
    ‖halfPeriod a₁‖ ≤ Real.exp (-(2 * a₁.re)) := by
  have hπ := Real.pi_pos
  obtain ⟨hn_lo, -⟩ := norm_two_mul_sub_one_bounds hσ him0 him1
  have hn1 : 1 ≤ ‖2 * a₁ - 1‖ := by linarith
  have hpos : 0 < π * Real.exp (2 * a₁.re) * ‖2 * a₁ - 1‖ :=
    mul_pos (mul_pos hπ (Real.exp_pos _)) (by linarith)
  have e : Real.exp (-(2 * a₁.re)) * (π * Real.exp (2 * a₁.re) * ‖2 * a₁ - 1‖) =
      π * ‖2 * a₁ - 1‖ * (Real.exp (-(2 * a₁.re)) * Real.exp (2 * a₁.re)) := by ring
  rw [halfPeriod, norm_div, norm_mul, norm_mul, norm_saddleP, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ, div_le_iff₀ hpos, e,
    SaddleRegion.exp_neg_two_mul_exp, mul_one]
  nlinarith

/-- **The family at a base point.** If `Re a₁ = σ ≥ 51`, `Re f(a₁) = 0`,
`3/10 ≤ (π/4 − Im a₁)σ ≤ 7/10` and `(2 + M)²σ⁴e^{−σ} ≤ 1/300000`, then for `0 ≤ t ≤ 1` the point
`a(s, t)` of the family is in the saddle region, within `1` of `a₁`, and
`|Q(a(s, t)) cos² ξ₀(s) e^{−2πit} − 1| ≤ 1/4096`. -/
theorem signSaddle_spec {a₁ : ℂ} (hσ : 51 ≤ a₁.re) (hf : (saddlePhaseValue a₁).re = 0)
    (hlo : 3 / 10 ≤ (π / 4 - a₁.im) * a₁.re) (hhi : (π / 4 - a₁.im) * a₁.re ≤ 7 / 10)
    (hK : (1 + (loopConst + 1)) ^ 2 * a₁.re ^ 4 * Real.exp (-a₁.re) ≤ 1 / 300000) (s : ℝ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SaddleRegion (signSaddle a₁ s t) ∧ a₁.re - 1 ≤ (signSaddle a₁ s t).re ∧
      ‖saddleRatioSq (signSaddle a₁ s t) * Complex.cos (turnPoint s) ^ 2 *
        cexp (-(2 * π * t * I)) - 1‖ ≤ 1 / 4096 := by
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
  have hhn : ‖loopShift a₁ s + t * halfPeriod a₁‖ ≤
      (loopConst + 1) * Real.exp (-(2 * a₁.re)) := by
    have h1 := norm_loopShift_le hσ him0 him1 hf s
    have h2 := norm_halfPeriod_le (by linarith : 1 ≤ a₁.re) him0 him1
    have h3 : ‖(t : ℂ) * halfPeriod a₁‖ ≤ Real.exp (-(2 * a₁.re)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      calc t * ‖halfPeriod a₁‖ ≤ 1 * ‖halfPeriod a₁‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ ≤ Real.exp (-(2 * a₁.re)) := by rw [one_mul]; exact h2
    have h4 := norm_add_le (loopShift a₁ s) ((t : ℂ) * halfPeriod a₁)
    linarith
  obtain ⟨hk1, hk2⟩ := loop_smallness hM0 hσ (norm_nonneg _) hhn
  have hhK : ‖loopShift a₁ s + t * halfPeriod a₁‖ ≤
      (1 + (loopConst + 1)) ^ 2 * a₁.re ^ 4 * Real.exp (-a₁.re) := by
    have h1 : ‖loopShift a₁ s + t * halfPeriod a₁‖ * 1 ≤
        ‖loopShift a₁ s + t * halfPeriod a₁‖ * a₁.re :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    linarith
  obtain ⟨hreg, hre⟩ := saddleRegion_add (h := loopShift a₁ s + t * halfPeriod a₁) hσ hlo hhi
    (hk1.trans hK)
  refine ⟨hreg, hre, ?_⟩
  -- the squared ratio on the family
  obtain ⟨hn_lo, -⟩ := norm_two_mul_sub_one_bounds (by linarith : 1 ≤ a₁.re) him0 him1
  have h2a : 2 * a₁ - 1 ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * a₁.re - 1) hn_lo)
  have hQne := (norm_log_saddleRatioSq_le (by linarith : 1 ≤ a₁.re) him0 him1 hf).1
  have h2h : 2 * a₁ - 1 + 2 * (loopShift a₁ s + t * halfPeriod a₁) ≠ 0 := by
    intro h0
    have hre' : (2 * a₁ - 1 + 2 * (loopShift a₁ s + t * halfPeriod a₁)).re =
        2 * a₁.re - 1 + 2 * (loopShift a₁ s + t * halfPeriod a₁).re := by simp
    rw [h0, Complex.zero_re] at hre'
    have h3 := (abs_le.mp ((Complex.abs_re_le_norm
      (loopShift a₁ s + t * halfPeriod a₁)).trans hhK)).1
    linarith
  have hcos0 := cos_turnPoint_ne_zero s
  have hP0 := saddleP_ne_zero a₁
  have hD0 : 2 * (saddleP a₁ * (2 * a₁ - 1)) ≠ 0 :=
    mul_ne_zero two_ne_zero (mul_ne_zero hP0 h2a)
  have hexp : cexp (2 * (saddleP a₁ * (2 * a₁ - 1)) * (loopShift a₁ s + t * halfPeriod a₁)) =
      (saddleRatioSq a₁)⁻¹ * (Complex.cos (turnPoint s) ^ 2)⁻¹ * cexp (2 * π * t * I) := by
    have e1 : 2 * (saddleP a₁ * (2 * a₁ - 1)) * loopShift a₁ s =
        -Complex.log (saddleRatioSq a₁) - 2 * Complex.log (Complex.cos (turnPoint s)) := by
      rw [loopShift, mul_div_cancel₀ _ hD0]
    have e2 : 2 * (saddleP a₁ * (2 * a₁ - 1)) * ((t : ℂ) * halfPeriod a₁) = 2 * π * t * I := by
      rw [halfPeriod]
      field_simp
    rw [mul_add, e1, e2, Complex.exp_add, Complex.exp_sub, Complex.exp_neg,
      Complex.exp_log hQne, two_mul, Complex.exp_add, Complex.exp_log hcos0, div_eq_mul_inv, sq]
  have hX := norm_remainder_sub_one_le (a₁ := a₁) (h := loopShift a₁ s + t * halfPeriod a₁)
    (by linarith) him0 him1
    (by linarith : (1 + (loopConst + 1)) ^ 2 * a₁.re ^ 4 * Real.exp (-a₁.re) ≤ 1 / 17) hhK hk2
  have key : ∀ Q C X E : ℂ, Q ≠ 0 → C ≠ 0 → E ≠ 0 →
      Q * (Q⁻¹ * C⁻¹ * E) * X * C * E⁻¹ = X := by
    intro Q C X E hQ hC hE
    field_simp
  rw [signSaddle, saddleRatioSq_add h2a h2h, hexp, Complex.exp_neg,
    key _ _ _ _ hQne (pow_ne_zero 2 hcos0) (Complex.exp_ne_zero _)]
  linarith

/-- The smallness of the family holds far out. -/
theorem exists_sign_threshold : ∃ σ₂ : ℝ, 51 ≤ σ₂ ∧ ∀ σ : ℝ, σ₂ ≤ σ →
    (1 + (loopConst + 1)) ^ 2 * σ ^ 4 * Real.exp (-σ) ≤ 1 / 300000 := by
  have ht : Tendsto (fun x : ℝ => (1 + (loopConst + 1)) ^ 2 * (x ^ 4 * Real.exp (-x))) atTop
      (𝓝 ((1 + (loopConst + 1)) ^ 2 * 0)) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul _
  rw [mul_zero] at ht
  obtain ⟨σ₂, hσ₂⟩ := eventually_atTop.mp
    (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 300000)))
  refine ⟨max σ₂ 51, le_max_right _ _, fun σ hσ => ?_⟩
  have h1 := (hσ₂ σ ((le_max_left _ _).trans hσ)).le
  calc (1 + (loopConst + 1)) ^ 2 * σ ^ 4 * Real.exp (-σ)
      = (1 + (loopConst + 1)) ^ 2 * (σ ^ 4 * Real.exp (-σ)) := by ring
    _ ≤ 1 / 300000 := h1

/-! ## The sign along a path of the family -/

theorem SaddleRegion.two_mul_sub_one_ne_zero {a : ℂ} (h : SaddleRegion a) : 2 * a - 1 ≠ 0 := by
  intro h0
  have hre : (2 * a - 1).re = 2 * a.re - 1 := by simp
  rw [h0, Complex.zero_re] at hre
  linarith [h.1]

theorem SaddleRegion.bulkTerm_ne_zero {a : ℂ} (h : SaddleRegion a) : bulkTerm a ≠ 0 := by
  have h1 := h.le_norm_bulkTerm
  have h2 : 0 < ‖kernelC 0‖ * Real.exp (-a.re) :=
    mul_pos (norm_pos_iff.mpr kernelC_zero_ne_zero) (Real.exp_pos _)
  exact norm_pos_iff.mp (lt_of_lt_of_le h2 h1)

/-- `A = 2S₀ c E` has `A² = (1 + e)B₀²` if `Q c² E² = 1 + e`. -/
theorem norm_sq_sub_sq_le {a c E : ℂ} (h : SaddleRegion a)
    (hQ : ‖saddleRatioSq a * c ^ 2 * E ^ 2 - 1‖ ≤ 1 / 4096) :
    ‖(2 * saddleTerm a * c * E) ^ 2 - bulkTerm a ^ 2‖ ≤ 1 / 4096 * ‖bulkTerm a‖ ^ 2 := by
  have hsq := two_mul_saddleTerm_sq h.ne_zero h.two_mul_sub_one_ne_zero
  have e : (2 * saddleTerm a * c * E) ^ 2 - bulkTerm a ^ 2 =
      bulkTerm a ^ 2 * (saddleRatioSq a * c ^ 2 * E ^ 2 - 1) := by
    rw [mul_pow, mul_pow, hsq]
    ring
  rw [e, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right hQ (sq_nonneg _)

/-- Both signs at one point are impossible. -/
theorem not_norm_sub_le_and_norm_add_le {A B : ℂ} (hB : B ≠ 0) (h1 : ‖A - B‖ ≤ 1 / 4096 * ‖B‖)
    (h2 : ‖A + B‖ ≤ 1 / 4096 * ‖B‖) : False := by
  have hBn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have h3 : ‖(A + B) - (A - B)‖ ≤ ‖A + B‖ + ‖A - B‖ := norm_sub_le _ _
  have e : (A + B) - (A - B) = 2 * B := by ring
  rw [e, norm_mul, Complex.norm_ofNat] at h3
  linarith

/-- **The sign is constant along a path of the family.** Let `a(r)` be a path of saddles of the
region with `|Q(a) cos² ξ₀(s(r)) e^{−2πit(r)} − 1| ≤ 1/4096`. If
`2S₀ cos ξ₀ e^{−iπt} = ηB₀` up to `|B₀|/4096` at one parameter, `η = ±1`, then at all. -/
theorem norm_signed_sub_le_of_path {a : ℝ → ℂ} {sp tp : ℝ → ℝ} (ha : Continuous a)
    (hR : ∀ r, SaddleRegion (a r)) (hsp : Continuous sp) (htp : Continuous tp)
    (hQ : ∀ r, ‖saddleRatioSq (a r) * Complex.cos (turnPoint (sp r)) ^ 2 *
      cexp (-(2 * π * tp r * I)) - 1‖ ≤ 1 / 4096)
    {η : ℂ} (hη : η = 1 ∨ η = -1) {r₀ : ℝ} (hr₀ : r₀ ∈ Icc (0 : ℝ) 1)
    (h0 : ‖2 * saddleTerm (a r₀) * Complex.cos (turnPoint (sp r₀)) * cexp (-(π * tp r₀ * I)) -
      η * bulkTerm (a r₀)‖ ≤ 1 / 4096 * ‖bulkTerm (a r₀)‖) :
    ∀ r ∈ Icc (0 : ℝ) 1,
      ‖2 * saddleTerm (a r) * Complex.cos (turnPoint (sp r)) * cexp (-(π * tp r * I)) -
        η * bulkTerm (a r)‖ ≤ 1 / 4096 * ‖bulkTerm (a r)‖ := by
  have hA : Continuous fun r =>
      2 * saddleTerm (a r) * Complex.cos (turnPoint (sp r)) * cexp (-(π * tp r * I)) := by
    have h1 : Continuous fun r => Complex.cos (turnPoint (sp r)) :=
      Complex.continuous_cos.comp (continuous_turnPoint.comp hsp)
    have h2 : Continuous fun r => cexp (-(π * tp r * I)) :=
      Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.comp htp)).mul continuous_const).neg
    exact ((continuous_const.mul (continuous_saddleTerm_comp ha hR)).mul h1).mul h2
  have hB := continuous_bulkTerm_comp ha hR
  have hsq : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖(2 * saddleTerm (a r) * Complex.cos (turnPoint (sp r)) * cexp (-(π * tp r * I))) ^ 2 -
        bulkTerm (a r) ^ 2‖ ≤ 1 / 4096 * ‖bulkTerm (a r)‖ ^ 2 := by
    intro r _
    refine norm_sq_sub_sq_le (hR r) ?_
    have e : cexp (-(π * tp r * I)) ^ 2 = cexp (-(2 * π * tp r * I)) := by
      rw [sq, ← Complex.exp_add]
      congr 1
      ring
    rw [e]
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

/-! ## Signed loops -/

/-- A closed loop of saddles in the saddle region on which `2S₀ cos ξ₀(s) = εB₀` up to
`|B₀|/4096`. -/
structure IsSignedLoop (ε : ℂ) (a : ℝ → ℂ) : Prop where
  continuous : Continuous a
  closed : a 1 = a 0
  region : ∀ s, SaddleRegion (a s)
  signed : ∀ s ∈ Icc (0 : ℝ) 1,
    ‖2 * saddleTerm (a s) * Complex.cos (turnPoint s) - ε * bulkTerm (a s)‖ ≤
      1 / 4096 * ‖bulkTerm (a s)‖

/-- **Signed loops of both signs exist**, as far out as wanted. -/
theorem exists_isSignedLoop (σ₀ : ℝ) : ∃ a₊ a₋ : ℝ → ℂ,
    IsSignedLoop 1 a₊ ∧ IsSignedLoop (-1) a₋ ∧ (∀ s, σ₀ ≤ (a₊ s).re) ∧ ∀ s, σ₀ ≤ (a₋ s).re := by
  obtain ⟨σ₂, h51, hthr⟩ := exists_sign_threshold
  obtain ⟨a₁, ha, hf, hlo, hhi⟩ := exists_basePoint (max σ₂ (σ₀ + 1))
  have h1 : σ₂ ≤ a₁.re := (le_max_left _ _).trans ha
  have h2 : σ₀ + 1 ≤ a₁.re := (le_max_right _ _).trans ha
  have hspec : ∀ (s : ℝ) {t : ℝ}, 0 ≤ t → t ≤ 1 →
      SaddleRegion (signSaddle a₁ s t) ∧ a₁.re - 1 ≤ (signSaddle a₁ s t).re ∧
        ‖saddleRatioSq (signSaddle a₁ s t) * Complex.cos (turnPoint s) ^ 2 *
          cexp (-(2 * π * t * I)) - 1‖ ≤ 1 / 4096 :=
    fun s t ht0 ht1 => signSaddle_spec (h51.trans h1) hf hlo hhi (hthr _ h1) s ht0 ht1
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hclamp : Continuous fun r : ℝ => max 0 (min r 1) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hc0 : ∀ r : ℝ, 0 ≤ max 0 (min r 1) := fun r => le_max_left _ _
  have hc1 : ∀ r : ℝ, max 0 (min r 1) ≤ 1 := fun r => max_le zero_le_one (min_le_right _ _)
  -- the sign of the first loop at its base
  have hdich := norm_sub_le_or_norm_add_le
    (A := fun _ : ℝ => 2 * saddleTerm (signSaddle a₁ 0 0) * Complex.cos (turnPoint 0) *
      cexp (-(π * (0 : ℝ) * I)))
    (B := fun _ : ℝ => bulkTerm (signSaddle a₁ 0 0)) continuousOn_const continuousOn_const
    (fun _ _ => (hspec 0 le_rfl zero_le_one).1.bulkTerm_ne_zero)
    (by norm_num : (1 / 4096 : ℝ) ≤ 1 / 2)
    (fun _ _ => norm_sq_sub_sq_le (hspec 0 le_rfl zero_le_one).1 (by
      have e : cexp (-(π * (0 : ℝ) * I)) ^ 2 = cexp (-(2 * π * (0 : ℝ) * I)) := by
        rw [sq, ← Complex.exp_add]
        congr 1
        ring
      rw [e]
      exact (hspec 0 le_rfl zero_le_one).2.2))
  obtain ⟨η, hη, hbase⟩ : ∃ η : ℂ, (η = 1 ∨ η = -1) ∧
      ‖2 * saddleTerm (signSaddle a₁ 0 0) * Complex.cos (turnPoint 0) *
        cexp (-(π * (0 : ℝ) * I)) - η * bulkTerm (signSaddle a₁ 0 0)‖ ≤
        1 / 4096 * ‖bulkTerm (signSaddle a₁ 0 0)‖ := by
    rcases hdich with hd | hd
    · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using hd 0 h00⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_mul, one_mul, sub_neg_eq_add] using hd 0 h00⟩
  -- the first loop, the bridge, the second loop
  have hL₀ := norm_signed_sub_le_of_path (a := fun s => signSaddle a₁ s 0) (sp := fun s => s)
    (tp := fun _ => 0) (continuous_signSaddle_left a₁ 0)
    (fun s => (hspec s le_rfl zero_le_one).1) continuous_id continuous_const
    (fun s => (hspec s le_rfl zero_le_one).2.2) hη h00 hbase
  have hbr := norm_signed_sub_le_of_path (a := fun r => signSaddle a₁ 0 (max 0 (min r 1)))
    (sp := fun _ => 0) (tp := fun r => max 0 (min r 1))
    ((continuous_signSaddle_right a₁ 0).comp hclamp)
    (fun r => (hspec 0 (hc0 r) (hc1 r)).1) continuous_const hclamp
    (fun r => (hspec 0 (hc0 r) (hc1 r)).2.2) hη h00
    (by simpa only [min_eq_left zero_le_one, max_self] using hbase)
  have hbr1 := hbr 1 h11
  simp only [min_self, max_eq_right zero_le_one] at hbr1
  have hL₁ := norm_signed_sub_le_of_path (a := fun s => signSaddle a₁ s 1) (sp := fun s => s)
    (tp := fun _ => 1) (continuous_signSaddle_left a₁ 1)
    (fun s => (hspec s zero_le_one le_rfl).1) continuous_id continuous_const
    (fun s => (hspec s zero_le_one le_rfl).2.2) hη h00 hbr1
  -- the two loops as signed loops
  have hS₀ : IsSignedLoop η (fun s => signSaddle a₁ s 0) :=
    ⟨continuous_signSaddle_left a₁ 0, signSaddle_one_left a₁ 0,
      fun s => (hspec s le_rfl zero_le_one).1, fun s hs => by
        have h := hL₀ s hs
        simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero,
          mul_one] at h
        exact h⟩
  have hS₁ : IsSignedLoop (-η) (fun s => signSaddle a₁ s 1) :=
    ⟨continuous_signSaddle_left a₁ 1, signSaddle_one_left a₁ 1,
      fun s => (hspec s zero_le_one le_rfl).1, fun s hs => by
        have h := hL₁ s hs
        have e : cexp (-(π * ((1 : ℝ) : ℂ) * I)) = -1 := by
          rw [Complex.ofReal_one, mul_one, Complex.exp_neg, Complex.exp_pi_mul_I]
          norm_num
        rw [e] at h
        have e2 : 2 * saddleTerm (signSaddle a₁ s 1) * Complex.cos (turnPoint s) -
            -η * bulkTerm (signSaddle a₁ s 1) =
            -(2 * saddleTerm (signSaddle a₁ s 1) * Complex.cos (turnPoint s) * -1 -
              η * bulkTerm (signSaddle a₁ s 1)) := by ring
        rw [e2, norm_neg]
        exact h⟩
  have hfar₀ : ∀ s, σ₀ ≤ (signSaddle a₁ s 0).re := fun s => by
    linarith [(hspec s le_rfl zero_le_one).2.1]
  have hfar₁ : ∀ s, σ₀ ≤ (signSaddle a₁ s 1).re := fun s => by
    linarith [(hspec s zero_le_one le_rfl).2.1]
  rcases hη with rfl | rfl
  · exact ⟨_, _, hS₀, hS₁, hfar₀, hfar₁⟩
  · exact ⟨_, _, by simpa only [neg_neg] using hS₁, hS₀, hfar₁, hfar₀⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
