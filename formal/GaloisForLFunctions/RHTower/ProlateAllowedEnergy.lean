import GaloisForLFunctions.RHTower.ProlateRadialBarrier

/-!
# Oscillatory-region energy for the radial prolate equation

Inside the turning point, put `q_s(y) = (s-y²)/(1-y²)`.  For a radial prolate solution,

`E(y) = Phi'(y)² + c² q_s(y) Phi(y)²`

satisfies `(E/q_s)' ≥ 0` on the positive allowed region.  Thus propagation through that region
costs only the algebraic factor `1/q_s`, never another exponential in `c`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set Filter MeasureTheory

open _root_.RHTower

/-- Positive oscillator potential inside the radial turning point. -/
def prolateAllowedPotential (s : ℝ) (y : ℝ) : ℝ :=
  (s - y ^ 2) / (1 - y ^ 2)

/-- Oscillatory energy of a radial prolate solution. -/
def prolateAllowedEnergy (c s : ℝ) (Φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  deriv Φ y ^ 2 + c ^ 2 * prolateAllowedPotential s y * Φ y ^ 2

/-- Energy divided by the positive oscillator potential. -/
def prolateAllowedEnergyRatio (c s : ℝ) (Φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  prolateAllowedEnergy c s Φ y / prolateAllowedPotential s y

theorem hasDerivAt_prolateAllowedPotential
    {s y : ℝ} (hp : 1 - y ^ 2 ≠ 0) :
    HasDerivAt (prolateAllowedPotential s)
      (-(2 * y * (1 - s)) / (1 - y ^ 2) ^ 2) y := by
  have hnum : HasDerivAt (fun t : ℝ => s - t ^ 2) (-(2 * y)) y := by
    have h := (hasDerivAt_pow 2 y).const_sub s
    refine h.congr_deriv ?_
    norm_num
  have hden : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y := by
    have h := (hasDerivAt_pow 2 y).const_sub (1 : ℝ)
    refine h.congr_deriv ?_
    norm_num
  have hquot := hnum.div hden hp
  refine hquot.congr_deriv ?_
  field_simp
  ring

theorem prolateAllowedPotential_pos
    {s y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (hturn : y ^ 2 < s) :
    0 < prolateAllowedPotential s y := by
  rw [prolateAllowedPotential]
  exact div_pos (sub_pos.2 hturn) (by nlinarith [hy.1, hy.2])

/-- Exact derivative of the oscillatory energy. -/
theorem hasDerivAt_prolateAllowedEnergy
    {c s y : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ x = -(s * c ^ 2) * Φ x)
    (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (prolateAllowedEnergy c s Φ)
      ((4 * y / (1 - y ^ 2)) * deriv Φ y ^ 2 +
        c ^ 2 * (-(2 * y * (1 - s)) / (1 - y ^ 2) ^ 2) * Φ y ^ 2) y := by
  have hp : 1 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
  have hΦ1 : HasDerivAt Φ (deriv Φ y) y :=
    ((contDiff_infty_iff_deriv.mp hsm).1 y).hasDerivAt
  have hΦ2raw : HasDerivAt (deriv Φ) (deriv (deriv Φ) y) y :=
    ((contDiff_infty_iff_deriv.mp
      (contDiff_infty_iff_deriv.mp hsm).2).1 y).hasDerivAt
  have heigy := heig y ⟨hy.1.le, hy.2.le⟩
  have hsecond : deriv (deriv Φ) y =
      (2 * y / (1 - y ^ 2)) * deriv Φ y -
        c ^ 2 * prolateAllowedPotential s y * Φ y := by
    rw [prolateSLAction] at heigy
    rw [prolateAllowedPotential]
    field_simp [hp]
    nlinarith [heigy]
  have hΦ2 : HasDerivAt (deriv Φ)
      ((2 * y / (1 - y ^ 2)) * deriv Φ y -
        c ^ 2 * prolateAllowedPotential s y * Φ y) y := by
    convert hΦ2raw using 1
    exact hsecond.symm
  have hq := hasDerivAt_prolateAllowedPotential (s := s) hp
  have hgrad := hΦ2.pow 2
  have hposition := hΦ1.pow 2
  have hpotential := (hq.const_mul (c ^ 2)).mul hposition
  have hsum := hgrad.add hpotential
  have hfun :
      deriv Φ ^ 2 + (fun t => c ^ 2 * prolateAllowedPotential s t) * Φ ^ 2 =
        prolateAllowedEnergy c s Φ := by
    funext t
    rfl
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  norm_num
  ring

/-- Exact derivative of `E/q`; all solution-dependent terms except `Phi'²` cancel. -/
theorem hasDerivAt_prolateAllowedEnergyRatio
    {c s y : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ x = -(s * c ^ 2) * Φ x)
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hturn : y ^ 2 < s) :
    HasDerivAt (prolateAllowedEnergyRatio c s Φ)
      ((((4 * y / (1 - y ^ 2)) * prolateAllowedPotential s y -
          (-(2 * y * (1 - s)) / (1 - y ^ 2) ^ 2)) * deriv Φ y ^ 2) /
        prolateAllowedPotential s y ^ 2) y := by
  have hp : 1 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
  have hqpos := prolateAllowedPotential_pos hy hturn
  have hE := hasDerivAt_prolateAllowedEnergy hsm heig hy
  have hq := hasDerivAt_prolateAllowedPotential (s := s) hp
  have hquot := hE.div hq hqpos.ne'
  refine hquot.congr_deriv ?_
  rw [prolateAllowedEnergy]
  field_simp
  ring

theorem deriv_prolateAllowedEnergyRatio_nonneg
    {c s y : ℝ} {Φ : ℝ → ℝ}
    (hs1 : s ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1) (hturn : y ^ 2 < s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ x = -(s * c ^ 2) * Φ x) :
    0 ≤ deriv (prolateAllowedEnergyRatio c s Φ) y := by
  have hy : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hy1⟩
  have hderiv := hasDerivAt_prolateAllowedEnergyRatio hsm heig hy hturn
  rw [hderiv.deriv]
  have hp : 0 < 1 - y ^ 2 := by nlinarith
  have hq : 0 < prolateAllowedPotential s y := prolateAllowedPotential_pos hy hturn
  have hfirst : 0 ≤ (4 * y / (1 - y ^ 2)) * prolateAllowedPotential s y := by
    positivity
  have hsecond : -(2 * y * (1 - s)) / (1 - y ^ 2) ^ 2 ≤ 0 := by
    have hnum : 0 ≤ 2 * y * (1 - s) :=
      mul_nonneg (mul_nonneg (by norm_num) hy0) (sub_nonneg.2 hs1)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hnum) (sq_nonneg _)
  exact div_nonneg
    (mul_nonneg (sub_nonneg.2 (hsecond.trans hfirst)) (sq_nonneg _))
    (sq_nonneg _)

/-- The normalized oscillatory energy is monotone toward the turning point. -/
theorem monotoneOn_prolateAllowedEnergyRatio
    {c s a b : ℝ} {Φ : ℝ → ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1) (hturn : b ^ 2 < s)
    (hs1 : s ≤ 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ x = -(s * c ^ 2) * Φ x) :
    MonotoneOn (prolateAllowedEnergyRatio c s Φ) (Icc a b) := by
  have hinside : ∀ y ∈ Icc a b, y ∈ Ioo (-1 : ℝ) 1 ∧ y ^ 2 < s := by
    intro y hy
    have hy0 : 0 ≤ y := ha0.trans hy.1
    have hy1 : y < 1 := hy.2.trans_lt hb1
    have hsq : y ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hy0 (ha0.trans hab)).2 hy.2
    exact ⟨⟨by linarith, hy1⟩, hsq.trans_lt hturn⟩
  have hcontQ : ContinuousOn (prolateAllowedPotential s) (Icc a b) := by
    unfold prolateAllowedPotential
    exact (continuousOn_const.sub (continuousOn_id.pow 2)).div
      (continuousOn_const.sub (continuousOn_id.pow 2)) fun y hy => by
        have h := (hinside y hy).1
        nlinarith [h.1, h.2]
  have hqne : ∀ y ∈ Icc a b, prolateAllowedPotential s y ≠ 0 :=
    fun y hy => (prolateAllowedPotential_pos (hinside y hy).1 (hinside y hy).2).ne'
  have hcontE : ContinuousOn (prolateAllowedEnergy c s Φ) (Icc a b) := by
    unfold prolateAllowedEnergy
    have hd : Continuous (deriv Φ) := (contDiff_infty_iff_deriv.mp hsm).2.continuous
    exact (hd.continuousOn.pow 2).add
      ((continuousOn_const.mul hcontQ).mul (hsm.continuous.continuousOn.pow 2))
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (hcontE.div hcontQ hqne) ?_ ?_
  · rw [interior_Icc]
    intro y hy
    exact (hasDerivAt_prolateAllowedEnergyRatio hsm heig
      (hinside y ⟨hy.1.le, hy.2.le⟩).1
      (hinside y ⟨hy.1.le, hy.2.le⟩).2).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact deriv_prolateAllowedEnergyRatio_nonneg hs1
      (ha0.trans hy.1.le) (hy.2.trans hb1)
      (hinside y ⟨hy.1.le, hy.2.le⟩).2 hsm heig

/-- The normalized allowed-region energy is increasing throughout every genuinely oscillatory
interval.  The sign does not require `s ≤ 1`: after cancellation its coefficient is
`2y (s + 1 - 2y²) / (1-y²)²`, positive whenever `0 ≤ y < 1` and `y² < s`. -/
theorem deriv_prolateAllowedEnergyRatio_nonneg_of_allowed
    {c s y : ℝ} {Φ : ℝ → ℝ}
    (hy0 : 0 ≤ y) (hy1 : y < 1) (hturn : y ^ 2 < s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ x = -(s * c ^ 2) * Φ x) :
    0 ≤ deriv (prolateAllowedEnergyRatio c s Φ) y := by
  have hy : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hy1⟩
  have hderiv := hasDerivAt_prolateAllowedEnergyRatio hsm heig hy hturn
  rw [hderiv.deriv]
  have hp : 0 < 1 - y ^ 2 := by nlinarith
  have hq : 0 < prolateAllowedPotential s y := prolateAllowedPotential_pos hy hturn
  have hcoeff :
      0 ≤ (4 * y / (1 - y ^ 2)) * prolateAllowedPotential s y -
        (-(2 * y * (1 - s)) / (1 - y ^ 2) ^ 2) := by
    have heq :
        (4 * y / (1 - y ^ 2)) * prolateAllowedPotential s y -
            (-(2 * y * (1 - s)) / (1 - y ^ 2) ^ 2) =
          2 * y * (s + 1 - 2 * y ^ 2) / (1 - y ^ 2) ^ 2 := by
      rw [prolateAllowedPotential]
      field_simp [hp.ne']
      ring
    rw [heq]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hy0) (by nlinarith))
      (sq_nonneg _)
  exact div_nonneg (mul_nonneg hcoeff (sq_nonneg _)) (sq_nonneg _)

/-- The normalized oscillatory energy is monotone on any positive allowed interval, including the
high-separation regime `s ≥ 1`. -/
theorem monotoneOn_prolateAllowedEnergyRatio_of_allowed
    {c s a b : ℝ} {Φ : ℝ → ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1) (hturn : b ^ 2 < s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ x = -(s * c ^ 2) * Φ x) :
    MonotoneOn (prolateAllowedEnergyRatio c s Φ) (Icc a b) := by
  have hinside : ∀ y ∈ Icc a b, y ∈ Ioo (-1 : ℝ) 1 ∧ y ^ 2 < s := by
    intro y hy
    have hy0 : 0 ≤ y := ha0.trans hy.1
    have hy1 : y < 1 := hy.2.trans_lt hb1
    have hsq : y ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hy0 (ha0.trans hab)).2 hy.2
    exact ⟨⟨by linarith, hy1⟩, hsq.trans_lt hturn⟩
  have hcontQ : ContinuousOn (prolateAllowedPotential s) (Icc a b) := by
    unfold prolateAllowedPotential
    exact (continuousOn_const.sub (continuousOn_id.pow 2)).div
      (continuousOn_const.sub (continuousOn_id.pow 2)) fun y hy => by
        have h := (hinside y hy).1
        nlinarith [h.1, h.2]
  have hqne : ∀ y ∈ Icc a b, prolateAllowedPotential s y ≠ 0 :=
    fun y hy => (prolateAllowedPotential_pos (hinside y hy).1 (hinside y hy).2).ne'
  have hcontE : ContinuousOn (prolateAllowedEnergy c s Φ) (Icc a b) := by
    unfold prolateAllowedEnergy
    have hd : Continuous (deriv Φ) := (contDiff_infty_iff_deriv.mp hsm).2.continuous
    exact (hd.continuousOn.pow 2).add
      ((continuousOn_const.mul hcontQ).mul (hsm.continuous.continuousOn.pow 2))
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (hcontE.div hcontQ hqne) ?_ ?_
  · rw [interior_Icc]
    intro y hy
    exact (hasDerivAt_prolateAllowedEnergyRatio hsm heig
      (hinside y ⟨hy.1.le, hy.2.le⟩).1
      (hinside y ⟨hy.1.le, hy.2.le⟩).2).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact deriv_prolateAllowedEnergyRatio_nonneg_of_allowed
      (ha0.trans hy.1.le) (hy.2.trans hb1)
      (hinside y ⟨hy.1.le, hy.2.le⟩).2 hsm heig

/-- Pointwise amplitude is controlled by normalized energy farther into any allowed interval. -/
theorem c_sq_mul_value_sq_le_allowedEnergyRatio_of_allowed
    {c s x z : ℝ} {Φ : ℝ → ℝ}
    (hx0 : 0 ≤ x) (hxz : x ≤ z) (hz1 : z < 1) (hzturn : z ^ 2 < s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ 2) * Φ y) :
    c ^ 2 * Φ x ^ 2 ≤ prolateAllowedEnergyRatio c s Φ z := by
  have hmono := monotoneOn_prolateAllowedEnergyRatio_of_allowed
    hx0 hxz hz1 hzturn hsm heig
  have hratio := hmono (left_mem_Icc.2 hxz) (right_mem_Icc.2 hxz) hxz
  have hx1 : x < 1 := hxz.trans_lt hz1
  have hxsq : x ^ 2 ≤ z ^ 2 := (sq_le_sq₀ hx0 (hx0.trans hxz)).2 hxz
  have hqx : 0 < prolateAllowedPotential s x :=
    prolateAllowedPotential_pos ⟨by linarith, hx1⟩ (hxsq.trans_lt hzturn)
  have henergy : c ^ 2 * prolateAllowedPotential s x * Φ x ^ 2 ≤
      prolateAllowedEnergy c s Φ x := by
    rw [prolateAllowedEnergy]
    nlinarith [sq_nonneg (deriv Φ x)]
  have hlocal : c ^ 2 * Φ x ^ 2 ≤
      prolateAllowedEnergy c s Φ x / prolateAllowedPotential s x := by
    rw [le_div_iff₀ hqx]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using henergy
  rw [prolateAllowedEnergyRatio] at hratio ⊢
  exact hlocal.trans hratio

/-- A regular endpoint-normalized solution whose whole aperture is oscillatory has amplitude at
most its endpoint amplitude.  This is the high-separation Sonin bound. -/
theorem abs_prolate_value_le_one_of_one_le
    {c s x : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs1 : 1 ≤ s) (hx : x ∈ Icc (0 : ℝ) 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1)
    (hend : 2 * deriv Φ 1 = s * c ^ 2 - c ^ 2) :
    |Φ x| ≤ 1 := by
  rcases eq_or_lt_of_le hx.2 with rfl | hx1
  · simp [hΦ1]
  have hd : Continuous (deriv Φ) := (contDiff_infty_iff_deriv.mp hsm).2.continuous
  have hxevent : ∀ᶠ z : ℝ in nhdsWithin (1 : ℝ) (Iio 1), x < z :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hx1)
  have hsq : c ^ 2 * Φ x ^ 2 ≤ c ^ 2 := by
    rcases eq_or_lt_of_le hs1 with rfl | hslt
    · have hend0 : deriv Φ 1 = 0 := by nlinarith
      let F : ℝ → ℝ := fun y => deriv Φ y ^ 2 + c ^ 2 * Φ y ^ 2
      have hFcont : ContinuousAt F 1 := by
        dsimp only [F]
        exact (hd.continuousAt.pow 2).add
          (continuousAt_const.mul (hsm.continuous.continuousAt.pow 2))
      have hlim : Tendsto F (nhdsWithin (1 : ℝ) (Iio 1)) (nhds (c ^ 2)) := by
        have hraw : Tendsto F (nhdsWithin (1 : ℝ) (Iio 1)) (nhds (F 1)) :=
          hFcont.continuousWithinAt
        norm_num [F, hend0, hΦ1] at hraw ⊢
        exact hraw
      apply ge_of_tendsto hlim
      filter_upwards [hxevent, self_mem_nhdsWithin] with z hxz hz1
      change z < 1 at hz1
      have hz0 : 0 ≤ z := hx.1.trans (le_of_lt hxz)
      have hzturn : z ^ 2 < (1 : ℝ) := by nlinarith
      have henergy := c_sq_mul_value_sq_le_allowedEnergyRatio_of_allowed
        hx.1 (le_of_lt hxz) hz1 hzturn hsm heig
      have hratio : prolateAllowedEnergyRatio c 1 Φ z = F z := by
        dsimp only [F, prolateAllowedEnergyRatio, prolateAllowedEnergy,
          prolateAllowedPotential]
        have hden : 1 - z ^ 2 ≠ 0 := by nlinarith
        field_simp [hden]
      simpa only [hratio] using henergy
    · let F : ℝ → ℝ := fun y =>
        deriv Φ y ^ 2 * (1 - y ^ 2) / (s - y ^ 2) + c ^ 2 * Φ y ^ 2
      have hden : s - (1 : ℝ) ^ 2 ≠ 0 := by nlinarith
      have hFcont : ContinuousAt F 1 := by
        dsimp only [F]
        exact (((hd.continuousAt.pow 2).mul
          (continuousAt_const.sub (continuousAt_id.pow 2))).div
            (continuousAt_const.sub (continuousAt_id.pow 2)) hden).add
          (continuousAt_const.mul (hsm.continuous.continuousAt.pow 2))
      have hlim : Tendsto F (nhdsWithin (1 : ℝ) (Iio 1)) (nhds (c ^ 2)) := by
        have hraw : Tendsto F (nhdsWithin (1 : ℝ) (Iio 1)) (nhds (F 1)) :=
          hFcont.continuousWithinAt
        simpa only [F, hΦ1, one_pow, sub_self, mul_zero, zero_div, mul_one,
          zero_add] using hraw
      apply ge_of_tendsto hlim
      filter_upwards [hxevent, self_mem_nhdsWithin] with z hxz hz1
      change z < 1 at hz1
      have hz0 : 0 ≤ z := hx.1.trans (le_of_lt hxz)
      have hzsq : z ^ 2 < 1 := by nlinarith
      have hzturn : z ^ 2 < s := hzsq.trans hslt
      have henergy := c_sq_mul_value_sq_le_allowedEnergyRatio_of_allowed
        hx.1 (le_of_lt hxz) hz1 hzturn hsm heig
      have hratio : prolateAllowedEnergyRatio c s Φ z = F z := by
        dsimp only [F, prolateAllowedEnergyRatio, prolateAllowedEnergy,
          prolateAllowedPotential]
        have hden1 : 1 - z ^ 2 ≠ 0 := by nlinarith
        have hdens : s - z ^ 2 ≠ 0 := by nlinarith
        field_simp [hden1, hdens]
      simpa only [hratio] using henergy
  have hvalueSq : Φ x ^ 2 ≤ 1 := by
    nlinarith [sq_pos_of_pos hc]
  exact (sq_le_one_iff_abs_le_one (Φ x)).mp hvalueSq

/-- In the high-separation regime the full aperture mass of an even endpoint-normalized regular
solution is at most the aperture length. -/
theorem integral_sq_le_two_of_one_le
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs1 : 1 ≤ s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heven : Function.Even Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1)
    (hend : 2 * deriv Φ 1 = s * c ^ 2 - c ^ 2) :
    (∫ y in (-1 : ℝ)..1, Φ y ^ 2) ≤ 2 := by
  have hint : IntervalIntegrable (fun y : ℝ => Φ y ^ 2) volume (-1) 1 :=
    (hsm.continuous.pow 2).intervalIntegrable _ _
  have hpoint : ∀ y ∈ Icc (-1 : ℝ) 1, Φ y ^ 2 ≤ (1 : ℝ) := by
    intro y hy
    have habsMem : |y| ∈ Icc (0 : ℝ) 1 := by
      exact ⟨abs_nonneg y, (abs_le).2 ⟨by linarith [hy.1], hy.2⟩⟩
    have hbound := abs_prolate_value_le_one_of_one_le
      hc hs1 habsMem hsm heig hΦ1 hend
    have heq : Φ |y| = Φ y := by
      rcases le_total 0 y with hy0 | hy0
      · rw [abs_of_nonneg hy0]
      · rw [abs_of_nonpos hy0, heven y]
    rw [heq] at hbound
    exact (sq_le_one_iff_abs_le_one (Φ y)).2 hbound
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (-1 : ℝ) ≤ 1) hint intervalIntegrable_const hpoint
  norm_num at hmono ⊢
  exact hmono

/-- Pointwise allowed-region amplitude is controlled by one energy value closer to the turning
point, with no exponential loss. -/
theorem c_sq_mul_value_sq_le_allowedEnergyRatio
    {c s x z : ℝ} {Φ : ℝ → ℝ}
    (hx0 : 0 ≤ x) (hxz : x ≤ z) (hz1 : z < 1) (hzturn : z ^ 2 < s)
    (hs1 : s ≤ 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ 2) * Φ y) :
    c ^ 2 * Φ x ^ 2 ≤ prolateAllowedEnergyRatio c s Φ z := by
  have hmono := monotoneOn_prolateAllowedEnergyRatio hx0 hxz hz1 hzturn hs1 hsm heig
  have hratio := hmono (left_mem_Icc.2 hxz) (right_mem_Icc.2 hxz) hxz
  have hx1 : x < 1 := hxz.trans_lt hz1
  have hxsq : x ^ 2 ≤ z ^ 2 := (sq_le_sq₀ hx0 (hx0.trans hxz)).2 hxz
  have hqx : 0 < prolateAllowedPotential s x :=
    prolateAllowedPotential_pos ⟨by linarith, hx1⟩ (hxsq.trans_lt hzturn)
  have henergy : c ^ 2 * prolateAllowedPotential s x * Φ x ^ 2 ≤
      prolateAllowedEnergy c s Φ x := by
    rw [prolateAllowedEnergy]
    nlinarith [sq_nonneg (deriv Φ x)]
  have hlocal : c ^ 2 * Φ x ^ 2 ≤
      prolateAllowedEnergy c s Φ x / prolateAllowedPotential s x := by
    rw [le_div_iff₀ hqx]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using henergy
  rw [prolateAllowedEnergyRatio] at hratio ⊢
  exact hlocal.trans hratio

end GaloisForLFunctions.RHTower

end
