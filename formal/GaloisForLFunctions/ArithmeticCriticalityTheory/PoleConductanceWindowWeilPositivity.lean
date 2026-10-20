import GaloisForLFunctions.ArithmeticCriticalityTheory.PlateauGaugeWindowWeilPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.NonnegativeConeZeroFormCriterion

/-!
# The pole product as a conductance: the Markov window

The Lorentz correction of the full zero form is the pole product `2E₊(F)E₋(F)`,
`E_± = ∫ F e^{±x/2}`. In a gauge `M` with `F = M F` it splits into a potential and a NEGATIVE jump
form with the pole density `2cosh(t/2)` (`two_mul_expMoments_eq_gauge`):

    2E₊E₋ = 2 ∫ F(x)² (∫ M(y) cosh((x−y)/2) dy) dx − 2 ∫_0^∞ cosh(t/2) I_M(t) dt,
    I_M(t) = ∫ M(x) M(x+t) (F(x) − F(x+t))² dx.

Together with the ground-state representation `Q(F) = J_M(F) − ∫F² 𝒲M` this writes the full zero
form on a window below the first prime as

    Ẑ(F) = ∫_0^∞ (ω(t) − 2cosh(t/2)) I_M(t) dt + ∫ F² [2 ∫ M(y) cosh((x−y)/2) dy − 𝒲M(x)] dx:

a jump form whose density is the archimedean Lévy density minus the pole density, plus one
potential. The density `ω(t) − 2cosh(t/2)` is positive for `t ≤ 0.22`
(`two_mul_cosh_le_archLevyDensity`): on windows of width `0.22` the full zero form is a Markov form in
every nonnegative gauge, the pole included. The pole now enters the potential with the sign of a
mass, `2∫M cosh((x−y)/2) ≥ 2∫M`.

**Theorem** (`fullZeroForm_ge_of_support_le_sharp`). Every real `F ∈ C²_c` vanishing outside
`[−0.105, 0.105]` satisfies `Ẑ(F) ≥ (1/30) ∫ F²`. The window is `1.55` times that of the plateau gauge
without the pole conductance (`fullZeroForm_ge_of_support_le`, `e^{−2}/2 ≈ 0.0677`), and `10.5` times the
aperture `1/100` of the Fourier method.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Integrability on boxes -/

/-- A continuous function on `ℝ × ℝ` vanishing outside a box is integrable for the product measure. -/
theorem integrable_prod_of_box {g : ℝ × ℝ → ℝ} (hg : Continuous g) {B : ℝ}
    (hsupp : ∀ p : ℝ × ℝ, g p ≠ 0 → |p.1| ≤ B ∧ |p.2| ≤ B) :
    Integrable g ((volume : Measure ℝ).prod volume) := by
  rw [← Measure.volume_eq_prod]
  refine hg.integrable_of_hasCompactSupport (HasCompactSupport.intro
    ((isCompact_Icc (a := -B) (b := B)).prod (isCompact_Icc (a := -B) (b := B))) fun p hp => ?_)
  by_contra h
  obtain ⟨h1, h2⟩ := hsupp p h
  exact hp ⟨abs_le.mp h1, abs_le.mp h2⟩

/-! ### The pole product in a gauge -/

section PoleProduct

variable {F M : ℝ → ℝ} {B : ℝ} (hF : Continuous F) (hM : Continuous M)
  (hFB : ∀ x, F x ≠ 0 → |x| ≤ B) (hMB : ∀ x, M x ≠ 0 → |x| ≤ B)
  (hFM : ∀ x, F x ≠ 0 → M x = 1)

/-- The autocorrelation `A(t) = ∫ F(x) F(x+t) dx`. -/
def autoCorr (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, F x * F (x + t)

/-- The gauge jump profile `I_M(t) = ∫ M(x) M(x+t) (F(x) − F(x+t))² dx`. -/
def gaugeJumpProfile (M F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, signedShiftJump M F t x

omit hFM in
include hFB in
theorem hasCompactSupport_of_bound : HasCompactSupport F :=
  HasCompactSupport.intro (isCompact_Icc (a := -B) (b := B)) fun x hx => by
    by_contra h
    exact hx (abs_le.mp (hFB x h))

omit hFM in
include hF hFB in
/-- The autocorrelation kernel `(t, x) ↦ F(x) F(x+t) e^{ct}` is integrable on `ℝ × ℝ`. -/
theorem integrable_autoCorr_kernel (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => F p.2 * F (p.2 + p.1) * Real.exp (c * p.1))
      ((volume : Measure ℝ).prod volume) := by
  refine integrable_prod_of_box (B := 2 * |B|) (by fun_prop) fun p hp => ?_
  have h1 : F p.2 ≠ 0 := fun h => hp (by rw [h]; ring)
  have h2 : F (p.2 + p.1) ≠ 0 := fun h => hp (by rw [h]; ring)
  have a1 := (hFB _ h1).trans (le_abs_self B)
  have a2 := (hFB _ h2).trans (le_abs_self B)
  have h3 : |p.1| ≤ |p.2 + p.1| + |p.2| := by
    have := abs_sub (p.2 + p.1) p.2
    rwa [add_sub_cancel_left] at this
  exact ⟨by linarith, by linarith [abs_nonneg B]⟩

omit hFM in
theorem autoCorr_neg (t : ℝ) : autoCorr F (-t) = autoCorr F t := by
  unfold autoCorr
  rw [← integral_add_right_eq_self (fun x => F x * F (x + -t)) t]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [add_neg_cancel_right]
  ring

omit hFM in
include hF hFB in
/-- `∫ e^{−t/2} A(t) dt = ∫ cosh(t/2) A(t) dt`: the autocorrelation is even. -/
theorem integral_exp_mul_autoCorr_eq_cosh :
    (∫ t, Real.exp (-(1 / 2) * t) * autoCorr F t) = ∫ t, Real.cosh (t / 2) * autoCorr F t := by
  have hint : ∀ c : ℝ, Integrable fun t => Real.exp (c * t) * autoCorr F t := fun c => by
    refine ((integrable_autoCorr_kernel hF hFB c).integral_prod_left).congr
      (Eventually.of_forall fun t => ?_)
    simp only [autoCorr]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hsym : (∫ t, Real.exp (-(1 / 2) * t) * autoCorr F t) =
      ∫ t, Real.exp ((1 / 2) * t) * autoCorr F t := by
    rw [← integral_neg_eq_self (fun t => Real.exp ((1 / 2) * t) * autoCorr F t)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [autoCorr_neg]
    ring_nf
  have hc : (fun t => Real.cosh (t / 2) * autoCorr F t) = fun t =>
      (Real.exp ((1 / 2) * t) * autoCorr F t + Real.exp (-(1 / 2) * t) * autoCorr F t) / 2 := by
    funext t
    rw [Real.cosh_eq]
    ring_nf
  rw [hc, integral_div, integral_add (hint _) (hint _), ← hsym]
  ring

include hF hM hFB hFM in
/-- The autocorrelation in the gauge: `A(t) = ½ ∫ F²(M(x+t) + M(x−t)) − ½ I_M(t)`. -/
theorem autoCorr_eq_gauge (t : ℝ) :
    autoCorr F t = (1 / 2) * (∫ x, F x ^ 2 * (M (x + t) + M (x - t))) -
      (1 / 2) * gaugeJumpProfile M F t := by
  have hFc := hasCompactSupport_of_bound hFB
  have hpt : ∀ x, F x * F (x + t) = (1 / 2) * (F x ^ 2 * M (x + t) + F (x + t) ^ 2 * M x) -
      (1 / 2) * signedShiftJump M F t x := fun x => by
    unfold signedShiftJump
    by_cases h1 : F x = 0 <;> by_cases h2 : F (x + t) = 0
    · rw [h1, h2]; ring
    · rw [h1, hFM _ h2]; ring
    · rw [h2, hFM _ h1]; ring
    · rw [hFM _ h1, hFM _ h2]; ring
  have i1 : Integrable fun x => F x ^ 2 * M (x + t) :=
    ((hF.pow 2).mul (hM.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hasCompactSupport_sq hFc).mul_right
  have i2 : Integrable fun x => F (x + t) ^ 2 * M x :=
    (((hF.comp (continuous_id.add continuous_const)).pow 2).mul hM).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).comp_homeomorph (Homeomorph.addRight t)).mul_right
  have i3 : Integrable fun x => signedShiftJump M F t x := by
    unfold signedShiftJump
    refine (((hM.mul (hM.comp (continuous_id.add continuous_const))).mul
      ((hF.sub (hF.comp (continuous_id.add continuous_const))).pow 2))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -|B| - |t|) (b := |B| + |t|)) fun x hx => ?_
    by_cases h1 : F x = 0 <;> by_cases h2 : F (x + t) = 0
    · simp [h1, h2]
    · exfalso; apply hx
      have := (hFB _ h2).trans (le_abs_self B)
      have h3 := abs_sub (x + t) t
      rw [add_sub_cancel_right] at h3
      have hxb : |x| ≤ |B| + |t| := by linarith
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    · exfalso; apply hx
      have hxb : |x| ≤ |B| + |t| := by linarith [(hFB _ h1).trans (le_abs_self B), abs_nonneg t]
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    · exfalso; apply hx
      have hxb : |x| ≤ |B| + |t| := by linarith [(hFB _ h1).trans (le_abs_self B), abs_nonneg t]
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hshift : (∫ x, F (x + t) ^ 2 * M x) = ∫ x, F x ^ 2 * M (x - t) := by
    rw [← integral_add_right_eq_self (fun x => F x ^ 2 * M (x - t)) t]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [add_sub_cancel_right]
  have i12 : Integrable fun x => F x ^ 2 * M (x + t) + F (x + t) ^ 2 * M x := i1.add i2
  have i4 : Integrable fun x => F x ^ 2 * M (x - t) :=
    ((hF.pow 2).mul (hM.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (hasCompactSupport_sq hFc).mul_right
  unfold autoCorr gaugeJumpProfile
  calc (∫ x, F x * F (x + t))
      = ∫ x, ((1 / 2) * (F x ^ 2 * M (x + t) + F (x + t) ^ 2 * M x) -
          (1 / 2) * signedShiftJump M F t x) := integral_congr_ae (Eventually.of_forall hpt)
    _ = (1 / 2) * ((∫ x, F x ^ 2 * M (x + t)) + ∫ x, F (x + t) ^ 2 * M x) -
          (1 / 2) * ∫ x, signedShiftJump M F t x := by
        rw [integral_sub (i12.const_mul _) (i3.const_mul _), integral_const_mul, integral_const_mul,
          integral_add i1 i2]
    _ = _ := by
        rw [hshift, ← integral_add i1 i4]
        congr 2
        exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

omit hFM in
theorem gaugeJumpProfile_neg (t : ℝ) : gaugeJumpProfile M F (-t) = gaugeJumpProfile M F t := by
  unfold gaugeJumpProfile signedShiftJump
  rw [← integral_add_right_eq_self (fun x => M x * M (x + -t) * (F x - F (x + -t)) ^ 2) t]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [add_neg_cancel_right]
  ring

omit hFB hFM in
include hF hM hMB in
/-- The gauge kernel `(t, x) ↦ cosh(t/2) M(x) M(x+t) (F(x) − F(x+t))²` is integrable on `ℝ × ℝ`. -/
theorem integrable_gaugeJump_kernel :
    Integrable (fun p : ℝ × ℝ => Real.cosh (p.1 / 2) * signedShiftJump M F p.1 p.2)
      ((volume : Measure ℝ).prod volume) := by
  unfold signedShiftJump
  refine integrable_prod_of_box (B := 2 * |B|) (by fun_prop) fun p hp => ?_
  have h1 : M p.2 ≠ 0 := fun h => hp (by rw [h]; ring)
  have h2 : M (p.2 + p.1) ≠ 0 := fun h => hp (by rw [h]; ring)
  have a1 := (hMB _ h1).trans (le_abs_self B)
  have a2 := (hMB _ h2).trans (le_abs_self B)
  have h3 : |p.1| ≤ |p.2 + p.1| + |p.2| := by
    have := abs_sub (p.2 + p.1) p.2
    rwa [add_sub_cancel_left] at this
  exact ⟨by linarith, by linarith [abs_nonneg B]⟩

include hF hM hFB hMB in
/-- The potential kernel `(t, x) ↦ cosh(t/2) F(x)² (M(x+t) + M(x−t))` is integrable on `ℝ × ℝ`. -/
theorem integrable_gaugeMass_kernel :
    Integrable (fun p : ℝ × ℝ => Real.cosh (p.1 / 2) * (F p.2 ^ 2 * (M (p.2 + p.1) + M (p.2 - p.1))))
      ((volume : Measure ℝ).prod volume) := by
  refine integrable_prod_of_box (B := 2 * |B|) (by fun_prop) fun p hp => ?_
  have h1 : F p.2 ≠ 0 := fun h => hp (by rw [h]; ring)
  have a1 := (hFB _ h1).trans (le_abs_self B)
  have hM' : M (p.2 + p.1) ≠ 0 ∨ M (p.2 - p.1) ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (by rw [h.1, h.2]; ring)
  refine ⟨?_, by linarith [abs_nonneg B]⟩
  rcases hM' with h2 | h2
  · have a2 := (hMB _ h2).trans (le_abs_self B)
    have h3 : |p.1| ≤ |p.2 + p.1| + |p.2| := by
      have := abs_sub (p.2 + p.1) p.2
      rwa [add_sub_cancel_left] at this
    linarith
  · have a2 := (hMB _ h2).trans (le_abs_self B)
    have h3 : |p.1| ≤ |p.2 - p.1| + |p.2| := by
      have := abs_sub p.2 (p.2 - p.1)
      rw [sub_sub_cancel] at this
      linarith [abs_sub_comm p.2 (p.2 - p.1)]
    linarith

include hF hM hFB hMB hFM in
/-- **The pole product in a gauge.** For `F = M F`,
`2E₊(F)E₋(F) = 2 ∫ F(x)² ∫ M(y) cosh((x−y)/2) dy dx − 2 ∫_0^∞ cosh(t/2) I_M(t) dt`. -/
theorem two_mul_expMoments_eq_gauge :
    2 * expHalfMoment F * expNegHalfMoment F =
      2 * (∫ x, F x ^ 2 * ∫ y, M y * Real.cosh ((x - y) / 2)) -
        2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M F t := by
  -- `E₊ E₋ = ∫ e^{−t/2} A(t) = ∫ cosh(t/2) A(t)`
  have hE : expHalfMoment F * expNegHalfMoment F = ∫ t, Real.cosh (t / 2) * autoCorr F t := by
    rw [← integral_exp_mul_autoCorr_eq_cosh hF hFB]
    have hin : ∀ x, F x * Real.exp (x / 2) * expNegHalfMoment F =
        ∫ t, F x * F (x + t) * Real.exp (-(1 / 2) * t) := fun x => by
      unfold expNegHalfMoment
      rw [← integral_add_left_eq_self (fun y => F y * Real.exp (-(y / 2))) x, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      have e : Real.exp (x / 2) * Real.exp (-((x + t) / 2)) = Real.exp (-(1 / 2) * t) := by
        rw [← Real.exp_add]; ring_nf
      linear_combination (F x * F (x + t)) * e
    unfold expHalfMoment
    rw [← integral_mul_const, integral_congr_ae (Eventually.of_forall hin),
      integral_integral_swap (f := fun x t => F x * F (x + t) * Real.exp (-(1 / 2) * t))
        (integrable_autoCorr_kernel hF hFB (-(1 / 2))).swap]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [autoCorr]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  -- split the autocorrelation in the gauge
  have hK1 := integrable_gaugeMass_kernel hF hM hFB hMB
  have hK2 := integrable_gaugeJump_kernel hF hM hMB
  have hi1 : Integrable fun t => Real.cosh (t / 2) * ∫ x, F x ^ 2 * (M (x + t) + M (x - t)) :=
    hK1.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only
      rw [integral_const_mul])
  have hi2 : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M F t :=
    hK2.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only [gaugeJumpProfile]
      rw [integral_const_mul])
  have hsplit : (∫ t, Real.cosh (t / 2) * autoCorr F t) =
      (1 / 2) * (∫ t, Real.cosh (t / 2) * ∫ x, F x ^ 2 * (M (x + t) + M (x - t))) -
        (1 / 2) * ∫ t, Real.cosh (t / 2) * gaugeJumpProfile M F t := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hi1.const_mul _) (hi2.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [autoCorr_eq_gauge hF hM hFB hFM]
    ring
  -- the potential part
  have hpot : (∫ t, Real.cosh (t / 2) * ∫ x, F x ^ 2 * (M (x + t) + M (x - t))) =
      2 * ∫ x, F x ^ 2 * ∫ y, M y * Real.cosh ((x - y) / 2) := by
    have hswap := integral_integral_swap
      (f := fun t x => Real.cosh (t / 2) * (F x ^ 2 * (M (x + t) + M (x - t)))) hK1
    have h1 : (∫ t, Real.cosh (t / 2) * ∫ x, F x ^ 2 * (M (x + t) + M (x - t))) =
        ∫ t, ∫ x, Real.cosh (t / 2) * (F x ^ 2 * (M (x + t) + M (x - t))) :=
      integral_congr_ae (Eventually.of_forall fun t => by simp only; rw [integral_const_mul])
    rw [h1, hswap, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    have hMc : HasCompactSupport M := hasCompactSupport_of_bound hMB
    have ia : Integrable fun t => Real.cosh (t / 2) * M (x + t) :=
      ((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul
        (hM.comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
        (hMc.comp_homeomorph (Homeomorph.addLeft x)).mul_left
    have ib : Integrable fun t => Real.cosh (t / 2) * M (x - t) :=
      ((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul
        (hM.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        ((hMc.comp_homeomorph (Homeomorph.subLeft x))).mul_left
    have e1 : (∫ t, Real.cosh (t / 2) * M (x + t)) = ∫ y, M y * Real.cosh ((x - y) / 2) := by
      rw [← integral_add_left_eq_self (fun y => M y * Real.cosh ((x - y) / 2)) x]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      rw [show (x - (x + t)) / 2 = -(t / 2) by ring, Real.cosh_neg]
      ring
    have e2 : (∫ t, Real.cosh (t / 2) * M (x - t)) = ∫ t, Real.cosh (t / 2) * M (x + t) := by
      rw [← integral_neg_eq_self (fun t => Real.cosh (t / 2) * M (x + t))]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      rw [show -t / 2 = -(t / 2) by ring, Real.cosh_neg, ← sub_eq_add_neg]
    have hsum : (∫ t, Real.cosh (t / 2) * (F x ^ 2 * (M (x + t) + M (x - t)))) =
        F x ^ 2 * ((∫ t, Real.cosh (t / 2) * M (x + t)) + ∫ t, Real.cosh (t / 2) * M (x - t)) := by
      rw [← integral_add ia ib, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
    rw [hsum, e2, e1]
    ring
  -- fold the jump part onto the half line
  have hfold : (∫ t, Real.cosh (t / 2) * gaugeJumpProfile M F t) =
      2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M F t := by
    rw [← integral_add_compl measurableSet_Ioi hi2, compl_Ioi]
    have hneg := integral_comp_neg_Ioi 0 (fun t => Real.cosh (t / 2) * gaugeJumpProfile M F t)
    rw [neg_zero] at hneg
    rw [← hneg]
    have : (∫ t in Ioi (0 : ℝ), Real.cosh (-t / 2) * gaugeJumpProfile M F (-t)) =
        ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M F t :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        rw [gaugeJumpProfile_neg, show -t / 2 = -(t / 2) by ring, Real.cosh_neg]
    rw [this]
    ring
  rw [mul_assoc, hE, hsplit, hpot, hfold]
  ring

end PoleProduct

/-! ### The window gauge -/

section Window

variable {F M : ℝ → ℝ} {R : ℝ} (hle : ∀ y, M y ≤ 1) (hnn : ∀ y, 0 ≤ M y)
  (hzero : ∀ y, R ≤ |y| → M y = 0)

include hzero in
theorem gaugeJumpProfile_eq_zero_of_ge {t : ℝ} (ht : 2 * R ≤ t) : gaugeJumpProfile M F t = 0 := by
  unfold gaugeJumpProfile signedShiftJump
  refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply]
  by_cases hx : |x| < R
  · rw [hzero (x + t) (by
      have ht0 : 0 ≤ t := le_trans (by linarith [abs_nonneg x]) ht
      have := abs_sub_abs_le_abs_sub t (-x)
      rw [abs_neg, sub_neg_eq_add, add_comm, abs_of_nonneg ht0] at this
      linarith), mul_zero, zero_mul]
  · rw [hzero x (not_lt.mp hx), zero_mul, zero_mul]

include hzero in
/-- Below the first prime the jump energy of a window gauge is purely archimedean. -/
theorem signedJumpEnergy_eq_arch_of_window (hR : 2 * R < Real.log 2) :
    signedJumpEnergy M F = ∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M F t := by
  unfold signedJumpEnergy
  have hprime : (∑' n : ℕ, vonMangoldtAtom n * ∫ x, signedShiftJump M F (Real.log n) x) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · unfold vonMangoldtAtom
      rw [if_neg (by omega), zero_mul]
    · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h2)
      rw [show (∫ x, signedShiftJump M F (Real.log n) x) = gaugeJumpProfile M F (Real.log n) from rfl,
        gaugeJumpProfile_eq_zero_of_ge hzero (by linarith), mul_zero]
  rw [hprime, add_zero]
  rfl

include hle hnn hzero in
/-- `I_M(t) ≤ 2R K² t²` for a `K`-Lipschitz test. -/
theorem gaugeJumpProfile_le {K : ℝ} (hR0 : 0 ≤ R) (hFc : Continuous F) (hMc : Continuous M)
    (hMcs : HasCompactSupport M) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) {t : ℝ} (ht : 0 ≤ t) :
    gaugeJumpProfile M F t ≤ 2 * R * (K ^ 2 * t ^ 2) := by
  have hint : Integrable fun x => signedShiftJump M F t x := by
    unfold signedShiftJump
    exact ((hMc.mul (hMc.comp (continuous_id.add continuous_const))).mul
      ((hFc.sub (hFc.comp (continuous_id.add continuous_const))).pow 2)).integrable_of_hasCompactSupport
        (hMcs.mul_right.mul_right)
  have hpt : ∀ x, signedShiftJump M F t x ≤ Set.indicator (Icc (-R) R) (fun _ => K ^ 2 * t ^ 2) x := by
    intro x
    unfold signedShiftJump
    have hsq : (F x - F (x + t)) ^ 2 ≤ K ^ 2 * t ^ 2 := by
      have h := hFL x (x + t)
      rw [show x - (x + t) = -t by ring, abs_neg, abs_of_nonneg ht] at h
      have h0 := abs_nonneg (F x - F (x + t))
      calc (F x - F (x + t)) ^ 2 = |F x - F (x + t)| ^ 2 := (sq_abs _).symm
        _ ≤ (K * t) ^ 2 := pow_le_pow_left₀ h0 h 2
        _ = _ := by ring
    by_cases hx : |x| < R
    · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨(abs_le.mp hx.le).1, (abs_le.mp hx.le).2⟩)]
      have hMM : M x * M (x + t) ≤ 1 :=
        mul_le_one₀ (hle x) (hnn _) (hle _)
      calc M x * M (x + t) * (F x - F (x + t)) ^ 2 ≤ 1 * (K ^ 2 * t ^ 2) :=
            mul_le_mul hMM hsq (sq_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [hzero x (not_lt.mp hx), zero_mul, zero_mul]
      exact Set.indicator_nonneg (fun _ _ => by positivity) x
  unfold gaugeJumpProfile
  calc (∫ x, signedShiftJump M F t x) ≤ ∫ x, Set.indicator (Icc (-R) R) (fun _ => K ^ 2 * t ^ 2) x :=
        integral_mono hint ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const (by simp))) hpt
    _ = _ := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Real.volume_real_Icc, max_eq_left (by linarith)]
        ring

include hle hnn hzero in
/-- `ω · I_M` is integrable on the half line: `ω(t) ≤ 3/(2t)` and `I_M(t) ≤ 2R K² t²`. -/
theorem integrableOn_archLevy_mul_gaugeJumpProfile {K : ℝ} (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 2)
    (hFc : Continuous F) (hMc : Continuous M) (hMcs : HasCompactSupport M)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) :
    IntegrableOn (fun t => archLevyDensity t * gaugeJumpProfile M F t) (Ioi 0) := by
  have hmeas : StronglyMeasurable (gaugeJumpProfile M F) := by
    have hc : Continuous (Function.uncurry fun t x => signedShiftJump M F t x) := by
      unfold signedShiftJump
      fun_prop
    exact hc.stronglyMeasurable.integral_prod_right
  have hm : AEStronglyMeasurable (fun t => archLevyDensity t * gaugeJumpProfile M F t)
      (volume.restrict (Ioi 0)) :=
    (measurable_archLevyDensity.mul hmeas.measurable).aestronglyMeasurable
  have hunion : Ioi (0 : ℝ) = Ioc 0 (2 * R) ∪ Ioi (2 * R) := by
    rcases hR0.lt_or_eq with h | h
    · exact (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    · rw [← h, mul_zero, Ioc_self, empty_union]
  rw [hunion]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 6 * R ^ 2 * K ^ 2) measure_Ioc_lt_top.ne
      (measurable_archLevyDensity.mul hmeas.measurable).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have hI := gaugeJumpProfile_le hle hnn hzero hR0 hFc hMc hMcs hFL ht0.le
    have hI0 : 0 ≤ gaugeJumpProfile M F t := integral_nonneg fun x => by
      unfold signedShiftJump
      exact mul_nonneg (mul_nonneg (hnn _) (hnn _)) (sq_nonneg _)
    have hω := archLevyDensity_le_of_le_one ht0 (by linarith [ht.2])
    have hω0 := (archLevyDensity_pos ht0).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hω0 hI0)]
    calc archLevyDensity t * gaugeJumpProfile M F t ≤ 3 / 2 / t * (2 * R * (K ^ 2 * t ^ 2)) :=
          mul_le_mul hω hI hI0 (by positivity)
      _ = 3 * R * K ^ 2 * t := by field_simp
      _ ≤ 3 * R * K ^ 2 * (2 * R) := by
          have := ht.2
          have h0 : 0 ≤ 3 * R * K ^ 2 := by positivity
          nlinarith
      _ = 6 * R ^ 2 * K ^ 2 := by ring
  · refine (integrableOn_zero (μ := volume)).congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [gaugeJumpProfile_eq_zero_of_ge hzero (le_of_lt ht), mul_zero]

end Window

/-! ### The sharp window killing -/

/-- `N(a) + N(b) ≥ −log(1 − e^{−(a+b)})`: the killing of a window is smallest at its centre. -/
theorem neg_log_one_sub_exp_le_sum {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    -Real.log (1 - Real.exp (-(a + b))) ≤
      -(1 / 2) * Real.log (1 - Real.exp (-2 * a)) + -(1 / 2) * Real.log (1 - Real.exp (-2 * b)) := by
  set u := Real.exp (-a)
  set v := Real.exp (-b)
  have hu0 : 0 < u := Real.exp_pos _
  have hv0 : 0 < v := Real.exp_pos _
  have hu1 : u < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hv1 : v < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have e1 : Real.exp (-2 * a) = u ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-2 * b) = v ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (-(a + b)) = u * v := by rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2, e3]
  have h1 : 0 < 1 - u ^ 2 := by nlinarith
  have h2 : 0 < 1 - v ^ 2 := by nlinarith
  have h3 : 0 < 1 - u * v := by nlinarith
  have hprod : (1 - u ^ 2) * (1 - v ^ 2) ≤ (1 - u * v) ^ 2 := by nlinarith [sq_nonneg (u - v)]
  have hlog := Real.log_le_log (mul_pos h1 h2) hprod
  rw [Real.log_mul h1.ne' h2.ne', Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **The sharp potential of a window gauge.** At a plateau point,
`−𝒲M(x) ≥ −log(1 − e^{−2R}) − (3/2) R − (γ + log π)`. -/
theorem neg_poleFreeWeilOperator_ge_sharp {M : ℝ → ℝ} {K R : ℝ} (hMc : Continuous M)
    (hLip : ∀ a b, |M a - M b| ≤ K * |a - b|) (hle : ∀ y, M y ≤ 1)
    (hsupp : ∀ y, R ≤ |y| → M y = 0) {x : ℝ} (hR : 2 * R < Real.log 2) (hx : |x| < R)
    (hMx : M x = 1) :
    -Real.log (1 - Real.exp (-2 * R)) - 3 / 2 * R - 2 * archConstantReal ≤
      -poleFreeWeilOperator M x := by
  have ha : 0 < R - x := by linarith [le_abs_self x]
  have hb : 0 < R + x := by linarith [neg_abs_le x]
  have hI := integral_profileArchTerm_ge hMc hLip hle hsupp hx hMx
  have hN := neg_log_one_sub_exp_le_sum ha hb
  rw [show -((R - x) + (R + x)) = -2 * R by ring] at hN
  unfold poleFreeWeilOperator
  rw [profilePrimeSum_eq_zero hsupp hR hx, hMx]
  linarith

/-! ### Numerical constants -/

/-- Fifth-order Taylor bound: `e^x ≤ 1 + x + x²/2 + x³/6 + x⁴/24 + |x|⁵/100` for `|x| ≤ 1`. -/
theorem exp_le_taylor_five {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + |x| ^ 5 / 100 := by
  have h := Real.exp_bound hx (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  linarith

theorem one_sub_exp_neg_le_exp_neg :
    1 - Real.exp (-2 * (11 / 100)) ≤ Real.exp (-1.6) := by
  have h1 := exp_le_taylor_five (x := 0.22) (by norm_num [abs_of_pos])
  have h2 := exp_le_taylor_five (x := 0.6) (by norm_num [abs_of_pos])
  have he := Real.exp_one_lt_d9
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.22)] at h1
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.6)] at h2
  norm_num at h1 h2
  have h16 : Real.exp 1.6 = Real.exp 1 * Real.exp 0.6 := by rw [← Real.exp_add]; norm_num
  have hE16 : Real.exp 1.6 ≤ 4.96 := by
    rw [h16]
    nlinarith [Real.exp_pos 1, Real.exp_pos 0.6]
  have hm22 : Real.exp (-2 * (11 / 100)) = (Real.exp 0.22)⁻¹ := by
    rw [← Real.exp_neg]; norm_num
  have hm16 : Real.exp (-1.6) = (Real.exp 1.6)⁻¹ := by rw [← Real.exp_neg]
  rw [hm22, hm16]
  have hp22 := Real.exp_pos 0.22
  have hp16 := Real.exp_pos 1.6
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', inv_eq_one_div, inv_eq_one_div,
    le_div_iff₀ hp22]
  have : 1 / Real.exp 1.6 ≥ 1 / 4.96 := one_div_le_one_div_of_le hp16 hE16
  nlinarith

theorem one_point_six_le_neg_log_window :
    1.6 ≤ -Real.log (1 - Real.exp (-2 * (11 / 100))) := by
  have h := one_sub_exp_neg_le_exp_neg
  have hpos : 0 < 1 - Real.exp (-2 * (11 / 100)) := by
    have : Real.exp (-2 * (11 / 100)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have := Real.log_le_log hpos h
  rw [Real.log_exp] at this
  linarith

/-- **The Z-type aperture.** `2cosh(t/2) ≤ ω(t)` for `0 < t ≤ 0.22`: the archimedean Lévy density
dominates the pole density on windows of width `0.22`. -/
theorem two_mul_cosh_le_archLevyDensity {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 0.22) :
    2 * Real.cosh (t / 2) ≤ archLevyDensity t := by
  have hc : Real.cosh (t / 2) ≤ Real.cosh 0.11 :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_pos (by linarith), abs_of_pos (by norm_num)]; linarith)
  have hT := exp_le_taylor_five (x := 0.11) (by norm_num [abs_of_pos])
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.11)] at hT
  norm_num at hT
  have hL := Real.add_one_le_exp (0.11 : ℝ)
  have hcosh : 2 * Real.cosh 0.11 ≤ 2.0175 := by
    rw [Real.cosh_eq, show -(0.11 : ℝ) = -0.11 by norm_num, Real.exp_neg]
    have hp := Real.exp_pos 0.11
    have : (Real.exp 0.11)⁻¹ ≤ 1 / 1.11 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    norm_num at this ⊢
    linarith
  have hnum : 0.89 ≤ Real.exp (-t / 2) := by
    have := Real.add_one_le_exp (-t / 2)
    linarith
  have hden0 : 0 < 1 - Real.exp (-2 * t) := by
    have : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hden : 1 - Real.exp (-2 * t) ≤ 0.44 := by
    have := Real.add_one_le_exp (-2 * t)
    linarith
  have hω : 0.89 / 0.44 ≤ archLevyDensity t := by
    unfold archLevyDensity
    exact div_le_div₀ (by linarith) hnum hden0 hden
  norm_num at hω
  linarith

/-! ### The gauge mass -/

theorem integral_gauge_cosh_eq {M : ℝ → ℝ} (hM : Continuous M) (hMc : HasCompactSupport M) (x : ℝ) :
    (∫ y, M y * Real.cosh ((x - y) / 2)) =
      Real.cosh (x / 2) * (∫ y, M y * Real.cosh (y / 2)) -
        Real.sinh (x / 2) * ∫ y, M y * Real.sinh (y / 2) := by
  have hc : Integrable fun y => M y * Real.cosh (y / 2) :=
    (hM.mul (by fun_prop)).integrable_of_hasCompactSupport hMc.mul_right
  have hs : Integrable fun y => M y * Real.sinh (y / 2) :=
    (hM.mul (by fun_prop)).integrable_of_hasCompactSupport hMc.mul_right
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hc.const_mul _) (hs.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [show (x - y) / 2 = x / 2 - y / 2 by ring, Real.cosh_sub]
  ring

/-- The gauge mass seen from any point is at least the plateau length: `∫ M(y) cosh((x−y)/2) ≥ 2r`. -/
theorem two_mul_le_integral_gauge_cosh {M : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r) (hM : Continuous M)
    (hMc : HasCompactSupport M) (hnn : ∀ y, 0 ≤ M y) (hone : ∀ y, |y| ≤ r → M y = 1) (x : ℝ) :
    2 * r ≤ ∫ y, M y * Real.cosh ((x - y) / 2) := by
  have hint : Integrable fun y => M y * Real.cosh ((x - y) / 2) :=
    (hM.mul (by fun_prop)).integrable_of_hasCompactSupport hMc.mul_right
  have hset : (∫ y in Icc (-r) r, M y * Real.cosh ((x - y) / 2)) ≤
      ∫ y, M y * Real.cosh ((x - y) / 2) :=
    setIntegral_le_integral hint (Eventually.of_forall fun y =>
      mul_nonneg (hnn y) (Real.cosh_pos _).le)
  have hlow : (∫ y in Icc (-r) r, (1 : ℝ)) ≤ ∫ y in Icc (-r) r, M y * Real.cosh ((x - y) / 2) :=
    setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc
      fun y hy => by
        rw [hone y (abs_le.mpr ⟨hy.1, hy.2⟩), one_mul]
        exact Real.one_le_cosh _
  rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc, max_eq_left (by linarith)]
    at hlow
  linarith

/-! ### Coercive positivity on the Markov window -/

/-- **Weil positivity on `[−0.105, 0.105]` with the pole as a conductance.** Every real `F ∈ C²_c`
vanishing outside `[−21/200, 21/200]` satisfies `Ẑ(F) ≥ (1/30) ∫ F²`. -/
theorem fullZeroForm_ge_of_support_le_sharp {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 21 / 200 < |x| → F x = 0) :
    1 / 30 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set R : ℝ := 11 / 100 with hRdef
  set δ : ℝ := 1 / 200 with hδdef
  have hδ : 0 < δ := by norm_num
  set M := plateauGauge R δ with hMdef
  have hMd : ContDiff ℝ 2 M := contDiff_plateauGauge R δ
  have hMcs : HasCompactSupport M := hasCompactSupport_plateauGauge hδ
  have hnn : ∀ y, 0 ≤ M y := plateauGauge_nonneg R δ
  have hle : ∀ y, M y ≤ 1 := plateauGauge_le_one R δ
  have hzero : ∀ y, R ≤ |y| → M y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  have hone : ∀ y, |y| ≤ 21 / 200 → M y = 1 := fun y hy =>
    plateauGauge_eq_one hδ (by rw [hRdef, hδdef]; norm_num; linarith)
  have hFM : ∀ x, F x ≠ 0 → M x = 1 := fun x hx => hone x (by
    by_contra h
    exact hx (hsupp x (not_le.mp h)))
  have hFx : ∀ x, F x ≠ 0 → |x| < R := fun x hx => by
    by_contra h
    exact hx (by
      have := hzero x (not_lt.mp h)
      rw [hFM x hx] at this
      norm_num at this)
  have hFB : ∀ x, F x ≠ 0 → |x| ≤ R := fun x hx => (hFx x hx).le
  have hMB : ∀ x, M x ≠ 0 → |x| ≤ R := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hlog2 : 2 * R < Real.log 2 := by
    have := Real.log_two_gt_d9
    rw [hRdef]
    linarith
  obtain ⟨KF, -, hKF⟩ := exists_lipschitz_bound_of_compactSupport (hF.of_le (by norm_num)) hFc
  have hFL : ∀ a b, |F a - F b| ≤ KF * |a - b| := fun a b => hKF b a
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hML : ∀ a b, |M a - M b| ≤ KM * |a - b| := fun a b => hKM b a
  -- the representation
  have hQ := markovEnergy_eq_gauge_window hF hFc hMd hMcs hle hnn hzero hFM
  have hJ := signedJumpEnergy_eq_arch_of_window (F := F) hzero hlog2
  have hE := two_mul_expMoments_eq_gauge hF.continuous hMd.continuous hFB hMB hFM
  have hZ := fullZeroForm_eq_markovEnergy_add_expMoments hF.continuous hFc
  -- the jump part: `ω − 2cosh(t/2) ≥ 0` below the Z-type aperture
  have hωI := integrableOn_archLevy_mul_gaugeJumpProfile hle hnn hzero (by norm_num) (by norm_num)
    hF.continuous hMd.continuous hMcs hFL
  have hcI : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M F t :=
    (integrable_gaugeJump_kernel hF.continuous hMd.continuous hMB).integral_prod_left.congr
      (Eventually.of_forall fun t => by
        simp only [gaugeJumpProfile]
        rw [integral_const_mul])
  have hjump : 2 * (∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M F t) ≤
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M F t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hcI.integrableOn.const_mul 2) hωI measurableSet_Ioi fun t ht => ?_
    have hI0 : 0 ≤ gaugeJumpProfile M F t := integral_nonneg fun x => by
      unfold signedShiftJump
      exact mul_nonneg (mul_nonneg (hnn _) (hnn _)) (sq_nonneg _)
    by_cases h : t ≤ 2 * R
    · rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (two_mul_cosh_le_archLevyDensity ht
        (by rw [hRdef] at h; linarith)) hI0
    · rw [gaugeJumpProfile_eq_zero_of_ge hzero (not_le.mp h).le]
      simp
  -- the potential
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * R) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hnn y), ← Real.exp_add]
      exact (hle y).trans (Real.one_le_exp (by nlinarith))
    · rw [hzero y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator M x :=
    (continuous_poleFreeWeilOperator hMd.continuous hML hdec8).neg
  have hG : Continuous fun x => ∫ y, M y * Real.cosh ((x - y) / 2) := by
    have e := funext (integral_gauge_cosh_eq hMd.continuous hMcs)
    rw [e]
    fun_prop
  set V := -Real.log (1 - Real.exp (-2 * R)) - 3 / 2 * R - 2 * archConstantReal + 4 * (21 / 200)
    with hVdef
  have hV : 1 / 30 ≤ V := by
    have h1 := one_point_six_le_neg_log_window
    have h2 := Real.eulerMascheroniConstant_lt_two_thirds
    have h3 := log_pi_lt
    rw [hVdef, hRdef]
    unfold archConstantReal
    linarith
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hP1 : Integrable fun x => F x ^ 2 * M x * -poleFreeWeilOperator M x :=
    (((hF.continuous.pow 2).mul hMd.continuous).mul hW).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  have hP2 : Integrable fun x => F x ^ 2 * ∫ y, M y * Real.cosh ((x - y) / 2) :=
    ((hF.continuous.pow 2).mul hG).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc).mul_right
  have hpot : V * ∫ x, F x ^ 2 ≤ (∫ x, F x ^ 2 * M x * -poleFreeWeilOperator M x) +
      2 * ∫ x, F x ^ 2 * ∫ y, M y * Real.cosh ((x - y) / 2) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hP1 (hP2.const_mul 2)]
    refine integral_mono (hF2.const_mul V) (hP1.add (hP2.const_mul 2)) fun x => ?_
    by_cases h : F x = 0
    · simp [h]
    · have hw := neg_poleFreeWeilOperator_ge_sharp hMd.continuous hML hle hzero hlog2 (hFx x h)
        (hFM x h)
      have hg := two_mul_le_integral_gauge_cosh (r := 21 / 200) (by norm_num) hMd.continuous hMcs
        hnn hone x
      rw [hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      nlinarith [mul_le_mul_of_nonneg_left hw hF0, mul_le_mul_of_nonneg_left hg hF0]
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hfin : (1 / 30) * ∫ x, F x ^ 2 ≤ V * ∫ x, F x ^ 2 := mul_le_mul_of_nonneg_right hV hI0
  rw [hZ, hQ, hJ, hE]
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
