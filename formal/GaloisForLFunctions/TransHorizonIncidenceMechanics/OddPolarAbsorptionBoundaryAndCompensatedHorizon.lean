import GaloisForLFunctions.TransHorizonIncidenceMechanics.CollectiveLowPrimeChebyshevTransportAndSinhAbsorption
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Odd-polar absorption boundary and minimal compensated correction

The literal theta source has an exponentially growing tail price. No fixed
coefficient absorbs its cosh mass into the sinh potential on all even compact
profiles. The positive survivor is a quantitative confinement law and the exact
smallest continuous nonnegative local correction, retaining the complete
reflected-prime compensation. This does not pay that correction with jump energy.
-/

open MeasureTheory Set Filter Topology
open scoped Real BigOperators
open RHTower RHTower.CHMDPolar RHTower.CHMDDoobGraph
open RHTower.CHMDPrimeCuts RHTower.CHMDPrimeChainSource
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
private theorem two_sinh_half_le (a : ℝ) :
    2 * Real.sinh (a / 2) ≤ a * Real.exp (a / 2) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-a))
    (Real.exp_pos (a / 2)).le
  have he : Real.exp (a / 2) * Real.exp (-a) = Real.exp (-(a / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  rw [Real.sinh_eq]
  nlinarith

/-- The shifted theta difference grows relative to theta at an explicit exponential rate. -/
theorem oddPolarFunction_tail_lower {a x : ℝ} (ha : 0 < a) (hx : Real.log 2 / 2 ≤ x - a) :
    Real.pi * Real.exp (2 * x - 5 * a / 2) ≤ oddPolarFunction a x := by
  have hx0 : 0 ≤ x := by linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  have hdrop := riemannKernelReal_sub_ge_linear_of_log_two_half_le hx (by linarith : x - a ≤ x)
  have hmono : riemannKernelReal (x + a) ≤ riemannKernelReal x :=
    strictAntiOn_riemannKernelReal_Ici.antitoneOn (mem_Ici.mpr hx0)
      (mem_Ici.mpr (by linarith : 0 ≤ x + a)) (by linarith)
  have hθ := riemannKernelReal_pos x
  have hs : 0 < 2 * Real.sinh (a / 2) := by positivity
  have hid : Real.exp (2 * x - 5 * a / 2) * Real.exp (a / 2) =
      Real.exp (2 * (x - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [oddPolarFunction_eq_oddProfile_div, le_div_iff₀ hθ]
  unfold oddProfile
  rw [le_div_iff₀ hs]
  calc Real.pi * Real.exp (2 * x - 5 * a / 2) * riemannKernelReal x *
        (2 * Real.sinh (a / 2))
      ≤ Real.pi * Real.exp (2 * x - 5 * a / 2) * riemannKernelReal x *
        (a * Real.exp (a / 2)) :=
        mul_le_mul_of_nonneg_left (two_sinh_half_le a) (by positivity)
    _ = Real.pi * Real.exp (2 * (x - a)) * riemannKernelReal x * (x - (x - a)) := by
        calc _ = Real.pi * (Real.exp (2 * x - 5 * a / 2) * Real.exp (a / 2)) *
            riemannKernelReal x * a := by ring
        _ = _ := by rw [hid]; ring
    _ ≤ riemannKernelReal (x - a) - riemannKernelReal (x + a) := by linarith

/-- A lower tail price uniform over the admitted positive shift interval. -/
theorem oddPolarFunction_cosh_tail_lower {a x : ℝ} (ha : 0 < a) (ha' : a ≤ Real.log 2 / 2)
    (hx : Real.log 2 ≤ x) :
    Real.pi * Real.exp (2 * x - 5 * Real.log 2 / 4) * Real.sinh (x / 2) ≤
      oddPolarFunction a x * Real.cosh (x / 2) := by
  have hx0 : 0 < x := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hx
  have hp : 0 < oddPolarFunction a x := oddPolarFunction_pos ha hx0
  have hbase : Real.pi * Real.exp (2 * x - 5 * Real.log 2 / 4) ≤
      Real.pi * Real.exp (2 * x - 5 * a / 2) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le
  have h := hbase.trans (oddPolarFunction_tail_lower ha (by linarith))
  exact (mul_le_mul_of_nonneg_right h (Real.sinh_pos_iff.mpr (half_pos hx0)).le).trans
    (mul_le_mul_of_nonneg_left (Real.sinh_lt_cosh (x / 2)).le hp.le)

private theorem exists_even_smooth_positive_integral {g : ℝ → ℝ}
    (hg : Continuous g) (heven : ∀ x, g (-x) = g x) {x₀ : ℝ} (hx₀ : 0 < g x₀) :
    ∃ w : ℝ → ℝ, ContDiff ℝ 2 w ∧ HasCompactSupport w ∧
      (∀ x, w (-x) = w x) ∧ 0 < ∫ x, g x * w x ^ 2 := by
  have hn : ∀ᶠ x in 𝓝 x₀, 0 < g x :=
    (isOpen_lt continuous_const hg).mem_nhds hx₀
  obtain ⟨r, hr, hrpos⟩ := Metric.eventually_nhds_iff.mp hn
  let b : ContDiffBump x₀ := ⟨r / 2, r, by positivity, by linarith⟩
  let w : ℝ → ℝ := fun x => b x + b (-x)
  have hw : ContDiff ℝ 2 w := b.contDiff.add (b.contDiff.comp contDiff_neg)
  have hwc : HasCompactSupport w :=
    b.hasCompactSupport.add (b.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ))
  have hwe : ∀ x, w (-x) = w x := by intro x; simp [w, add_comm]
  have hsqc : HasCompactSupport (fun x => w x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hwc ⊢
    filter_upwards [hwc] with x hx
    simp [hx]
  have hnonneg : ∀ x, 0 ≤ g x * w x ^ 2 := by
    intro x
    by_cases hzero : w x = 0
    · simp [hzero]
    have hgx : 0 < g x := by
      by_cases hb : b x = 0
      · have hb' : b (-x) ≠ 0 := by
          intro hz
          apply hzero
          simp [w, hb, hz]
        have hmem : -x ∈ Function.support b := hb'
        rw [b.support_eq, Metric.mem_ball] at hmem
        simpa only [heven x] using hrpos hmem
      · have hmem : x ∈ Function.support b := hb
        rw [b.support_eq, Metric.mem_ball] at hmem
        exact hrpos hmem
    exact mul_nonneg hgx.le (sq_nonneg _)
  have hwx : 0 < w x₀ := by
    have hb : b x₀ = 1 := b.one_of_mem_closedBall (by simp [b]; positivity)
    have hb' : 0 ≤ b (-x₀) := b.nonneg
    dsimp [w]
    linarith
  refine ⟨w, hw, hwc, hwe, ?_⟩
  exact (hg.mul (hw.continuous.pow 2)).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hsqc.mul_left hnonneg (mul_pos hx₀ (sq_pos_of_pos hwx)).ne'

private theorem evenIntegralSquare_nonneg_iff {g : ℝ → ℝ} (hg : Continuous g) (heven : ∀ x, g (-x) = g x) :
    (∀ w : ℝ → ℝ, ContDiff ℝ 2 w → HasCompactSupport w →
      (∀ x, w (-x) = w x) → 0 ≤ ∫ x, g x * w x ^ 2) ↔ ∀ x, 0 ≤ g x := by
  constructor
  · intro h x
    by_contra hx
    obtain ⟨w, hw, hwc, hwe, hi⟩ := exists_even_smooth_positive_integral hg.neg
      (fun y => by simp [heven y]) (neg_pos.mpr (lt_of_not_ge hx))
    have hle := h w hw hwc hwe
    have hid : (∫ x, (-g) x * w x ^ 2) = -(∫ x, g x * w x ^ 2) := by
      simp only [Pi.neg_apply, neg_mul, integral_neg]
    rw [hid] at hi
    linarith
  · intro h w _ _ _
    exact integral_nonneg fun x => mul_nonneg (h x) (sq_nonneg _)

/-- The complete sinh potential, with its full-line normalization. -/
def oddSinhPotential (a : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ x, oddProfile a x * Real.sinh (x / 2) * w x ^ 2

/-- The local excess of cosh mass over a chosen sinh potential. -/
def oddPolarDefectDensity (a θ x : ℝ) : ℝ :=
  riemannKernelReal x * oddPolarFunction a x ^ 2 * Real.cosh (x / 2) -
    θ * (oddProfile a x * Real.sinh (x / 2))

/-- The nonnegative multiplication correction required by the cosh excess. -/
def oddPolarDefect (a θ : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ x, max (oddPolarDefectDensity a θ x) 0 * w x ^ 2

/-- The nonnegative potential left over where the sinh contribution is larger. -/
def oddPolarReserve (a θ : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ x, max (-oddPolarDefectDensity a θ x) 0 * w x ^ 2

private theorem compact_sq {w : ℝ → ℝ} (hwc : HasCompactSupport w) :
    HasCompactSupport (fun x => w x ^ 2) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hwc ⊢
  filter_upwards [hwc] with x hx
  simp [hx]

private theorem weighted_sq_integrable {w k : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (hk : Continuous k) :
    Integrable (fun x => k x * w x ^ 2) :=
  (hk.mul (hw.pow 2)).integrable_of_hasCompactSupport (compact_sq hwc).mul_left

private theorem continuous_mass_kernel (a : ℝ) :
    Continuous (fun x => riemannKernelReal x * oddPolarFunction a x ^ 2 *
      Real.cosh (x / 2)) :=
  (continuous_riemannKernelReal.mul ((continuous_oddPolarFunction a).pow 2)).mul
    (Real.continuous_cosh.comp (continuous_id.div_const 2))

private theorem continuous_sinh_kernel (a : ℝ) :
    Continuous (fun x => oddProfile a x * Real.sinh (x / 2)) :=
  (continuous_oddProfile a).mul (Real.continuous_sinh.comp (continuous_id.div_const 2))

theorem continuous_oddPolarDefectDensity (a θ : ℝ) :
    Continuous (oddPolarDefectDensity a θ) :=
  (continuous_mass_kernel a).sub (continuous_const.mul (continuous_sinh_kernel a))

theorem oddPolarDefectDensity_even (a θ x : ℝ) :
    oddPolarDefectDensity a θ (-x) = oddPolarDefectDensity a θ x := by
  unfold oddPolarDefectDensity
  rw [WeilExcess.riemannKernelReal_neg, oddPolarFunction_neg, oddProfile_neg,
    neg_div, Real.cosh_neg, Real.sinh_neg]
  ring

theorem oddSinhPotential_eq_halfLine (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    oddSinhPotential a w =
      2 * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
  have h := integral_oddProfileTest_sq_mul_sinh_eq_two_mul_Ioi a hw hwc heven
  simpa only [oddSinhPotential, oddProfileTest, mul_right_comm] using h

theorem oddPolarDefect_nonneg (a θ : ℝ) (w : ℝ → ℝ) : 0 ≤ oddPolarDefect a θ w :=
  integral_nonneg fun _ => mul_nonneg (le_max_right _ _) (sq_nonneg _)

theorem oddPolarReserve_nonneg (a θ : ℝ) (w : ℝ → ℝ) : 0 ≤ oddPolarReserve a θ w :=
  integral_nonneg fun _ => mul_nonneg (le_max_right _ _) (sq_nonneg _)

theorem coshMass_sub_sinh_eq_defect_sub_reserve (a θ : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) - θ * oddSinhPotential a w =
      oddPolarDefect a θ w - oddPolarReserve a θ w := by
  have hi := weighted_sq_integrable hw hwc (continuous_mass_kernel a)
  have hj := weighted_sq_integrable hw hwc (continuous_sinh_kernel a)
  have hd := continuous_oddPolarDefectDensity a θ
  have hp := weighted_sq_integrable hw hwc (hd.max (continuous_const (y := (0 : ℝ))))
  have hn := weighted_sq_integrable hw hwc (hd.neg.max (continuous_const (y := (0 : ℝ))))
  change Integrable (fun x => max (-oddPolarDefectDensity a θ x) 0 * w x ^ 2) at hn
  have hmass : phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) =
      ∫ x, (riemannKernelReal x * oddPolarFunction a x ^ 2 * Real.cosh (x / 2)) * w x ^ 2 := by
    unfold phiDoobCoshMass phiDoobTest oddPolarWeight
    congr 1
    funext x
    ring
  rw [hmass, oddSinhPotential, oddPolarDefect, oddPolarReserve,
    ← integral_const_mul, ← integral_sub hi (hj.const_mul θ), ← integral_sub hp hn]
  apply integral_congr_ae
  filter_upwards [] with x
  have hmax : max (oddPolarDefectDensity a θ x) 0 -
      max (-oddPolarDefectDensity a θ x) 0 = oddPolarDefectDensity a θ x := by
    by_cases h : 0 ≤ oddPolarDefectDensity a θ x
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  rw [← sub_mul, hmax]
  unfold oddPolarDefectDensity
  ring

/-- Complete signed energy with its exact nonnegative local correction and reserve. -/
theorem oddProfile_complete_compensated_identity (a θ : ℝ) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    markovEnergy (fun x => (oddProfileTest a w x : ℂ)) + θ * oddSinhPotential a w +
        oddPolarDefect a θ w =
      phiDoobArchJumpEnergy (oddPolarWeight a w) + 2 * sameSide (oddPolarWeight a w) +
        (∑' q : ChainIndex, chainIntegral (oddPolarWeight a w) q) + oddPolarReserve a θ w := by
  have h := oddProfileTest_markovEnergy_eq_chain_variances_sub_cosh a hw hwc heven
  have hd := coshMass_sub_sinh_eq_defect_sub_reserve a θ hw.continuous hwc
  linarith

/-- The exact local correction gives a complete lower bound at every finite support radius. -/
theorem oddProfile_complete_compensated_nonneg (a θ : ℝ) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    0 ≤ markovEnergy (fun x => (oddProfileTest a w x : ℂ)) + θ * oddSinhPotential a w +
      oddPolarDefect a θ w := by
  rw [oddProfile_complete_compensated_identity a θ hw hwc heven]
  exact add_nonneg (add_nonneg (add_nonneg (phiDoobArchJumpEnergy_nonneg _)
    (mul_nonneg (by norm_num) (sameSide_nonneg _)))
    (tsum_nonneg fun q => chainIntegral_nonneg _ q)) (oddPolarReserve_nonneg a θ w)

/-- An exponential lower price for sinh mass lying beyond `L`. -/
def oddPolarTailPrice (L : ℝ) : ℝ :=
  Real.pi * Real.exp (2 * L - 5 * Real.log 2 / 4)

theorem oddPolarTailPrice_pos (L : ℝ) : 0 < oddPolarTailPrice L := by
  unfold oddPolarTailPrice
  positivity

theorem oddPolarTailPrice_gt_one {L : ℝ} (hL : Real.log 2 ≤ L) :
    1 < oddPolarTailPrice L := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp (2 * L - 5 * Real.log 2 / 4) :=
    Real.one_le_exp_iff.mpr (by linarith)
  have hp := Real.pi_gt_three
  unfold oddPolarTailPrice
  nlinarith

theorem coshSinhPolarRatio_ge_tailPrice {a M R : ℝ}
    (ha : 0 < a) (ha' : a ≤ Real.log 2 / 2) (hR : Real.log 2 ≤ R)
    (hM : ∀ u ∈ Icc (a - R) (a + R), ‖deriv riemannKernelReal u‖ ≤ M) :
    oddPolarTailPrice R ≤ coshSinhPolarRatio a M R := by
  have hR0 : 0 ≤ R := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨by linarith, by linarith⟩)
  have hlo := oddPolarFunction_cosh_tail_lower ha ha' hR
  have hhi := oddPolarFunction_mul_cosh_le_sinh_of_deriv_bound ha hM0 hM
    (show R ∈ Icc (0 : ℝ) R from ⟨hR0, le_rfl⟩)
  exact le_of_mul_le_mul_right (hlo.trans hhi)
    (Real.sinh_pos_iff.mpr (half_pos ((Real.log_pos (by norm_num)).trans_le hR)))

/-- Unit absorption by a derivative majorant is infeasible at every radius at least `log 2`. -/
theorem no_unit_coshSinhPolarRatio :
    ¬ ∃ a M R : ℝ, 0 < a ∧ a ≤ Real.log 2 / 2 ∧ Real.log 2 ≤ R ∧
      (∀ u ∈ Icc (a - R) (a + R), ‖deriv riemannKernelReal u‖ ≤ M) ∧
      coshSinhPolarRatio a M R ≤ 1 := by
  rintro ⟨a, M, R, ha, ha', hR, hM, hratio⟩
  exact (not_le_of_gt (oddPolarTailPrice_gt_one hR))
    ((coshSinhPolarRatio_ge_tailPrice ha ha' hR hM).trans hratio)

/-- Sinh potential beyond a positive horizon, with both odd-source halves included. -/
def oddSinhTail (a L : ℝ) (w : ℝ → ℝ) : ℝ :=
  2 * ∫ x in Ioi L, oddProfile a x * Real.sinh (x / 2) * w x ^ 2

theorem oddPolarTailPrice_mono : Monotone oddPolarTailPrice := by
  intro L R hLR
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le

/-- Bounded cosh mass forces exponential confinement of the literal sinh potential. -/
theorem oddSinhTail_mul_price_le_coshMass {a L : ℝ}
    (ha : 0 < a) (ha' : a ≤ Real.log 2 / 2) (hL : Real.log 2 ≤ L)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) :
    oddPolarTailPrice L * oddSinhTail a L w ≤
      phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) := by
  have hv := continuous_oddPolarWeight a hw
  have hvc := hasCompactSupport_oddPolarWeight a hwc
  have hcs : HasCompactSupport (fun x => oddPolarWeight a w x ^ 2) := compact_sq hvc
  have hc : Integrable (fun x => riemannKernelReal x * oddPolarWeight a w x ^ 2 *
      Real.cosh (x / 2)) :=
    ((continuous_riemannKernelReal.mul (hv.pow 2)).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hcs.mul_left.mul_right
  have hp := weighted_sq_integrable hw hwc (continuous_sinh_kernel a)
  have hprice :
      oddPolarTailPrice L * (∫ x in Ioi L, oddProfile a x * Real.sinh (x / 2) * w x ^ 2) ≤
        ∫ x in Ioi L, riemannKernelReal x * oddPolarWeight a w x ^ 2 * Real.cosh (x / 2) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hp.const_mul _).integrableOn hc.integrableOn measurableSet_Ioi
    intro x hx
    have hLx : L ≤ x := (mem_Ioi.mp hx).le
    have hx0 : 0 < x := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le (hL.trans hLx)
    have hbound := (mul_le_mul_of_nonneg_right (oddPolarTailPrice_mono hLx)
      (Real.sinh_pos_iff.mpr (half_pos hx0)).le).trans (oddPolarFunction_cosh_tail_lower ha ha' (hL.trans hLx))
    have hmul := mul_le_mul_of_nonneg_left hbound
      (mul_nonneg (oddProfile_pos ha hx0).le (sq_nonneg (w x)))
    have hm : oddProfile a x = riemannKernelReal x * oddPolarFunction a x := by
      rw [oddPolarFunction_eq_oddProfile_div, mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']
    calc oddPolarTailPrice L * (oddProfile a x * Real.sinh (x / 2) * w x ^ 2)
        = (oddProfile a x * w x ^ 2) * (oddPolarTailPrice L * Real.sinh (x / 2)) := by ring
      _ ≤ (oddProfile a x * w x ^ 2) *
          (oddPolarFunction a x * Real.cosh (x / 2)) := hmul
      _ = _ := by rw [hm]; unfold oddPolarWeight; ring
  have hsubset : Ioi L ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_le_of_lt ((Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hL) hx
  have htail := setIntegral_mono_set (s := Ioi L) (t := Ioi (0 : ℝ)) hc.integrableOn
    (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (mul_nonneg (riemannKernelReal_pos x).le (sq_nonneg _)) (Real.cosh_pos _).le))
    (Filter.Eventually.of_forall hsubset)
  rw [phiDoobCoshMass_sq_eq_two_mul_integral_Ioi_of_odd hv hvc
    (oddPolarWeight_odd_of_even a heven)]
  unfold oddSinhTail
  calc oddPolarTailPrice L * (2 * ∫ x in Ioi L, oddProfile a x * Real.sinh (x / 2) * w x ^ 2)
      = 2 * (oddPolarTailPrice L * ∫ x in Ioi L, oddProfile a x * Real.sinh (x / 2) * w x ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hprice.trans htail) (by norm_num)

theorem coshMass_sub_sinh_eq_integral_defect (a θ : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) - θ * oddSinhPotential a w =
      ∫ x, oddPolarDefectDensity a θ x * w x ^ 2 := by
  have hi := weighted_sq_integrable hw hwc (continuous_mass_kernel a)
  have hj := weighted_sq_integrable hw hwc (continuous_sinh_kernel a)
  have hmass : phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) =
      ∫ x, (riemannKernelReal x * oddPolarFunction a x ^ 2 * Real.cosh (x / 2)) * w x ^ 2 := by
    unfold phiDoobCoshMass phiDoobTest oddPolarWeight
    congr 1
    funext x
    ring
  rw [hmass, oddSinhPotential, ← integral_const_mul, ← integral_sub hi (hj.const_mul θ)]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold oddPolarDefectDensity
  ring

/-- A continuous even correction pays cosh mass on every compact even source exactly
when it dominates the literal signed defect pointwise. -/
theorem oddPolar_correction_iff (a θ : ℝ) {h : ℝ → ℝ}
    (hh : Continuous h) (heven : ∀ x, h (-x) = h x) :
    (∀ w : ℝ → ℝ, ContDiff ℝ 2 w → HasCompactSupport w →
      (∀ x, w (-x) = w x) →
      phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) ≤
        θ * oddSinhPotential a w + ∫ x, h x * w x ^ 2) ↔
      ∀ x, oddPolarDefectDensity a θ x ≤ h x := by
  let g : ℝ → ℝ := fun x => h x - oddPolarDefectDensity a θ x
  have hg : Continuous g := hh.sub (continuous_oddPolarDefectDensity a θ)
  have hge : ∀ x, g (-x) = g x := by
    intro x
    simp only [g, heven, oddPolarDefectDensity_even]
  have hid (w : ℝ → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
      (∫ x, g x * w x ^ 2) = (∫ x, h x * w x ^ 2) -
        (phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) - θ * oddSinhPotential a w) := by
    rw [coshMass_sub_sinh_eq_integral_defect a θ hw hwc,
      ← integral_sub (weighted_sq_integrable hw hwc hh)
        (weighted_sq_integrable hw hwc (continuous_oddPolarDefectDensity a θ))]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [g]
    ring
  constructor
  · intro hall
    have hgn := (evenIntegralSquare_nonneg_iff hg hge).mp
      (fun w hw hwc hwe => by rw [hid w hw.continuous hwc]; linarith [hall w hw hwc hwe])
    intro x
    exact sub_nonneg.mp (hgn x)
  · intro hpoint w hw hwc hwe
    have hgn : 0 ≤ ∫ x : ℝ, g x * w x ^ 2 := integral_nonneg (fun x =>
      mul_nonneg (sub_nonneg.mpr (hpoint x)) (sq_nonneg (w x)))
    rw [hid w hw.continuous hwc] at hgn
    linarith

/-- The positive part is the smallest nonnegative local correction; no universal
integrated improvement can reduce it on a nonempty open interval. -/
theorem oddPolar_minimal_nonnegative_correction (a θ : ℝ) {h : ℝ → ℝ}
    (hh : Continuous h) (heven : ∀ x, h (-x) = h x) (hpos : ∀ x, 0 ≤ h x) :
    (∀ w : ℝ → ℝ, ContDiff ℝ 2 w → HasCompactSupport w →
      (∀ x, w (-x) = w x) →
      phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) ≤
        θ * oddSinhPotential a w + ∫ x, h x * w x ^ 2) ↔
      ∀ x, max (oddPolarDefectDensity a θ x) 0 ≤ h x := by
  rw [oddPolar_correction_iff a θ hh heven]
  constructor
  · intro hd x
    exact max_le (hd x) (hpos x)
  · intro hd x
    exact (le_max_left _ _).trans (hd x)

private theorem exists_tailPrice_gt (θ : ℝ) :
    ∃ L : ℝ, Real.log 2 ≤ L ∧ θ < oddPolarTailPrice L := by
  let L := Real.log 2 + |θ| + 1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨L, by dsimp [L]; linarith [abs_nonneg θ], ?_⟩
  have he := Real.add_one_le_exp (2 * L - 5 * Real.log 2 / 4)
  have hθ : θ < Real.exp (2 * L - 5 * Real.log 2 / 4) := by
    dsimp [L] at he
    linarith [le_abs_self θ, abs_nonneg θ]
  have hp : Real.exp (2 * L - 5 * Real.log 2 / 4) ≤ oddPolarTailPrice L := by
    unfold oddPolarTailPrice
    nlinarith [Real.pi_gt_three, Real.exp_pos (2 * L - 5 * Real.log 2 / 4)]
  exact hθ.trans_le hp

private theorem defect_pos_of_tailPrice_gt {a θ L : ℝ}
    (ha : 0 < a) (ha' : a ≤ Real.log 2 / 2) (hL : Real.log 2 ≤ L)
    (hθ : θ < oddPolarTailPrice L) : 0 < oddPolarDefectDensity a θ L := by
  have hL0 : 0 < L := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hL
  have hm := oddProfile_pos ha hL0
  have hs := Real.sinh_pos_iff.mpr (half_pos hL0)
  have hb := oddPolarFunction_cosh_tail_lower ha ha' hL
  have ht : θ * Real.sinh (L / 2) < oddPolarFunction a L * Real.cosh (L / 2) :=
    (mul_lt_mul_of_pos_right hθ hs).trans_le hb
  have hid : oddPolarDefectDensity a θ L =
      oddProfile a L * (oddPolarFunction a L * Real.cosh (L / 2) - θ * Real.sinh (L / 2)) := by
    unfold oddPolarDefectDensity
    have hp : oddProfile a L = riemannKernelReal L * oddPolarFunction a L := by
      rw [oddPolarFunction_eq_oddProfile_div, mul_div_cancel₀ _ (riemannKernelReal_pos L).ne']
    rw [hp]
    ring
  rw [hid]
  exact mul_pos hm (sub_pos.mpr ht)

/-- No fixed coefficient absorbs cosh mass into the sinh potential, even on smooth
compact even profiles of the actual theta source. -/
theorem oddPolar_integrated_absorption_counterexample {a : ℝ}
    (ha : 0 < a) (ha' : a ≤ Real.log 2 / 2) (θ : ℝ) :
    ∃ w : ℝ → ℝ, ContDiff ℝ 2 w ∧ HasCompactSupport w ∧ (∀ x, w (-x) = w x) ∧
      θ * oddSinhPotential a w < phiDoobCoshMass (fun x => oddPolarWeight a w x ^ 2) := by
  obtain ⟨L, hL, hθ⟩ := exists_tailPrice_gt θ
  obtain ⟨w, hw, hwc, hwe, hi⟩ := exists_even_smooth_positive_integral
    (continuous_oddPolarDefectDensity a θ) (oddPolarDefectDensity_even a θ)
    (defect_pos_of_tailPrice_gt ha ha' hL hθ)
  refine ⟨w, hw, hwc, hwe, ?_⟩
  rw [← coshMass_sub_sinh_eq_integral_defect a θ hw.continuous hwc] at hi
  exact sub_pos.mp hi

/-- Even smooth localization preserves the actual compact odd source, its zero mean,
and both support restrictions. -/
theorem oddProfile_localized_source_class (a : ℝ) {w χ : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (hwe : ∀ x, w (-x) = w x)
    (hχ : ContDiff ℝ 2 χ) (hχe : ∀ x, χ (-x) = χ x) :
    ContDiff ℝ 2 (oddProfileTest a (fun x => χ x * w x)) ∧
    HasCompactSupport (oddProfileTest a (fun x => χ x * w x)) ∧
    (∀ x, oddProfileTest a (fun y => χ y * w y) (-x) =
      -oddProfileTest a (fun y => χ y * w y) x) ∧
    (∫ x, oddProfileTest a (fun y => χ y * w y) x) = 0 ∧
    Function.support (oddProfileTest a (fun x => χ x * w x)) ⊆
      Function.support w ∩ Function.support χ := by
  have hodd : ∀ x, oddProfileTest a (fun y => χ y * w y) (-x) =
      -oddProfileTest a (fun y => χ y * w y) x := by
    intro x
    simp only [oddProfileTest, oddProfile_neg, hwe, hχe]
    ring
  refine ⟨(contDiff_oddProfile a).mul (hχ.mul hw), hwc.mul_left.mul_left,
    hodd, RHTower.CHMDPolar.integral_eq_zero_of_odd hodd, ?_⟩
  intro x hx
  simp only [Function.mem_support, oddProfileTest, mul_ne_zero_iff] at hx
  exact ⟨hx.2.2, hx.2.1⟩

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
