import GaloisForLFunctions.SignedWindowCriticality.TheWindowReadsTheOutsideChargesOfAThetaGauge
import GaloisForLFunctions.SignedWindowCriticality.ShiftedGroundStatesArePoleChargedOnEveryWindow
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm

/-!
# Gauge-Extension Invariance and the Two-Profile `L^{1/2}` Dual Obstruction

On a symmetric window `S = (−c, c)`, dropping the pole-charge variance `2V_s^S(u)` from
`fullZeroForm_phiDoob_mul_eq` yields the signed-certificate lower bound

    Ẑ(Φωu) ≥ J_{Φω}(u) + ∫ u² ω (markovDefect ω − 2σ_s(ω, S) Φ sinh(x/2))

for compact gauges `ω ∈ C²_c(ℝ)`, and

    Ẑ(Φωu) ≥ J_M(u) + 2τ_s^S ∫ u² M sinh(x/2)

for odd non-compact theta gauges `ω = translateSpan s α b` (`M = Φω`), including every shifted
ground state `ω_a`. This module establishes three structural laws governing all such certificates:

* **Exact pole-conductance identity** (`two_mul_chargeVariance_eq_setIntegral_sq_sub`). The dropped
  variance is the all-pairs jump form `2V(u) = ∫_S ∫_S m(x)m(y)(u(x) − u(y))² dy dx`, whose odd-sector
  weight `m_s = M sinh(x/2)` supplies the `4 sinh(x/2) sinh(y/2)` conductance completing `J_M` into
  the odd light cone.
* **Gauge-extension invariance and two-profile `L^{1/2}` dual bound**
  (`signedJumpEnergy_add_sinhDefect_eq_markovEnergy_sub`,
  `signedJumpEnergy_add_outsideSinh_thetaGauge_eq`,
  `not_exists_odd_sinhCharged_gauge_of_two_odd_tests`). Modifying a gauge outside `S` shifts
  potential between `J_{Φω}(u)` and the charged defect without changing their sum
  `markovEnergy(F) − 2σ_s(ω, S) ∫ u² m_s`. Tested on any two odd profiles `(F₁, F₂)` supported in a
  compact sub-interval of `S` (after excising an `ε`-ball at the origin, which has zero `H^{1/2}`
  Lévy capacity on functions vanishing at `0`), Cauchy–Schwarz bounds that sum above uniformly over
  all positive gauges by `markovEnergy(F₁) + markovEnergy(F₂) − 2(∫_S √(F₁² + F₂²)|sinh(x/2)|)²`.
* **Even-sector outside-cosh deficit** (`outsideCosh_thetaGauge_pos_of_tail_pos`,
  `evenThetaGauge_coshChargedDefect_neg`). Every nonnegative even theta gauge with positive mass
  outside `(−c, c)` (in particular every nonzero nonnegative linear combination of translates of `Φ`)
  carries strictly positive outside cosh charge, making its cosh-charged defect strictly negative
  wherever the gauge is positive.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.BelowLogFour

open _root_.RHTower _root_.RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SignedWindowCriticality

/-! ### 1. The dropped pole variance as an all-pairs jump conductance -/

/-- **All-pairs conductance representation of `2V(u)`.** For a continuous weight `m` and a continuous
profile `u` vanishing outside `S = (b, c)`, twice the charge variance equals the symmetric double
integral `∫_S ∫_S m(x) m(y) (u(x) − u(y))² dy dx`. -/
theorem two_mul_chargeVariance_eq_setIntegral_sq_sub {m u : ℝ → ℝ} {b c : ℝ}
    (hm : Continuous m) (hu : Continuous u) (hub : ∀ x, x ∉ Ioo b c → u x = 0) :
    2 * chargeVariance m (Ioo b c) u =
      ∫ x in Ioo b c, ∫ y in Ioo b c, m x * m y * (u x - u y) ^ 2 := by
  have e2 : (∫ x, u x ^ 2 * m x) = ∫ x in Ioo b c, u x ^ 2 * m x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hub x hx]).symm
  have e1 : (∫ x, u x * m x) = ∫ x in Ioo b c, u x * m x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hub x hx]).symm
  have hi0 : IntegrableOn m (Ioo b c) := integrableOn_Ioo_of_continuous hm
  have hi1 : IntegrableOn (fun y => u y * m y) (Ioo b c) :=
    integrableOn_Ioo_of_continuous (hu.mul hm)
  have hi2 : IntegrableOn (fun y => u y ^ 2 * m y) (Ioo b c) :=
    integrableOn_Ioo_of_continuous ((hu.pow 2).mul hm)
  have hinner : ∀ x : ℝ,
      (∫ y in Ioo b c, m x * m y * (u x - u y) ^ 2) =
        (u x ^ 2 * m x) * (∫ y in Ioo b c, m y) -
          2 * (u x * m x) * (∫ y in Ioo b c, u y * m y) +
          m x * (∫ y in Ioo b c, u y ^ 2 * m y) := fun x => by
    have hpt : (fun y => m x * m y * (u x - u y) ^ 2) =
        fun y => ((u x ^ 2 * m x) * m y - (2 * (u x * m x)) * (u y * m y)) +
          m x * (u y ^ 2 * m y) := by funext y; ring
    rw [hpt, integral_add ((hi0.const_mul _).sub (hi1.const_mul _)) (hi2.const_mul _),
      integral_sub (hi0.const_mul _) (hi1.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo fun x _ => hinner x,
    integral_add ((hi2.mul_const _).sub ((hi1.const_mul 2).mul_const _)) (hi0.mul_const _),
    integral_sub (hi2.mul_const _) ((hi1.const_mul 2).mul_const _),
    integral_mul_const, integral_mul_const, integral_const_mul, integral_mul_const]
  unfold chargeVariance
  rw [e1, e2]
  ring

/-! ### 2. Exact gauge-extension invariance in compact and non-compact gauges -/

/-- **Local gauge-sum identity for `C²_c` gauges.** The sum of the signed Dirichlet form `J_{Φω}(u)`
and the sinh-charged defect potential equals `markovEnergy(Φωu) − 2σ_s(ω, S) ∫ u² Φω sinh(x/2)`,
which depends only on the restriction of `ω` to `S` whenever `u` vanishes off `S`. -/
theorem signedJumpEnergy_add_sinhDefect_eq_markovEnergy_sub {ω u : ℝ → ℝ} (S : Set ℝ)
    (hω : ContDiff ℝ 2 ω) (hωc : HasCompactSupport ω)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    signedJumpEnergy (fun y => riemannKernelReal y * ω y) u +
        (∫ x, u x ^ 2 * ω x *
          (markovDefect ω x - 2 * sinhCharge ω S * (riemannKernelReal x * Real.sinh (x / 2)))) =
      markovEnergy (fun x => (phiDoobTest (fun y => ω y * u y) x : ℂ)) -
        2 * sinhCharge ω S * ∫ x, u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)) := by
  have hD := continuous_markovDefect hω hωc
  have hsupp2 : HasCompactSupport fun x => u x ^ 2 :=
    huc.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
  have hiD : Integrable fun x => u x ^ 2 * ω x * markovDefect ω x :=
    (((hu.continuous.pow 2).mul hω.continuous).mul hD).integrable_of_hasCompactSupport
      (hsupp2.mul_right.mul_right)
  have his : Integrable fun x => u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)) :=
    ((hu.continuous.pow 2).mul (continuous_mul_sinh hω.continuous)).integrable_of_hasCompactSupport
      hsupp2.mul_right
  have hsplit :
      (∫ x, u x ^ 2 * ω x *
          (markovDefect ω x - 2 * sinhCharge ω S * (riemannKernelReal x * Real.sinh (x / 2)))) =
        (∫ x, u x ^ 2 * ω x * markovDefect ω x) -
          2 * sinhCharge ω S * ∫ x, u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)) := by
    have hpt : (fun x => u x ^ 2 * ω x *
        (markovDefect ω x - 2 * sinhCharge ω S * (riemannKernelReal x * Real.sinh (x / 2)))) =
        fun x => u x ^ 2 * ω x * markovDefect ω x -
          (2 * sinhCharge ω S) * (u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2))) := by
      funext x; ring
    rw [hpt, integral_sub hiD (his.const_mul _), integral_const_mul]
  rw [markovEnergy_phiDoob_mul_eq_signedJump_add_defect hω hωc hu huc, hsplit]
  ring

/-- Every odd theta gauge has vanishing total cosh coefficient `A = 0`. -/
theorem translateCoshCoefficient_eq_zero_of_odd {ι : Type*} (s : Finset ι) (α b : ι → ℝ)
    (hModd : ∀ x, riemannKernelReal (-x) * translateSpan s α b (-x) =
      -(riemannKernelReal x * translateSpan s α b x)) :
    translateCoshCoefficient s α b = 0 := by
  have hint := integral_thetaGauge_mul_cosh s α b
  have hz : (∫ x, riemannKernelReal x * translateSpan s α b x * Real.cosh (x / 2)) = 0 :=
    integral_eq_zero_of_odd fun x => by
      rw [hModd x, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]; ring
  linarith

/-- **Local gauge-sum identity for non-compact odd theta gauges.** Including the outside sinh-charge
slack `2τ_s^S ∫ u² M sinh(x/2)` reproduces the exact same local right-hand side
`markovEnergy(Φωu) − 2σ_s(ω, S) ∫ u² M sinh(x/2)` as a compactly supported gauge. -/
theorem signedJumpEnergy_add_outsideSinh_thetaGauge_eq {ι : Type*} (s : Finset ι) (α b : ι → ℝ)
    (S : Set ℝ) (hA : translateCoshCoefficient s α b = 0)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u +
        2 * (translateSinhCoefficient s α b / 2 - sinhCharge (translateSpan s α b) S) *
          (∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x * Real.sinh (x / 2))) =
      markovEnergy (fun x => (phiDoobTest (fun y => translateSpan s α b y * u y) x : ℂ)) -
        2 * sinhCharge (translateSpan s α b) S *
          ∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x * Real.sinh (x / 2)) := by
  set ω := translateSpan s α b
  have hω := (contDiff_translateSpan s α b).continuous
  have hsupp2 : HasCompactSupport fun x => u x ^ 2 :=
    huc.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
  have his : Integrable fun x => u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)) :=
    ((hu.continuous.pow 2).mul (continuous_mul_sinh hω)).integrable_of_hasCompactSupport
      hsupp2.mul_right
  have hsrc : (∫ x, u x ^ 2 * (riemannKernelReal x * ω x) * translateSource s α b x) =
      translateSinhCoefficient s α b *
        ∫ x, u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [translateSource, hA]
    ring
  rw [markovEnergy_thetaGauge s α b hu huc, hsrc]
  ring

/-- **Local gauge-sum identity for shifted ground states.** The lower-bound form of
`fullZeroForm_shiftedGroundState_ge` equals `markovEnergy(m_a u) − 2σ_s(ω_a, (−c, c)) ∫ u² m_a sinh`. -/
theorem shiftedGroundState_windowLower_eq_markovEnergy_sub {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u +
        8 * outsideCharge a c *
          (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) =
      markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) -
        2 * sinhCharge (shiftedGroundState a) (Ioo (-c) c) *
          ∫ x, u x ^ 2 * (riemannKernelReal x * shiftedGroundState a x * Real.sinh (x / 2)) := by
  have hM := markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hu huc heven
  have hcoord : ∀ x, riemannKernelReal x * shiftedGroundState a x = shiftDifference a x :=
    riemannKernelReal_mul_shiftedGroundState a
  have hcont_u : Continuous fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) :=
    ((hu.continuous.pow 2).mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hint_u : Integrable fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) :=
    hcont_u.integrable_of_hasCompactSupport
      ((huc.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)).mul_right.mul_right)
  have heven_u : ∀ x, u (-x) ^ 2 * shiftDifference a (-x) * Real.sinh (-x / 2) =
      u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := fun x => by
    rw [heven, shiftDifference_neg, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]; ring
  have hfull : (∫ x, u x ^ 2 * (riemannKernelReal x * shiftedGroundState a x * Real.sinh (x / 2))) =
      2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
    rw [← integral_eq_two_mul_Ioi_of_even' hint_u heven_u]
    exact integral_congr_ae (Eventually.of_forall fun x => by rw [hcoord]; ring)
  have hσ : sinhCharge (shiftedGroundState a) (Ioo (-c) c) =
      2 * ∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2) := by
    unfold sinhCharge
    have hce : ∀ x, riemannKernelReal x * shiftedGroundState a x * Real.sinh (x / 2) =
        shiftDifference a x * Real.sinh (x / 2) := fun x => by rw [hcoord]
    simp_rw [hce]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_add_adjacent_intervals
        ((continuous_shiftDifference a).mul
          (Real.continuous_sinh.comp (continuous_id.div_const 2)) |>.intervalIntegrable (-c) 0)
        ((continuous_shiftDifference a).mul
          (Real.continuous_sinh.comp (continuous_id.div_const 2)) |>.intervalIntegrable 0 c)]
    have hleft : (∫ x in (-c)..0, shiftDifference a x * Real.sinh (x / 2)) =
        ∫ x in (0 : ℝ)..c, shiftDifference a x * Real.sinh (x / 2) := by
      have hcomp := intervalIntegral.integral_comp_neg
        (fun x => shiftDifference a x * Real.sinh (x / 2)) (a := 0) (b := c)
      rw [neg_zero] at hcomp
      rw [← hcomp]
      exact intervalIntegral.integral_congr fun x _ => by
        simp only
        rw [shiftDifference_neg, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]; ring
    rw [hleft, intervalIntegral.integral_of_le hc, integral_Ioc_eq_integral_Ioo]
    ring
  rw [hM, hfull, hσ]
  unfold outsideCharge
  ring

/-! ### 3. Smooth gauge division away from the origin and two-profile Cauchy–Schwarz -/

/-- Smooth division `F / M` on `(−c, −ε/2) ∪ (ε/2, c)` extended by `0` outside, for `F` vanishing on
`[−ε, ε]` and outside `[−c′, c′]` (`0 < ε < c′ < c`). -/
def windowGaugeQuotient (ε c' c : ℝ) (M F : ℝ → ℝ) (x : ℝ) : ℝ :=
  if |x| ≤ ε / 2 ∨ (c' + c) / 2 ≤ |x| then 0 else F x / M x

lemma windowGaugeQuotient_mul {ε c' c : ℝ} (hε : 0 < ε) (hc : c' < c)
    {M F : ℝ → ℝ} (hM : ∀ x ∈ Ioo (-c) c, x ≠ 0 → M x ≠ 0)
    (hF0 : ∀ x, |x| ≤ ε → F x = 0) (hFc' : ∀ x, c' < |x| → F x = 0) (x : ℝ) :
    M x * windowGaugeQuotient ε c' c M F x = F x := by
  unfold windowGaugeQuotient
  split_ifs with h
  · rcases h with h1 | h2
    · rw [mul_zero, hF0 x (by linarith)]
    · rw [mul_zero, hFc' x (by linarith)]
  · push Not at h
    have hxI : x ∈ Ioo (-c) c := abs_lt.mp (by linarith [h.2])
    have hx0 : x ≠ 0 := fun hx => by simp [hx] at h; linarith [h.1]
    exact mul_div_cancel₀ (F x) (hM x hxI hx0)

lemma windowGaugeQuotient_even {ε c' c : ℝ} {M F : ℝ → ℝ}
    (hModd : ∀ x ∈ Ioo (-c) c, M (-x) = -M x) (hFodd : ∀ x, F (-x) = -F x) (x : ℝ) :
    windowGaugeQuotient ε c' c M F (-x) = windowGaugeQuotient ε c' c M F x := by
  unfold windowGaugeQuotient
  rw [abs_neg]
  split_ifs with h
  · rfl
  · push Not at h
    have hxI : x ∈ Ioo (-c) c := abs_lt.mp (by linarith [h.2])
    rw [hFodd x, hModd x hxI, neg_div_neg_eq]

lemma windowGaugeQuotient_eq_zero_off {ε c' c : ℝ} (hc : c' < c) (M F : ℝ → ℝ)
    {x : ℝ} (hx : x ∉ Ioo (-c) c) : windowGaugeQuotient ε c' c M F x = 0 := by
  unfold windowGaugeQuotient
  have habs : c ≤ |x| := not_lt.mp fun hlt => hx (abs_lt.mp hlt)
  exact if_pos (Or.inr (by linarith))

lemma hasCompactSupport_windowGaugeQuotient {ε c' c : ℝ} (hc : c' < c) (M F : ℝ → ℝ) :
    HasCompactSupport (windowGaugeQuotient ε c' c M F) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c)) fun x hx => ?_
  exact windowGaugeQuotient_eq_zero_off hc M F fun h => hx (Ioo_subset_Icc_self h)

lemma contDiff_windowGaugeQuotient {ε c' c : ℝ} (hε : 0 < ε) (hc : c' < c)
    {M F : ℝ → ℝ} (hM : ContDiff ℝ 2 M) (hMnz : ∀ x ∈ Ioo (-c) c, x ≠ 0 → M x ≠ 0)
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ x, |x| ≤ ε → F x = 0) (hFc' : ∀ x, c' < |x| → F x = 0) :
    ContDiff ℝ 2 (windowGaugeQuotient ε c' c M F) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  by_cases h1 : |x₀| < ε
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have hmem : {x : ℝ | |x| < ε} ∈ 𝓝 x₀ :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds h1
    filter_upwards [hmem] with x hx
    unfold windowGaugeQuotient
    split_ifs with hcnd
    · rfl
    · simp [hF0 x (le_of_lt hx)]
  · by_cases h2 : c' < |x₀|
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      have hmem : {x : ℝ | c' < |x|} ∈ 𝓝 x₀ :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds h2
      filter_upwards [hmem] with x hx
      unfold windowGaugeQuotient
      split_ifs with hcnd
      · rfl
      · simp [hFc' x hx]
    · push Not at h1 h2
      have hx₀_lo : ε / 2 < |x₀| := by linarith
      have hx₀_hi : |x₀| < (c' + c) / 2 := by linarith
      have hx₀I : x₀ ∈ Ioo (-c) c := abs_lt.mp (by linarith)
      have hx₀0 : x₀ ≠ 0 := fun h0 => by simp [h0] at hx₀_lo; linarith
      refine (hF.contDiffAt.div hM.contDiffAt (hMnz x₀ hx₀I hx₀0)).congr_of_eventuallyEq ?_
      have hmem : {x : ℝ | ε / 2 < |x| ∧ |x| < (c' + c) / 2} ∈ 𝓝 x₀ :=
        ((isOpen_lt continuous_const continuous_abs).inter
          (isOpen_lt continuous_abs continuous_const)).mem_nhds ⟨hx₀_lo, hx₀_hi⟩
      filter_upwards [hmem] with x hx
      unfold windowGaugeQuotient
      exact if_neg (by push Not; exact ⟨hx.1, hx.2⟩)

/-- **Two-profile `L^{1/2}` Cauchy–Schwarz bound on profiles with an origin hole.** -/
theorem two_profile_sinhQuotient_ge_halfNorm_sq {ε c' c : ℝ} (hε : 0 < ε) (hc' : ε < c')
    (hc : c' < c) {ω F₁ F₂ : ℝ → ℝ} (hω : ContDiff ℝ 2 ω)
    (hωpos : ∀ x ∈ Ioo (-c) c, x ≠ 0 → 0 < ω x * Real.sinh (x / 2))
    (hF₁ : ContDiff ℝ 2 F₁) (hF₁0 : ∀ x, |x| ≤ ε → F₁ x = 0) (hF₁c : ∀ x, c' < |x| → F₁ x = 0)
    (hF₂ : ContDiff ℝ 2 F₂) (hF₂0 : ∀ x, |x| ≤ ε → F₂ x = 0) (hF₂c : ∀ x, c' < |x| → F₂ x = 0) :
    let M := fun x => riemannKernelReal x * ω x
    let u₁ := windowGaugeQuotient ε c' c M F₁
    let u₂ := windowGaugeQuotient ε c' c M F₂
    (∫ x in Ioo (-c) c, Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|) ^ 2 ≤
      sinhCharge ω (Ioo (-c) c) *
        ((∫ x, u₁ x ^ 2 * (M x * Real.sinh (x / 2))) +
          ∫ x, u₂ x ^ 2 * (M x * Real.sinh (x / 2))) := by
  intro M u₁ u₂
  have hMdiff : ContDiff ℝ 2 M := contDiff_riemannKernelReal.mul hω
  have hMnz : ∀ x ∈ Ioo (-c) c, x ≠ 0 → M x ≠ 0 := fun x hx hx0 => by
    have hpos := hωpos x hx hx0
    have hΦ := riemannKernelReal_pos x
    intro hMz
    have hωz : ω x = 0 := by
      rcases mul_eq_zero.mp hMz with h1 | h2
      · linarith
      · exact h2
    rw [hωz, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  have hu₁c := (contDiff_windowGaugeQuotient hε hc hMdiff hMnz hF₁ hF₁0 hF₁c).continuous
  have hu₂c := (contDiff_windowGaugeQuotient hε hc hMdiff hMnz hF₂ hF₂0 hF₂c).continuous
  have hu₁_supp := hasCompactSupport_windowGaugeQuotient (ε := ε) hc M F₁
  have hu₂_supp := hasCompactSupport_windowGaugeQuotient (ε := ε) hc M F₂
  set m : ℝ → ℝ := fun x => M x * Real.sinh (x / 2)
  have hm_cont : Continuous m := continuous_mul_sinh hω.continuous
  have hm_nn : ∀ x ∈ Ioo (-c) c, 0 ≤ m x := fun x hx => by
    by_cases hx0 : x = 0
    · simp [m, hx0]
    · exact mul_nonneg (riemannKernelReal_pos x).le (hωpos x hx hx0).le
  set a : ℝ → ℝ := fun x => Real.sqrt (m x)
  set b : ℝ → ℝ := fun x => Real.sqrt (u₁ x ^ 2 + u₂ x ^ 2) * Real.sqrt (m x)
  have ha_cont : Continuous a := Real.continuous_sqrt.comp hm_cont
  have hb_cont : Continuous b :=
    (Real.continuous_sqrt.comp ((hu₁c.pow 2).add (hu₂c.pow 2))).mul ha_cont
  have hpt : ∀ x ∈ Ioo (-c) c,
      Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)| = a x * b x := fun x hx => by
    have hm0 := hm_nn x hx
    have h1 := windowGaugeQuotient_mul hε hc hMnz hF₁0 hF₁c x
    have h2 := windowGaugeQuotient_mul hε hc hMnz hF₂0 hF₂c x
    change M x * u₁ x = F₁ x at h1
    change M x * u₂ x = F₂ x at h2
    have hsqM : F₁ x ^ 2 + F₂ x ^ 2 = M x ^ 2 * (u₁ x ^ 2 + u₂ x ^ 2) := by
      rw [← h1, ← h2]; ring
    have habsM : |M x| * |Real.sinh (x / 2)| = m x := by
      rw [← abs_mul, abs_of_nonneg hm0]
    calc Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|
        = Real.sqrt (M x ^ 2 * (u₁ x ^ 2 + u₂ x ^ 2)) * |Real.sinh (x / 2)| := by rw [hsqM]
      _ = |M x| * Real.sqrt (u₁ x ^ 2 + u₂ x ^ 2) * |Real.sinh (x / 2)| := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      _ = Real.sqrt (u₁ x ^ 2 + u₂ x ^ 2) * m x := by rw [← habsM]; ring
      _ = a x * b x := by
          simp only [a, b]
          have hmsq : Real.sqrt (m x) * Real.sqrt (m x) = m x := Real.mul_self_sqrt hm0
          linear_combination -Real.sqrt (u₁ x ^ 2 + u₂ x ^ 2) * hmsq
  have hint_eq : (∫ x in Ioo (-c) c, Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|) =
      ∫ x in Ioo (-c) c, a x * b x := setIntegral_congr_fun measurableSet_Ioo hpt
  -- Quadratic discriminant Cauchy–Schwarz on `Ioo (-c) c`
  have ha2 : IntegrableOn (fun x => a x ^ 2) (Ioo (-c) c) :=
    integrableOn_Ioo_of_continuous (ha_cont.pow 2)
  have hb2 : IntegrableOn (fun x => b x ^ 2) (Ioo (-c) c) :=
    integrableOn_Ioo_of_continuous (hb_cont.pow 2)
  have hab : IntegrableOn (fun x => a x * b x) (Ioo (-c) c) :=
    integrableOn_Ioo_of_continuous (ha_cont.mul hb_cont)
  have hq : ∀ t : ℝ, 0 ≤ (∫ x in Ioo (-c) c, a x ^ 2) * (t * t) +
      (-2 * ∫ x in Ioo (-c) c, a x * b x) * t + ∫ x in Ioo (-c) c, b x ^ 2 := fun t => by
    have h0 : 0 ≤ ∫ x in Ioo (-c) c, (t * a x - b x) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioo fun _ _ => sq_nonneg _
    have hexp : (∫ x in Ioo (-c) c, (t * a x - b x) ^ 2) =
        (∫ x in Ioo (-c) c, a x ^ 2) * (t * t) +
          (-2 * ∫ x in Ioo (-c) c, a x * b x) * t + ∫ x in Ioo (-c) c, b x ^ 2 := by
      have hp : (fun x => (t * a x - b x) ^ 2) =
          fun x => ((t * t) * a x ^ 2 - (2 * t) * (a x * b x)) + b x ^ 2 := by funext x; ring
      rw [hp, integral_add ((ha2.const_mul _).sub (hab.const_mul _)) hb2,
        integral_sub (ha2.const_mul _) (hab.const_mul _), integral_const_mul, integral_const_mul]
      ring
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have ha2_eq : (∫ x in Ioo (-c) c, a x ^ 2) = sinhCharge ω (Ioo (-c) c) := by
    unfold sinhCharge
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => Real.sq_sqrt (hm_nn x hx)
  have hb2_eq : (∫ x in Ioo (-c) c, b x ^ 2) =
      (∫ x, u₁ x ^ 2 * m x) + ∫ x, u₂ x ^ 2 * m x := by
    have hptb : ∀ x ∈ Ioo (-c) c, b x ^ 2 = u₁ x ^ 2 * m x + u₂ x ^ 2 * m x := fun x hx => by
      simp only [b, mul_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
        Real.sq_sqrt (hm_nn x hx)]
      ring
    have hi1 : IntegrableOn (fun x => u₁ x ^ 2 * m x) (Ioo (-c) c) :=
      integrableOn_Ioo_of_continuous ((hu₁c.pow 2).mul hm_cont)
    have hi2 : IntegrableOn (fun x => u₂ x ^ 2 * m x) (Ioo (-c) c) :=
      integrableOn_Ioo_of_continuous ((hu₂c.pow 2).mul hm_cont)
    have e1 : (∫ x in Ioo (-c) c, u₁ x ^ 2 * m x) = ∫ x, u₁ x ^ 2 * m x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [u₁, windowGaugeQuotient_eq_zero_off hc M F₁ hx]
    have e2 : (∫ x in Ioo (-c) c, u₂ x ^ 2 * m x) = ∫ x, u₂ x ^ 2 * m x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [u₂, windowGaugeQuotient_eq_zero_off hc M F₂ hx]
    rw [setIntegral_congr_fun measurableSet_Ioo hptb, integral_add hi1 hi2, e1, e2]
  rw [hint_eq]
  rw [ha2_eq, hb2_eq] at hd
  nlinarith

/-! ### 4. Zero `H^{1/2}` capacity of the origin on odd `C²_c` profiles -/

/-- The origin-excised perturbation `d_ε(x) = −smoothPlateau 1 (x/ε) · F(x)`. -/
def originExcisionPerturb (ε : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(smoothPlateau 1 (x / ε) * F x)

/-- The origin-excised profile `F_ε(x) = F(x) + d_ε(x) = (1 − smoothPlateau 1 (x/ε)) F(x)`. -/
def originExcisedProfile (ε : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  F x + originExcisionPerturb ε F x

lemma originExcisedProfile_odd (ε : ℝ) {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) (x : ℝ) :
    originExcisedProfile ε F (-x) = -originExcisedProfile ε F x := by
  unfold originExcisedProfile originExcisionPerturb
  rw [show -x / ε = -(x / ε) by ring, smoothPlateau_neg, hodd x]
  ring

lemma originExcisedProfile_eq_zero_near {ε : ℝ} (hε : 0 < ε) (F : ℝ → ℝ) {x : ℝ} (hx : |x| ≤ ε) :
    originExcisedProfile ε F x = 0 := by
  unfold originExcisedProfile originExcisionPerturb
  have hdiv : |x / ε| ≤ 1 := by
    rw [abs_div, abs_of_pos hε, div_le_one hε]
    exact hx
  rw [smoothPlateau_eq_one hdiv]
  ring

lemma originExcisionPerturb_eq_zero_far {ε : ℝ} (hε : 0 < ε) (F : ℝ → ℝ) {x : ℝ}
    (hx : 2 * ε ≤ |x|) : originExcisionPerturb ε F x = 0 := by
  unfold originExcisionPerturb
  have hdiv : 1 + 1 ≤ |x / ε| := by
    rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]
    linarith
  rw [smoothPlateau_eq_zero hdiv, zero_mul, neg_zero]

lemma originExcisedProfile_eq_zero_far (ε : ℝ) {c' : ℝ} {F : ℝ → ℝ}
    (hFc : ∀ x, c' < |x| → F x = 0) {x : ℝ} (hx : c' < |x|) :
    originExcisedProfile ε F x = 0 := by
  unfold originExcisedProfile originExcisionPerturb
  rw [hFc x hx, mul_zero, neg_zero, add_zero]

lemma contDiff_originExcisionPerturb (ε : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (originExcisionPerturb ε F) := by
  unfold originExcisionPerturb
  exact (((contDiff_smoothPlateau 1).comp (contDiff_id.div_const ε)).mul hF).neg

lemma hasCompactSupport_originExcisionPerturb (ε : ℝ) {F : ℝ → ℝ} (hFc : HasCompactSupport F) :
    HasCompactSupport (originExcisionPerturb ε F) := by
  unfold originExcisionPerturb
  exact (hFc.mul_left).neg

/-- Uniform global Lipschitz constant `(4Λ + 1)K` for `d_ε` across all `ε > 0` when `F(0) = 0` and
`F` is `K`-Lipschitz. -/
lemma lipschitz_originExcisionPerturb {ε K Λ : ℝ} (hε : 0 < ε) (hK0 : 0 ≤ K) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ L x y : ℝ, |smoothPlateau L y - smoothPlateau L x| ≤ Λ * |y - x|)
    {F : ℝ → ℝ} (hF0 : F 0 = 0) (hFLip : ∀ x y, |F y - F x| ≤ K * |y - x|) :
    ∀ u v : ℝ, |originExcisionPerturb ε F u - originExcisionPerturb ε F v| ≤
      ((2 * Λ + 1) * K) * |u - v| := by
  have hFx : ∀ x, |F x| ≤ K * |x| := fun x => by
    have := hFLip 0 x
    rwa [hF0, sub_zero, sub_zero] at this
  have hin : ∀ u v, |u| ≤ 2 * ε → |v| ≤ 2 * ε →
      |originExcisionPerturb ε F u - originExcisionPerturb ε F v| ≤
        ((2 * Λ + 1) * K) * |u - v| := fun u v hu hv => by
    unfold originExcisionPerturb
    rw [show -(smoothPlateau 1 (u / ε) * F u) - -(smoothPlateau 1 (v / ε) * F v) =
      -((smoothPlateau 1 (u / ε) - smoothPlateau 1 (v / ε)) * F u +
        smoothPlateau 1 (v / ε) * (F u - F v)) by ring, abs_neg]
    have hp1 : |smoothPlateau 1 (u / ε) - smoothPlateau 1 (v / ε)| ≤ (Λ / ε) * |u - v| := by
      have h := hΛ 1 (v / ε) (u / ε)
      rwa [show u / ε - v / ε = (u - v) / ε by ring, abs_div, abs_of_pos hε,
        mul_div_assoc', mul_div_right_comm] at h
    have hp2 : |(smoothPlateau 1 (u / ε) - smoothPlateau 1 (v / ε)) * F u| ≤
        2 * Λ * K * |u - v| := by
      rw [abs_mul]
      calc |smoothPlateau 1 (u / ε) - smoothPlateau 1 (v / ε)| * |F u|
          ≤ ((Λ / ε) * |u - v|) * (K * (2 * ε)) :=
            mul_le_mul hp1 ((hFx u).trans (mul_le_mul_of_nonneg_left hu hK0))
              (abs_nonneg _) (by positivity)
        _ = 2 * Λ * K * |u - v| := by field_simp [hε.ne']; ring
    have hp3 : |smoothPlateau 1 (v / ε) * (F u - F v)| ≤ K * |u - v| := by
      rw [abs_mul, abs_of_nonneg (smoothPlateau_nonneg 1 _)]
      have hFu := hFLip v u
      exact (mul_le_mul (smoothPlateau_le_one 1 _) hFu (abs_nonneg _) zero_le_one).trans
        (by linarith)
    exact (abs_add_le _ _).trans (by linarith)
  -- Clamp outside `[-2ε, 2ε]` where `d_ε = 0`
  intro u v
  set cl : ℝ → ℝ := fun z => max (-(2 * ε)) (min (2 * ε) z)
  have hcl_eq : ∀ z, originExcisionPerturb ε F z = originExcisionPerturb ε F (cl z) := fun z => by
    simp only [cl]
    rcases lt_or_ge z (-(2 * ε)) with hlt | hge
    · rw [min_eq_right (by linarith), max_eq_left hlt.le,
        originExcisionPerturb_eq_zero_far hε F (by rw [abs_of_neg (by linarith)]; linarith),
        originExcisionPerturb_eq_zero_far hε F (by rw [abs_neg, abs_of_pos (by positivity)])]
    · rcases lt_or_ge (2 * ε) z with hgt | hle
      · rw [min_eq_left hgt.le, max_eq_right (by linarith),
          originExcisionPerturb_eq_zero_far hε F (by rw [abs_of_pos (by linarith)]; linarith),
          originExcisionPerturb_eq_zero_far hε F (by rw [abs_of_pos (by positivity)])]
      · rw [min_eq_right hle, max_eq_right hge]
  have hcl_abs : ∀ z, |cl z| ≤ 2 * ε := fun z => abs_le.mpr
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hcl_lip : |cl u - cl v| ≤ |u - v| := by
    have hl : LipschitzWith 1 cl := (LipschitzWith.id.const_min (2 * ε)).const_max (-(2 * ε))
    have hd := hl.dist_le_mul u v
    simpa [Real.dist_eq] using hd
  rw [hcl_eq u, hcl_eq v]
  exact (hin (cl u) (cl v) (hcl_abs u) (hcl_abs v)).trans
    (mul_le_mul_of_nonneg_left hcl_lip (by positivity))

lemma markovEnergy_eq_weilQuad_add_odd_sq_of_odd {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) :
    markovEnergy (fun x => (F x : ℂ)) =
      SpacingScaleHarmonicAnalysis.weilQuad F + 2 * oddPoleMoment F ^ 2 := by
  have hZ : fullZeroForm F = SpacingScaleHarmonicAnalysis.weilQuad F :=
    ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc
  have he : evenPoleMoment F = 0 :=
    integral_eq_zero_of_odd fun x => by
      rw [hodd x, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]; ring
  unfold fullZeroForm at hZ
  rw [he] at hZ
  linarith

/-- **Zero `H^{1/2}` capacity of the origin on odd `C²_c` profiles.** As `ε → 0⁺`,
`markovEnergy(F_ε) → markovEnergy(F)`. -/
theorem tendsto_markovEnergy_originExcisedProfile {c' : ℝ} (hc' : 0 < c') {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, c' < |x| → F x = 0) :
    Tendsto (fun ε : ℝ => markovEnergy (fun x => (originExcisedProfile ε F x : ℂ)))
      (𝓝[>] 0) (𝓝 (markovEnergy (fun x => (F x : ℂ)))) := by
  obtain ⟨K, hK0, hFLip⟩ := exists_lipschitz_bound_of_compactSupport (hF.of_le (by norm_num)) hFc
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  have hF0 : F 0 = 0 := by have := hodd 0; rw [neg_zero] at this; linarith
  have hFx : ∀ x, |F x| ≤ K * |x| := fun x => by
    have := hFLip 0 x; rwa [hF0, sub_zero, sub_zero] at this
  set R := max c' 1
  have hR_pos : 0 < R := lt_of_lt_of_le hc' (le_max_left _ _)
  have hFR : SpacingScaleHarmonicAnalysis.SupportedIn R F := fun x hx =>
    hsupp x (lt_of_le_of_lt (le_max_left _ _) hx)
  -- Show both `weilQuad` and `oddPoleMoment` converge as `ε → 0⁺`
  have hd_bounds : ∀ ε : ℝ, 0 < ε → ε ≤ min (1 / 2) (R / 2) →
      (∫ u, |originExcisionPerturb ε F u|) ≤ 8 * K * ε ^ 2 ∧
        (∫ u, originExcisionPerturb ε F u ^ 2) ≤ 16 * K ^ 2 * ε ^ 3 := fun ε hε hεm => by
    have hd_abs : ∀ u, |originExcisionPerturb ε F u| ≤
        (Icc (-(2 * ε)) (2 * ε)).indicator (fun _ => 2 * K * ε) u := fun u => by
      by_cases hu : u ∈ Icc (-(2 * ε)) (2 * ε)
      · rw [indicator_of_mem hu]
        unfold originExcisionPerturb
        rw [abs_neg, abs_mul, abs_of_nonneg (smoothPlateau_nonneg 1 _)]
        calc smoothPlateau 1 (u / ε) * |F u|
            ≤ 1 * (K * (2 * ε)) := mul_le_mul (smoothPlateau_le_one 1 _)
              ((hFx u).trans (mul_le_mul_of_nonneg_left (abs_le.mpr hu) hK0))
              (abs_nonneg _) zero_le_one
          _ = 2 * K * ε := by ring
      · rw [indicator_of_notMem hu, originExcisionPerturb_eq_zero_far hε F
          (not_lt.mp fun hlt => hu (abs_le.mp hlt.le)), abs_zero]
    have hd_sq : ∀ u, originExcisionPerturb ε F u ^ 2 ≤
        (Icc (-(2 * ε)) (2 * ε)).indicator (fun _ => 4 * K ^ 2 * ε ^ 2) u := fun u => by
      by_cases hu : u ∈ Icc (-(2 * ε)) (2 * ε)
      · have hb := hd_abs u
        rw [indicator_of_mem hu] at hb ⊢
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
        rw [sq_abs] at hsq
        linarith [show (2 * K * ε) ^ 2 = 4 * K ^ 2 * ε ^ 2 by ring]
      · rw [indicator_of_notMem hu, originExcisionPerturb_eq_zero_far hε F
          (not_lt.mp fun hlt => hu (abs_le.mp hlt.le)), sq, zero_mul]
    have hd_cont := (contDiff_originExcisionPerturb ε hF).continuous
    have hd_cs := hasCompactSupport_originExcisionPerturb ε hFc
    have hi1 := integral_mono (hd_cont.integrable_of_hasCompactSupport hd_cs).abs
      ((integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
        measurableSet_Icc) hd_abs
    have hi2 := integral_mono ((hd_cont.pow 2).integrable_of_hasCompactSupport hd_cs.sq)
      ((integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
        measurableSet_Icc) hd_sq
    rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc,
      max_eq_left (by linarith)] at hi1 hi2
    exact ⟨by nlinarith [hi1], by nlinarith [hi2]⟩
  -- `oddPoleMoment (F_ε) → oddPoleMoment F`
  have hodd_tendsto : Tendsto (fun ε : ℝ => oddPoleMoment (originExcisedProfile ε F))
      (𝓝[>] 0) (𝓝 (oddPoleMoment F)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hpos_m : 0 < min (1 / 2) (R / 2) := lt_min (by norm_num) (by positivity)
    have hch : 0 < Real.cosh (R / 2) := Real.cosh_pos _
    set ε₀ := min (min (1 / 2) (R / 2)) (Real.sqrt (δ / (16 * Real.cosh (R / 2) * (K + 1))))
    have hε₀ : 0 < ε₀ := lt_min hpos_m (Real.sqrt_pos.mpr (by positivity))
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεm : ε ≤ min (1 / 2) (R / 2) := hε.2.le.trans (min_le_left _ _)
    have hεsq : ε ^ 2 < δ / (16 * Real.cosh (R / 2) * (K + 1)) := by
      have hlt : ε < Real.sqrt (δ / (16 * Real.cosh (R / 2) * (K + 1))) :=
        lt_of_lt_of_le hε.2 (min_le_right _ _)
      have hsq := pow_lt_pow_left₀ hlt hε0.le two_ne_zero
      rwa [Real.sq_sqrt (by positivity)] at hsq
    have hdR : SpacingScaleHarmonicAnalysis.SupportedIn R (originExcisionPerturb ε F) :=
      fun u hu => originExcisionPerturb_eq_zero_far hε0 F
        (le_trans (by linarith [min_le_right (1 / 2 : ℝ) (R / 2)]) hu.le)
    have hadd := oddPoleMoment_add hF.continuous hFc
      (contDiff_originExcisionPerturb ε hF).continuous (hasCompactSupport_originExcisionPerturb ε hFc)
    have hm_le := SpacingScaleHarmonicAnalysis.abs_moment_le
      (contDiff_originExcisionPerturb ε hF).continuous (hasCompactSupport_originExcisionPerturb ε hFc)
      hdR (Real.continuous_sinh.comp (continuous_id.div_const 2))
      fun u hu => SpacingScaleHarmonicAnalysis.abs_sinh_half_le hu
    rw [Real.dist_eq, show originExcisedProfile ε F = fun x => F x + originExcisionPerturb ε F x
      from rfl, hadd, add_sub_cancel_left]
    have hb1 := (hd_bounds ε hε0 hεm).1
    have hstep : Real.cosh (R / 2) * (8 * K * ε ^ 2) < δ := by
      have hden : 0 < 16 * Real.cosh (R / 2) * (K + 1) := by positivity
      have hmul := (lt_div_iff₀ hden).mp hεsq
      nlinarith [hch, hK0, sq_nonneg ε]
    exact lt_of_le_of_lt (hm_le.trans (mul_le_mul_of_nonneg_left hb1 hch.le)) hstep
  -- `weilQuad (F_ε) → weilQuad F` via `SSHA.weilQuad_add_le` applied in both directions
  have hQ_tendsto : Tendsto (fun ε : ℝ =>
      SpacingScaleHarmonicAnalysis.weilQuad (originExcisedProfile ε F))
      (𝓝[>] 0) (𝓝 (SpacingScaleHarmonicAnalysis.weilQuad F)) := by
    -- Bound `levyEnergy d_ε → 0`, `‖d_ε‖₂ → 0`, `‖d_ε‖₁ → 0`
    have hN2_tendsto : Tendsto (fun ε : ℝ => ∫ u, originExcisionPerturb ε F u ^ 2) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by positivity))]
          with ε hε
        exact (hd_bounds ε hε.1 hε.2.le).2
      · have h0 : Tendsto (fun ε : ℝ => 16 * K ^ 2 * ε ^ 3) (𝓝 0) (𝓝 (16 * K ^ 2 * 0 ^ 3)) :=
          ((tendsto_id.pow 3).const_mul (16 * K ^ 2)).comp tendsto_id
        simpa using h0.mono_left nhdsWithin_le_nhds
    have hN1_tendsto : Tendsto (fun ε : ℝ => ∫ u, |originExcisionPerturb ε F u|) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _) ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by positivity))]
          with ε hε
        exact (hd_bounds ε hε.1 hε.2.le).1
      · have h0 : Tendsto (fun ε : ℝ => 8 * K * ε ^ 2) (𝓝 0) (𝓝 (8 * K * 0 ^ 2)) :=
          ((tendsto_id.pow 2).const_mul (8 * K)).comp tendsto_id
        simpa using h0.mono_left nhdsWithin_le_nhds
    have hL_tendsto : Tendsto (fun ε : ℝ =>
        SpacingScaleHarmonicAnalysis.levyEnergy (originExcisionPerturb ε F)) (𝓝[>] 0) (𝓝 0) := by
      set KL := (2 * Λ + 1) * K
      set C₁ := |SpacingScaleHarmonicAnalysis.levyLipConstant| + 2
      refine squeeze_zero' (Eventually.of_forall fun ε =>
        setIntegral_nonneg measurableSet_Ioi fun y hy =>
          mul_nonneg (archLevyDensity_pos hy).le (integral_nonneg fun _ => sq_nonneg _)) ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by positivity))]
          with ε hε
        have hε0 : 0 < ε := hε.1
        have hε1 : ε ≤ 1 := (hε.2.le.trans (min_le_left _ _)).trans (by norm_num)
        have hlip := SpacingScaleHarmonicAnalysis.levyEnergy_le_lipschitz
          (contDiff_originExcisionPerturb ε hF) (hasCompactSupport_originExcisionPerturb ε hFc)
          (lipschitz_originExcisionPerturb hε0 hK0 hΛ0 hΛ hF0 hFLip) hε0 hε1
        obtain ⟨hb1, hb2⟩ := hd_bounds ε hε0 hε.2.le
        -- Use `log(1/ε) ≤ 1/ε` (`log x ≤ x - 1 ≤ x` for `x = 1/ε > 0`) to keep pure polynomial `O(ε²)`!
        have hlog : Real.log (1 / ε) ≤ 1 / ε :=
          (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
        have hlogC : 2 * Real.log (1 / ε) + SpacingScaleHarmonicAnalysis.levyLipConstant ≤
            2 / ε + C₁ := by
          have := le_abs_self SpacingScaleHarmonicAnalysis.levyLipConstant
          linarith
        have hterm2 : (2 * Real.log (1 / ε) + SpacingScaleHarmonicAnalysis.levyLipConstant) *
            (∫ u, originExcisionPerturb ε F u ^ 2) ≤ 32 * K ^ 2 * ε ^ 2 + C₁ * (16 * K ^ 2 * ε ^ 3) := by
          have hnn : 0 ≤ 2 / ε + C₁ := by positivity
          calc (2 * Real.log (1 / ε) + SpacingScaleHarmonicAnalysis.levyLipConstant) *
                (∫ u, originExcisionPerturb ε F u ^ 2)
              ≤ (2 / ε + C₁) * (∫ u, originExcisionPerturb ε F u ^ 2) :=
                mul_le_mul_of_nonneg_right hlogC (integral_nonneg fun _ => sq_nonneg _)
            _ ≤ (2 / ε + C₁) * (16 * K ^ 2 * ε ^ 3) := mul_le_mul_of_nonneg_left hb2 hnn
            _ = 32 * K ^ 2 * ε ^ 2 + C₁ * (16 * K ^ 2 * ε ^ 3) := by field_simp [hε0.ne']; ring
        have hterm1 : Real.exp (1 / 2) * KL * ε * (∫ u, |originExcisionPerturb ε F u|) ≤
            Real.exp (1 / 2) * KL * 8 * K * ε ^ 3 := by
          calc Real.exp (1 / 2) * KL * ε * (∫ u, |originExcisionPerturb ε F u|)
              ≤ Real.exp (1 / 2) * KL * ε * (8 * K * ε ^ 2) :=
                mul_le_mul_of_nonneg_left hb1 (by positivity)
            _ = Real.exp (1 / 2) * KL * 8 * K * ε ^ 3 := by ring
        exact hlip.trans (add_le_add hterm1 hterm2)
      · have h0 : Tendsto (fun ε : ℝ =>
            Real.exp (1 / 2) * KL * 8 * K * ε ^ 3 +
              (32 * K ^ 2 * ε ^ 2 + C₁ * (16 * K ^ 2 * ε ^ 3))) (𝓝 0)
            (𝓝 (Real.exp (1 / 2) * KL * 8 * K * 0 ^ 3 +
              (32 * K ^ 2 * 0 ^ 2 + C₁ * (16 * K ^ 2 * 0 ^ 3)))) :=
          (((tendsto_id.pow 3).const_mul _).add
            (((tendsto_id.pow 2).const_mul _).add ((tendsto_id.pow 3).const_mul _)))
        simpa using h0.mono_left nhdsWithin_le_nhds
    -- Combine upper and lower bounds from `weilQuad_add_le` on `(F, d_ε)` and `(F_ε, -d_ε)`
    set errF : ℝ → ℝ := fun ε =>
      2 * |gammaHardyPhaseRate 0| *
          (2 * (Real.sqrt (∫ u, F u ^ 2) * Real.sqrt (∫ u, originExcisionPerturb ε F u ^ 2)) +
            ∫ u, originExcisionPerturb ε F u ^ 2) +
        (2 * (Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy F) *
            Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy (originExcisionPerturb ε F))) +
          SpacingScaleHarmonicAnalysis.levyEnergy (originExcisionPerturb ε F)) +
        2 * SpacingScaleHarmonicAnalysis.primeMass R *
          (2 * (Real.sqrt (∫ u, F u ^ 2) * Real.sqrt (∫ u, originExcisionPerturb ε F u ^ 2)) +
            ∫ u, originExcisionPerturb ε F u ^ 2) +
        4 * Real.cosh (R / 2) * (|coshHalfMoment F| + |sinhHalfMoment F| +
            Real.cosh (R / 2) * ∫ u, |originExcisionPerturb ε F u|) *
          (∫ u, |originExcisionPerturb ε F u|) +
        4 * Real.cosh (R / 2) ^ 2 * (∫ u, |originExcisionPerturb ε F u|) ^ 2 +
        -- Extra dominated terms for reverse application `F = F_ε + (-d_ε)` where `‖F_ε‖₂ ≤ ‖F‖₂` and `levyEnergy F_ε ≤ (√(L F) + √(L d_ε))²`
        2 * (|gammaHardyPhaseRate 0| + SpacingScaleHarmonicAnalysis.primeMass R) *
          (2 * ((Real.sqrt (∫ u, F u ^ 2) + Real.sqrt (∫ u, originExcisionPerturb ε F u ^ 2)) *
              Real.sqrt (∫ u, originExcisionPerturb ε F u ^ 2)) +
            ∫ u, originExcisionPerturb ε F u ^ 2) +
        (2 * ((Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy F) +
              Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy (originExcisionPerturb ε F))) *
            Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy (originExcisionPerturb ε F))) +
          SpacingScaleHarmonicAnalysis.levyEnergy (originExcisionPerturb ε F))
    have herr_tendsto : Tendsto errF (𝓝[>] 0) (𝓝 0) := by
      have hsqN2 : Tendsto (fun ε => Real.sqrt (∫ u, originExcisionPerturb ε F u ^ 2)) (𝓝[>] 0) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.tendsto 0).comp hN2_tendsto
      have hsqL : Tendsto (fun ε =>
          Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy (originExcisionPerturb ε F)))
          (𝓝[>] 0) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.tendsto 0).comp hL_tendsto
      unfold errF
      have h :=
        (((((((hsqN2.const_mul _).const_mul 2).add hN2_tendsto).const_mul _).add
          (((hsqL.const_mul _).const_mul 2).add hL_tendsto)).add
          ((((hsqN2.const_mul _).const_mul 2).add hN2_tendsto).const_mul _)).add
          ((((tendsto_const_nhds.add (hN1_tendsto.const_mul _)).const_mul _).mul hN1_tendsto)).add
          ((hN1_tendsto.pow 2).const_mul _)).add
          ((((((tendsto_const_nhds.add hsqN2).mul hsqN2).const_mul 2).add hN2_tendsto).const_mul _)).add
          (((((tendsto_const_nhds.add hsqL).mul hsqL).const_mul 2).add hL_tendsto))
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using tendsto_const_nhds.sub herr_tendsto)
      (by simpa using tendsto_const_nhds.add herr_tendsto) ?_ ?_
    · -- Lower bound: `weilQuad F ≤ weilQuad F_ε + errF ε` via `F = F_ε + (-d_ε)`
      filter_upwards [Ioo_mem_nhdsGT (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by positivity))]
        with ε hε
      have hε0 : 0 < ε := hε.1
      set d := originExcisionPerturb ε F
      set Fε := originExcisedProfile ε F
      have hd : ContDiff ℝ 2 d := contDiff_originExcisionPerturb ε hF
      have hdc : HasCompactSupport d := hasCompactSupport_originExcisionPerturb ε hFc
      have hdR : SpacingScaleHarmonicAnalysis.SupportedIn R d := fun u hu =>
        originExcisionPerturb_eq_zero_far hε0 F
          (le_trans (by linarith [min_le_right (1 / 2 : ℝ) (R / 2), hε.2.le]) hu.le)
      have hFε : ContDiff ℝ 2 Fε := hF.add hd
      have hFεc : HasCompactSupport Fε := hFc.add hdc
      have hFεR : SpacingScaleHarmonicAnalysis.SupportedIn R Fε := fun u hu => by
        simp [Fε, originExcisedProfile, hFR u hu, hdR u hu]
      have hrev := SpacingScaleHarmonicAnalysis.weilQuad_add_le hFε hFεc hd.neg hdc.neg hFεR
        (fun u hu => by simp [hdR u hu])
      have hsum : (fun u => Fε u + (-d) u) = F := by funext u; simp [Fε, originExcisedProfile]
      rw [hsum] at hrev
      have hnd_neg : (∫ u, ((-d) u) ^ 2) = ∫ u, d u ^ 2 := by simp
      have hn1_neg : (∫ u, |(-d) u|) = ∫ u, |d u| := by simp
      have hL_neg : SpacingScaleHarmonicAnalysis.levyEnergy (-d) =
          SpacingScaleHarmonicAnalysis.levyEnergy d := by
        unfold SpacingScaleHarmonicAnalysis.levyEnergy
        refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
        congr 1; refine integral_congr_ae (Eventually.of_forall fun u => ?_); simp; ring
      -- Bound `√(∫ F_ε²) ≤ √(∫ F²) + √(∫ d²)` and `√(L F_ε) ≤ √(L F) + √(L d)`
      have hFε_L2 : Real.sqrt (∫ u, Fε u ^ 2) ≤ Real.sqrt (∫ u, F u ^ 2) + Real.sqrt (∫ u, d u ^ 2) := by
        have hfi : Integrable fun u => F u ^ 2 :=
          (hF.continuous.pow 2).integrable_of_hasCompactSupport hFc.sq
        have hdi : Integrable fun u => d u ^ 2 :=
          (hd.continuous.pow 2).integrable_of_hasCompactSupport hdc.sq
        have hfdi : Integrable fun u => F u * d u :=
          (hF.continuous.mul hd.continuous).integrable_of_hasCompactSupport hFc.mul_right
        have hcs := SpacingScaleHarmonicAnalysis.abs_integral_mul_le hfi hdi hfdi
        have hexp : ∫ u, Fε u ^ 2 = (∫ u, F u ^ 2) + 2 * (∫ u, F u * d u) + ∫ u, d u ^ 2 := by
          rw [show (fun u => Fε u ^ 2) = fun u => 1 * F u ^ 2 + 2 * (F u * d u) + d u ^ 2 by
            funext u; simp [Fε, originExcisedProfile]; ring,
            SpacingScaleHarmonicAnalysis.integral_lin3 hfi hfdi hdi]; ring
        have hle : ∫ u, Fε u ^ 2 ≤ (Real.sqrt (∫ u, F u ^ 2) + Real.sqrt (∫ u, d u ^ 2)) ^ 2 := by
          rw [hexp, add_sq, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
            Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
          linarith [le_abs_self (∫ u, F u * d u)]
        exact (Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_sq (by positivity))
      have hFε_levy : Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy Fε) ≤
          Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy F) +
            Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy d) := by
        have hle := SpacingScaleHarmonicAnalysis.levyEnergy_add_le hF hFc hd hdc
        have hLf : 0 ≤ SpacingScaleHarmonicAnalysis.levyEnergy F :=
          setIntegral_nonneg measurableSet_Ioi fun y hy =>
            mul_nonneg (archLevyDensity_pos hy).le (integral_nonneg fun _ => sq_nonneg _)
        have hLd : 0 ≤ SpacingScaleHarmonicAnalysis.levyEnergy d :=
          setIntegral_nonneg measurableSet_Ioi fun y hy =>
            mul_nonneg (archLevyDensity_pos hy).le (integral_nonneg fun _ => sq_nonneg _)
        have hsq : SpacingScaleHarmonicAnalysis.levyEnergy Fε ≤
            (Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy F) +
              Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy d)) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hLf, Real.sq_sqrt hLd]
          exact hle.trans_eq (by ring)
        exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))
      have hC_Fε : |coshHalfMoment Fε| = 0 := by
        have h0 : coshHalfMoment Fε = 0 := integral_eq_zero_of_odd fun x => by
          rw [originExcisedProfile_odd ε hodd x, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
          ring
        simp [h0]
      have hS_Fε : |sinhHalfMoment Fε| ≤ |sinhHalfMoment F| + Real.cosh (R / 2) * ∫ u, |d u| := by
        have hcf : Continuous fun u => Real.sinh (u / 2) :=
          Real.continuous_sinh.comp (continuous_id.div_const 2)
        have hSadd : sinhHalfMoment Fε = sinhHalfMoment F + sinhHalfMoment d := by
          unfold sinhHalfMoment
          rw [← integral_add ((hF.continuous.mul hcf).integrable_of_hasCompactSupport hFc.mul_right)
            ((hd.continuous.mul hcf).integrable_of_hasCompactSupport hdc.mul_right)]
          exact integral_congr_ae (Eventually.of_forall fun u => by simp [Fε, originExcisedProfile]; ring)
        have hSd := SpacingScaleHarmonicAnalysis.abs_moment_le hd.continuous hdc hdR hcf
          fun u hu => SpacingScaleHarmonicAnalysis.abs_sinh_half_le hu
        rw [hSadd]
        exact (abs_add_le _ _).trans (add_le_add le_rfl hSd)
      rw [hnd_neg, hn1_neg, hL_neg, hC_Fε, zero_add] at hrev
      have hN1_nn : 0 ≤ ∫ u, |d u| := integral_nonneg fun _ => abs_nonneg _
      have hnd_nn : 0 ≤ Real.sqrt (∫ u, d u ^ 2) := Real.sqrt_nonneg _
      have hLd_nn : 0 ≤ Real.sqrt (SpacingScaleHarmonicAnalysis.levyEnergy d) := Real.sqrt_nonneg _
      have hpm_nn : 0 ≤ SpacingScaleHarmonicAnalysis.primeMass R := by
        unfold SpacingScaleHarmonicAnalysis.primeMass
        exact tsum_nonneg fun k => by split_ifs <;> [exact SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k; linarith]
      have hm1 := mul_le_mul_of_nonneg_right hFε_L2 hnd_nn
      have hm2 := mul_le_mul_of_nonneg_right hFε_levy hLd_nn
      have hm3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS_Fε (by positivity : 0 ≤ 4 * Real.cosh (R / 2))) hN1_nn
      unfold errF
      nlinarith [abs_nonneg (gammaHardyPhaseRate 0), abs_nonneg (coshHalfMoment F),
        Real.cosh_pos (R / 2), integral_nonneg fun u => sq_nonneg (d u),
        (show 0 ≤ SpacingScaleHarmonicAnalysis.levyEnergy d from
          setIntegral_nonneg measurableSet_Ioi fun y hy =>
            mul_nonneg (archLevyDensity_pos hy).le (integral_nonneg fun _ => sq_nonneg _))]
    · -- Upper bound: `weilQuad F_ε ≤ weilQuad F + errF ε` directly from `weilQuad_add_le`
      filter_upwards [Ioo_mem_nhdsGT (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by positivity))]
        with ε hε
      have hε0 : 0 < ε := hε.1
      set d := originExcisionPerturb ε F
      have hd : ContDiff ℝ 2 d := contDiff_originExcisionPerturb ε hF
      have hdc : HasCompactSupport d := hasCompactSupport_originExcisionPerturb ε hFc
      have hdR : SpacingScaleHarmonicAnalysis.SupportedIn R d := fun u hu =>
        originExcisionPerturb_eq_zero_far hε0 F
          (le_trans (by linarith [min_le_right (1 / 2 : ℝ) (R / 2), hε.2.le]) hu.le)
      have hfwd := SpacingScaleHarmonicAnalysis.weilQuad_add_le hF hFc hd hdc hFR hdR
      have hN1_nn : 0 ≤ ∫ u, |d u| := integral_nonneg fun _ => abs_nonneg _
      have hpm_nn : 0 ≤ SpacingScaleHarmonicAnalysis.primeMass R := by
        unfold SpacingScaleHarmonicAnalysis.primeMass
        exact tsum_nonneg fun k => by split_ifs <;> [exact SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k; linarith]
      unfold errF
      change SpacingScaleHarmonicAnalysis.weilQuad (fun u => F u + d u) ≤ _
      nlinarith [hfwd, Real.cosh_pos (R / 2), abs_nonneg (gammaHardyPhaseRate 0),
        Real.sqrt_nonneg (∫ u, F u ^ 2), Real.sqrt_nonneg (∫ u, d u ^ 2),
        Real.sqrt_nonneg (SpacingScaleHarmonicAnalysis.levyEnergy F),
        Real.sqrt_nonneg (SpacingScaleHarmonicAnalysis.levyEnergy d),
        integral_nonneg fun u => sq_nonneg (d u),
        (show 0 ≤ SpacingScaleHarmonicAnalysis.levyEnergy d from
          setIntegral_nonneg measurableSet_Ioi fun y hy =>
            mul_nonneg (archLevyDensity_pos hy).le (integral_nonneg fun _ => sq_nonneg _))]
  -- Combine `weilQuad` and `2 * oddPoleMoment ^ 2`
  have hcomb := hQ_tendsto.add ((hodd_tendsto.pow 2).const_mul 2)
  rw [← markovEnergy_eq_weilQuad_add_odd_sq_of_odd hF hFc hodd] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε _
  exact (markovEnergy_eq_weilQuad_add_odd_sq_of_odd
    (hF.add (contDiff_originExcisionPerturb ε hF))
    (hFc.add (hasCompactSupport_originExcisionPerturb ε hFc))
    (originExcisedProfile_odd ε hodd)).symm

/-- Convergence of the two-profile `L^{1/2}` half-norm integral under origin excision. -/
theorem tendsto_halfNorm_originExcisedProfile {c : ℝ} (hc : 0 < c) {F₁ F₂ : ℝ → ℝ}
    (hF₁ : Continuous F₁) (hF₂ : Continuous F₂) :
    Tendsto (fun ε : ℝ => ∫ x in Ioo (-c) c,
        Real.sqrt (originExcisedProfile ε F₁ x ^ 2 + originExcisedProfile ε F₂ x ^ 2) *
          |Real.sinh (x / 2)|)
      (𝓝[>] 0)
      (𝓝 (∫ x in Ioo (-c) c, Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun x => Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun ε => ?_
    have hc1 : Continuous (originExcisedProfile ε F₁) :=
      hF₁.add ((((contDiff_smoothPlateau 1).continuous.comp (continuous_id.div_const ε)).mul hF₁).neg)
    have hc2 : Continuous (originExcisedProfile ε F₂) :=
      hF₂.add ((((contDiff_smoothPlateau 1).continuous.comp (continuous_id.div_const ε)).mul hF₂).neg)
    exact ((Real.continuous_sqrt.comp ((hc1.pow 2).add (hc2.pow 2))).mul
      (continuous_abs.comp (Real.continuous_sinh.comp (continuous_id.div_const 2)))).continuousOn.aestronglyMeasurable
      measurableSet_Ioo
  · exact integrableOn_Ioo_of_continuous
      ((Real.continuous_sqrt.comp ((hF₁.pow 2).add (hF₂.pow 2))).mul
        (continuous_abs.comp (Real.continuous_sinh.comp (continuous_id.div_const 2))))
  · refine Eventually.of_forall fun ε => ae_restrict_of_forall_mem measurableSet_Ioo fun x _ => ?_
    have hp0 : 0 ≤ 1 - smoothPlateau 1 (x / ε) := sub_nonneg.mpr (smoothPlateau_le_one 1 _)
    have hp1 : 1 - smoothPlateau 1 (x / ε) ≤ 1 := by linarith [smoothPlateau_nonneg 1 (x / ε)]
    have he1 : originExcisedProfile ε F₁ x = (1 - smoothPlateau 1 (x / ε)) * F₁ x := by
      unfold originExcisedProfile originExcisionPerturb; ring
    have he2 : originExcisedProfile ε F₂ x = (1 - smoothPlateau 1 (x / ε)) * F₂ x := by
      unfold originExcisedProfile originExcisionPerturb; ring
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)), he1, he2]
    refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (abs_nonneg _)
    have hsq1 : (1 - smoothPlateau 1 (x / ε)) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (F₁ x), sq_nonneg (F₂ x)]
  ·-- For every `x ≠ 0` (which holds a.e. on `Ioo (-c) c`), `originExcisedProfile ε F_i x = F_i x` once `2ε ≤ |x|`
    have h0_ae : ∀ᵐ x ∂volume.restrict (Ioo (-c) c), x ≠ 0 :=
      ae_restrict_of_ae (by simp [compl_singleton_mem_ae_iff])
    filter_upwards [h0_ae] with x hx0
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show 0 < |x| / 2 from half_pos (abs_pos.mpr hx0))] with ε hε
    have hf1 : originExcisionPerturb ε F₁ x = 0 :=
      originExcisionPerturb_eq_zero_far hε.1 F₁ (by linarith [hε.2])
    have hf2 : originExcisionPerturb ε F₂ x = 0 :=
      originExcisionPerturb_eq_zero_far hε.1 F₂ (by linarith [hε.2])
    simp [originExcisedProfile, hf1, hf2]

/-! ### 5. Master universal refutation theorems from a negative two-profile dual -/

/-- Existence of origin-excised profiles preserving any strict negativity of the two-profile
`L^{1/2}` dual functional. -/
theorem exists_originExcised_pair_of_halfNormDual_neg {c' c : ℝ} (hc' : 0 < c') (hc : c' < c)
    {F₁ F₂ : ℝ → ℝ} (hF₁ : ContDiff ℝ 2 F₁) (hF₁c : HasCompactSupport F₁)
    (hF₁odd : ∀ x, F₁ (-x) = -F₁ x) (hF₁supp : ∀ x, c' < |x| → F₁ x = 0)
    (hF₂ : ContDiff ℝ 2 F₂) (hF₂c : HasCompactSupport F₂)
    (hF₂odd : ∀ x, F₂ (-x) = -F₂ x) (hF₂supp : ∀ x, c' < |x| → F₂ x = 0)
    (hneg : markovEnergy (fun x => (F₁ x : ℂ)) + markovEnergy (fun x => (F₂ x : ℂ)) <
      2 * (∫ x in Ioo (-c) c, Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|) ^ 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε < c' ∧
      markovEnergy (fun x => (originExcisedProfile ε F₁ x : ℂ)) +
          markovEnergy (fun x => (originExcisedProfile ε F₂ x : ℂ)) <
        2 * (∫ x in Ioo (-c) c,
          Real.sqrt (originExcisedProfile ε F₁ x ^ 2 + originExcisedProfile ε F₂ x ^ 2) *
            |Real.sinh (x / 2)|) ^ 2 := by
  have hc0 : 0 < c := lt_trans hc' hc
  have ht1 := tendsto_markovEnergy_originExcisedProfile hc' hF₁ hF₁c hF₁odd hF₁supp
  have ht2 := tendsto_markovEnergy_originExcisedProfile hc' hF₂ hF₂c hF₂odd hF₂supp
  have htI := tendsto_halfNorm_originExcisedProfile hc0 hF₁.continuous hF₂.continuous
  have htdiff := (ht1.add ht2).sub ((htI.pow 2).const_mul 2)
  have hlim_neg : markovEnergy (fun x => (F₁ x : ℂ)) + markovEnergy (fun x => (F₂ x : ℂ)) -
      2 * (∫ x in Ioo (-c) c, Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|) ^ 2 < 0 := by
    linarith
  have hev := (htdiff.eventually (Iio_mem_nhds hlim_neg)).and (Ioo_mem_nhdsGT hc')
  obtain ⟨ε, hεneg, hεI⟩ := hev.exists
  exact ⟨ε, hεI.1, hεI.2, by dsimp at hεneg; linarith⟩

/-- **No odd sinh-charged supersolution exists when the two-profile `L^{1/2}` dual is negative.**
Any gauge `ω ∈ C²_c(ℝ)` (compactly supported on any interval around `(−c, c)`), odd on `(−c, c)` and
strictly positive on `(0, c)`, fails either the sinh-charged defect inequality on `(−c, c)` or
nonnegativity of `J_{Φω}` on even `C²_c` profiles supported in `(−c, c)`. -/
theorem not_exists_odd_sinhCharged_gauge_of_two_odd_tests {c' c : ℝ} (hc' : 0 < c') (hc : c' < c)
    {F₁ F₂ : ℝ → ℝ} (hF₁ : ContDiff ℝ 2 F₁) (hF₁c : HasCompactSupport F₁)
    (hF₁odd : ∀ x, F₁ (-x) = -F₁ x) (hF₁supp : ∀ x, c' < |x| → F₁ x = 0)
    (hF₂ : ContDiff ℝ 2 F₂) (hF₂c : HasCompactSupport F₂)
    (hF₂odd : ∀ x, F₂ (-x) = -F₂ x) (hF₂supp : ∀ x, c' < |x| → F₂ x = 0)
    (hneg : markovEnergy (fun x => (F₁ x : ℂ)) + markovEnergy (fun x => (F₂ x : ℂ)) <
      2 * (∫ x in Ioo (-c) c, Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|) ^ 2) :
    ¬ ∃ ω : ℝ → ℝ, ContDiff ℝ 2 ω ∧ HasCompactSupport ω ∧
      (∀ x ∈ Ioo (-c) c, ω (-x) = -ω x) ∧
      (∀ x ∈ Ioo (0 : ℝ) c, 0 < ω x) ∧
      (∀ x ∈ Ioo (-c) c, 0 ≤ ω x * (markovDefect ω x -
        2 * sinhCharge ω (Ioo (-c) c) * (riemannKernelReal x * Real.sinh (x / 2)))) ∧
      (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → (∀ x, u (-x) = u x) →
        (∀ x, x ∉ Ioo (-c) c → u x = 0) →
        0 ≤ signedJumpEnergy (fun y => riemannKernelReal y * ω y) u) := by
  rintro ⟨ω, hω, hωc, hωodd, hωpos, hsuper, hJ⟩
  obtain ⟨ε, hε0, hεc', hεneg⟩ := exists_originExcised_pair_of_halfNormDual_neg hc' hc
    hF₁ hF₁c hF₁odd hF₁supp hF₂ hF₂c hF₂odd hF₂supp hneg
  set G₁ := originExcisedProfile ε F₁
  set G₂ := originExcisedProfile ε F₂
  set M := fun x => riemannKernelReal x * ω x
  have hω_sinh_pos : ∀ x ∈ Ioo (-c) c, x ≠ 0 → 0 < ω x * Real.sinh (x / 2) := fun x hx hx0 => by
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · have hnx : -x ∈ Ioo (0 : ℝ) c := ⟨by linarith, by linarith [hx.1]⟩
      have hp := hωpos (-x) hnx
      rw [hωodd x hx] at hp
      exact mul_pos_of_neg_of_neg (by linarith) (Real.sinh_neg_iff.mpr (by linarith))
    · exact absurd rfl hx0
    · exact mul_pos (hωpos x ⟨hgt, hx.2⟩) (Real.sinh_pos_iff.mpr (by linarith))
  have hModd : ∀ x ∈ Ioo (-c) c, M (-x) = -M x := fun x hx => by
    simp only [M, riemannKernelReal_neg', hωodd x hx, mul_neg]
  have hMnz : ∀ x ∈ Ioo (-c) c, x ≠ 0 → M x ≠ 0 := fun x hx hx0 hMz => by
    have hp := hω_sinh_pos x hx hx0
    rcases mul_eq_zero.mp hMz with h1 | h2
    · linarith [riemannKernelReal_pos x]
    · rw [h2, zero_mul] at hp; exact lt_irrefl 0 hp
  have hG₁ : ContDiff ℝ 2 G₁ := hF₁.add (contDiff_originExcisionPerturb ε hF₁)
  have hG₂ : ContDiff ℝ 2 G₂ := hF₂.add (contDiff_originExcisionPerturb ε hF₂)
  set u₁ := windowGaugeQuotient ε c' c M G₁
  set u₂ := windowGaugeQuotient ε c' c M G₂
  have hu₁ : ContDiff ℝ 2 u₁ := contDiff_windowGaugeQuotient hε0 hc
    (contDiff_riemannKernelReal.mul hω) hMnz hG₁
    (fun x hx => originExcisedProfile_eq_zero_near hε0 F₁ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₁supp hx)
  have hu₂ : ContDiff ℝ 2 u₂ := contDiff_windowGaugeQuotient hε0 hc
    (contDiff_riemannKernelReal.mul hω) hMnz hG₂
    (fun x hx => originExcisedProfile_eq_zero_near hε0 F₂ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₂supp hx)
  have hu₁c := hasCompactSupport_windowGaugeQuotient (ε := ε) hc M G₁
  have hu₂c := hasCompactSupport_windowGaugeQuotient (ε := ε) hc M G₂
  have hu₁e : ∀ x, u₁ (-x) = u₁ x := windowGaugeQuotient_even hModd (originExcisedProfile_odd ε hF₁odd)
  have hu₂e : ∀ x, u₂ (-x) = u₂ x := windowGaugeQuotient_even hModd (originExcisedProfile_odd ε hF₂odd)
  have hu₁off : ∀ x, x ∉ Ioo (-c) c → u₁ x = 0 := fun x hx => windowGaugeQuotient_eq_zero_off hc M G₁ hx
  have hu₂off : ∀ x, x ∉ Ioo (-c) c → u₂ x = 0 := fun x hx => windowGaugeQuotient_eq_zero_off hc M G₂ hx
  have hJ₁ := hJ u₁ hu₁ hu₁c hu₁e hu₁off
  have hJ₂ := hJ u₂ hu₂ hu₂c hu₂e hu₂off
  have hdef₁ : 0 ≤ ∫ x, u₁ x ^ 2 * ω x *
      (markovDefect ω x - 2 * sinhCharge ω (Ioo (-c) c) * (riemannKernelReal x * Real.sinh (x / 2))) := by
    refine integral_nonneg fun x => ?_
    by_cases hx : x ∈ Ioo (-c) c
    · rw [mul_assoc]; exact mul_nonneg (sq_nonneg _) (hsuper x hx)
    · simp [hu₁off x hx]
  have hdef₂ : 0 ≤ ∫ x, u₂ x ^ 2 * ω x *
      (markovDefect ω x - 2 * sinhCharge ω (Ioo (-c) c) * (riemannKernelReal x * Real.sinh (x / 2))) := by
    refine integral_nonneg fun x => ?_
    by_cases hx : x ∈ Ioo (-c) c
    · rw [mul_assoc]; exact mul_nonneg (sq_nonneg _) (hsuper x hx)
    · simp [hu₂off x hx]
  have eq₁ := signedJumpEnergy_add_sinhDefect_eq_markovEnergy_sub (Ioo (-c) c) hω hωc hu₁ hu₁c
  have eq₂ := signedJumpEnergy_add_sinhDefect_eq_markovEnergy_sub (Ioo (-c) c) hω hωc hu₂ hu₂c
  have hF₁_eq : phiDoobTest (fun y => ω y * u₁ y) = G₁ := funext fun x => by
    simp only [phiDoobTest, ← mul_assoc]
    exact windowGaugeQuotient_mul hε0 hc hMnz
      (fun y hy => originExcisedProfile_eq_zero_near hε0 F₁ hy)
      (fun y hy => originExcisedProfile_eq_zero_far ε hF₁supp hy) x
  have hF₂_eq : phiDoobTest (fun y => ω y * u₂ y) = G₂ := funext fun x => by
    simp only [phiDoobTest, ← mul_assoc]
    exact windowGaugeQuotient_mul hε0 hc hMnz
      (fun y hy => originExcisedProfile_eq_zero_near hε0 F₂ hy)
      (fun y hy => originExcisedProfile_eq_zero_far ε hF₂supp hy) x
  rw [hF₁_eq] at eq₁
  rw [hF₂_eq] at eq₂
  have hcs := two_profile_sinhQuotient_ge_halfNorm_sq hε0 hεc' hc hω hω_sinh_pos
    hG₁ (fun x hx => originExcisedProfile_eq_zero_near hε0 F₁ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₁supp hx)
    hG₂ (fun x hx => originExcisedProfile_eq_zero_near hε0 F₂ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₂supp hx)
  dsimp only at hcs
  linarith

/-- **No odd non-compact theta-gauge outside-charge certificate exists when the two-profile `L^{1/2}`
dual is negative.** -/
theorem not_exists_odd_thetaGauge_certificate_of_two_odd_tests {c' c : ℝ} (hc' : 0 < c')
    (hc : c' < c) {F₁ F₂ : ℝ → ℝ} (hF₁ : ContDiff ℝ 2 F₁) (hF₁c : HasCompactSupport F₁)
    (hF₁odd : ∀ x, F₁ (-x) = -F₁ x) (hF₁supp : ∀ x, c' < |x| → F₁ x = 0)
    (hF₂ : ContDiff ℝ 2 F₂) (hF₂c : HasCompactSupport F₂)
    (hF₂odd : ∀ x, F₂ (-x) = -F₂ x) (hF₂supp : ∀ x, c' < |x| → F₂ x = 0)
    (hneg : markovEnergy (fun x => (F₁ x : ℂ)) + markovEnergy (fun x => (F₂ x : ℂ)) <
      2 * (∫ x in Ioo (-c) c, Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|) ^ 2)
    {ι : Type*} (s : Finset ι) (α b : ι → ℝ)
    (hModd : ∀ x, riemannKernelReal (-x) * translateSpan s α b (-x) =
      -(riemannKernelReal x * translateSpan s α b x))
    (hωpos : ∀ x ∈ Ioo (0 : ℝ) c, 0 < translateSpan s α b x) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      (∀ x, x ∉ Ioo (-c) c → u x = 0) ∧
      signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u +
        2 * (translateSinhCoefficient s α b / 2 - sinhCharge (translateSpan s α b) (Ioo (-c) c)) *
          (∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x * Real.sinh (x / 2))) < 0 := by
  by_contra hall
  push Not at hall
  set ω := translateSpan s α b
  have hω : ContDiff ℝ 2 ω := contDiff_translateSpan s α b
  have hA := translateCoshCoefficient_eq_zero_of_odd s α b hModd
  obtain ⟨ε, hε0, hεc', hεneg⟩ := exists_originExcised_pair_of_halfNormDual_neg hc' hc
    hF₁ hF₁c hF₁odd hF₁supp hF₂ hF₂c hF₂odd hF₂supp hneg
  set G₁ := originExcisedProfile ε F₁
  set G₂ := originExcisedProfile ε F₂
  set M := fun x => riemannKernelReal x * ω x
  have hω_sinh_pos : ∀ x ∈ Ioo (-c) c, x ≠ 0 → 0 < ω x * Real.sinh (x / 2) := fun x hx hx0 => by
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · have hnx : -x ∈ Ioo (0 : ℝ) c := ⟨by linarith, by linarith [hx.1]⟩
      have hp := hωpos (-x) hnx
      have hMx := hModd x
      rw [riemannKernelReal_neg'] at hMx
      have hωn : ω (-x) = -ω x :=
        mul_left_cancel₀ (riemannKernelReal_pos x).ne' (by linarith)
      rw [hωn] at hp
      exact mul_pos_of_neg_of_neg (by linarith) (Real.sinh_neg_iff.mpr (by linarith))
    · exact absurd rfl hx0
    · exact mul_pos (hωpos x ⟨hgt, hx.2⟩) (Real.sinh_pos_iff.mpr (by linarith))
  have hMnz : ∀ x ∈ Ioo (-c) c, x ≠ 0 → M x ≠ 0 := fun x hx hx0 hMz => by
    have hp := hω_sinh_pos x hx hx0
    rcases mul_eq_zero.mp hMz with h1 | h2
    · linarith [riemannKernelReal_pos x]
    · rw [h2, zero_mul] at hp; exact lt_irrefl 0 hp
  have hG₁ : ContDiff ℝ 2 G₁ := hF₁.add (contDiff_originExcisionPerturb ε hF₁)
  have hG₂ : ContDiff ℝ 2 G₂ := hF₂.add (contDiff_originExcisionPerturb ε hF₂)
  set u₁ := windowGaugeQuotient ε c' c M G₁
  set u₂ := windowGaugeQuotient ε c' c M G₂
  have hu₁ : ContDiff ℝ 2 u₁ := contDiff_windowGaugeQuotient hε0 hc
    (contDiff_riemannKernelReal.mul hω) hMnz hG₁
    (fun x hx => originExcisedProfile_eq_zero_near hε0 F₁ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₁supp hx)
  have hu₂ : ContDiff ℝ 2 u₂ := contDiff_windowGaugeQuotient hε0 hc
    (contDiff_riemannKernelReal.mul hω) hMnz hG₂
    (fun x hx => originExcisedProfile_eq_zero_near hε0 F₂ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₂supp hx)
  have hu₁c := hasCompactSupport_windowGaugeQuotient (ε := ε) hc M G₁
  have hu₂c := hasCompactSupport_windowGaugeQuotient (ε := ε) hc M G₂
  have hu₁e : ∀ x, u₁ (-x) = u₁ x := windowGaugeQuotient_even (fun x _ => hModd x) (originExcisedProfile_odd ε hF₁odd)
  have hu₂e : ∀ x, u₂ (-x) = u₂ x := windowGaugeQuotient_even (fun x _ => hModd x) (originExcisedProfile_odd ε hF₂odd)
  have hge₁ := hall u₁ hu₁ hu₁c hu₁e (fun x hx => windowGaugeQuotient_eq_zero_off hc M G₁ hx)
  have hge₂ := hall u₂ hu₂ hu₂c hu₂e (fun x hx => windowGaugeQuotient_eq_zero_off hc M G₂ hx)
  have eq₁ := signedJumpEnergy_add_outsideSinh_thetaGauge_eq s α b (Ioo (-c) c) hA hu₁ hu₁c
  have eq₂ := signedJumpEnergy_add_outsideSinh_thetaGauge_eq s α b (Ioo (-c) c) hA hu₂ hu₂c
  have hF₁_eq : phiDoobTest (fun y => ω y * u₁ y) = G₁ := funext fun x => by
    simp only [phiDoobTest, ← mul_assoc]
    exact windowGaugeQuotient_mul hε0 hc hMnz
      (fun y hy => originExcisedProfile_eq_zero_near hε0 F₁ hy)
      (fun y hy => originExcisedProfile_eq_zero_far ε hF₁supp hy) x
  have hF₂_eq : phiDoobTest (fun y => ω y * u₂ y) = G₂ := funext fun x => by
    simp only [phiDoobTest, ← mul_assoc]
    exact windowGaugeQuotient_mul hε0 hc hMnz
      (fun y hy => originExcisedProfile_eq_zero_near hε0 F₂ hy)
      (fun y hy => originExcisedProfile_eq_zero_far ε hF₂supp hy) x
  rw [hF₁_eq] at eq₁
  rw [hF₂_eq] at eq₂
  have hcs := two_profile_sinhQuotient_ge_halfNorm_sq hε0 hεc' hc hω hω_sinh_pos
    hG₁ (fun x hx => originExcisedProfile_eq_zero_near hε0 F₁ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₁supp hx)
    hG₂ (fun x hx => originExcisedProfile_eq_zero_near hε0 F₂ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₂supp hx)
  dsimp only at hcs
  linarith

/-- **Every shifted ground state `ω_a` (`a > 0`) fails its variance-dropped window certificate
whenever the two-profile `L^{1/2}` dual is negative.** -/
theorem exists_shiftedGroundState_windowLower_neg_of_two_odd_tests {c' c : ℝ} (hc' : 0 < c')
    (hc : c' < c) {F₁ F₂ : ℝ → ℝ} (hF₁ : ContDiff ℝ 2 F₁) (hF₁c : HasCompactSupport F₁)
    (hF₁odd : ∀ x, F₁ (-x) = -F₁ x) (hF₁supp : ∀ x, c' < |x| → F₁ x = 0)
    (hF₂ : ContDiff ℝ 2 F₂) (hF₂c : HasCompactSupport F₂)
    (hF₂odd : ∀ x, F₂ (-x) = -F₂ x) (hF₂supp : ∀ x, c' < |x| → F₂ x = 0)
    (hneg : markovEnergy (fun x => (F₁ x : ℂ)) + markovEnergy (fun x => (F₂ x : ℂ)) <
      2 * (∫ x in Ioo (-c) c, Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|) ^ 2)
    {a : ℝ} (ha : 0 < a) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      (∀ x, x ∉ Ioo (-c) c → u x = 0) ∧
      2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u +
        8 * outsideCharge a c *
          (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) < 0 := by
  by_contra hall
  push Not at hall
  have hc0 : 0 ≤ c := (lt_trans hc' hc).le
  obtain ⟨ε, hε0, hεc', hεneg⟩ := exists_originExcised_pair_of_halfNormDual_neg hc' hc
    hF₁ hF₁c hF₁odd hF₁supp hF₂ hF₂c hF₂odd hF₂supp hneg
  set G₁ := originExcisedProfile ε F₁
  set G₂ := originExcisedProfile ε F₂
  set ω := shiftedGroundState a
  set M := fun x => riemannKernelReal x * ω x
  have hω : ContDiff ℝ 2 ω := contDiff_shiftedGroundState a
  have hModd : ∀ x ∈ Ioo (-c) c, M (-x) = -M x := fun x _ => by
    simp only [M, ω, riemannKernelReal_mul_shiftedGroundState, shiftDifference_neg]
  have hω_sinh_pos : ∀ x ∈ Ioo (-c) c, x ≠ 0 → 0 < ω x * Real.sinh (x / 2) := fun x _ hx0 => by
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · have hp : 0 < shiftDifference a (-x) := shiftDifference_pos ha (by linarith)
      rw [shiftDifference_neg] at hp
      have hωn : ω x < 0 := by
        unfold ω shiftedGroundState
        exact div_neg_of_neg_of_pos (by linarith) (riemannKernelReal_pos x)
      exact mul_pos_of_neg_of_neg hωn (Real.sinh_neg_iff.mpr (by linarith))
    · exact absurd rfl hx0
    · have hp : 0 < shiftDifference a x := shiftDifference_pos ha hgt
      have hωp : 0 < ω x := by
        unfold ω shiftedGroundState
        exact div_pos hp (riemannKernelReal_pos x)
      exact mul_pos hωp (Real.sinh_pos_iff.mpr (by linarith))
  have hMnz : ∀ x ∈ Ioo (-c) c, x ≠ 0 → M x ≠ 0 := fun x hx hx0 hMz => by
    have hp := hω_sinh_pos x hx hx0
    rcases mul_eq_zero.mp hMz with h1 | h2
    · linarith [riemannKernelReal_pos x]
    · rw [h2, zero_mul] at hp; exact lt_irrefl 0 hp
  have hG₁ : ContDiff ℝ 2 G₁ := hF₁.add (contDiff_originExcisionPerturb ε hF₁)
  have hG₂ : ContDiff ℝ 2 G₂ := hF₂.add (contDiff_originExcisionPerturb ε hF₂)
  set u₁ := windowGaugeQuotient ε c' c M G₁
  set u₂ := windowGaugeQuotient ε c' c M G₂
  have hu₁ : ContDiff ℝ 2 u₁ := contDiff_windowGaugeQuotient hε0 hc
    (contDiff_riemannKernelReal.mul hω) hMnz hG₁
    (fun x hx => originExcisedProfile_eq_zero_near hε0 F₁ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₁supp hx)
  have hu₂ : ContDiff ℝ 2 u₂ := contDiff_windowGaugeQuotient hε0 hc
    (contDiff_riemannKernelReal.mul hω) hMnz hG₂
    (fun x hx => originExcisedProfile_eq_zero_near hε0 F₂ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₂supp hx)
  have hu₁c := hasCompactSupport_windowGaugeQuotient (ε := ε) hc M G₁
  have hu₂c := hasCompactSupport_windowGaugeQuotient (ε := ε) hc M G₂
  have hu₁e : ∀ x, u₁ (-x) = u₁ x := windowGaugeQuotient_even hModd (originExcisedProfile_odd ε hF₁odd)
  have hu₂e : ∀ x, u₂ (-x) = u₂ x := windowGaugeQuotient_even hModd (originExcisedProfile_odd ε hF₂odd)
  have hge₁ := hall u₁ hu₁ hu₁c hu₁e (fun x hx => windowGaugeQuotient_eq_zero_off hc M G₁ hx)
  have hge₂ := hall u₂ hu₂ hu₂c hu₂e (fun x hx => windowGaugeQuotient_eq_zero_off hc M G₂ hx)
  have eq₁ := shiftedGroundState_windowLower_eq_markovEnergy_sub ha hc0 hu₁ hu₁c hu₁e
  have eq₂ := shiftedGroundState_windowLower_eq_markovEnergy_sub ha hc0 hu₂ hu₂c hu₂e
  have hF₁_eq : phiDoobTest (fun y => ω y * u₁ y) = G₁ := funext fun x => by
    simp only [phiDoobTest, ← mul_assoc]
    exact windowGaugeQuotient_mul hε0 hc hMnz
      (fun y hy => originExcisedProfile_eq_zero_near hε0 F₁ hy)
      (fun y hy => originExcisedProfile_eq_zero_far ε hF₁supp hy) x
  have hF₂_eq : phiDoobTest (fun y => ω y * u₂ y) = G₂ := funext fun x => by
    simp only [phiDoobTest, ← mul_assoc]
    exact windowGaugeQuotient_mul hε0 hc hMnz
      (fun y hy => originExcisedProfile_eq_zero_near hε0 F₂ hy)
      (fun y hy => originExcisedProfile_eq_zero_far ε hF₂supp hy) x
  rw [hF₁_eq] at eq₁
  rw [hF₂_eq] at eq₂
  have hcs := two_profile_sinhQuotient_ge_halfNorm_sq hε0 hεc' hc hω hω_sinh_pos
    hG₁ (fun x hx => originExcisedProfile_eq_zero_near hε0 F₁ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₁supp hx)
    hG₂ (fun x hx => originExcisedProfile_eq_zero_near hε0 F₂ hx)
    (fun x hx => originExcisedProfile_eq_zero_far ε hF₂supp hx)
  dsimp only at hcs
  linarith

/-! ### 6. Even-sector outside-cosh obstruction for nonnegative theta gauges -/

/-- Any nonnegative theta gauge `M = Φω ≥ 0` that is strictly positive at a single point `x₀` outside
`[−c, c]` has strictly positive outside cosh charge `A/2 − coshCharge ω (−c, c) > 0`. -/
theorem outsideCosh_thetaGauge_pos_of_tail_pos {ι : Type*} (s : Finset ι) (α b : ι → ℝ)
    {c x₀ : ℝ} (hc : 0 ≤ c)
    (hM0 : ∀ x, 0 ≤ riemannKernelReal x * translateSpan s α b x)
    (hx₀ : c < |x₀|) (hMx₀ : 0 < riemannKernelReal x₀ * translateSpan s α b x₀) :
    0 < translateCoshCoefficient s α b / 2 - coshCharge (translateSpan s α b) (Ioo (-c) c) := by
  set ω := translateSpan s α b
  set m : ℝ → ℝ := fun x => riemannKernelReal x * ω x * Real.cosh (x / 2)
  have hm_cont : Continuous m := continuous_mul_cosh (contDiff_translateSpan s α b).continuous
  have hm_int : Integrable m := by
    have h : m = fun x => ∑ j ∈ s, α j * (riemannKernelReal (x - b j) * Real.cosh (x / 2)) := by
      funext x; simp only [m, thetaGauge_coordinate, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h]
    exact integrable_finsetSum _ fun j _ =>
      (integrable_riemannKernelReal_sub_mul_cosh_half (b j)).const_mul (α j)
  have hm_nn : ∀ x, 0 ≤ m x := fun x => mul_nonneg (hM0 x) (Real.cosh_pos _).le
  have hsplit := integral_add_compl (s := Ioo (-c) c) measurableSet_Ioo hm_int
  have htot : ∫ x, m x = translateCoshCoefficient s α b / 2 := integral_thetaGauge_mul_cosh s α b
  have hmx₀ : 0 < m x₀ := mul_pos hMx₀ (Real.cosh_pos _)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hm_cont.continuousAt (m x₀ / 2) (by linarith)
  set r := min (δ / 2) ((|x₀| - c) / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hsub : Icc (x₀ - r) (x₀ + r) ⊆ (Ioo (-c) c)ᶜ := fun x hx hmem => by
    have h1 := abs_lt.mpr hmem
    have h2 : |x₀| - |x| ≤ |x₀ - x| := abs_sub_abs_le_abs_sub x₀ x
    have h3 : |x₀ - x| ≤ r := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    linarith [min_le_right (δ / 2) ((|x₀| - c) / 2)]
  have hIcc_pos : 0 < ∫ x in Icc (x₀ - r) (x₀ + r), m x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (hm_cont.intervalIntegrable (x₀ - r) (x₀ + r)) (fun x hx => ?_) (by linarith)
    have hdist : dist x x₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      have := min_le_left (δ / 2) ((|x₀| - c) / 2)
      constructor <;> linarith [hx.1, hx.2]
    have hb := hball hdist
    rw [Real.dist_eq, abs_lt] at hb
    linarith [hb.1]
  have hcompl_ge : (∫ x in Icc (x₀ - r) (x₀ + r), m x) ≤ ∫ x in (Ioo (-c) c)ᶜ, m x :=
    setIntegral_mono_set (hm_int.integrableOn)
      (ae_restrict_of_forall_mem measurableSet_Ioo.compl fun x _ => hm_nn x)
      (Eventually.of_forall hsub)
  unfold coshCharge
  change 0 < translateCoshCoefficient s α b / 2 - ∫ x in Ioo (-c) c, m x
  linarith

/-- **Even-sector cosh-charged defect obstruction.** In any even theta gauge `ω = translateSpan s α b`
with `M = Φω ≥ 0` and positive mass somewhere outside `[−c, c]` (in particular every nonzero
combination with `α_j ≥ 0`), the cosh-charged subsolution defect
`Φω · (twoSidedGenerator ω − Φ cosh(x/2) ω) + 2σ_c(ω, (−c, c)) Φ² ω cosh(x/2)` is strictly negative
at every point where `ω(x) > 0`. -/
theorem evenThetaGauge_coshChargedDefect_neg {ι : Type*} (s : Finset ι) (α b : ι → ℝ)
    {c x₀ : ℝ} (hc : 0 ≤ c) (hB : translateSinhCoefficient s α b = 0)
    (hM0 : ∀ x, 0 ≤ riemannKernelReal x * translateSpan s α b x)
    (hx₀ : c < |x₀|) (hMx₀ : 0 < riemannKernelReal x₀ * translateSpan s α b x₀)
    {x : ℝ} (hωx : 0 < translateSpan s α b x) :
    (riemannKernelReal x * translateSpan s α b x) *
        (twoSidedGenerator (translateSpan s α b) x -
          riemannKernelReal x * Real.cosh (x / 2) * translateSpan s α b x +
          2 * coshCharge (translateSpan s α b) (Ioo (-c) c) *
            (riemannKernelReal x * Real.cosh (x / 2))) < 0 := by
  have hτ := outsideCosh_thetaGauge_pos_of_tail_pos s α b hc hM0 hx₀ hMx₀
  have hgen := twoSidedGenerator_translateSpan_sub_potential s α b x
  unfold translateSource at hgen
  rw [hB] at hgen
  have hΦ := riemannKernelReal_pos x
  have hch := Real.cosh_pos (x / 2)
  have hMx : 0 < riemannKernelReal x * translateSpan s α b x := mul_pos hΦ hωx
  nlinarith

/-- Corollary for every nonzero nonnegative-weight even theta gauge (`∀ j ∈ s, 0 ≤ α j`,
`∃ j₀ ∈ s, 0 < α j₀`): outside cosh charge is strictly positive on every bounded window. -/
theorem outsideCosh_pos_of_nonneg_weights {ι : Type*} (s : Finset ι) (α b : ι → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hα0 : ∀ j ∈ s, 0 ≤ α j) (hαpos : ∃ j ∈ s, 0 < α j) :
    0 < translateCoshCoefficient s α b / 2 - coshCharge (translateSpan s α b) (Ioo (-c) c) := by
  obtain ⟨j₀, hj₀, hαj₀⟩ := hαpos
  refine outsideCosh_thetaGauge_pos_of_tail_pos s α b hc (fun x => ?_)
    (x₀ := c + 1) (by rw [abs_of_pos (by linarith)]; linarith) ?_
  · rw [thetaGauge_coordinate]
    exact Finset.sum_nonneg fun j hj => mul_nonneg (hα0 j hj) (riemannKernelReal_pos _).le
  · rw [thetaGauge_coordinate]
    exact Finset.sum_pos' (fun j hj => mul_nonneg (hα0 j hj) (riemannKernelReal_pos _).le)
      ⟨j₀, hj₀, mul_pos hαj₀ (riemannKernelReal_pos _)⟩

end GaloisForLFunctions.SignedWindowCriticality.BelowLogFour

end
