import GaloisForLFunctions.RHTower.ThetaCuspC5CoupledSturmTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
/-! Denominator-clock comparison for the complete C5 source.
The actual numerator J3 divided by sinh(k D2) strictly decreases, where
k^2=9/(2c(u)) and D2 is the first Green denominator. The positive Green
kernel transports this shape order to a strict flux-growth comparison.
The full Bose compensation strictly exceeds the corresponding explicit
comparison integral after positive rescaling. Positivity of that remaining
comparison integral and arbitrary-degree positivity are not asserted. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section


local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "e" => completedCurvatureEven
local notation "d" => completedLocalDenominator
local notation "d₁" => descentDenominatorJet
local notation "y" => completedFirstDenominator
local notation "J" => localDescentNumerator
local notation "J₁" => localDescentNumeratorJet
local notation "J₂" => localDescentNumeratorJetTwo

theorem completedCurvatureEven_monotoneOn (u : ℝ) : MonotoneOn (e u) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro s _
    exact (hasDerivAt_completedCurvatureEven u s).continuousAt.continuousWithinAt
  · intro s _
    exact (hasDerivAt_completedCurvatureEven u s).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs0 : 0 ≤ s := interior_subset hs
    rw [(hasDerivAt_completedCurvatureEven u s).deriv]
    exact div_nonneg (sub_nonneg.mpr (thetaCuspLogCurvatureJet_strictMono.monotone (by linarith))) (by norm_num)

theorem centerCurvature_le_completedCurvatureEven (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    c u ≤ e u t := by
  have h := completedCurvatureEven_monotoneOn u (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) ht ht
  simpa only [completedCurvatureEven,add_zero,sub_zero,add_self_div_two] using h

def denominatorClockRate (u : ℝ) : ℝ := Real.sqrt (9/(2*c u))
def denominatorClockProfile (u t : ℝ) : ℝ := Real.sinh (denominatorClockRate u*y u t)
def denominatorClockProfileJet (u t : ℝ) : ℝ :=
  denominatorClockRate u*d u t*Real.cosh (denominatorClockRate u*y u t)
def denominatorClockProfileJetTwo (u t : ℝ) : ℝ :=
  denominatorClockRate u*d₁ u t*Real.cosh (denominatorClockRate u*y u t)+
    (denominatorClockRate u)^2*(d u t)^2*denominatorClockProfile u t

theorem denominatorClockRate_pos (u : ℝ) : 0 < denominatorClockRate u := by
  unfold denominatorClockRate
  exact Real.sqrt_pos.mpr (div_pos (by norm_num) (mul_pos (by norm_num) (thetaCuspLogCurvature_pos u)))

theorem denominatorClockRate_sq (u : ℝ) : (denominatorClockRate u)^2*(2*c u)=9 := by
  have hcpos := thetaCuspLogCurvature_pos u
  rw [denominatorClockRate,Real.sq_sqrt (by positivity : 0 ≤ 9/(2*c u))]
  have hc := (thetaCuspLogCurvature_pos u).ne'
  field_simp

theorem denominatorClockProfile_zero (u : ℝ) : denominatorClockProfile u 0=0 := by
  simp only [denominatorClockProfile,completedFirstDenominator_zero,mul_zero,Real.sinh_zero]

theorem denominatorClockProfile_pos (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < denominatorClockProfile u t := by
  exact Real.sinh_pos_iff.mpr (mul_pos (denominatorClockRate_pos u) (completedFirstDenominator_pos u ht))

theorem hasDerivAt_denominatorClockProfile (u t : ℝ) :
    HasDerivAt (denominatorClockProfile u) (denominatorClockProfileJet u t) t := by
  convert! (Real.hasDerivAt_sinh (denominatorClockRate u*y u t)).comp t
    ((hasDerivAt_completedFirstDenominator u t).const_mul (denominatorClockRate u)) using 1
  unfold denominatorClockProfileJet
  ring

theorem hasDerivAt_denominatorClockProfileJet (u t : ℝ) :
    HasDerivAt (denominatorClockProfileJet u) (denominatorClockProfileJetTwo u t) t := by
  have hd : HasDerivAt (d u) (d₁ u t) t := hasDerivAt_completedLocalDenominator u t
  have hc := (Real.hasDerivAt_cosh (denominatorClockRate u*y u t)).comp t
    ((hasDerivAt_completedFirstDenominator u t).const_mul (denominatorClockRate u))
  convert! (hd.const_mul (denominatorClockRate u)).mul hc using 1
  dsimp only [Function.comp_apply]
  unfold denominatorClockProfileJetTwo denominatorClockProfile
  ring

theorem denominatorClock_potential_dominates (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    18*e u t ≤ (denominatorClockRate u)^2*(d u t)^2 := by
  have hc := thetaCuspLogCurvature_pos u
  have he := completedCurvatureEven_pos u t
  have hce := centerCurvature_le_completedCurvatureEven u ht
  have hvel := thetaCuspLogCurvatureJet_strictMono.monotone (show u-t ≤ u+t by linarith)
  have hprod := mul_nonneg ht (div_nonneg (sub_nonneg.mpr hvel) (by norm_num : (0:ℝ) ≤ 2))
  have hd : 2*e u t ≤ d u t := by unfold completedLocalDenominator; linarith only [hprod]
  have hsq : 4*(e u t)^2 ≤ (d u t)^2 := by nlinarith only [hd,he]
  have h1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg (denominatorClockRate u))
  have h2 := mul_nonneg he.le (sub_nonneg.mpr hce)
  have hk := denominatorClockRate_sq u
  have h3 := mul_nonneg (sq_nonneg (denominatorClockRate u)) h2
  have hke := congrArg (fun z : ℝ => z*e u t) hk
  nlinarith only [h1,h3,hke]

def denominatorClockWronskian (u t : ℝ) : ℝ :=
  (J₁ u t*denominatorClockProfile u t-J u t*denominatorClockProfileJet u t)/d u t

theorem localDescentNumerator_zero (u : ℝ) : J u 0=0 := by
  simp only [localDescentNumerator,add_zero,sub_zero,sub_self,zero_div,mul_zero,zero_mul,add_zero]

theorem denominatorClockWronskian_zero (u : ℝ) : denominatorClockWronskian u 0=0 := by
  simp only [denominatorClockWronskian,denominatorClockProfile_zero,localDescentNumerator_zero,
    mul_zero,zero_mul,sub_self,zero_div]

theorem hasDerivAt_denominatorClockWronskian (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (denominatorClockWronskian u)
      (((J₂ u t*denominatorClockProfile u t-J u t*denominatorClockProfileJetTwo u t)*d u t-
        (J₁ u t*denominatorClockProfile u t-J u t*denominatorClockProfileJet u t)*d₁ u t)/(d u t)^2) t := by
  have hd : HasDerivAt (d u) (d₁ u t) t := hasDerivAt_completedLocalDenominator u t
  convert! (((hasDerivAt_localDescentNumeratorJet u t).mul (hasDerivAt_denominatorClockProfile u t)).sub
    ((hasDerivAt_localDescentNumerator u t).mul (hasDerivAt_denominatorClockProfileJet u t))).div
    hd (completedLocalDenominator_pos_nonneg u ht).ne' using 1
  dsimp only [Pi.sub_apply,Pi.mul_apply]
  ring

theorem denominatorClockWronskian_strictAntiOn (u : ℝ) :
    StrictAntiOn (denominatorClockWronskian u) (Icc 0 u) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_denominatorClockWronskian u ht.1).continuousAt.continuousWithinAt
  · intro t ht
    have htu : t ∈ Ioo 0 u := by simpa only [interior_Icc] using ht
    rw [(hasDerivAt_denominatorClockWronskian u htu.1.le).deriv]
    have hd := completedLocalDenominator_pos_nonneg u htu.1.le
    have hP := denominatorClockProfile_pos u htu.1
    have hJ := localDescentNumerator_pos htu.1 htu.2.le
    have hL := localDescentNumerator_sturm_subsolution htu.1 htu.2.le
    rw [iteratedDeriv_two_localDescentNumerator,(hasDerivAt_localDescentNumerator u t).deriv,
      (hasDerivAt_completedLocalDenominator u t).deriv] at hL
    change J₂ u t-(d₁ u t/d u t)*J₁ u t < 18*e u t*J u t at hL
    have hc := denominatorClock_potential_dominates u htu.1.le
    have hLm := mul_lt_mul_of_pos_right hL hd
    have heq : (J₂ u t-(d₁ u t/d u t)*J₁ u t)*d u t = J₂ u t*d u t-d₁ u t*J₁ u t := by
      field_simp [hd.ne']
    rw [heq] at hLm
    have h1 := mul_lt_mul_of_pos_right hLm hP
    have h2 := mul_le_mul_of_nonneg_right hc (mul_nonneg hJ.le (mul_nonneg hd.le hP.le))
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos hd)
    unfold denominatorClockProfileJetTwo denominatorClockProfileJet
    nlinarith only [h1,h2]

theorem denominatorClockWronskian_neg {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    denominatorClockWronskian u t < 0 := by
  have hu := ht.trans_le htu
  have h := denominatorClockWronskian_strictAntiOn u
    (show (0:ℝ) ∈ Icc 0 u from ⟨le_rfl,hu.le⟩) ⟨ht.le,htu⟩ ht
  simpa only [denominatorClockWronskian_zero] using h

def denominatorClockSourceRatio (u t : ℝ) : ℝ := J u t/denominatorClockProfile u t

theorem hasDerivAt_denominatorClockSourceRatio (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (denominatorClockSourceRatio u)
      (d u t*denominatorClockWronskian u t/(denominatorClockProfile u t)^2) t := by
  have hd := completedLocalDenominator_pos_nonneg u ht.le
  convert! (hasDerivAt_localDescentNumerator u t).div (hasDerivAt_denominatorClockProfile u t)
    (denominatorClockProfile_pos u ht).ne' using 1
  unfold denominatorClockWronskian
  field_simp [hd.ne']

theorem denominatorClockSourceRatio_strictAntiOn (u : ℝ) :
    StrictAntiOn (denominatorClockSourceRatio u) (Ioc 0 u) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
  · intro t ht
    exact (hasDerivAt_denominatorClockSourceRatio u ht.1).continuousAt.continuousWithinAt
  · intro t ht
    have htu : t ∈ Ioc 0 u := interior_subset ht
    rw [(hasDerivAt_denominatorClockSourceRatio u htu.1).deriv]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (completedLocalDenominator_pos_nonneg u htu.1.le)
        (denominatorClockWronskian_neg htu.1 htu.2))
      (sq_pos_of_pos (denominatorClockProfile_pos u htu.1))


def denominatorClockDensity (u s : ℝ) : ℝ := denominatorClockProfile u s/(d u s)^2

def denominatorClockGreenMass (u t : ℝ) : ℝ :=
  4*∫ s in (0:ℝ)..t, denominatorClockDensity u s*descentGreenKernel u t s

def denominatorClockGreenOuter (u t : ℝ) : ℝ :=
  4*∫ s in (0:ℝ)..t, denominatorClockDensity u s*descentGreenKernelOuter u t s

private theorem clockDensity_continuousOn (u : ℝ) {t : ℝ} :
    ContinuousOn (denominatorClockDensity u) (Icc 0 t) := by
  intro s hs
  exact ((hasDerivAt_denominatorClockProfile u s).continuousAt.div
    ((hasDerivAt_completedLocalDenominator u s).continuousAt.pow 2)
    (pow_ne_zero _ (completedLocalDenominator_pos_nonneg u hs.1).ne')).continuousWithinAt

private theorem sourceDensity_continuousOn (u : ℝ) {t : ℝ} :
    ContinuousOn (localDescentDensity u) (Icc 0 t) := by
  intro s hs
  exact ((hasDerivAt_localDescentNumerator u s).continuousAt.div
    ((hasDerivAt_completedLocalDenominator u s).continuousAt.pow 2)
    (pow_ne_zero _ (completedLocalDenominator_pos_nonneg u hs.1).ne')).continuousWithinAt

private theorem density_cross_pos {u a b : ℝ} (ha : 0 < a) (hab : a < b) (hbu : b ≤ u) :
    0 < localDescentDensity u a*denominatorClockDensity u b-
      localDescentDensity u b*denominatorClockDensity u a := by
  have h := denominatorClockSourceRatio_strictAntiOn u ⟨ha,hab.le.trans hbu⟩
    ⟨ha.trans hab,hbu⟩ hab
  have he := (div_lt_div_iff₀ (denominatorClockProfile_pos u (ha.trans hab))
    (denominatorClockProfile_pos u ha)).mp h
  have hd1 := completedLocalDenominator_pos_nonneg u ha.le
  have hd2 := completedLocalDenominator_pos_nonneg u (ha.trans hab).le
  have heq : localDescentDensity u a*denominatorClockDensity u b-
      localDescentDensity u b*denominatorClockDensity u a =
      (J u a*denominatorClockProfile u b-J u b*denominatorClockProfile u a)/((d u a)^2*(d u b)^2) := by
    unfold localDescentDensity denominatorClockDensity
    field_simp
  rw [heq]
  exact div_pos (by nlinarith only [he]) (mul_pos (sq_pos_of_pos hd1) (sq_pos_of_pos hd2))

private theorem green_cross_pos {u t a b : ℝ} (ha : 0 < a) (hab : a < b) (hbt : b ≤ t) :
    0 < descentGreenKernel u t a*descentGreenKernelOuter u t b-
      descentGreenKernelOuter u t a*descentGreenKernel u t b := by
  rcases eq_or_lt_of_le hbt with rfl | hbt
  · rw [descentGreenKernel_self,mul_zero,sub_zero]
    exact mul_pos (descentGreenKernel_pos u ha hab)
      (descentGreenKernelOuter_pos u (ha.trans hab) le_rfl)
  · have ht := ha.trans (hab.trans hbt)
    have h := descentGreenLogGrowth_strictMonoOn u ht ⟨ha,hab.trans hbt⟩ ⟨ha.trans hab,hbt⟩ hab
    have he := (div_lt_div_iff₀ (descentGreenKernel_pos u ha (hab.trans hbt))
      (descentGreenKernel_pos u (ha.trans hab) hbt)).mp h
    nlinarith only [he]

private def clockGreenCross (u t a b : ℝ) : ℝ :=
  (localDescentDensity u a*denominatorClockDensity u b-localDescentDensity u b*denominatorClockDensity u a)*
    (descentGreenKernel u t a*descentGreenKernelOuter u t b-
      descentGreenKernelOuter u t a*descentGreenKernel u t b)

private theorem clockGreenCross_pos {u t a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hbt : b ≤ t) (htu : t ≤ u) : 0 < clockGreenCross u t a b :=
  mul_pos (density_cross_pos ha hab (hbt.trans htu)) (green_cross_pos ha hab hbt)

private theorem clockGreenCross_nonneg {u t a b : ℝ} (ha : a ∈ Icc 0 t)
    (hb : b ∈ Icc 0 t) (htu : t ≤ u) : 0 ≤ clockGreenCross u t a b := by
  rcases eq_or_lt_of_le ha.1 with rfl | ha0
  · simp [clockGreenCross,localDescentDensity,localDescentNumerator_zero,
      denominatorClockDensity,denominatorClockProfile_zero]
  rcases eq_or_lt_of_le hb.1 with rfl | hb0
  · simp [clockGreenCross,localDescentDensity,localDescentNumerator_zero,
      denominatorClockDensity,denominatorClockProfile_zero]
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact (clockGreenCross_pos ha0 hab hb.2 htu).le
  · simp only [clockGreenCross,sub_self,zero_mul,le_refl]
  · have he : clockGreenCross u t a b=clockGreenCross u t b a := by unfold clockGreenCross; ring
    rw [he]
    exact (clockGreenCross_pos hb0 hba ha.2 htu).le

/-- Strict growth comparison after the signed source shape passes through the positive Green kernel. -/
theorem denominatorClockGreen_growth_comparison {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    (-thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet u t)*denominatorClockGreenMass u t <
      (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t)*denominatorClockGreenOuter u t := by
  let A := localDescentDensity u
  let B := denominatorClockDensity u
  let G := descentGreenKernel u t
  let T := descentGreenKernelOuter u t
  have hA : ContinuousOn A (Icc 0 t) := sourceDensity_continuousOn u
  have hB : ContinuousOn B (Icc 0 t) := clockDensity_continuousOn u
  have hG : ContinuousOn G (Icc 0 t) := fun s _ =>
    (hasDerivAt_descentGreenKernel_inner u t s).continuousAt.continuousWithinAt
  have hT : ContinuousOn T (Icc 0 t) := fun s _ =>
    (hasDerivAt_descentGreenKernelOuter_inner u t s).continuousAt.continuousWithinAt
  have hiAG : IntervalIntegrable (fun s => A s*G s) volume 0 t := (hA.mul hG).intervalIntegrable_of_Icc ht.le
  have hiAT : IntervalIntegrable (fun s => A s*T s) volume 0 t := (hA.mul hT).intervalIntegrable_of_Icc ht.le
  have hiBG : IntervalIntegrable (fun s => B s*G s) volume 0 t := (hB.mul hG).intervalIntegrable_of_Icc ht.le
  have hiBT : IntervalIntegrable (fun s => B s*T s) volume 0 t := (hB.mul hT).intervalIntegrable_of_Icc ht.le
  let M : ℝ → ℝ := fun s =>
    A s*G s*(∫ r in (0:ℝ)..t, B r*T r)-A s*T s*(∫ r in (0:ℝ)..t, B r*G r)-
      B s*G s*(∫ r in (0:ℝ)..t, A r*T r)+B s*T s*(∫ r in (0:ℝ)..t, A r*G r)
  have hM : ContinuousOn M (Icc 0 t) := by
    exact ((((hA.mul hG).mul continuousOn_const).sub ((hA.mul hT).mul continuousOn_const)).sub
      ((hB.mul hG).mul continuousOn_const)).add ((hB.mul hT).mul continuousOn_const)
  have hMeq (s : ℝ) : M s=∫ r in (0:ℝ)..t, clockGreenCross u t s r := by
    have heq (r : ℝ) : clockGreenCross u t s r=
        (A s*G s)*(B r*T r)-(A s*T s)*(B r*G r)-
          (B s*G s)*(A r*T r)+(B s*T s)*(A r*G r) := by
      dsimp only [clockGreenCross,A,B,G,T]
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_add (((hiBT.const_mul _).sub (hiBG.const_mul _)).sub (hiAT.const_mul _))
        (hiAG.const_mul _),
      intervalIntegral.integral_sub ((hiBT.const_mul _).sub (hiBG.const_mul _)) (hiAT.const_mul _),
      intervalIntegral.integral_sub (hiBT.const_mul _) (hiBG.const_mul _)]
    simp only [intervalIntegral.integral_const_mul,M]
  have hMnonneg (s : ℝ) (hs : s ∈ Icc 0 t) : 0 ≤ M s := by
    rw [hMeq]
    exact intervalIntegral.integral_nonneg ht.le (fun r hr => clockGreenCross_nonneg hs hr htu)
  have hMpos : 0 < M (t/3) := by
    have hs : t/3 ∈ Icc 0 t := by constructor <;> linarith
    have hcross : ContinuousOn (clockGreenCross u t (t/3)) (Icc 0 t) := by
      exact ((continuousOn_const.mul hB).sub (hA.mul continuousOn_const)).mul
        ((continuousOn_const.mul hT).sub (continuousOn_const.mul hG))
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
      continuousOn_const hcross (fun r hr => clockGreenCross_nonneg hs ⟨hr.1.le,hr.2⟩ htu)
      ⟨2*t/3,⟨by linarith,by linarith⟩,clockGreenCross_pos (by linarith) (by linarith) (by linarith) htu⟩
    simpa only [intervalIntegral.integral_zero,←hMeq] using h
  have hI : 0 < ∫ s in (0:ℝ)..t, M s := by
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
      continuousOn_const hM (fun s hs => hMnonneg s ⟨hs.1.le,hs.2⟩)
      ⟨t/3,⟨by linarith,by linarith⟩,hMpos⟩
    simpa only [intervalIntegral.integral_zero] using h
  have hIeq : (∫ s in (0:ℝ)..t, M s)=
      2*((∫ s in (0:ℝ)..t,A s*G s)*(∫ s in (0:ℝ)..t,B s*T s)-
        (∫ s in (0:ℝ)..t,A s*T s)*(∫ s in (0:ℝ)..t,B s*G s)) := by
    dsimp only [M]
    rw [intervalIntegral.integral_add (((hiAG.mul_const _).sub (hiAT.mul_const _)).sub (hiBG.mul_const _))
        (hiBT.mul_const _),
      intervalIntegral.integral_sub ((hiAG.mul_const _).sub (hiAT.mul_const _)) (hiBG.mul_const _),
      intervalIntegral.integral_sub (hiAG.mul_const _) (hiAT.mul_const _)]
    simp only [intervalIntegral.integral_mul_const]
    ring
  rw [hIeq] at hI
  rw [neg_centerTimeJet_eq_positive_integral u ht.le,neg_centerNumerator_eq_positive_integral u ht.le]
  dsimp only [denominatorClockGreenMass,denominatorClockGreenOuter,A,B,G,T] at hI ⊢
  nlinarith only [hI]


theorem denominatorClockGreenMass_pos (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < denominatorClockGreenMass u t := by
  have hG : ContinuousOn (descentGreenKernel u t) (Icc 0 t) := fun s _ =>
    (hasDerivAt_descentGreenKernel_inner u t s).continuousAt.continuousWithinAt
  have hpos (s : ℝ) (hs : s ∈ Ioo 0 t) :
      0 < denominatorClockDensity u s*descentGreenKernel u t s := by
    exact mul_pos (div_pos (denominatorClockProfile_pos u hs.1)
      (sq_pos_of_pos (completedLocalDenominator_pos_nonneg u hs.1.le)))
      (descentGreenKernel_pos u hs.1 hs.2)
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    continuousOn_const ((clockDensity_continuousOn u).mul hG)
    (fun s hs => by
      rcases eq_or_lt_of_le hs.2 with rfl | hst
      · simp only [Pi.mul_apply,descentGreenKernel_self,mul_zero,le_refl]
      · exact (hpos s ⟨hs.1,hst⟩).le)
    ⟨t/2,⟨by linarith,by linarith⟩,hpos (t/2) ⟨by linarith,by linarith⟩⟩
  simp only [intervalIntegral.integral_zero] at hi
  exact mul_pos (by norm_num : (0:ℝ)<4) hi

def denominatorClockGreenCompensation (u t : ℝ) : ℝ :=
  (c5CompletedBoseWeight u t-5)*denominatorClockGreenMass u t-
    5*t*denominatorClockGreenOuter u t

/-- The complete Bose compensation strictly exceeds its denominator-clock comparison. -/
theorem denominatorClock_compensation_transfer {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t)*denominatorClockGreenCompensation u t <
      c5CompletedCompensationMargin u t*denominatorClockGreenMass u t := by
  have h := mul_lt_mul_of_pos_left (denominatorClockGreen_growth_comparison ht htu.le)
    (show 0 < 5*t by positivity)
  rw [c5CompletedCompensationMargin_eq_excess_form ht htu]
  unfold denominatorClockGreenCompensation c5CompletedScalingExcess
  nlinarith only [h]


private theorem completedLocalDenominator_pos_all (u t : ℝ) : 0 < d u t := by
  rcases le_or_gt 0 t with ht | ht
  · exact completedLocalDenominator_pos_nonneg u ht
  · have hp := thetaCuspLogCurvatureJet_strictMono.monotone (show u+t ≤ u-t by linarith)
    have hm := mul_nonneg_of_nonpos_of_nonpos ht.le
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) (by norm_num : (0:ℝ) ≤ 2))
    have he := completedCurvatureEven_pos u t
    unfold completedLocalDenominator
    linarith only [he,hm]

private theorem clockDensity_continuous (u : ℝ) : Continuous (denominatorClockDensity u) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_denominatorClockProfile u t).continuousAt.div
    ((hasDerivAt_completedLocalDenominator u t).continuousAt.pow 2)
    (pow_ne_zero _ (completedLocalDenominator_pos_all u t).ne')

/-- The explicit comparison integral has the asserted outer derivative, including its moving endpoint. -/
theorem hasDerivAt_denominatorClockGreenMass (u t : ℝ) :
    HasDerivAt (denominatorClockGreenMass u) (denominatorClockGreenOuter u t) t := by
  let B := denominatorClockDensity u
  let D := descentDenominator u
  let Y := y u
  let f₁ : ℝ → ℝ := fun s => B s*D s
  let f₂ : ℝ → ℝ := fun s => B s*Y s
  let f₃ : ℝ → ℝ := fun s => s*B s*Y s
  let I₁ : ℝ → ℝ := fun s => ∫ r in (0:ℝ)..s, f₁ r
  let I₂ : ℝ → ℝ := fun s => ∫ r in (0:ℝ)..s, f₂ r
  let I₃ : ℝ → ℝ := fun s => ∫ r in (0:ℝ)..s, f₃ r
  have hD : Continuous D := continuous_iff_continuousAt.mpr
    (fun s => (hasDerivAt_mul_completedDecayEvenPrimitive u s).continuousAt)
  have hY : Continuous Y := continuous_iff_continuousAt.mpr
    (fun s => (hasDerivAt_completedFirstDenominator u s).continuousAt)
  have hB : Continuous B := clockDensity_continuous u
  have h₁ : Continuous f₁ := hB.mul hD
  have h₂ : Continuous f₂ := hB.mul hY
  have h₃ : Continuous f₃ := (continuous_id.mul hB).mul hY
  have hi₁ (s : ℝ) : IntervalIntegrable f₁ volume 0 s := h₁.intervalIntegrable 0 s
  have hi₂ (s : ℝ) : IntervalIntegrable f₂ volume 0 s := h₂.intervalIntegrable 0 s
  have hi₃ (s : ℝ) : IntervalIntegrable f₃ volume 0 s := h₃.intervalIntegrable 0 s
  have hd₁ : HasDerivAt I₁ (f₁ t) t := intervalIntegral.integral_hasDerivAt_right
    (hi₁ t) (h₁.stronglyMeasurableAtFilter volume (nhds t)) h₁.continuousAt
  have hd₂ : HasDerivAt I₂ (f₂ t) t := intervalIntegral.integral_hasDerivAt_right
    (hi₂ t) (h₂.stronglyMeasurableAtFilter volume (nhds t)) h₂.continuousAt
  have hd₃ : HasDerivAt I₃ (f₃ t) t := intervalIntegral.integral_hasDerivAt_right
    (hi₃ t) (h₃.stronglyMeasurableAtFilter volume (nhds t)) h₃.continuousAt
  have hmass : denominatorClockGreenMass u=
      (fun s => 4*(Y s*I₁ s+(s*Y s-D s)*I₂ s-Y s*I₃ s)) := by
    funext s
    have heq (r : ℝ) : denominatorClockDensity u r*descentGreenKernel u s r=
        Y s*f₁ r+(s*Y s-D s)*f₂ r-Y s*f₃ r := by
      dsimp only [f₁,f₂,f₃,B,D,Y,descentGreenKernel]
      ring
    unfold denominatorClockGreenMass
    simp_rw [heq]
    rw [intervalIntegral.integral_sub ((hi₁ s).const_mul _ |>.add ((hi₂ s).const_mul _))
      ((hi₃ s).const_mul _),intervalIntegral.integral_add ((hi₁ s).const_mul _) ((hi₂ s).const_mul _)]
    simp only [intervalIntegral.integral_const_mul,I₁,I₂,I₃]
  have houter : denominatorClockGreenOuter u t=4*d u t*(I₁ t+t*I₂ t-I₃ t) := by
    have heq (r : ℝ) : denominatorClockDensity u r*descentGreenKernelOuter u t r=
        d u t*f₁ r+(d u t*t)*f₂ r-d u t*f₃ r := by
      dsimp only [f₁,f₂,f₃,B,D,Y,descentGreenKernelOuter]
      ring
    unfold denominatorClockGreenOuter
    simp_rw [heq]
    rw [intervalIntegral.integral_sub ((hi₁ t).const_mul _ |>.add ((hi₂ t).const_mul _))
      ((hi₃ t).const_mul _),intervalIntegral.integral_add ((hi₁ t).const_mul _) ((hi₂ t).const_mul _)]
    simp only [intervalIntegral.integral_const_mul,I₁,I₂,I₃]
    ring
  rw [hmass,houter]
  have hy : HasDerivAt Y (d u t) t := hasDerivAt_completedFirstDenominator u t
  have hd : HasDerivAt D (Y t) t := hasDerivAt_mul_completedDecayEvenPrimitive u t
  convert! (((hy.mul hd₁).add ((((hasDerivAt_id t).mul hy).sub hd).mul hd₂)).sub (hy.mul hd₃)).const_mul 4 using 1
  dsimp only [Pi.mul_apply,Pi.sub_apply,Pi.add_apply,f₁,f₂,f₃,id_eq]
  ring

end
end RHTower.ThetaCuspDefect
