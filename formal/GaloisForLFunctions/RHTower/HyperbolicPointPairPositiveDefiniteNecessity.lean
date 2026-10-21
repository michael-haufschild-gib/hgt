import GaloisForLFunctions.RHTower.HyperbolicPointPairFormHorocyclicCoordinates
import GaloisForLFunctions.RHTower.BochnerConeFejerTrapezoidWindows

/-!
# Positive definite point-pair kernels have Abel transform in the Bochner cone

A continuous profile `k` vanishing on `(R, ∞)` defines a **positive definite** point-pair kernel if
`Re Q_k(g) ≥ 0` for every continuous compactly supported `g : ℍ → ℂ`
(`IsPositiveDefinitePointPair`).  Then the Abel transform `𝒜k` lies in the Bochner cone
(`isBochnerPositive_abelTransform`), and the Selberg transform is nonnegative on the critical line
(`selbergTransform_critical_re_nonneg`).

**Proof.**  Test with the horocyclic wave packet `g_L(x + iy) = φ_L(x) β(y)`, where `φ_L` is the
Fejér trapezoid and `β(y) = f(log y) √y`.  Integrating over `y, y'` first,
`Q_k(g_L) = ∫∫ W(x − x') φ_L(x) φ_L(x') dx dx'` with
`W(t) = ∫∫ y⁻² y'⁻² β(y) β̄(y') k((t² + (y − y')²)/(4yy')) dy dy'` continuous with compact support, so
`Q_k(g_L) = 2L ∫ W + O(1)` (Fejér).  By the horocyclic slice
`∫ W = ∫∫ y⁻² y'⁻² β(y) β̄(y') √(yy') 𝒜k(log y − log y') dy dy'`, and `y = e^a`, `y' = e^b` turn this
into the Bochner form `∫∫ 𝒜k(a − b) f(a) f̄(b) da db`.  Positivity for all `L` forces
`Re ∫ W ≥ 0`.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.RHTower.MehlerFock

open DeckPointPair

/-- **Positive definiteness** of the point-pair kernel `k(u(z, w))` on `ℍ`. -/
def IsPositiveDefinitePointPair (k : ℝ → ℝ) : Prop :=
  ∀ g : ℍ → ℂ, Continuous g → HasCompactSupport g → 0 ≤ (pointPairForm k g).re

/-! ### Reordering four integrations -/

/-- For an integrand integrable on `(ℝ × ℝ) × (ℝ × ℝ)`, `∫_y ∫_{y'} ∫_x ∫_{x'} = ∫_x ∫_{x'} ∫_y ∫_{y'}`. -/
theorem integral4_swap {F : ℝ → ℝ → ℝ → ℝ → ℂ}
    (hF : Integrable (fun r : (ℝ × ℝ) × (ℝ × ℝ) => F r.1.1 r.1.2 r.2.1 r.2.2)) :
    ∫ y, ∫ y', ∫ x, ∫ x', F y y' x x' = ∫ x, ∫ x', ∫ y, ∫ y', F y y' x x' := by
  set G : (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun r => F r.1.1 r.1.2 r.2.1 r.2.2 with hG
  have hG' : Integrable G ((volume.prod volume).prod (volume.prod volume)) := by
    simpa only [← Measure.volume_eq_prod] using hF
  -- the order `(y, y')` outside
  have hL : ∫ r, G r ∂((volume.prod volume).prod (volume.prod volume)) =
      ∫ y, ∫ y', ∫ x, ∫ x', F y y' x x' := by
    rw [integral_prod _ hG']
    have hH := hG'.integral_prod_left
    rw [integral_prod _ hH]
    have hae := Measure.ae_ae_of_ae_prod hG'.prod_right_ae
    refine integral_congr_ae (hae.mono fun y hy => integral_congr_ae (hy.mono fun y' hy' => ?_))
    exact integral_prod _ hy'
  -- the order `(x, x')` outside
  have hR : ∫ r, G r ∂((volume.prod volume).prod (volume.prod volume)) =
      ∫ x, ∫ x', ∫ y, ∫ y', F y y' x x' := by
    rw [integral_prod_symm _ hG']
    have hH := hG'.integral_prod_right
    rw [integral_prod _ hH]
    have hae := Measure.ae_ae_of_ae_prod hG'.prod_left_ae
    refine integral_congr_ae (hae.mono fun x hx => integral_congr_ae (hx.mono fun x' hx' => ?_))
    exact integral_prod _ hx'
  rw [← hL, hR]

/-! ### The horocyclic wave packets -/

/-- `β(y) = f(log y) √y` for `y > 0`, and `0` for `y ≤ 0`. -/
def logChartWeight (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  if 0 < y then f (Real.log y) * (Real.sqrt y : ℂ) else 0

/-- The horocyclic wave packet `g_L(x + iy) = φ_L(x) β(y)`. -/
def horocyclicPacket (L : ℝ) (f : ℝ → ℂ) (z : ℍ) : ℂ :=
  (fejerTrapezoid L z.re : ℂ) * logChartWeight f z.im

theorem logChartWeight_of_pos (f : ℝ → ℂ) {y : ℝ} (hy : 0 < y) :
    logChartWeight f y = f (Real.log y) * (Real.sqrt y : ℂ) := if_pos hy

theorem logChartWeight_of_nonpos (f : ℝ → ℂ) {y : ℝ} (hy : y ≤ 0) : logChartWeight f y = 0 :=
  if_neg (not_lt.mpr hy)

section Packet

variable {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
include hf hfc

omit hfc in
theorem continuous_horocyclicPacket (L : ℝ) : Continuous (horocyclicPacket L f) := by
  have h : horocyclicPacket L f = fun z : ℍ => (fejerTrapezoid L z.re : ℂ) *
      (f (Real.log z.im) * (Real.sqrt z.im : ℂ)) := by
    funext z; rw [horocyclicPacket, logChartWeight_of_pos f z.im_pos]
  rw [h]
  have hre : Continuous fun z : ℍ => z.re := UpperHalfPlane.continuous_re
  have him : Continuous fun z : ℍ => z.im := UpperHalfPlane.continuous_im
  exact (continuous_ofReal.comp ((continuous_fejerTrapezoid L).comp hre)).mul
    ((hf.comp (Real.continuousOn_log.comp_continuous him fun z => z.im_pos.ne')).mul
      (continuous_ofReal.comp (Real.continuous_sqrt.comp him)))

omit hf in
/-- The support of `f` lies in `[-A, A]`. -/
theorem exists_abs_le_of_ne_zero_of_compactSupport : ∃ A : ℝ, 0 ≤ A ∧ ∀ t, f t ≠ 0 → |t| ≤ A := by
  obtain ⟨A, hA⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max A 0, le_max_right _ _, fun t ht => ?_⟩
  have := hA (subset_tsupport f ht)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

omit hf hfc in
theorem logChartWeight_ne_zero {A : ℝ} (hA : ∀ t, f t ≠ 0 → |t| ≤ A) {y : ℝ}
    (hy : logChartWeight f y ≠ 0) : Real.exp (-A) ≤ y ∧ y ≤ Real.exp A := by
  have hy0 : 0 < y := by
    by_contra h; exact hy (logChartWeight_of_nonpos f (not_lt.mp h))
  rw [logChartWeight_of_pos f hy0] at hy
  have hlog := abs_le.mp (hA _ (left_ne_zero_of_mul hy))
  constructor
  · calc Real.exp (-A) ≤ Real.exp (Real.log y) := Real.exp_le_exp.mpr hlog.1
      _ = y := Real.exp_log hy0
  · calc y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
      _ ≤ Real.exp A := Real.exp_le_exp.mpr hlog.2

omit hf in
theorem hasCompactSupport_horocyclicPacket (L : ℝ) : HasCompactSupport (horocyclicPacket L f) := by
  obtain ⟨A, -, hA⟩ := exists_abs_le_of_ne_zero_of_compactSupport hfc
  set box := Icc (-(L + 1)) (L + 1) ×ℂ Icc (Real.exp (-A)) (Real.exp A) with hbox
  have hboxc : IsCompact box := isCompact_Icc.reProdIm isCompact_Icc
  have hK : IsCompact (ofComplex '' box) := hboxc.image_of_continuousOn
    (continuousOn_ofComplex_of_im_pos.mono fun w hw => by
      have := (Complex.mem_reProdIm.mp hw).2.1
      exact lt_of_lt_of_le (Real.exp_pos _) this)
  refine HasCompactSupport.intro hK fun z hz => ?_
  by_contra hne
  apply hz
  have h1 := left_ne_zero_of_mul hne
  have h2 := right_ne_zero_of_mul hne
  have hre : |z.re| < L + 1 := by
    by_contra h
    exact h1 (by rw [fejerTrapezoid_eq_zero (not_lt.mp h), Complex.ofReal_zero])
  have him := logChartWeight_ne_zero hA h2
  refine ⟨(z : ℂ), Complex.mem_reProdIm.mpr ⟨?_, him⟩, ofComplex_apply z⟩
  rw [UpperHalfPlane.coe_re]
  exact ⟨by linarith [neg_abs_le z.re], by linarith [le_abs_self z.re]⟩

omit hf hfc in
theorem zeroExtendC_horocyclicPacket (L : ℝ) (x y : ℝ) :
    zeroExtendC (horocyclicPacket L f) ⟨x, y⟩ = (fejerTrapezoid L x : ℂ) * logChartWeight f y := by
  rcases le_or_gt y 0 with hy | hy
  · rw [zeroExtendC_of_im_nonpos _ (show (⟨x, y⟩ : ℂ).im ≤ 0 from hy),
      logChartWeight_of_nonpos f hy, mul_zero]
  · rw [zeroExtendC_of_im_pos _ (show 0 < (⟨x, y⟩ : ℂ).im from hy), horocyclicPacket,
      ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)]
    rfl

end Packet

/-! ### The packet profile -/

/-- The packet kernel `w(t; y, y') = y⁻² y'⁻² k((t² + (y − y')²)/(4yy')) β(y) β̄(y')`. -/
def horocyclicPacketKernel (k : ℝ → ℝ) (f : ℝ → ℂ) (t y y' : ℝ) : ℂ :=
  (((y ^ 2)⁻¹ * (y' ^ 2)⁻¹ * k (pairUCoord t y 0 y') : ℝ) : ℂ) * logChartWeight f y *
    conj (logChartWeight f y')

/-- The packet profile `W(t) = ∫∫ w(t; y, y') dy dy'`. -/
def horocyclicPacketProfile (k : ℝ → ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ := ∫ y, ∫ y', horocyclicPacketKernel k f t y y'

theorem formIntegrand_horocyclicPacket (k : ℝ → ℝ) (L : ℝ) (f : ℝ → ℂ) (y y' x x' : ℝ) :
    formIntegrand k (horocyclicPacket L f) y y' x x' =
      ((fejerTrapezoid L x * fejerTrapezoid L x' : ℝ) : ℂ) * horocyclicPacketKernel k f (x - x') y y' := by
  rw [formIntegrand, zeroExtendC_horocyclicPacket, zeroExtendC_horocyclicPacket, horocyclicPacketKernel,
    show pairUCoord x y x' y' = pairUCoord (x - x') y 0 y' by simp [pairUCoord]]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem measurable_logChartWeight {f : ℝ → ℂ} (hf : Continuous f) :
    Measurable (logChartWeight f) := by
  unfold logChartWeight
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact (hf.measurable.comp Real.measurable_log).mul
    (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)

theorem measurable_packetKernel {k : ℝ → ℝ} (hkc : Continuous k) {f : ℝ → ℂ} (hf : Continuous f) :
    Measurable fun p : ℝ × ℝ × ℝ => horocyclicPacketKernel k f p.1 p.2.1 p.2.2 := by
  have hβ := measurable_logChartWeight hf
  unfold horocyclicPacketKernel pairUCoord
  refine ((Complex.measurable_ofReal.comp ?_).mul (hβ.comp measurable_snd.fst)).mul
    ((Complex.continuous_conj.measurable).comp (hβ.comp measurable_snd.snd))
  exact ((measurable_snd.fst.pow_const 2).inv.mul (measurable_snd.snd.pow_const 2).inv).mul
    (hkc.measurable.comp (by fun_prop))

/-- The indicator of `[a, b]`. -/
def intervalIndicator (a b y : ℝ) : ℝ := (Icc a b).indicator (fun _ => (1 : ℝ)) y

theorem intervalIndicator_nonneg (a b y : ℝ) : 0 ≤ intervalIndicator a b y :=
  indicator_nonneg (fun _ _ => zero_le_one) y

theorem integrable_intervalIndicator (a b : ℝ) : Integrable (intervalIndicator a b) :=
  (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) (by simp))

theorem integral_intervalIndicator {a b : ℝ} (hab : a ≤ b) :
    ∫ y, intervalIndicator a b y = b - a :=
  integral_indicator_Icc hab

theorem measurable_intervalIndicator (a b : ℝ) : Measurable (intervalIndicator a b) :=
  measurable_const.indicator measurableSet_Icc

theorem abs_fejerTrapezoid_le_intervalIndicator (L x : ℝ) :
    |fejerTrapezoid L x| ≤ intervalIndicator (-(L + 1)) (L + 1) x := by
  rw [abs_of_nonneg (fejerTrapezoid_nonneg _ _), intervalIndicator]
  by_cases hx : x ∈ Icc (-(L + 1)) (L + 1)
  · rw [indicator_of_mem hx]; exact fejerTrapezoid_le_one _ _
  · rw [indicator_of_notMem hx, fejerTrapezoid_eq_zero]
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]

section Bounds

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : KernelSupport k R)
  {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
include hkc hkR hf hfc

/-- `|w(t; y, y')| ≤ C 1_{[a,b]}(y) 1_{[a,b]}(y')` with `[a, b] = [e^{−A}, e^{A}]`. -/
theorem exists_norm_packetKernel_le : ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ t y y',
    ‖horocyclicPacketKernel k f t y y'‖ ≤ C * (intervalIndicator (Real.exp (-A)) (Real.exp A) y *
      intervalIndicator (Real.exp (-A)) (Real.exp A) y') := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_le_of_ne_zero_of_compactSupport hfc
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_kernelSupport hkc hkR
  obtain ⟨Cf, hCf0, hCf⟩ := (hfc.exists_bound_of_continuous hf).imp fun C h =>
    (⟨(norm_nonneg _).trans (h 0), h⟩ : 0 ≤ C ∧ ∀ t, ‖f t‖ ≤ C)
  set a := Real.exp (-A)
  set b := Real.exp A
  have ha : 0 < a := Real.exp_pos _
  set Cβ := Cf * Real.sqrt b
  refine ⟨A, (a ^ 2)⁻¹ * (a ^ 2)⁻¹ * M * Cβ * Cβ, hA0, by positivity, fun t y y' => ?_⟩
  have hβ : ∀ y, logChartWeight f y ≠ 0 →
      intervalIndicator a b y = 1 ∧ 0 < y ∧ a ≤ y ∧ ‖logChartWeight f y‖ ≤ Cβ := by
    intro y hy
    have hyab := logChartWeight_ne_zero hA hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hyab.1
    refine ⟨by rw [intervalIndicator, indicator_of_mem (show y ∈ Icc a b from hyab)], hy0,
      hyab.1, ?_⟩
    rw [logChartWeight_of_pos f hy0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (hCf _) (Real.sqrt_le_sqrt hyab.2) (Real.sqrt_nonneg _) hCf0
  by_cases h1 : logChartWeight f y = 0
  · rw [horocyclicPacketKernel, h1, mul_zero, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (intervalIndicator_nonneg _ _ _)
      (intervalIndicator_nonneg _ _ _))
  by_cases h2 : logChartWeight f y' = 0
  · rw [horocyclicPacketKernel, h2, map_zero, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (intervalIndicator_nonneg _ _ _)
      (intervalIndicator_nonneg _ _ _))
  obtain ⟨hi1, hy0, hay, hβy⟩ := hβ y h1
  obtain ⟨hi2, hy0', hay', hβy'⟩ := hβ y' h2
  rw [hi1, hi2, mul_one, mul_one, horocyclicPacketKernel, norm_mul, norm_mul, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2)⁻¹), abs_of_pos (by positivity : (0 : ℝ) < (y' ^ 2)⁻¹)]
  have hinv : (y ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hay 2)
  have hinv' : (y' ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hay' 2)
  have hk : |k (pairUCoord t y 0 y')| ≤ M := hM _ (by unfold pairUCoord; positivity)
  gcongr

omit hkc hf hfc in
/-- `w(t; ·, ·) = 0` for `|t| > 2 e^A √R`. -/
theorem horocyclicPacketKernel_eq_zero_of_lt {A t : ℝ} (hA : ∀ t, f t ≠ 0 → |t| ≤ A)
    (ht : 2 * Real.exp A * Real.sqrt (max R 0) < |t|) (y y' : ℝ) : horocyclicPacketKernel k f t y y' = 0 := by
  by_cases h1 : logChartWeight f y = 0
  · rw [horocyclicPacketKernel, h1, mul_zero, zero_mul]
  by_cases h2 : logChartWeight f y' = 0
  · rw [horocyclicPacketKernel, h2, map_zero, mul_zero]
  have hy := logChartWeight_ne_zero hA h1
  have hy' := logChartWeight_ne_zero hA h2
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy.1
  have hy0' : 0 < y' := lt_of_lt_of_le (Real.exp_pos _) hy'.1
  rw [horocyclicPacketKernel, hkR, mul_zero, Complex.ofReal_zero, zero_mul, zero_mul]
  unfold pairUCoord
  rw [sub_zero, lt_div_iff₀ (by positivity)]
  have hR := Real.sq_sqrt (le_max_right R 0)
  have hb : y * y' ≤ Real.exp A * Real.exp A := mul_le_mul hy.2 hy'.2 hy0'.le (Real.exp_pos _).le
  have ht2 : (2 * Real.exp A * Real.sqrt (max R 0)) ^ 2 < t ^ 2 := by
    rw [← sq_abs t]; exact pow_lt_pow_left₀ ht (by positivity) two_ne_zero
  have hRle : R ≤ max R 0 := le_max_left _ _
  have e1 : (2 * Real.exp A * Real.sqrt (max R 0)) ^ 2 =
      4 * (Real.exp A * Real.exp A) * max R 0 := by rw [mul_pow, mul_pow, hR]; ring
  have e2 : 4 * (y * y') * max R 0 ≤ 4 * (Real.exp A * Real.exp A) * max R 0 :=
    mul_le_mul_of_nonneg_right (by linarith) (le_max_right R 0)
  have e3 : R * (4 * y * y') ≤ 4 * (y * y') * max R 0 := by
    have := mul_le_mul_of_nonneg_right hRle (by positivity : (0 : ℝ) ≤ 4 * y * y')
    linarith
  nlinarith [sq_nonneg (y - y')]

/-- **The form of a packet.**  `Q_k(g_L) = ∫∫ W(x − x') φ_L(x) φ_L(x') dx dx'`. -/
theorem pointPairForm_horocyclicPacket (L : ℝ) :
    pointPairForm k (horocyclicPacket L f) =
      ∫ x, ∫ x', horocyclicPacketProfile k f (x - x') * fejerTrapezoid L x * fejerTrapezoid L x' := by
  obtain ⟨A, C, -, hC0, hC⟩ := exists_norm_packetKernel_le hkc hkR hf hfc
  set a := Real.exp (-A)
  set b := Real.exp A
  rw [pointPairForm_eq_iterated hkc hkR (continuous_horocyclicPacket hf L)
    (hasCompactSupport_horocyclicPacket hfc L)]
  simp only [formIntegrand_horocyclicPacket]
  rw [integral4_swap]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
    simp only [integral_const_mul, horocyclicPacketProfile]
    push_cast
    ring
  · set I := intervalIndicator (-(L + 1)) (L + 1)
    have hab : Integrable (fun p : ℝ × ℝ => intervalIndicator a b p.1 * intervalIndicator a b p.2)
        (volume.prod volume) :=
      (integrable_intervalIndicator a b).mul_prod (integrable_intervalIndicator a b)
    have hII : Integrable (fun p : ℝ × ℝ => I p.1 * I p.2) (volume.prod volume) :=
      (integrable_intervalIndicator _ _).mul_prod (integrable_intervalIndicator _ _)
    have hb0 : Integrable (fun r : (ℝ × ℝ) × (ℝ × ℝ) =>
        (intervalIndicator a b r.1.1 * intervalIndicator a b r.1.2) * (I r.2.1 * I r.2.2))
        ((volume.prod volume).prod (volume.prod volume)) := hab.mul_prod hII
    have hb : Integrable fun r : (ℝ × ℝ) × (ℝ × ℝ) =>
        C * ((intervalIndicator a b r.1.1 * intervalIndicator a b r.1.2) * (I r.2.1 * I r.2.2)) := by
      rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
      exact hb0.const_mul C
    have hφ : Measurable fun r : (ℝ × ℝ) × (ℝ × ℝ) =>
        fejerTrapezoid L r.2.1 * fejerTrapezoid L r.2.2 :=
      ((continuous_fejerTrapezoid L).comp continuous_snd.fst |>.mul
        ((continuous_fejerTrapezoid L).comp continuous_snd.snd)).measurable
    have hw : Measurable fun r : (ℝ × ℝ) × (ℝ × ℝ) =>
        horocyclicPacketKernel k f (r.2.1 - r.2.2) r.1.1 r.1.2 :=
      (measurable_packetKernel hkc hf).comp (f := fun r : (ℝ × ℝ) × (ℝ × ℝ) =>
        (r.2.1 - r.2.2, r.1.1, r.1.2)) (by fun_prop)
    have hmeas : Measurable fun r : (ℝ × ℝ) × (ℝ × ℝ) =>
        ((fejerTrapezoid L r.2.1 * fejerTrapezoid L r.2.2 : ℝ) : ℂ) *
          horocyclicPacketKernel k f (r.2.1 - r.2.2) r.1.1 r.1.2 :=
      (Complex.measurable_ofReal.comp hφ).mul hw
    refine hb.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h1 := abs_fejerTrapezoid_le_intervalIndicator L r.2.1
    have h2 := abs_fejerTrapezoid_le_intervalIndicator L r.2.2
    have h3 := hC (r.2.1 - r.2.2) r.1.1 r.1.2
    calc |fejerTrapezoid L r.2.1| * |fejerTrapezoid L r.2.2| *
          ‖horocyclicPacketKernel k f (r.2.1 - r.2.2) r.1.1 r.1.2‖
        ≤ I r.2.1 * I r.2.2 * (C * (intervalIndicator a b r.1.1 * intervalIndicator a b r.1.2)) :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (intervalIndicator_nonneg _ _ _)) h3
            (norm_nonneg _) (mul_nonneg (intervalIndicator_nonneg _ _ _)
              (intervalIndicator_nonneg _ _ _))
      _ = _ := by ring

omit hkR hfc in
theorem measurable_packetKernel_yy (t : ℝ) :
    Measurable fun p : ℝ × ℝ => horocyclicPacketKernel k f t p.1 p.2 :=
  (measurable_packetKernel hkc hf).comp (f := fun p : ℝ × ℝ => (t, p.1, p.2)) (by fun_prop)

omit hkR hfc in
theorem measurable_packetKernel_t (y : ℝ) :
    Measurable fun p : ℝ × ℝ => horocyclicPacketKernel k f p.1 y p.2 :=
  (measurable_packetKernel hkc hf).comp (f := fun p : ℝ × ℝ => (p.1, y, p.2)) (by fun_prop)

omit hkR hf hfc in
theorem continuous_packetKernel_t (y y' : ℝ) : Continuous fun t => horocyclicPacketKernel k f t y y' := by
  unfold horocyclicPacketKernel pairUCoord
  exact ((continuous_ofReal.comp (continuous_const.mul (hkc.comp (by fun_prop)))).mul
    continuous_const).mul continuous_const

omit hkc hkR hf hfc in
theorem norm_integral_packetKernel_le {A C : ℝ} (hA : 0 ≤ A)
    (hC : ∀ t y y', ‖horocyclicPacketKernel k f t y y'‖ ≤ C * (intervalIndicator (Real.exp (-A))
      (Real.exp A) y * intervalIndicator (Real.exp (-A)) (Real.exp A) y')) (t y : ℝ) :
    ‖∫ y', horocyclicPacketKernel k f t y y'‖ ≤
      C * (Real.exp A - Real.exp (-A)) * intervalIndicator (Real.exp (-A)) (Real.exp A) y := by
  have hab : Real.exp (-A) ≤ Real.exp A := Real.exp_le_exp.mpr (by linarith)
  have hint : Integrable fun y' => C * (intervalIndicator (Real.exp (-A)) (Real.exp A) y *
      intervalIndicator (Real.exp (-A)) (Real.exp A) y') :=
    ((integrable_intervalIndicator _ _).const_mul
      (C * intervalIndicator (Real.exp (-A)) (Real.exp A) y)).congr
      (Eventually.of_forall fun y' => by ring)
  calc ‖∫ y', horocyclicPacketKernel k f t y y'‖ ≤ ∫ y', ‖horocyclicPacketKernel k f t y y'‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y', C * (intervalIndicator (Real.exp (-A)) (Real.exp A) y *
          intervalIndicator (Real.exp (-A)) (Real.exp A) y') :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
          (Eventually.of_forall fun y' => hC t y y')
    _ = C * intervalIndicator (Real.exp (-A)) (Real.exp A) y *
          ∫ y', intervalIndicator (Real.exp (-A)) (Real.exp A) y' := by
        rw [← integral_const_mul]; congr 1 with y'; ring
    _ = _ := by
        rw [integral_intervalIndicator hab]; ring

/-- The packet profile is continuous. -/
theorem continuous_packetProfile : Continuous (horocyclicPacketProfile k f) := by
  obtain ⟨A, C, hA0, hC0, hC⟩ := exists_norm_packetKernel_le hkc hkR hf hfc
  have hinner : ∀ y, Continuous fun t => ∫ y', horocyclicPacketKernel k f t y y' := fun y =>
    continuous_of_dominated
      (bound := fun y' => C * (intervalIndicator (Real.exp (-A)) (Real.exp A) y *
        intervalIndicator (Real.exp (-A)) (Real.exp A) y'))
      (fun t => ((measurable_packetKernel_yy hkc hf t).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (fun t => Eventually.of_forall fun y' => hC t y y')
      (((integrable_intervalIndicator _ _).const_mul
        (C * intervalIndicator (Real.exp (-A)) (Real.exp A) y)).congr
          (Eventually.of_forall fun y' => by ring))
      (Eventually.of_forall fun y' => continuous_packetKernel_t hkc y y')
  refine continuous_of_dominated
    (bound := fun y => C * (Real.exp A - Real.exp (-A)) *
      intervalIndicator (Real.exp (-A)) (Real.exp A) y)
    (fun t => (measurable_packetKernel_yy hkc hf t).stronglyMeasurable.integral_prod_right'
      |>.aestronglyMeasurable)
    (fun t => Eventually.of_forall fun y => norm_integral_packetKernel_le hA0 hC t y)
    ((integrable_intervalIndicator _ _).const_mul _)
    (Eventually.of_forall hinner)

omit hkc hf in
/-- The packet profile has compact support. -/
theorem hasCompactSupport_packetProfile : HasCompactSupport (horocyclicPacketProfile k f) := by
  obtain ⟨A, -, hA⟩ := exists_abs_le_of_ne_zero_of_compactSupport hfc
  set T₀ := 2 * Real.exp A * Real.sqrt (max R 0)
  refine HasCompactSupport.intro (isCompact_Icc (a := -T₀) (b := T₀)) fun t ht => ?_
  have hlt : T₀ < |t| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · linarith [neg_le_abs t]
    · linarith [le_abs_self t]
  rw [horocyclicPacketProfile]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  rw [Pi.zero_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y' => ?_)
  rw [Pi.zero_apply]
  exact horocyclicPacketKernel_eq_zero_of_lt hkR hA hlt y y'

end Bounds

/-! ### The integral of the packet profile -/

/-- The slice `y⁻² y'⁻² √(yy') 𝒜k(log y − log y') β(y) β̄(y')`. -/
def horocyclicPacketSlice (k : ℝ → ℝ) (f : ℝ → ℂ) (y y' : ℝ) : ℂ :=
  (((y ^ 2)⁻¹ * (y' ^ 2)⁻¹ * (Real.sqrt (y * y') * abelTransform k (Real.log y - Real.log y')) :
    ℝ) : ℂ) * logChartWeight f y * conj (logChartWeight f y')

theorem pos_of_logChartWeight_ne_zero {f : ℝ → ℂ} {y : ℝ} (hy : logChartWeight f y ≠ 0) : 0 < y := by
  by_contra h; exact hy (logChartWeight_of_nonpos f (not_lt.mp h))

/-- The `t`-integral of the packet kernel is the horocyclic slice. -/
theorem integral_packetKernel_t (k : ℝ → ℝ) (f : ℝ → ℂ) (y y' : ℝ) :
    ∫ t, horocyclicPacketKernel k f t y y' = horocyclicPacketSlice k f y y' := by
  by_cases h1 : logChartWeight f y = 0
  · simp [horocyclicPacketKernel, horocyclicPacketSlice, h1]
  by_cases h2 : logChartWeight f y' = 0
  · simp [horocyclicPacketKernel, horocyclicPacketSlice, h2]
  have hy := pos_of_logChartWeight_ne_zero h1
  have hy' := pos_of_logChartWeight_ne_zero h2
  have hslice := integral_pairU_slice k hy hy' 0
  have hfun : (fun x : ℝ => k (pairU (ofComplex ⟨x, y⟩) (ofComplex ⟨0, y'⟩))) =
      fun t => k (pairUCoord t y 0 y') := by
    funext t; rw [pairU_ofComplex_eq hy hy']; rfl
  rw [hfun] at hslice
  simp only [horocyclicPacketKernel, horocyclicPacketSlice]
  rw [integral_mul_const, integral_mul_const, integral_complex_ofReal, integral_const_mul, hslice]

section Integral

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : KernelSupport k R)
  {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
include hkc hkR hf hfc

/-- `∫ W = ∫∫ y⁻² y'⁻² √(yy') 𝒜k(log y − log y') β(y) β̄(y') dy dy'`. -/
theorem integral_packetProfile :
    ∫ t, horocyclicPacketProfile k f t = ∫ y, ∫ y', horocyclicPacketSlice k f y y' := by
  obtain ⟨A, C, hA0, hC0, hC⟩ := exists_norm_packetKernel_le hkc hkR hf hfc
  obtain ⟨A', -, hA'⟩ := exists_abs_le_of_ne_zero_of_compactSupport hfc
  set a := Real.exp (-A)
  set b := Real.exp A
  set T₀ := 2 * Real.exp A' * Real.sqrt (max R 0)
  have hzero : ∀ t, T₀ < |t| → ∀ y y', horocyclicPacketKernel k f t y y' = 0 :=
    fun t ht => horocyclicPacketKernel_eq_zero_of_lt hkR hA' ht
  have hT : ∀ t y y', ‖horocyclicPacketKernel k f t y y'‖ ≤
      C * (intervalIndicator (-T₀) T₀ t * (intervalIndicator a b y * intervalIndicator a b y')) := by
    intro t y y'
    by_cases ht : T₀ < |t|
    · rw [hzero t ht, norm_zero]
      exact mul_nonneg hC0 (mul_nonneg (intervalIndicator_nonneg _ _ _)
        (mul_nonneg (intervalIndicator_nonneg _ _ _) (intervalIndicator_nonneg _ _ _)))
    · rw [intervalIndicator, indicator_of_mem (show t ∈ Icc (-T₀) T₀ from
        abs_le.mp (not_lt.mp ht)), one_mul]
      exact hC t y y'
  -- first swap: `t` past `y`
  have hswap1 : ∫ t, ∫ y, ∫ y', horocyclicPacketKernel k f t y y' =
      ∫ y, ∫ t, ∫ y', horocyclicPacketKernel k f t y y' := by
    refine integral_integral_swap ?_
    have hb : Integrable (fun p : ℝ × ℝ => (C * (b - a)) *
        (intervalIndicator (-T₀) T₀ p.1 * intervalIndicator a b p.2)) (volume.prod volume) :=
      ((integrable_intervalIndicator _ _).mul_prod (integrable_intervalIndicator _ _)).const_mul _
    have hm : StronglyMeasurable fun q : (ℝ × ℝ) × ℝ => horocyclicPacketKernel k f q.1.1 q.1.2 q.2 :=
      ((measurable_packetKernel hkc hf).comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2))
        (by fun_prop)).stronglyMeasurable
    refine hb.mono' hm.integral_prod_right'.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have hab : a ≤ b := Real.exp_le_exp.mpr (by linarith)
    calc ‖∫ y', horocyclicPacketKernel k f p.1 p.2 y'‖ ≤ ∫ y', ‖horocyclicPacketKernel k f p.1 p.2 y'‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y', C * (intervalIndicator (-T₀) T₀ p.1 * (intervalIndicator a b p.2 *
            intervalIndicator a b y')) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (((integrable_intervalIndicator a b).const_mul (C * (intervalIndicator (-T₀) T₀ p.1 *
              intervalIndicator a b p.2))).congr (Eventually.of_forall fun y' => by ring))
            (Eventually.of_forall fun y' => hT p.1 p.2 y')
      _ = ∫ y', (C * (intervalIndicator (-T₀) T₀ p.1 * intervalIndicator a b p.2)) *
            intervalIndicator a b y' :=
          integral_congr_ae (Eventually.of_forall fun y' => by ring)
      _ = C * (b - a) * (intervalIndicator (-T₀) T₀ p.1 * intervalIndicator a b p.2) := by
          rw [integral_const_mul, integral_intervalIndicator hab]; ring
  -- second swap: `t` past `y'`
  have hswap2 : ∀ y, ∫ t, ∫ y', horocyclicPacketKernel k f t y y' = ∫ y', ∫ t, horocyclicPacketKernel k f t y y' := by
    intro y
    refine integral_integral_swap ?_
    have hb : Integrable (fun p : ℝ × ℝ => (C * intervalIndicator a b y) *
        (intervalIndicator (-T₀) T₀ p.1 * intervalIndicator a b p.2)) (volume.prod volume) :=
      ((integrable_intervalIndicator _ _).mul_prod (integrable_intervalIndicator _ _)).const_mul _
    refine hb.mono' (measurable_packetKernel_t hkc hf y).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    calc ‖horocyclicPacketKernel k f p.1 y p.2‖ ≤ C * (intervalIndicator (-T₀) T₀ p.1 *
          (intervalIndicator a b y * intervalIndicator a b p.2)) := hT p.1 y p.2
      _ = _ := by ring
  rw [show (∫ t, horocyclicPacketProfile k f t) = ∫ t, ∫ y, ∫ y', horocyclicPacketKernel k f t y y' from rfl, hswap1]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [hswap2 y]
  exact integral_congr_ae (Eventually.of_forall fun y' => integral_packetKernel_t k f y y')

end Integral

/-! ### The logarithmic chart -/

theorem horocyclicPacketSlice_exp (k : ℝ → ℝ) (f : ℝ → ℂ) (a b : ℝ) :
    (Real.exp a * Real.exp b : ℝ) • horocyclicPacketSlice k f (Real.exp a) (Real.exp b) =
      (abelTransform k (a - b) : ℂ) * f a * conj (f b) := by
  have ea : Real.exp a = Real.exp (a / 2) * Real.exp (a / 2) := by rw [← Real.exp_add]; ring_nf
  have eb : Real.exp b = Real.exp (b / 2) * Real.exp (b / 2) := by rw [← Real.exp_add]; ring_nf
  have hs : Real.sqrt (Real.exp a * Real.exp b) = Real.exp (a / 2) * Real.exp (b / 2) := by
    rw [← Real.exp_add, sqrt_realExp_eq_exp_half, ← Real.exp_add]; ring_nf
  have ha := Real.exp_pos (a / 2)
  have hb := Real.exp_pos (b / 2)
  rw [horocyclicPacketSlice, logChartWeight_of_pos f (Real.exp_pos a), logChartWeight_of_pos f (Real.exp_pos b),
    Real.log_exp, Real.log_exp, hs, sqrt_realExp_eq_exp_half, sqrt_realExp_eq_exp_half, ea, eb,
    Complex.real_smul, map_mul, Complex.conj_ofReal]
  push_cast
  field_simp

theorem horocyclicPacketSlice_eq_zero_of_nonpos_left (k : ℝ → ℝ) (f : ℝ → ℂ) {y : ℝ} (hy : y ≤ 0) (y' : ℝ) :
    horocyclicPacketSlice k f y y' = 0 := by
  rw [horocyclicPacketSlice, logChartWeight_of_nonpos f hy, mul_zero, zero_mul]

theorem horocyclicPacketSlice_eq_zero_of_nonpos_right (k : ℝ → ℝ) (f : ℝ → ℂ) (y : ℝ) {y' : ℝ} (hy : y' ≤ 0) :
    horocyclicPacketSlice k f y y' = 0 := by
  rw [horocyclicPacketSlice, logChartWeight_of_nonpos f hy, map_zero, mul_zero]

/-- **The slice integral is the Bochner form of `𝒜k`.**  `y = e^a`, `y' = e^b`. -/
theorem integral_packetSlice_eq_bochnerForm (k : ℝ → ℝ) (f : ℝ → ℂ) :
    ∫ y, ∫ y', horocyclicPacketSlice k f y y' = bochnerForm (fun t => (abelTransform k t : ℂ)) f := by
  have hout : ∀ y, y ∉ Ioi (0 : ℝ) → ∫ y', horocyclicPacketSlice k f y y' = 0 := fun y hy => by
    simp [horocyclicPacketSlice_eq_zero_of_nonpos_left k f (not_lt.mp hy)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, integral_Ioi_eq_integral_realExp_smul]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  have hin : ∀ y', y' ∉ Ioi (0 : ℝ) → horocyclicPacketSlice k f (Real.exp a) y' = 0 := fun y' hy' =>
    horocyclicPacketSlice_eq_zero_of_nonpos_right k f _ (not_lt.mp hy')
  simp only
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hin, integral_Ioi_eq_integral_realExp_smul,
    ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [smul_smul, mul_comm (Real.exp a), ← horocyclicPacketSlice_exp]
  rw [mul_comm (Real.exp b)]

/-! ### Necessity -/

/-- If `Re X_L ≥ 0` and `|X_L − 2Lc| ≤ D` for all `L ≥ 0`, then `Re c ≥ 0`. -/
theorem re_nonneg_of_linear_growth {X : ℝ → ℂ} {c : ℂ} {D : ℝ}
    (hpos : ∀ L, 0 ≤ L → 0 ≤ (X L).re) (hgrowth : ∀ L, 0 ≤ L → ‖X L - 2 * L * c‖ ≤ D) :
    0 ≤ c.re := by
  by_contra hneg
  push Not at hneg
  have hD : 0 ≤ D := (norm_nonneg _).trans (hgrowth 0 le_rfl)
  have hc : 0 < -c.re := by linarith
  set L := D / (-c.re) + 1 with hLdef
  have hL : 0 ≤ L := by rw [hLdef]; have := div_nonneg hD hc.le; linarith
  have h1 := hpos L hL
  have h2 := (Complex.re_le_norm _).trans (hgrowth L hL)
  have hre : (X L - 2 * L * c).re = (X L).re - 2 * L * c.re := by
    rw [Complex.sub_re, show (2 * (L : ℂ)) = ((2 * L : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hre] at h2
  have hLc : L * (-c.re) = D + (-c.re) := by
    rw [hLdef, add_mul, div_mul_cancel₀ D hc.ne', one_mul]
  nlinarith

/-- **Necessity.**  If the point-pair kernel of `k` is positive definite on `ℍ`, its Abel transform
lies in the Bochner cone. -/
theorem isBochnerPositive_abelTransform {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k)
    (hkR : KernelSupport k R) (hpd : IsPositiveDefinitePointPair k) :
    IsBochnerPositive (abelTransform k) := by
  intro f hf hfc
  have hW := continuous_packetProfile hkc hkR hf hfc
  have hWs := hasCompactSupport_packetProfile hkR hfc
  rw [← integral_packetSlice_eq_bochnerForm, ← integral_packetProfile hkc hkR hf hfc]
  refine re_nonneg_of_linear_growth (X := fun L => pointPairForm k (horocyclicPacket L f))
    (D := ∫ t, ‖horocyclicPacketProfile k f t‖ * (4 + 4 * |t|))
    (fun L _ => hpd _ (continuous_horocyclicPacket hf L) (hasCompactSupport_horocyclicPacket hfc L))
    (fun L hL => ?_)
  rw [pointPairForm_horocyclicPacket hkc hkR hf hfc]
  exact norm_fejerTrapezoidForm_sub_le hW hWs hL

/-- **The spectral side.**  A positive definite point-pair kernel has nonnegative Selberg transform
on the critical line: `h_k(½ + iτ) ≥ 0`. -/
theorem selbergTransform_critical_re_nonneg {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k)
    (hkR : KernelSupport k R) (hpd : IsPositiveDefinitePointPair k) (τ : ℝ) :
    0 ≤ (selbergTransform k (1 / 2 + τ * Complex.I)).re := by
  rw [selbergTransform_critical_eq_ofReal hkc hkR, Complex.ofReal_re]
  exact integral_mul_cos_nonneg_of_isBochnerPositive (continuous_abelTransform hkc hkR)
    (hasCompactSupport_abelTransform hkR) (isBochnerPositive_abelTransform hkc hkR hpd) τ

end GaloisForLFunctions.RHTower.MehlerFock
