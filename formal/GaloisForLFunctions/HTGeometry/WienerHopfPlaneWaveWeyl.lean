import GaloisForLFunctions.HTGeometry.SchurKernelOperator

/-!
# Plane-wave Weyl sequences for Wiener–Hopf operators

Let `W` be the Wiener–Hopf operator `(W f)(y) = ∫_0^∞ κ(y - z) f(z) dz` on `L²(0, ∞)` with an
integrable real kernel `κ` of finite first moment, and let `κ̂(ξ) = ∫ κ(s) e^{-iξs} ds`.  The
normalized plane-wave packet

`f(z) = L^{-1/2} e^{iξz} 1_{[a, a+L)}(z)`,   `a ≥ 0`,

satisfies `‖W f - κ̂(ξ) f‖² ≤ (2/L) (∫|κ|) (∫|s||κ(s)| ds)`.  Indeed
`(W f)(y) - κ̂(ξ) f(y) = L^{-1/2} ∫ κ(s) e^{iξ(y-s)} (1_{[a,a+L)}(y - s) - 1_{[a,a+L)}(y)) ds`;
Cauchy–Schwarz with weight `|κ|` and Tonelli reduce the estimate to the measure `≤ 2|s|` of the
symmetric difference of an interval and its translate by `s`.  Packets on the disjoint intervals
`[(n+1)², (n+1)² + n + 1)` form an orthonormal sequence, so every `κ̂(ξ)` is a Weyl value of `W`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

/-- The half-line measure. -/
abbrev halfLineMeasure : Measure ℝ := volume.restrict (Ici (0 : ℝ))

/-- The Fourier value `κ̂(ξ) = ∫ κ(s) e^{-iξs} ds`. -/
def convSymbol (κ : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ s : ℝ, (κ s : ℂ) * Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I)

/-- The window indicator `1_{[a, a+L)}`. -/
def windowIndicator (a L : ℝ) (z : ℝ) : ℝ := (Ico a (a + L)).indicator 1 z

/-- The plane-wave packet `L^{-1/2} e^{iξz} 1_{[a,a+L)}(z)`. -/
def planeWavePacketFun (ξ a L : ℝ) (z : ℝ) : ℂ :=
  (((Real.sqrt L)⁻¹ * windowIndicator a L z : ℝ) : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I)

theorem windowIndicator_eq (a L z : ℝ) :
    windowIndicator a L z = if z ∈ Ico a (a + L) then 1 else 0 := by
  unfold windowIndicator; split_ifs with h <;> simp [h]

theorem windowIndicator_nonneg (a L z : ℝ) : 0 ≤ windowIndicator a L z := by
  rw [windowIndicator_eq]; split_ifs <;> norm_num

theorem windowIndicator_sq (a L z : ℝ) : windowIndicator a L z ^ 2 = windowIndicator a L z := by
  rw [windowIndicator_eq]; split_ifs <;> norm_num

theorem measurable_windowIndicator (a L : ℝ) : Measurable (windowIndicator a L) :=
  measurable_const.indicator measurableSet_Ico

theorem measurable_planeWavePacketFun (ξ a L : ℝ) : Measurable (planeWavePacketFun ξ a L) := by
  unfold planeWavePacketFun
  exact (Complex.measurable_ofReal.comp (measurable_const.mul (measurable_windowIndicator a L))).mul
    (by fun_prop)

theorem norm_exp_mul_I (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem norm_planeWavePacketFun (ξ a L z : ℝ) :
    ‖planeWavePacketFun ξ a L z‖ = (Real.sqrt L)⁻¹ * windowIndicator a L z := by
  unfold planeWavePacketFun
  rw [norm_mul, show (ξ : ℂ) * (z : ℂ) * Complex.I = ((ξ * z : ℝ) : ℂ) * Complex.I by push_cast; ring,
    norm_exp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (windowIndicator_nonneg a L z))]

theorem planeWavePacketFun_eq_zero_of_notMem {ξ a L z : ℝ} (hz : z ∉ Ico a (a + L)) :
    planeWavePacketFun ξ a L z = 0 := by
  rw [planeWavePacketFun, windowIndicator_eq, if_neg hz]; simp

theorem lintegral_enorm_planeWavePacketFun_sq {ξ a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    ∫⁻ z, ‖planeWavePacketFun ξ a L z‖ₑ ^ 2 ∂halfLineMeasure = 1 := by
  have hpt : ∀ z, ‖planeWavePacketFun ξ a L z‖ₑ ^ 2 =
      (Ico a (a + L)).indicator (fun _ => ENNReal.ofReal L⁻¹) z := by
    intro z
    rw [← ofReal_norm, norm_planeWavePacketFun, ← ENNReal.ofReal_pow (by
      exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (windowIndicator_nonneg a L z)),
      mul_pow, windowIndicator_sq, inv_pow, Real.sq_sqrt hL.le, windowIndicator_eq]
    split_ifs with h
    · rw [Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, mul_zero, ENNReal.ofReal_zero]
  simp_rw [hpt]
  rw [lintegral_indicator measurableSet_Ico, setLIntegral_const, halfLineMeasure,
    Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (show Ico a (a + L) ⊆ Ici 0 from fun z hz => le_trans ha hz.1),
    Real.volume_Ico,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hL.le)]
  rw [show a + L - a = L by ring, inv_mul_cancel₀ hL.ne', ENNReal.ofReal_one]

theorem memLp_planeWavePacketFun {ξ a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    MemLp (planeWavePacketFun ξ a L) 2 halfLineMeasure := by
  refine ⟨(measurable_planeWavePacketFun ξ a L).aestronglyMeasurable, ?_⟩
  rw [SchurKernel.eLpNorm_two_eq, lintegral_enorm_planeWavePacketFun_sq ha hL, ENNReal.one_rpow]
  exact ENNReal.one_lt_top

/-- The plane-wave packet as an element of `L²(0, ∞)`. -/
def planeWavePacket (ξ a L : ℝ) (ha : 0 ≤ a) (hL : 0 < L) : Lp ℂ 2 halfLineMeasure :=
  (memLp_planeWavePacketFun (ξ := ξ) ha hL).toLp _

theorem planeWave_coeFn {ξ a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    (planeWavePacket ξ a L ha hL : ℝ → ℂ) =ᵐ[halfLineMeasure] planeWavePacketFun ξ a L :=
  MemLp.coeFn_toLp _

theorem norm_planeWave {ξ a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) : ‖planeWavePacket ξ a L ha hL‖ = 1 := by
  rw [planeWavePacket, Lp.norm_toLp, SchurKernel.eLpNorm_two_eq, lintegral_enorm_planeWavePacketFun_sq ha hL,
    ENNReal.one_rpow, ENNReal.toReal_one]

/-! ### The symmetric-difference estimate -/

theorem enorm_windowIndicator_sub_sq_le (a L s y : ℝ) :
    ‖windowIndicator a L (y - s) - windowIndicator a L y‖ₑ ^ 2 ≤
      (uIcc a (a + s) ∪ uIcc (a + L) (a + L + s)).indicator 1 y := by
  rw [windowIndicator_eq, windowIndicator_eq]
  by_cases h1 : y - s ∈ Ico a (a + L) <;> by_cases h2 : y ∈ Ico a (a + L)
  · simp [h1, h2]
  · have hmem : y ∈ uIcc a (a + s) ∪ uIcc (a + L) (a + L + s) := by
      simp only [mem_Ico, not_and_or, not_le, not_lt] at h1 h2
      rcases h2 with h2 | h2
      · left; rw [mem_uIcc]; right; constructor <;> linarith [h1.1]
      · right; rw [mem_uIcc]; left; constructor <;> linarith [h1.2]
    rw [if_pos h1, if_neg h2, Set.indicator_of_mem hmem]
    simp
  · have hmem : y ∈ uIcc a (a + s) ∪ uIcc (a + L) (a + L + s) := by
      simp only [mem_Ico, not_and_or, not_le, not_lt] at h1 h2
      rcases h1 with h1 | h1
      · left; rw [mem_uIcc]; left; constructor <;> linarith [h2.1]
      · right; rw [mem_uIcc]; right; constructor <;> linarith [h2.2]
    rw [if_neg h1, if_pos h2, Set.indicator_of_mem hmem]
    simp
  · simp [h1, h2]

theorem lintegral_enorm_windowIndicator_sub_sq_le (a L s : ℝ) :
    ∫⁻ y, ‖windowIndicator a L (y - s) - windowIndicator a L y‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * |s|) := by
  calc ∫⁻ y, ‖windowIndicator a L (y - s) - windowIndicator a L y‖ₑ ^ 2
      ≤ ∫⁻ y, (uIcc a (a + s) ∪ uIcc (a + L) (a + L + s)).indicator 1 y :=
        lintegral_mono fun y => enorm_windowIndicator_sub_sq_le a L s y
    _ = volume (uIcc a (a + s) ∪ uIcc (a + L) (a + L + s)) :=
        lintegral_indicator_one (measurableSet_uIcc.union measurableSet_uIcc)
    _ ≤ volume (uIcc a (a + s)) + volume (uIcc (a + L) (a + L + s)) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * |s|) := by
        rw [Real.volume_interval, Real.volume_interval, ← ENNReal.ofReal_add (abs_nonneg _)
          (abs_nonneg _)]
        congr 1
        rw [show a + s - a = s by ring, show a + L + s - (a + L) = s by ring]
        ring

/-! ### Cauchy–Schwarz with a weight -/

theorem sq_lintegral_mul_le {g h : ℝ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ s, g s * h s) ^ 2 ≤ (∫⁻ s, g s) * ∫⁻ s, g s * h s ^ 2 := by
  have h1 := SchurKernel.sq_lintegral_le_measure_mul (volume.withDensity g) hh.aemeasurable
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ hg hh,
    lintegral_withDensity_eq_lintegral_mul _ hg (hh.pow_const 2)] at h1
  simpa [Pi.mul_apply] using h1

/-! ### The Weyl estimate -/

section Weyl

variable (k : SchurKernel halfLineMeasure) {κ : ℝ → ℝ}

/-- **Plane-wave estimate.**  `‖W f - κ̂(ξ) f‖² ≤ (2/L)(∫|κ|)(∫|s||κ(s)|)`. -/
theorem norm_op_planeWave_sub_sq_le (hκm : Measurable κ) (hκ : Integrable κ)
    (hκ1 : Integrable fun s => |s| * κ s) (hk : ∀ y z, k.toFun y z = (κ (y - z) : ℂ)) (ξ : ℝ)
    {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    ‖k.op (planeWavePacket ξ a L ha hL) - convSymbol κ ξ • planeWavePacket ξ a L ha hL‖ ^ 2 ≤
      2 / L * (∫ s, |κ s|) * ∫ s, |s| * |κ s| := by
  set f := planeWavePacket ξ a L ha hL
  set F := planeWavePacketFun ξ a L
  set c := convSymbol κ ξ
  set Δ : ℝ → ℝ → ℝ := fun y s => windowIndicator a L (y - s) - windowIndicator a L y with hΔ
  have hFm : Measurable F := measurable_planeWavePacketFun ξ a L
  have hFb : ∀ z, ‖F z‖ ≤ (Real.sqrt L)⁻¹ := fun z => by
    rw [norm_planeWavePacketFun]
    have : windowIndicator a L z ≤ 1 := by rw [windowIndicator_eq]; split_ifs <;> norm_num
    exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) this
  have hFsupp : ∀ z, z ∉ Ici (0 : ℝ) → F z = 0 := fun z hz =>
    planeWavePacketFun_eq_zero_of_notMem fun h => hz (le_trans ha h.1)
  -- the pointwise identity
  have hdiff : ∀ y s, F (y - s) - Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I) * F y =
      (((Real.sqrt L)⁻¹ * Δ y s : ℝ) : ℂ) *
        Complex.exp ((ξ : ℂ) * ((y - s : ℝ) : ℂ) * Complex.I) := by
    intro y s
    simp only [F, planeWavePacketFun, hΔ]
    have he : Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I) *
        Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I) =
        Complex.exp ((ξ : ℂ) * ((y - s : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    push_cast at he ⊢
    linear_combination (-(((Real.sqrt L : ℝ) : ℂ))⁻¹ * (windowIndicator a L y : ℂ)) * he
  have hΔm : Measurable fun q : ℝ × ℝ => Δ q.1 q.2 := by
    simp only [hΔ]
    exact ((measurable_windowIndicator a L).comp (measurable_fst.sub measurable_snd)).sub
      ((measurable_windowIndicator a L).comp measurable_fst)
  have hκc : Integrable fun s => (κ s : ℂ) := hκ.ofReal
  have hint1 : ∀ y, Integrable fun s => (κ s : ℂ) * F (y - s) := fun y =>
    hκc.mul_bdd (hFm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun s => hFb (y - s))
  have hint2 : Integrable fun s => (κ s : ℂ) * Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I) :=
    hκc.mul_bdd (by fun_prop : Continuous fun s : ℝ =>
      Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I)).aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [show -((ξ : ℂ) * (s : ℂ)) * Complex.I = ((-(ξ * s) : ℝ) : ℂ) * Complex.I by
          push_cast; ring, norm_exp_mul_I])
  -- the operator value as a convolution over the line
  have happly : ∀ y, k.apply f y = ∫ s, (κ s : ℂ) * F (y - s) := by
    intro y
    rw [SchurKernel.apply]
    have h1 : ∫ z, k.toFun y z * (f : ℝ → ℂ) z ∂halfLineMeasure =
        ∫ z, (κ (y - z) : ℂ) * F z ∂halfLineMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [planeWave_coeFn (ξ := ξ) ha hL] with z hz
      rw [hk, hz]
    rw [h1, halfLineMeasure, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by rw [hFsupp z hz, mul_zero])]
    have h2 := integral_sub_left_eq_self (fun s => (κ s : ℂ) * F (y - s)) volume y
    simp only [sub_sub_cancel] at h2
    exact h2
  -- the pointwise defect
  have hpt : ∀ y, ‖k.apply f y - c * F y‖ₑ ≤
      ENNReal.ofReal (Real.sqrt L)⁻¹ * ∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ := by
    intro y
    rw [happly y]
    have hc : c * F y = ∫ s, (κ s : ℂ) * Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I) * F y := by
      rw [integral_mul_const]; rfl
    rw [hc, ← integral_sub (hint1 y) (hint2.mul_const _)]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun s => ?_
    rw [mul_assoc, ← mul_sub, hdiff y s, ← ofReal_norm, Real.enorm_eq_ofReal_abs,
      Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    congr 1
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, show (ξ : ℂ) * ((y - s : ℝ) : ℂ) * Complex.I =
        ((ξ * (y - s) : ℝ) : ℂ) * Complex.I by push_cast; ring, norm_exp_mul_I, mul_one, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg L))]
    ring
  have hsq : ∀ y, ‖k.apply f y - c * F y‖ₑ ^ 2 ≤
      ENNReal.ofReal L⁻¹ * ((∫⁻ s, ‖κ s‖ₑ) * ∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ ^ 2) := by
    intro y
    have hΔy : Measurable fun s => Δ y s := hΔm.comp (measurable_const.prodMk measurable_id)
    have hCS : (∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ) ^ 2 ≤
        (∫⁻ s, ‖κ s‖ₑ) * ∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ ^ 2 :=
      sq_lintegral_mul_le hκm.enorm hΔy.enorm
    have hL2 : ENNReal.ofReal (Real.sqrt L)⁻¹ ^ 2 = ENNReal.ofReal L⁻¹ := by
      rw [← ENNReal.ofReal_pow (inv_nonneg.mpr (Real.sqrt_nonneg _)), inv_pow,
        Real.sq_sqrt hL.le]
    calc ‖k.apply f y - c * F y‖ₑ ^ 2
        ≤ (ENNReal.ofReal (Real.sqrt L)⁻¹ * ∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ) ^ 2 :=
          pow_le_pow_left' (hpt y) 2
      _ = ENNReal.ofReal (Real.sqrt L)⁻¹ ^ 2 * (∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ) ^ 2 := mul_pow _ _ _
      _ ≤ _ := by rw [hL2]; gcongr
  -- integrate in `y`
  have hcoe : (k.op f - c • f : Lp ℂ 2 halfLineMeasure) =ᵐ[halfLineMeasure]
      fun y => k.apply f y - c * F y := by
    filter_upwards [Lp.coeFn_sub (k.op f) (c • f), Lp.coeFn_smul c f, k.op_coeFn f,
      planeWave_coeFn (ξ := ξ) ha hL] with y h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, smul_eq_mul]
    simp only [f] at h4 ⊢
    rw [h4]
  have hκint : ∫⁻ s, ‖κ s‖ₑ = ENNReal.ofReal (∫ s, |κ s|) := by
    rw [ofReal_integral_eq_lintegral_ofReal hκ.abs (Eventually.of_forall fun s => abs_nonneg _)]
    simp_rw [Real.enorm_eq_ofReal_abs]
  have hκ1int : ∫⁻ s, ‖κ s‖ₑ * ENNReal.ofReal (2 * |s|) =
      ENNReal.ofReal (2 * ∫ s, |s| * |κ s|) := by
    have hi : Integrable fun s => 2 * (|s| * |κ s|) :=
      (hκ1.abs.congr (Eventually.of_forall fun s => by simp [abs_mul])).const_mul 2
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun s => by positivity)]
    refine lintegral_congr fun s => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1; ring
  have htot : ∫⁻ y, ‖(k.op f - c • f : Lp ℂ 2 halfLineMeasure) y‖ₑ ^ 2 ∂halfLineMeasure ≤
      ENNReal.ofReal L⁻¹ * (ENNReal.ofReal (∫ s, |κ s|) * ENNReal.ofReal (2 * ∫ s, |s| * |κ s|)) := by
    calc ∫⁻ y, ‖(k.op f - c • f : Lp ℂ 2 halfLineMeasure) y‖ₑ ^ 2 ∂halfLineMeasure
        = ∫⁻ y, ‖k.apply f y - c * F y‖ₑ ^ 2 ∂halfLineMeasure := by
          refine lintegral_congr_ae ?_
          filter_upwards [hcoe] with y hy
          rw [hy]
      _ ≤ ∫⁻ y, ENNReal.ofReal L⁻¹ * ((∫⁻ s, ‖κ s‖ₑ) * ∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ ^ 2)
            ∂halfLineMeasure := lintegral_mono hsq
      _ ≤ ∫⁻ y, ENNReal.ofReal L⁻¹ * ((∫⁻ s, ‖κ s‖ₑ) * ∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ ^ 2) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal L⁻¹ * ((∫⁻ s, ‖κ s‖ₑ) *
            ∫⁻ y, ∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ ^ 2) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul'' _
            (show Measurable fun y => ∫⁻ s, ‖κ s‖ₑ * ‖Δ y s‖ₑ ^ 2 from
              ((hκm.enorm.comp measurable_snd).mul
                (hΔm.enorm.pow_const 2)).lintegral_prod_right').aemeasurable]
      _ = ENNReal.ofReal L⁻¹ * ((∫⁻ s, ‖κ s‖ₑ) *
            ∫⁻ s, ‖κ s‖ₑ * ∫⁻ y, ‖Δ y s‖ₑ ^ 2) := by
          rw [lintegral_lintegral_swap ((hκm.enorm.comp measurable_snd).mul
            (hΔm.enorm.pow_const 2)).aemeasurable]
          congr 2
          refine lintegral_congr fun s => ?_
          rw [lintegral_const_mul' _ _ enorm_ne_top]
      _ ≤ ENNReal.ofReal L⁻¹ * ((∫⁻ s, ‖κ s‖ₑ) * ∫⁻ s, ‖κ s‖ₑ * ENNReal.ofReal (2 * |s|)) := by
          gcongr with s
          exact lintegral_enorm_windowIndicator_sub_sq_le a L s
      _ = _ := by rw [hκint, hκ1int]
  have hA : 0 ≤ ∫ s, |κ s| := integral_nonneg fun s => abs_nonneg _
  have hB : 0 ≤ ∫ s, |s| * |κ s| := integral_nonneg fun s => by positivity
  rw [Lp.norm_def, ← ENNReal.toReal_pow, SchurKernel.eLpNorm_two_sq]
  calc (∫⁻ y, ‖(k.op f - c • f : Lp ℂ 2 halfLineMeasure) y‖ₑ ^ 2 ∂halfLineMeasure).toReal
      ≤ (ENNReal.ofReal L⁻¹ * (ENNReal.ofReal (∫ s, |κ s|) *
          ENNReal.ofReal (2 * ∫ s, |s| * |κ s|))).toReal :=
        ENNReal.toReal_mono (by finiteness) htot
    _ = 2 / L * (∫ s, |κ s|) * ∫ s, |s| * |κ s| := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hL.le),
          ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal (by positivity)]
        ring

/-- The packets on the windows `[(n+1)², (n+1)² + n + 1)`. -/
def planeWavePacketSeq (ξ : ℝ) (n : ℕ) : Lp ℂ 2 halfLineMeasure :=
  planeWavePacket ξ (((n : ℝ) + 1) ^ 2) ((n : ℝ) + 1) (by positivity) (by positivity)

theorem disjoint_window {m n : ℕ} (hmn : m < n) :
    Disjoint (Ico (((m : ℝ) + 1) ^ 2) (((m : ℝ) + 1) ^ 2 + ((m : ℝ) + 1)))
      (Ico (((n : ℝ) + 1) ^ 2) (((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1))) := by
  have h : (m : ℝ) + 1 + 1 ≤ (n : ℝ) + 1 := by
    have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
    linarith
  refine Set.disjoint_left.mpr fun z hz1 hz2 => ?_
  have : ((m : ℝ) + 1) ^ 2 + ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  linarith [hz1.2, hz2.1]

theorem orthonormal_planeWavePacketSeq (ξ : ℝ) : Orthonormal ℂ (planeWavePacketSeq ξ) := by
  rw [orthonormal_iff_ite]
  intro m n
  split_ifs with h
  · subst h
    rw [inner_self_eq_norm_sq_to_K, planeWavePacketSeq, norm_planeWave]; norm_num
  · rw [planeWavePacketSeq, planeWavePacketSeq, L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [planeWave_coeFn (ξ := ξ) (a := ((m : ℝ) + 1) ^ 2) (L := (m : ℝ) + 1)
      (by positivity) (by positivity), planeWave_coeFn (ξ := ξ) (a := ((n : ℝ) + 1) ^ 2)
      (L := (n : ℝ) + 1) (by positivity) (by positivity)] with z hm hn
    rw [hm, hn, RCLike.inner_apply, Pi.zero_apply]
    have hdisj : Disjoint (Ico (((m : ℝ) + 1) ^ 2) (((m : ℝ) + 1) ^ 2 + ((m : ℝ) + 1)))
        (Ico (((n : ℝ) + 1) ^ 2) (((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1))) := by
      rcases lt_or_gt_of_ne h with h' | h'
      · exact disjoint_window h'
      · exact (disjoint_window h').symm
    by_cases hzm : z ∈ Ico (((m : ℝ) + 1) ^ 2) (((m : ℝ) + 1) ^ 2 + ((m : ℝ) + 1))
    · rw [planeWavePacketFun_eq_zero_of_notMem (Set.disjoint_left.mp hdisj hzm), zero_mul]
    · rw [planeWavePacketFun_eq_zero_of_notMem hzm, map_zero, mul_zero]

/-- **Every Fourier value is a Weyl value of the Wiener–Hopf operator.**  The plane-wave packets form
an orthonormal sequence with `‖W fₙ - κ̂(ξ) fₙ‖ → 0`. -/
theorem tendsto_norm_op_planeWavePacketSeq_sub (hκm : Measurable κ) (hκ : Integrable κ)
    (hκ1 : Integrable fun s => |s| * κ s) (hk : ∀ y z, k.toFun y z = (κ (y - z) : ℂ)) (ξ : ℝ) :
    Tendsto (fun n => ‖k.op (planeWavePacketSeq ξ n) - convSymbol κ ξ • planeWavePacketSeq ξ n‖) atTop
      (𝓝 0) := by
  set C := 2 * (∫ s, |κ s|) * ∫ s, |s| * |κ s|
  have hbound : ∀ n : ℕ, ‖k.op (planeWavePacketSeq ξ n) - convSymbol κ ξ • planeWavePacketSeq ξ n‖ ^ 2 ≤
      C * (1 / ((n : ℝ) + 1)) := by
    intro n
    refine (norm_op_planeWave_sub_sq_le k hκm hκ hκ1 hk ξ _ _).trans (le_of_eq ?_)
    simp only [C]
    ring
  have hlim : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
  have h2 : Tendsto (fun n => ‖k.op (planeWavePacketSeq ξ n) - convSymbol κ ξ • planeWavePacketSeq ξ n‖ ^ 2)
      atTop (𝓝 0) := squeeze_zero (fun n => by positivity) hbound hlim
  have := h2.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end Weyl

end

end GaloisForLFunctions.HTGeometry
