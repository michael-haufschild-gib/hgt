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

/-- The half-line measure. -/
abbrev halfLineMeasure : Measure ℝ := volume.restrict (Ici (0 : ℝ))

/-- The Fourier value `κ̂(ξ) = ∫ κ(s) e^{-iξs} ds`. -/
def convSymbol (κ : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ s : ℝ, (κ s : ℂ) * Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I)

/-- The window indicator `1_{[a, a+L)}`. -/
def windowIndicator (a L : ℝ) (z : ℝ) : ℝ := (Ico a (a + L)).indicator 1 z

/-- The plane-wave packet `L^{-1/2} e^{iξz} 1_{[a,a+L)}(z)`. -/
def planeWaveFun (ξ a L : ℝ) (z : ℝ) : ℂ :=
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

theorem measurable_planeWaveFun (ξ a L : ℝ) : Measurable (planeWaveFun ξ a L) := by
  unfold planeWaveFun
  exact (Complex.measurable_ofReal.comp (measurable_const.mul (measurable_windowIndicator a L))).mul
    (by fun_prop)

theorem norm_exp_mul_I (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem norm_planeWaveFun (ξ a L z : ℝ) :
    ‖planeWaveFun ξ a L z‖ = (Real.sqrt L)⁻¹ * windowIndicator a L z := by
  unfold planeWaveFun
  rw [norm_mul, show (ξ : ℂ) * (z : ℂ) * Complex.I = ((ξ * z : ℝ) : ℂ) * Complex.I by push_cast; ring,
    norm_exp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (windowIndicator_nonneg a L z))]

theorem planeWaveFun_eq_zero_of_notMem {ξ a L z : ℝ} (hz : z ∉ Ico a (a + L)) :
    planeWaveFun ξ a L z = 0 := by
  rw [planeWaveFun, windowIndicator_eq, if_neg hz]; simp

theorem lintegral_enorm_planeWaveFun_sq {ξ a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    ∫⁻ z, ‖planeWaveFun ξ a L z‖ₑ ^ 2 ∂halfLineMeasure = 1 := by
  have hpt : ∀ z, ‖planeWaveFun ξ a L z‖ₑ ^ 2 =
      (Ico a (a + L)).indicator (fun _ => ENNReal.ofReal L⁻¹) z := by
    intro z
    rw [← ofReal_norm, norm_planeWaveFun, ← ENNReal.ofReal_pow (by
      exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (windowIndicator_nonneg a L z)),
      mul_pow, windowIndicator_sq, inv_pow, Real.sq_sqrt hL.le, windowIndicator_eq]
    split_ifs with h
    · rw [Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, mul_zero, ENNReal.ofReal_zero]
  simp_rw [hpt]
  rw [lintegral_indicator measurableSet_Ico, setLIntegral_const, halfLineMeasure,
    Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (fun z hz => le_trans ha hz.1), Real.volume_Ico,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hL.le)]
  rw [show a + L - a = L by ring, inv_mul_cancel₀ hL.ne', ENNReal.ofReal_one]

theorem memLp_planeWaveFun {ξ a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    MemLp (planeWaveFun ξ a L) 2 halfLineMeasure := by
  refine ⟨(measurable_planeWaveFun ξ a L).aestronglyMeasurable, ?_⟩
  rw [SchurKernel.eLpNorm_two_eq, lintegral_enorm_planeWaveFun_sq ha hL, ENNReal.one_rpow]
  exact ENNReal.one_lt_top

/-- The plane-wave packet as an element of `L²(0, ∞)`. -/
def planeWave (ξ a L : ℝ) (ha : 0 ≤ a) (hL : 0 < L) : Lp ℂ 2 halfLineMeasure :=
  (memLp_planeWaveFun (ξ := ξ) ha hL).toLp _

theorem planeWave_coeFn {ξ a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    (planeWave ξ a L ha hL : ℝ → ℂ) =ᵐ[halfLineMeasure] planeWaveFun ξ a L :=
  MemLp.coeFn_toLp _

theorem norm_planeWave {ξ a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) : ‖planeWave ξ a L ha hL‖ = 1 := by
  rw [planeWave, Lp.norm_toLp, SchurKernel.eLpNorm_two_eq, lintegral_enorm_planeWaveFun_sq ha hL,
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
    ‖k.op (planeWave ξ a L ha hL) - convSymbol κ ξ • planeWave ξ a L ha hL‖ ^ 2 ≤
      2 / L * (∫ s, |κ s|) * ∫ s, |s| * |κ s| := by
  set f := planeWave ξ a L ha hL
  set F := planeWaveFun ξ a L
  set c := convSymbol κ ξ
  set Δ : ℝ → ℝ → ℝ := fun y s => windowIndicator a L (y - s) - windowIndicator a L y with hΔ
  have hFm : Measurable F := measurable_planeWaveFun ξ a L
  have hFb : ∀ z, ‖F z‖ ≤ (Real.sqrt L)⁻¹ := fun z => by
    rw [norm_planeWaveFun]
    have : windowIndicator a L z ≤ 1 := by rw [windowIndicator_eq]; split_ifs <;> norm_num
    exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) this
  have hFsupp : ∀ z, z ∉ Ici (0 : ℝ) → F z = 0 := fun z hz =>
    planeWaveFun_eq_zero_of_notMem fun h => hz (le_trans ha h.1)
  -- the pointwise identity
  have hdiff : ∀ y s, F (y - s) - Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I) * F y =
      (((Real.sqrt L)⁻¹ * Δ y s : ℝ) : ℂ) *
        Complex.exp ((ξ : ℂ) * ((y - s : ℝ) : ℂ) * Complex.I) := by
    intro y s
    simp only [F, planeWaveFun, hΔ]
    have he : Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I) *
        Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I) =
        Complex.exp ((ξ : ℂ) * ((y - s : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    push_cast
    rw [show ∀ u v w x : ℂ, u * x - w * (v * y') = 0 → True from fun _ _ _ _ _ => trivial] at *
    linear_combination (((Real.sqrt L)⁻¹ : ℂ) * (windowIndicator a L y : ℂ)) * he
  sorry

end Weyl

end

end GaloisForLFunctions.HTGeometry
