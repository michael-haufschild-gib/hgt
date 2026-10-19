import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateEnergyComparison

/-!
# The pole-free variation inequality

Let `μ_a = m_a(x) sinh(x/2) dx` on `(0, ∞)`, a positive measure of mass `sinh(a/2)/2`. The source
of the two-sided representation, `4 sinh(a/2) ∫ u² dμ_a`, splits as

    4 sinh(a/2) ∫ u² dμ_a = 8 (∫ u dμ_a)² + 4 sinh(a/2) ∫ (u − ū)² dμ_a,   ū = 2 ∫ u dμ_a / sinh(a/2),

the first term being the pole term `2 (∫ m_a u e^{−x/2})²` of the explicit formula for the odd test
`m_a u`, the second the **profile variance** `V_a(u)`. Subtracting from `u` its mean `ū` times a
wide plateau `u_L` gives a test `m_a (u − ū u_L)` whose source is at most `V_a(u)`, whose
same-side and reflected energies differ from those of `u` by terms controlled through Young's
inequality by the energies of the plateau, which are `O(e^{−8L})`. Hence, unconditionally,

    markovEnergy(Φ(ω_a (u − ū u_L))) → 2 S(ω_a, u) − D(ω_a, u) + V_a(u)   (L → ∞),

so the **pole-free variation inequality** `D ≤ 2S + V_a(u)`, sharper than
`D ≤ 2S + 4 sinh(a/2) ∫ u² dμ_a` by the pole term and invariant under `u ↦ u + c`, holds exactly
when the Markov energies of the mean-corrected tests are asymptotically nonnegative; nonnegativity
of the odd Markov form on compactly supported tests, the content of the Riemann Hypothesis in the
odd-sector criterion, implies it.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The profile variance -/

/-- The half-line moment `∫_{x>0} u m_a sinh(x/2)`. -/
def profileMoment (a : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)

/-- The profile variance `4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2) − 8 (∫_{x>0} u m_a sinh(x/2))²`. -/
def profileVariance (a : ℝ) (u : ℝ → ℝ) : ℝ :=
  4 * Real.sinh (a / 2) * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
    8 * profileMoment a u ^ 2

theorem integrableOn_mul_shiftDifference_mul_sinh {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (a : ℝ) :
    IntegrableOn (fun x => u x * shiftDifference a x * Real.sinh (x / 2)) (Ioi 0) := by
  have hc : Continuous fun x => u x * shiftDifference a x * Real.sinh (x / 2) :=
    (hu.mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hcs : HasCompactSupport fun x => u x * shiftDifference a x * Real.sinh (x / 2) :=
    (huc.mul_right (f' := shiftDifference a)).mul_right (f' := fun x => Real.sinh (x / 2))
  exact (hc.integrable_of_hasCompactSupport hcs).integrableOn

theorem integrableOn_sq_mul_shiftDifference_mul_sinh {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (a : ℝ) :
    IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) (Ioi 0) := by
  have hg : Continuous fun x => shiftDifference a x * Real.sinh (x / 2) :=
    (continuous_shiftDifference a).mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  refine (integrableOn_continuous_mul_sq hg hu huc (Ioi 0)).congr_fun (fun x _ => ?_)
    measurableSet_Ioi
  show shiftDifference a x * Real.sinh (x / 2) * u x ^ 2 = _
  ring

/-- The profile variance is `4 sinh(a/2)` times the variance of `u` against `μ_a`. -/
theorem profileVariance_eq {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    profileVariance a u = 4 * Real.sinh (a / 2) *
      ∫ x in Ioi (0 : ℝ), (u x - 2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 *
        shiftDifference a x * Real.sinh (x / 2) := by
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  set m := profileMoment a u with hm
  set c := 2 * m / Real.sinh (a / 2) with hc
  have h1 := integrableOn_sq_mul_shiftDifference_mul_sinh hu huc a
  have h2 := integrableOn_mul_shiftDifference_mul_sinh hu huc a
  have h3 := (integrable_shiftDifference_mul_sinh_half a).integrableOn (s := Ioi 0)
  have e : ∀ x, (u x - c) ^ 2 * shiftDifference a x * Real.sinh (x / 2) =
      u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) -
        2 * c * (u x * shiftDifference a x * Real.sinh (x / 2)) +
        c ^ 2 * (shiftDifference a x * Real.sinh (x / 2)) := fun x => by ring
  have h2c : IntegrableOn (fun x => 2 * c * (u x * shiftDifference a x * Real.sinh (x / 2)))
    (Ioi 0) := h2.const_mul _
  have h12 : IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) -
    2 * c * (u x * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) := h1.sub h2c
  have h3c : IntegrableOn (fun x => c ^ 2 * (shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) :=
    h3.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi fun x _ => e x, integral_add h12 h3c,
    integral_sub h1 h2c, integral_const_mul, integral_const_mul,
    integral_Ioi_shiftDifference_mul_sinh_half]
  unfold profileVariance
  rw [← hm]
  show 4 * Real.sinh (a / 2) * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
      8 * m ^ 2 = 4 * Real.sinh (a / 2) *
      ((∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) - 2 * c * m +
        c ^ 2 * (Real.sinh (a / 2) / 2))
  rw [hc]
  field_simp
  ring

theorem profileVariance_nonneg {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) : 0 ≤ profileVariance a u := by
  rw [profileVariance_eq ha hu huc]
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
  have hx0 : 0 < x := hx
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (shiftDifference_nonneg_of_nonneg ha.le hx0.le))
    (Real.sinh_nonneg_iff.mpr (by positivity))

/-- The profile variance is at most the source of the two-sided representation. -/
theorem profileVariance_le_source (a : ℝ) (u : ℝ → ℝ) :
    profileVariance a u ≤
      4 * Real.sinh (a / 2) * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  unfold profileVariance
  nlinarith [sq_nonneg (profileMoment a u)]

/-! ### The source of the mean-corrected profile -/

/-- The mean-corrected profile `u − ū u_L`, `ū = 2 ∫ u dμ_a / sinh(a/2)`. -/
def meanCorrectedProfile (a : ℝ) (u : ℝ → ℝ) (L : ℝ) : ℝ → ℝ :=
  fun x => u x - 2 * profileMoment a u / Real.sinh (a / 2) * smoothPlateau L x

/-- For `L` beyond the support of `u`, the source of `u − ū u_L` is the profile variance plus
`4 sinh(a/2) ū² (∫ u_L² dμ_a − sinh(a/2)/2)`. -/
theorem source_meanCorrectedProfile_eq {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) {R L : ℝ} (hsupp : ∀ x, R < |x| → u x = 0) (hRL : R ≤ L) :
    4 * Real.sinh (a / 2) *
      (∫ x in Ioi (0 : ℝ), meanCorrectedProfile a u L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) =
      profileVariance a u + 4 * Real.sinh (a / 2) * (2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 *
        ((∫ x in Ioi (0 : ℝ), smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
          Real.sinh (a / 2) / 2) := by
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  set m := profileMoment a u with hm
  set c := 2 * m / Real.sinh (a / 2) with hc
  have h1 := integrableOn_sq_mul_shiftDifference_mul_sinh hu huc a
  have h2 := integrableOn_mul_shiftDifference_mul_sinh hu huc a
  have hpl := integrableOn_sq_mul_shiftDifference_mul_sinh (contDiff_smoothPlateau L).continuous
    (hasCompactSupport_smoothPlateau L) a
  have huL : ∀ x, u x * smoothPlateau L x = u x := by
    intro x
    by_cases hx : R < |x|
    · rw [hsupp x hx, zero_mul]
    · rw [not_lt] at hx
      rw [smoothPlateau_eq_one (hx.trans hRL), mul_one]
  have e : ∀ x, meanCorrectedProfile a u L x ^ 2 * shiftDifference a x * Real.sinh (x / 2) =
      u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) -
        2 * c * (u x * shiftDifference a x * Real.sinh (x / 2)) +
        c ^ 2 * (smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) := fun x => by
    have := huL x
    show (u x - c * smoothPlateau L x) ^ 2 * shiftDifference a x * Real.sinh (x / 2) = _
    linear_combination (-(2 * c) * shiftDifference a x * Real.sinh (x / 2)) * this
  have h2c : IntegrableOn (fun x => 2 * c * (u x * shiftDifference a x * Real.sinh (x / 2)))
    (Ioi 0) := h2.const_mul _
  have h12 : IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) -
    2 * c * (u x * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) := h1.sub h2c
  have hplc : IntegrableOn (fun x => c ^ 2 *
    (smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) := hpl.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi fun x _ => e x, integral_add h12 hplc,
    integral_sub h1 h2c, integral_const_mul, integral_const_mul]
  have hm' : (∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)) = m := rfl
  rw [hm']
  unfold profileVariance
  rw [← hm, hc]
  field_simp
  ring

theorem integral_sq_smoothPlateau_mul_le {a : ℝ} (ha : 0 < a) (L : ℝ) :
    (∫ x in Ioi (0 : ℝ), smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) ≤
      Real.sinh (a / 2) / 2 := by
  rw [← integral_Ioi_shiftDifference_mul_sinh_half a]
  refine setIntegral_mono_on (integrableOn_sq_mul_shiftDifference_mul_sinh
    (contDiff_smoothPlateau L).continuous (hasCompactSupport_smoothPlateau L) a)
    (integrable_shiftDifference_mul_sinh_half a).integrableOn measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  have hms : 0 ≤ shiftDifference a x * Real.sinh (x / 2) :=
    mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx0.le)
      (Real.sinh_nonneg_iff.mpr (by positivity))
  have hp1 : smoothPlateau L x ^ 2 ≤ 1 :=
    pow_le_one₀ (smoothPlateau_nonneg L x) (smoothPlateau_le_one L x)
  calc smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)
      = smoothPlateau L x ^ 2 * (shiftDifference a x * Real.sinh (x / 2)) := by ring
    _ ≤ 1 * (shiftDifference a x * Real.sinh (x / 2)) := mul_le_mul_of_nonneg_right hp1 hms
    _ = _ := one_mul _

/-- The source of the mean-corrected profile is at most the profile variance. -/
theorem source_meanCorrectedProfile_le {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) {R L : ℝ} (hsupp : ∀ x, R < |x| → u x = 0) (hRL : R ≤ L) :
    4 * Real.sinh (a / 2) *
      (∫ x in Ioi (0 : ℝ), meanCorrectedProfile a u L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) ≤
      profileVariance a u := by
  rw [source_meanCorrectedProfile_eq ha hu huc hsupp hRL]
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have h0 : 0 ≤ 4 * Real.sinh (a / 2) * (2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 := by
    positivity
  have h := mul_nonpos_of_nonneg_of_nonpos h0 (sub_nonpos.mpr (integral_sq_smoothPlateau_mul_le ha L))
  linarith only [h]

/-- The source of the mean-corrected profile is at least the profile variance minus
`4 sinh(a/2) ū² C e^{16a} e^{−8L}`. -/
theorem source_meanCorrectedProfile_ge {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(16 * |x|))) {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) {R L : ℝ}
    (hsupp : ∀ x, R < |x| → u x = 0) (hRL : R ≤ L) (hL0 : 0 ≤ L) :
    profileVariance a u - 4 * Real.sinh (a / 2) * (2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 *
        (C * Real.exp (16 * a) * Real.exp (-(8 * L))) ≤
      4 * Real.sinh (a / 2) *
        ∫ x in Ioi (0 : ℝ), meanCorrectedProfile a u L x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  rw [source_meanCorrectedProfile_eq ha hu huc hsupp hRL]
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have h0 : 0 ≤ 4 * Real.sinh (a / 2) * (2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 := by
    positivity
  have hP := integral_sq_mul_shiftDifference_mul_sinh_ge hC0 hC ha
    (contDiff_smoothPlateau L).continuous (hasCompactSupport_smoothPlateau L) hL0
    (fun x hx => smoothPlateau_eq_one hx)
  have h := mul_le_mul_of_nonneg_left (show -(C * Real.exp (16 * a) * Real.exp (-(8 * L))) ≤
    (∫ x in Ioi (0 : ℝ), smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
      Real.sinh (a / 2) / 2 by linarith only [hP]) h0
  linarith only [h]

/-! ### Constants -/

/-- `Φ(0) C e^{16a} Λ² (∫ archLevyDensity(t) t dt + Σ n^{−3})`. -/
def plateauSameSideConstant (C Λ a : ℝ) : ℝ :=
  riemannKernelReal 0 * (C * Real.exp (16 * a)) * Λ ^ 2 *
    ((∫ t in Ioi (0 : ℝ), archLevyDensity t * t) + ∑' n : ℕ, 1 / (n : ℝ) ^ 3)

/-- `Φ(0) C e^{16a} (∫ archLevyDensity(t) t dt + Σ n^{−2})`. -/
def plateauReflectedConstant (C a : ℝ) : ℝ :=
  riemannKernelReal 0 * (C * Real.exp (16 * a)) *
    ((∫ t in Ioi (0 : ℝ), archLevyDensity t * t) + ∑' n : ℕ, 1 / (n : ℝ) ^ 2)

/-- The constant of the limit identity for the mean-corrected tests. -/
def poleFreeConstant (C Λ a : ℝ) (u : ℝ → ℝ) : ℝ :=
  4 * sameSideEnergy (shiftedGroundState a) u + 2 * reflectedDifferenceEnergy (shiftedGroundState a) u +
    8 * (2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 * plateauSameSideConstant C Λ a +
    4 * (2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 * plateauReflectedConstant C a +
    4 * Real.sinh (a / 2) * (2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 * (C * Real.exp (16 * a))

theorem integral_archLevyDensity_mul_id_nonneg : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * t :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => mul_nonneg (archLevyDensity_pos ht).le (le_of_lt ht)

theorem plateauSameSideConstant_nonneg {C : ℝ} (hC0 : 0 ≤ C) (Λ a : ℝ) :
    0 ≤ plateauSameSideConstant C Λ a := by
  unfold plateauSameSideConstant
  have := integral_archLevyDensity_mul_id_nonneg
  have hsum : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 3 := tsum_nonneg fun n => by positivity
  have := (riemannKernelReal_pos 0).le
  positivity

theorem plateauReflectedConstant_nonneg {C : ℝ} (hC0 : 0 ≤ C) (a : ℝ) :
    0 ≤ plateauReflectedConstant C a := by
  unfold plateauReflectedConstant
  have := integral_archLevyDensity_mul_id_nonneg
  have hsum : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := tsum_nonneg fun n => by positivity
  have := (riemannKernelReal_pos 0).le
  positivity

theorem reflectedDifferenceEnergy_shiftedGroundState_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ → ℝ) :
    0 ≤ reflectedDifferenceEnergy (shiftedGroundState a) u :=
  add_nonneg (setIntegral_nonneg measurableSet_Ioi fun t ht => mul_nonneg (archLevyDensity_pos ht).le
      (integral_reflectedDifference_shiftedGroundState_nonneg ha u t))
    (tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n)
      (integral_reflectedDifference_shiftedGroundState_nonneg ha u _))

theorem poleFreeConstant_nonneg {C : ℝ} (hC0 : 0 ≤ C) (Λ : ℝ) {a : ℝ} (ha : 0 < a) (u : ℝ → ℝ) :
    0 ≤ poleFreeConstant C Λ a u := by
  unfold poleFreeConstant
  have h1 := sameSideEnergy_nonneg ha u
  have h2 := reflectedDifferenceEnergy_shiftedGroundState_nonneg ha u
  have h3 := plateauSameSideConstant_nonneg hC0 Λ a
  have h4 := plateauReflectedConstant_nonneg hC0 a
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  positivity

/-! ### The limit identity for the mean-corrected tests -/

/-- **Two-sided bound for the mean-corrected tests.** For `L ≥ max(R, 0)`, with `R` a support
radius of `u` and `Λ` a Lipschitz constant of the plateaus,

    |markovEnergy(Φ(ω_a (u − ū u_L))) − (2 S(ω_a,u) − D(ω_a,u) + V_a(u))| ≤ K e^{−4L}. -/
theorem abs_markovEnergy_meanCorrectedProfile_sub_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(16 * |x|))) {Λ : ℝ}
    (hΛ : ∀ L x y : ℝ, |smoothPlateau L y - smoothPlateau L x| ≤ Λ * |y - x|) {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    {R L : ℝ} (hsupp : ∀ x, R < |x| → u x = 0) (hRL : R ≤ L) (hL0 : 0 ≤ L) :
    |markovEnergy (fun x =>
        (phiDoobTest (fun y => shiftedGroundState a y * meanCorrectedProfile a u L y) x : ℂ)) -
      (2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u)| ≤
      poleFreeConstant C Λ a u * Real.exp (-(4 * L)) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hS0 : 0 ≤ sameSideEnergy (shiftedGroundState a) u := sameSideEnergy_nonneg ha u
  have hD0 := reflectedDifferenceEnergy_shiftedGroundState_nonneg ha u
  have hKS0 := plateauSameSideConstant_nonneg hC0 Λ a
  have hKD0 := plateauReflectedConstant_nonneg hC0 a
  set S := sameSideEnergy (shiftedGroundState a) u with hS
  set D := reflectedDifferenceEnergy (shiftedGroundState a) u with hD
  set V := profileVariance a u with hV
  set c := 2 * profileMoment a u / Real.sinh (a / 2) with hc
  set KS := plateauSameSideConstant C Λ a with hKS
  set KD := plateauReflectedConstant C a with hKD
  set Ce := C * Real.exp (16 * a) with hCe
  have hCe0 : 0 ≤ Ce := by positivity
  set F := Real.exp (-(4 * L)) with hF
  have hF0 : 0 < F := Real.exp_pos _
  have hF1 : F ≤ 1 := by
    rw [hF, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith only [hL0])
  have hF2 : Real.exp (-(8 * L)) = F ^ 2 := by
    rw [hF, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hFF : F ^ 2 ≤ F := by
    calc F ^ 2 = F * F := sq F
      _ ≤ F * 1 := mul_le_mul_of_nonneg_left hF1 hF0.le
      _ = F := mul_one F
  have hFinv : (1 + F⁻¹) * F ^ 2 = F ^ 2 + F := by
    field_simp
  -- the plateau
  have hp1 : ContDiff ℝ 1 (smoothPlateau L) := (contDiff_smoothPlateau L).of_le (by norm_num)
  have hpc := hasCompactSupport_smoothPlateau L
  have hone : ∀ x, |x| ≤ L → smoothPlateau L x = 1 := fun x hx => smoothPlateau_eq_one hx
  have hSL : sameSideEnergy (shiftedGroundState a) (smoothPlateau L) ≤ KS * F ^ 2 := by
    have h := sameSideEnergy_plateau_le hC0 hC ha hp1 hpc (fun x y => hΛ L x y) hone
    rw [hF2] at h
    exact h
  have hDL : reflectedDifferenceEnergy (shiftedGroundState a) (smoothPlateau L) ≤ KD * F ^ 2 := by
    have h := reflectedDifferenceEnergy_plateau_le hC0 hC ha hp1 hpc (smoothPlateau_nonneg L)
      (smoothPlateau_le_one L) hone
    rw [hF2] at h
    exact h
  -- the corrected profile
  set w := meanCorrectedProfile a u L with hw
  have hwx : ∀ x, w x = u x - c * smoothPlateau L x := fun x => rfl
  have hwcd : ContDiff ℝ 2 w := by
    show ContDiff ℝ 2 fun x => u x - c * smoothPlateau L x
    exact hu.sub (contDiff_const.mul (contDiff_smoothPlateau L))
  have hw1 : ContDiff ℝ 1 w := hwcd.of_le (by norm_num)
  have hwc : HasCompactSupport w := by
    show HasCompactSupport fun x => u x - c * smoothPlateau L x
    exact huc.sub hpc.mul_left
  have hweven : ∀ x, w (-x) = w x := fun x => by
    rw [hwx, hwx, heven, smoothPlateau_neg]
  have hQ := markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hwcd hwc hweven
  have hsrc_le := source_meanCorrectedProfile_le ha hu.continuous huc hsupp hRL
  have hsrc_ge := source_meanCorrectedProfile_ge hC0 hC ha hu.continuous huc hsupp hRL hL0
  rw [hF2] at hsrc_ge
  -- Young comparisons
  have hSw : sameSideEnergy (shiftedGroundState a) w ≤
      (1 + F) * S + (1 + F⁻¹) * c ^ 2 * sameSideEnergy (shiftedGroundState a) (smoothPlateau L) := by
    refine sameSideEnergy_le_combination ha hu1 huc hp1 hpc hw1 hwc fun x y => ?_
    calc (w x - w y) ^ 2
        = ((u x - u y) - c * (smoothPlateau L x - smoothPlateau L y)) ^ 2 := by
          rw [hwx, hwx]
          ring
      _ ≤ _ := young_sq_sub hF0 _ _ _
  have hDw : reflectedDifferenceEnergy (shiftedGroundState a) w ≤
      (1 + F) * D + (1 + F⁻¹) * c ^ 2 *
        reflectedDifferenceEnergy (shiftedGroundState a) (smoothPlateau L) := by
    refine reflectedDifferenceEnergy_le_combination ha hu1 huc hp1 hpc hw1 hwc fun x y => ?_
    calc (w x - w y) ^ 2
        = ((u x - u y) - c * (smoothPlateau L x - smoothPlateau L y)) ^ 2 := by
          rw [hwx, hwx]
          ring
      _ ≤ _ := young_sq_sub hF0 _ _ _
  have hSu : S ≤ (1 + F) * sameSideEnergy (shiftedGroundState a) w +
      (1 + F⁻¹) * c ^ 2 * sameSideEnergy (shiftedGroundState a) (smoothPlateau L) := by
    refine sameSideEnergy_le_combination ha hw1 hwc hp1 hpc hu1 huc fun x y => ?_
    calc (u x - u y) ^ 2
        = ((w x - w y) - (-c) * (smoothPlateau L x - smoothPlateau L y)) ^ 2 := by
          rw [hwx, hwx]
          ring
      _ ≤ (1 + F) * (w x - w y) ^ 2 +
          (1 + F⁻¹) * (-c) ^ 2 * (smoothPlateau L x - smoothPlateau L y) ^ 2 :=
          young_sq_sub hF0 _ _ _
      _ = _ := by ring
  have hDu : D ≤ (1 + F) * reflectedDifferenceEnergy (shiftedGroundState a) w +
      (1 + F⁻¹) * c ^ 2 * reflectedDifferenceEnergy (shiftedGroundState a) (smoothPlateau L) := by
    refine reflectedDifferenceEnergy_le_combination ha hw1 hwc hp1 hpc hu1 huc fun x y => ?_
    calc (u x - u y) ^ 2
        = ((w x - w y) - (-c) * (smoothPlateau L x - smoothPlateau L y)) ^ 2 := by
          rw [hwx, hwx]
          ring
      _ ≤ (1 + F) * (w x - w y) ^ 2 +
          (1 + F⁻¹) * (-c) ^ 2 * (smoothPlateau L x - smoothPlateau L y) ^ 2 :=
          young_sq_sub hF0 _ _ _
      _ = _ := by ring
  have hc2 : 0 ≤ (1 + F⁻¹) * c ^ 2 := by positivity
  have hSL' := mul_le_mul_of_nonneg_left hSL hc2
  have hDL' := mul_le_mul_of_nonneg_left hDL hc2
  have hKSE : (1 + F⁻¹) * c ^ 2 * (KS * F ^ 2) = c ^ 2 * KS * (F ^ 2 + F) := by
    rw [← hFinv]
    ring
  have hKDE : (1 + F⁻¹) * c ^ 2 * (KD * F ^ 2) = c ^ 2 * KD * (F ^ 2 + F) := by
    rw [← hFinv]
    ring
  set Sw := sameSideEnergy (shiftedGroundState a) w with hSw_def
  set Dw := reflectedDifferenceEnergy (shiftedGroundState a) w with hDw_def
  have hSw' : Sw ≤ (1 + F) * S + c ^ 2 * KS * (F ^ 2 + F) := by linarith only [hSw, hSL', hKSE]
  have hDw' : Dw ≤ (1 + F) * D + c ^ 2 * KD * (F ^ 2 + F) := by linarith only [hDw, hDL', hKDE]
  have hSu' : S ≤ (1 + F) * Sw + c ^ 2 * KS * (F ^ 2 + F) := by linarith only [hSu, hSL', hKSE]
  have hDu' : D ≤ (1 + F) * Dw + c ^ 2 * KD * (F ^ 2 + F) := by linarith only [hDu, hDL', hKDE]
  -- elementary bounds in `F`
  have hE2 : F ^ 2 + F ≤ 2 * F := by linarith only [hFF]
  have hE2' : F ^ 2 + F ≤ 2 := by linarith only [hFF, hF1]
  have hcKS0 : 0 ≤ c ^ 2 * KS := by positivity
  have hcKD0 : 0 ≤ c ^ 2 * KD := by positivity
  have hcKS_E : c ^ 2 * KS * (F ^ 2 + F) ≤ c ^ 2 * KS * (2 * F) := mul_le_mul_of_nonneg_left hE2 hcKS0
  have hcKD_E : c ^ 2 * KD * (F ^ 2 + F) ≤ c ^ 2 * KD * (2 * F) := mul_le_mul_of_nonneg_left hE2 hcKD0
  have hcKS_2 : c ^ 2 * KS * (F ^ 2 + F) ≤ c ^ 2 * KS * 2 := mul_le_mul_of_nonneg_left hE2' hcKS0
  have hcKD_2 : c ^ 2 * KD * (F ^ 2 + F) ≤ c ^ 2 * KD * 2 := mul_le_mul_of_nonneg_left hE2' hcKD0
  have hFS : F * S ≤ S := mul_le_of_le_one_left hS0 hF1
  have hFD : F * D ≤ D := mul_le_of_le_one_left hD0 hF1
  have hSwU : Sw ≤ 2 * S + 2 * (c ^ 2 * KS) := by linarith only [hSw', hcKS_2, hFS]
  have hDwU : Dw ≤ 2 * D + 2 * (c ^ 2 * KD) := by linarith only [hDw', hcKD_2, hFD]
  have hFSw := mul_le_mul_of_nonneg_left hSwU hF0.le
  have hFDw := mul_le_mul_of_nonneg_left hDwU hF0.le
  have hSwL : S - F * (2 * S + 4 * (c ^ 2 * KS)) ≤ Sw := by linarith only [hSu', hcKS_E, hFSw]
  have hDwL : D - F * (2 * D + 4 * (c ^ 2 * KD)) ≤ Dw := by linarith only [hDu', hcKD_E, hFDw]
  have hsrcF : 4 * Real.sinh (a / 2) * c ^ 2 * (Ce * F ^ 2) ≤ 4 * Real.sinh (a / 2) * c ^ 2 * (Ce * F) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFF hCe0) (by positivity)
  have hKdef : poleFreeConstant C Λ a u =
      4 * S + 2 * D + 8 * c ^ 2 * KS + 4 * c ^ 2 * KD + 4 * Real.sinh (a / 2) * c ^ 2 * Ce := rfl
  rw [hQ, hKdef, abs_sub_le_iff]
  constructor
  · nlinarith only [hSw', hcKS_E, hDwL, hsrc_le, hFS, hFD, hcKS0, hcKD0, hS0, hD0, hCe0, hF0, hs,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hs.le) (mul_nonneg (sq_nonneg c) (mul_nonneg hCe0 hF0.le))]
  · nlinarith only [hSwL, hDw', hcKD_E, hsrc_ge, hsrcF, hFS, hFD, hcKS0, hcKD0, hS0, hD0, hF0, hs]

/-- **The pole-free form is the limit of Markov energies of compactly supported odd tests.**
For every `a > 0` and every even `u ∈ C²_c(ℝ)`,

    markovEnergy(Φ(ω_a (u − ū u_L))) → 2 S(ω_a,u) − D(ω_a,u) + V_a(u)   as L → ∞. -/
theorem tendsto_markovEnergy_meanCorrectedProfile {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    Tendsto (fun L => markovEnergy (fun x =>
        (phiDoobTest (fun y => shiftedGroundState a y * meanCorrectedProfile a u L y) x : ℂ)))
      atTop (𝓝 (2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le_exp_sixteen
  obtain ⟨Λ, _, hΛ⟩ := exists_smoothPlateau_lipschitz
  obtain ⟨R, hR1, hsupp⟩ := exists_support_radius huc
  set K := poleFreeConstant C Λ a u with hK
  have hK0 : 0 ≤ K := poleFreeConstant_nonneg hC0 Λ ha u
  rw [Metric.tendsto_atTop]
  intro η hη
  have hpos : 0 < K / η + 1 := by positivity
  refine ⟨max R (Real.log (K / η + 1) / 4), fun L hL => ?_⟩
  have hRL : R ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : 0 ≤ L := le_trans (by linarith only [hR1]) hRL
  rw [Real.dist_eq]
  have h1 := abs_markovEnergy_meanCorrectedProfile_sub_le hC0 hC hΛ ha hu huc heven hsupp hRL hL0
  have hexp : Real.exp (-(4 * L)) ≤ (K / η + 1)⁻¹ := by
    have h := Real.exp_le_exp.mpr (show -(4 * L) ≤ -(Real.log (K / η + 1)) by
      linarith only [le_max_right R (Real.log (K / η + 1) / 4), hL])
    rw [Real.exp_neg (Real.log (K / η + 1)), Real.exp_log hpos] at h
    exact h
  have hKη : K * (K / η + 1)⁻¹ < η := by
    rw [div_add_one hη.ne', inv_div]
    have hden : 0 < K + η := by positivity
    calc K * (η / (K + η)) = η * (K / (K + η)) := by ring
      _ < η * 1 := mul_lt_mul_of_pos_left ((div_lt_one hden).mpr (by linarith only [hη])) hη
      _ = η := mul_one η
  calc _ ≤ K * Real.exp (-(4 * L)) := h1
    _ ≤ K * (K / η + 1)⁻¹ := mul_le_mul_of_nonneg_left hexp hK0
    _ < η := hKη

/-- The pole-free variation inequality `D ≤ 2S + V_a(u)` holds exactly when the Markov energies of
the mean-corrected tests are eventually bounded below by every `−η < 0`. -/
theorem reflectedDifferenceEnergy_le_poleFree_iff {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    reflectedDifferenceEnergy (shiftedGroundState a) u ≤
        2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u ↔
      ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, -η ≤ markovEnergy (fun x =>
        (phiDoobTest (fun y => shiftedGroundState a y * meanCorrectedProfile a u L y) x : ℂ)) := by
  have ht := tendsto_markovEnergy_meanCorrectedProfile ha hu huc heven
  constructor
  · intro h η hη
    exact (ht.eventually (eventually_gt_nhds (by linarith : -η < 2 * sameSideEnergy (shiftedGroundState a) u -
      reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u))).mono fun L hL => hL.le
  · intro h
    have hX : ∀ η : ℝ, 0 < η → -η ≤ 2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u :=
      fun η hη => ge_of_tendsto ht (h η hη)
    have h0 : 0 ≤ 2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u :=
      le_of_forall_pos_le_add fun η hη => by linarith only [hX η hη]
    linarith only [h0]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
