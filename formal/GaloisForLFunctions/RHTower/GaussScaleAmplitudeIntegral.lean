import GaloisForLFunctions.RHTower.GaussPrimeScaleFourier

/-!
# The moving amplitude and its exact period average

The prime scale of a Gauss component is `s_p(x) = p^{1-x} = b_p(x)^2`, extended one-periodically.
Its moving translate

`a_δ(x) = s_p(x) / s_p(x + δ)`

is a two-valued function of `x` on one period: it equals `p^δ` while `x + δ` stays below the
period, and `p^{δ-1}` after the wrap.  Consequently

`∫₀¹ a_δ(x)^m dx = (1 - δ) e^{m δ log p} + δ e^{m (δ - 1) log p)`,

which is the closed form the harmonic logarithmic rotation is applied to.
-/

namespace RHTower

open MeasureTheory Set

noncomputable section

/-! ## Integrals of functions constant off one point -/

theorem intervalIntegrable_of_eq_const_off_point
    {f : ℝ → ℝ} {a b c s : ℝ}
    (h : ∀ x ∈ Set.uIoc a b, x ≠ s → f x = c) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  have hnull : (volume : Measure ℝ) {s} = 0 := measure_singleton s
  have hae : (fun _ : ℝ => c) =ᵐ[volume.restrict (Set.uIoc a b)] f := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx hmem
    exact (h x hmem hx).symm
  exact (integrableOn_const (by simp [Real.volume_uIoc])).congr hae

theorem intervalIntegral_eq_const_off_point
    {f : ℝ → ℝ} {a b c s : ℝ}
    (h : ∀ x ∈ Set.uIoc a b, x ≠ s → f x = c) :
    ∫ x in a..b, f x = (b - a) * c := by
  have hnull : (volume : Measure ℝ) {s} = 0 := measure_singleton s
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc a b → f x = c := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx hmem
    exact h x hmem hx
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const, smul_eq_mul]

/-! ## The periodic prime scale -/

/-- The prime scale `s_p(x) = p^{1-x}` on one period. -/
def gaussScaleSegment (p : ℝ) (x : ℝ) : ℝ :=
  Real.exp ((1 - x) * Real.log p)

theorem gaussScaleSegment_pos (p x : ℝ) : 0 < gaussScaleSegment p x := Real.exp_pos _

/-- The prime scale is the square of the prime-scale amplitude. -/
theorem gaussScaleSegment_eq_gaussPrimeScale_sq (p x : ℝ) :
    gaussScaleSegment p x = gaussPrimeScale p x ^ 2 := by
  rw [gaussScaleSegment, gaussPrimeScale, ← Real.exp_nat_mul]
  ring_nf

/-- One-periodic extension of the prime scale. -/
def gaussScalePeriodic (p : ℝ) (x : ℝ) : ℝ :=
  gaussScaleSegment p (Int.fract x)

theorem gaussScalePeriodic_pos (p x : ℝ) : 0 < gaussScalePeriodic p x :=
  gaussScaleSegment_pos _ _

theorem gaussScalePeriodic_of_mem_Ico {p x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    gaussScalePeriodic p x = Real.exp ((1 - x) * Real.log p) := by
  rw [gaussScalePeriodic, Int.fract_eq_self.mpr ⟨hx0, hx1⟩, gaussScaleSegment]

/-- The moving amplitude `a_δ(x) = s_p(x)/s_p(x + δ)`. -/
def gaussMovingAmplitude (p δ x : ℝ) : ℝ :=
  gaussScalePeriodic p x / gaussScalePeriodic p (x + δ)

/-- Before the wrap the moving amplitude is the constant `p^δ`. -/
theorem gaussMovingAmplitude_of_lt_one {p δ x : ℝ}
    (hx0 : 0 ≤ x) (hδ0 : 0 ≤ δ) (h : x + δ < 1) :
    gaussMovingAmplitude p δ x = Real.exp (δ * Real.log p) := by
  have hx1 : x < 1 := by linarith
  have hxδ0 : 0 ≤ x + δ := by linarith
  rw [gaussMovingAmplitude, gaussScalePeriodic_of_mem_Ico hx0 hx1,
    gaussScalePeriodic_of_mem_Ico hxδ0 h, ← Real.exp_sub]
  congr 1
  ring

/-- After the wrap the moving amplitude is the constant `p^{δ-1}`. -/
theorem gaussMovingAmplitude_of_one_le {p δ x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hδ1 : δ ≤ 1) (h : 1 ≤ x + δ) :
    gaussMovingAmplitude p δ x = Real.exp ((δ - 1) * Real.log p) := by
  have hlow : 0 ≤ x + δ - 1 := by linarith
  have hhigh : x + δ - 1 < 1 := by linarith
  have hfract : Int.fract (x + δ) = x + δ - 1 := by
    have hshift : Int.fract (x + δ - 1) = Int.fract (x + δ) := Int.fract_sub_one (x + δ)
    rw [← hshift, Int.fract_eq_self.mpr ⟨hlow, hhigh⟩]
  rw [gaussMovingAmplitude, gaussScalePeriodic_of_mem_Ico hx0 hx1, gaussScalePeriodic,
    hfract, gaussScaleSegment, ← Real.exp_sub]
  congr 1
  ring

/-! ## The exact period average -/

/-- **Exact period average of the `m`-th power of the moving amplitude.**  The value is the
closed form `gaussAmplitudeSegment`. -/
theorem intervalIntegral_gaussMovingAmplitude_pow
    (p : ℝ) (m : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∫ x in (0:ℝ)..1, gaussMovingAmplitude p δ x ^ m) = gaussAmplitudeSegment p m δ := by
  have hlow : ∀ x ∈ Set.uIoc (0:ℝ) (1 - δ), x ≠ 1 - δ →
      gaussMovingAmplitude p δ x ^ m = Real.exp (((m : ℝ) * Real.log p) * δ) := by
    intro x hx hne
    rw [Set.uIoc_of_le (by linarith)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hlt : x + δ < 1 := by
      rcases lt_or_eq_of_le hx1 with h | h
      · linarith
      · exact absurd h hne
    rw [gaussMovingAmplitude_of_lt_one hx0.le hδ0 hlt, ← Real.exp_nat_mul]
    congr 1
    ring
  have hhigh : ∀ x ∈ Set.uIoc (1 - δ) (1:ℝ), x ≠ 1 →
      gaussMovingAmplitude p δ x ^ m = Real.exp (((m : ℝ) * Real.log p) * (δ - 1)) := by
    intro x hx hne
    rw [Set.uIoc_of_le (by linarith)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxlt : x < 1 := lt_of_le_of_ne hx1 hne
    have hx0' : 0 ≤ x := by linarith
    have hge : 1 ≤ x + δ := by linarith
    rw [gaussMovingAmplitude_of_one_le hx0' hxlt hδ1 hge, ← Real.exp_nat_mul]
    congr 1
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_eq_const_off_point hlow)
    (intervalIntegrable_of_eq_const_off_point hhigh)
  rw [← hsplit, intervalIntegral_eq_const_off_point hlow,
    intervalIntegral_eq_const_off_point hhigh, gaussAmplitudeSegment]
  ring

/-- **Exact two-variable average.**  Averaging the `m`-th power of the moving amplitude over both
the period and the translation gives the product of the two elementary scale moments. -/
theorem intervalIntegral_intervalIntegral_gaussMovingAmplitude_pow
    (p : ℝ) (hp : 1 < p) (m : ℕ) (hm : 1 ≤ m) :
    (∫ δ in (0:ℝ)..1, ∫ x in (0:ℝ)..1, gaussMovingAmplitude p δ x ^ m)
      = (p ^ m - 1) ^ 2 / (p ^ m * (m : ℝ) ^ 2 * (Real.log p) ^ 2) := by
  have hcongr : ∀ δ ∈ Set.uIcc (0:ℝ) 1,
      (∫ x in (0:ℝ)..1, gaussMovingAmplitude p δ x ^ m) = gaussAmplitudeSegment p m δ := by
    intro δ hδ
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hδ
    exact intervalIntegral_gaussMovingAmplitude_pow p m hδ.1 hδ.2
  rw [intervalIntegral.integral_congr hcongr]
  exact intervalIntegral_gaussAmplitudeSegment p hp m hm

end

end RHTower
