import GaloisForLFunctions.HTGeometry.ObserverTemporalBirthValuationLaw
import Mathlib

/-!
# Universal temporal wall crossing of an analytic spectral character

An active analytic spectral relation has an exact integer birth order.
Observe it for a time proportional to the inverse `r`th power of a positive
coupling. Its symmetric time-average character has exactly three regimes:

* below birth it tends to one and the detuning is unresolved;
* at birth it tends to a nontrivial universal sinc profile;
* above birth it tends to zero and the detuning is fully dephased.

The theorem is per character and makes no finiteness assumption on the
ambient spectrum. This is the finite-character core of temporal dimensional
wall crossing.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The real sinc reporter vanishes at arbitrarily large phase. -/
theorem tendsto_real_sinc_atTop_zero :
    Tendsto Real.sinc atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (f := fun x : ℝ => ‖Real.sinc x‖)
    (g := fun x : ℝ => |x|⁻¹) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _
  · filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with x hx
    have habs : 0 < |x| := abs_pos.mpr hx
    rw [Real.sinc_of_ne_zero hx, Real.norm_eq_abs, abs_div]
    simpa [one_div] using
      (div_le_div_iff_of_pos_right habs).2 (Real.abs_sin_le_one x)
  · apply tendsto_inv_atTop_zero.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    simp [abs_of_nonneg hx]

/-- A positive variable raised to a positive natural power tends to zero
through positive values. -/
theorem tendsto_pow_nhdsGT_zero
    {q : ℕ} (hq : 0 < q) :
    Tendsto (fun g : ℝ => g ^ q) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h :=
      (continuousAt_id.pow q).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hz : (0 : ℝ) ^ q = 0 := zero_pow hq.ne'
    simpa [hz] using h
  · filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    exact pow_pos hg q

/-- A detuning has exact positive leading profile `c g^b`. -/
def HasPositiveBirthProfile
    (detuning : ℝ → ℝ) (b : ℕ) (c : ℝ) : Prop :=
  Tendsto (fun g => detuning g / g ^ b) (𝓝[>] 0) (𝓝 c) ∧ 0 < c

/-- Positive real couplings approach the punctured complex origin. -/
theorem tendsto_ofReal_nhdsGT_zero_nhdsNE_zero :
    Tendsto (fun g : ℝ => (g : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt hg))

/-- Every active analytic detuning has a positive exact norm profile along
the physical positive-coupling ray. -/
theorem hasPositiveBirthProfile_norm_of_active
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hactive : AnalyticSectorActive f) :
    HasPositiveBirthProfile
      (fun g : ℝ => ‖f g‖)
      (analyticBirthOrder series)
      ‖analyticBirthUnit f series 0‖ := by
  constructor
  · have hcomplex :=
      tendsto_norm_div_norm_pow_analyticBirthOrder hf
    have hreal :=
      hcomplex.comp tendsto_ofReal_nhdsGT_zero_nhdsNE_zero
    apply hreal.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  · exact norm_pos_iff.mpr (analyticBirthUnit_zero_ne hf hactive)

/-- Below the birth horizon the scaled detuning is unresolved. -/
theorem tendsto_scaledDetuning_zero_of_lt_birth
    {detuning : ℝ → ℝ} {b r : ℕ} {c : ℝ}
    (hprofile : HasPositiveBirthProfile detuning b c)
    (hrb : r < b) :
    Tendsto (fun g => detuning g / g ^ r) (𝓝[>] 0) (𝓝 0) := by
  have hpow :
      Tendsto (fun g : ℝ => g ^ (b - r)) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_pow_nhdsGT_zero (Nat.sub_pos_of_lt hrb)).mono_right
      inf_le_left
  have hmul := hprofile.1.mul hpow
  simpa only [mul_zero] using hmul.congr' (by
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    have hg0 : g ≠ 0 := ne_of_gt hg
    rw [show b = r + (b - r) by omega, pow_add]
    field_simp
    rw [Nat.add_sub_cancel_left])

/-- At the birth horizon the scaled detuning converges to its nonzero
leading coefficient. -/
theorem tendsto_scaledDetuning_birth
    {detuning : ℝ → ℝ} {b : ℕ} {c : ℝ}
    (hprofile : HasPositiveBirthProfile detuning b c) :
    Tendsto (fun g => detuning g / g ^ b) (𝓝[>] 0) (𝓝 c) :=
  hprofile.1

/-- Beyond the birth horizon the scaled positive detuning diverges. -/
theorem tendsto_scaledDetuning_atTop_of_birth_lt
    {detuning : ℝ → ℝ} {b r : ℕ} {c : ℝ}
    (hprofile : HasPositiveBirthProfile detuning b c)
    (hbr : b < r) :
    Tendsto (fun g => detuning g / g ^ r) (𝓝[>] 0) atTop := by
  have hpow :
      Tendsto (fun g : ℝ => g ^ (r - b)) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_pow_nhdsGT_zero (Nat.sub_pos_of_lt hbr)
  have hinv :
      Tendsto (fun g : ℝ => (g ^ (r - b))⁻¹) (𝓝[>] 0) atTop :=
    hpow.inv_tendsto_nhdsGT_zero
  have hmul := hprofile.1.pos_mul_atTop hprofile.2 hinv
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with g hg
  change 0 < g at hg
  have hg0 : g ≠ 0 := ne_of_gt hg
  rw [show r = b + (r - b) by omega, pow_add]
  field_simp
  rw [Nat.add_sub_cancel_left]

/-- **Universal character wall crossing.** A time-averaged phase reporter
is one below its birth horizon, has a nontrivial sinc profile at birth, and
vanishes beyond birth. -/
theorem spectralCharacterReporter_wallCrossing
    {detuning : ℝ → ℝ} {b : ℕ} {c τ : ℝ}
    (hprofile : HasPositiveBirthProfile detuning b c)
    (hτ : 0 < τ) :
    (∀ r < b,
      Tendsto
        (fun g => Real.sinc (τ * (detuning g / g ^ r)))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g => Real.sinc (τ * (detuning g / g ^ b)))
      (𝓝[>] 0) (𝓝 (Real.sinc (τ * c))) ∧
    (∀ r, b < r →
      Tendsto
        (fun g => Real.sinc (τ * (detuning g / g ^ r)))
        (𝓝[>] 0) (𝓝 0)) := by
  constructor
  · intro r hr
    have harg :=
      (tendsto_scaledDetuning_zero_of_lt_birth hprofile hr).const_mul τ
    simpa using
      (Real.continuous_sinc.continuousAt.tendsto.comp harg)
  constructor
  · have harg := hprofile.1.const_mul τ
    exact Real.continuous_sinc.continuousAt.tendsto.comp harg
  · intro r hr
    have harg0 :=
      tendsto_scaledDetuning_atTop_of_birth_lt hprofile hr
    have harg : Tendsto
        (fun g => τ * (detuning g / g ^ r)) (𝓝[>] 0) atTop :=
      (harg0.atTop_mul_const hτ).congr' (by
        filter_upwards [] with g
        ring)
    exact tendsto_real_sinc_atTop_zero.comp harg

/-- **Analytic observer-time wall crossing.** For every active analytic
spectral relation, observation on the `g⁻ʳ` time scale has three and only
three universal regimes: unresolved below birth, sinc crossover at birth,
and complete dephasing above birth. -/
theorem analyticSectorReporter_wallCrossing
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hactive : AnalyticSectorActive f)
    {τ : ℝ} (hτ : 0 < τ) :
    (∀ r < analyticBirthOrder series,
      Tendsto
        (fun g : ℝ =>
          Real.sinc (τ * (‖f g‖ / g ^ r)))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g : ℝ =>
        Real.sinc
          (τ * (‖f g‖ / g ^ analyticBirthOrder series)))
      (𝓝[>] 0)
      (𝓝 (Real.sinc
        (τ * ‖analyticBirthUnit f series 0‖))) ∧
    (∀ r, analyticBirthOrder series < r →
      Tendsto
        (fun g : ℝ =>
          Real.sinc (τ * (‖f g‖ / g ^ r)))
        (𝓝[>] 0) (𝓝 0)) :=
  spectralCharacterReporter_wallCrossing
    (hasPositiveBirthProfile_norm_of_active hf hactive) hτ

end GaloisForLFunctions.HTGeometry
