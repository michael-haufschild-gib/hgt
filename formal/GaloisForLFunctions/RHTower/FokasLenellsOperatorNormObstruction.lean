import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeBounds
import GaloisForLFunctions.RHTower.FokasLenellsTimeMultiplier
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# An origin obstruction to operator-norm time differentiation

Interval indicators turn a right origin norm limit of a multiplier symbol
into an operator-norm lower bound. For the actual upper scattering channel,
the difference-quotient error has limit half the compatibility moment norm.
This detects a failure invisible to strong L2 differentiation.
-/

open MeasureTheory Complex Matrix Filter Topology Set
open scoped ENNReal NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem multiplier_norm_lower_of_origin_limit
    (T : SoninL2 →L[ℂ] SoninL2) (φ : ℝ → ℂ) (L : ℝ)
    (hT : ∀ u : SoninL2, (T u : ℝ → ℂ) =ᵐ[volume] fun z => φ z*u z)
    (hlim : Tendsto (fun z => ‖φ z‖) (𝓝[>] 0) (𝓝 L)) : L ≤ ‖T‖ := by
  by_contra hh
  have hLT : ‖T‖ < L := lt_of_not_ge hh
  let c := (L+‖T‖)/2
  have hc : 0 ≤ c := by dsimp [c]; linarith [norm_nonneg T]
  have hcL : c < L := by dsimp [c]; linarith
  have hTc : ‖T‖ < c := by dsimp [c]; linarith
  obtain ⟨δ,hδ,hwindow⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hlim.eventually_const_lt hcL)
  have hfinite : volume (Ioo (0:ℝ) δ) ≠ ∞ := by simp only [Real.volume_Ioo]; finiteness
  let u : SoninL2 := indicatorConstLp 2 measurableSet_Ioo hfinite (1:ℂ)
  have hu : 0 < ‖u‖ := by
    dsimp [u]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num),norm_one,one_mul,
      Real.volume_real_Ioo_of_le hδ.le,sub_zero]
    exact Real.rpow_pos_of_pos hδ _
  have hle : ‖c • u‖ ≤ ‖T u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul c u,hT u,
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioo) (hμs := hfinite) (c := (1:ℂ)))] with z hs ht hi
    change u z = (Ioo (0:ℝ) δ).indicator (fun _ => (1:ℂ)) z at hi
    rw [hs,ht,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,norm_mul,hi]
    by_cases hz : z ∈ Ioo (0:ℝ) δ
    · rw [indicator_of_mem hz,norm_one,mul_one,mul_one]
      exact (hwindow hz).le
    · rw [indicator_of_notMem hz,norm_zero,mul_zero,mul_zero]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc] at hle
  have hbound := hle.trans (T.le_opNorm u)
  nlinarith

/-- The upper first inverse-frequency reflection has the compatibility moment as its actual right origin trace. -/
theorem regularInverseFrequencyReflection_upper_origin_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (regularInverseFrequencyReflection q true) (𝓝[>] 0)
      (𝓝 (compatibilityMoment (globalSmallScatteringPotential q))) := by
  apply (regularSecondInverseReflection_upper_residue_tendsto (globalSmallScatteringPotential q)).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change 0 < z at hz
  rw [regularSecondInverseReflection_globalSmall_eq]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))

/-- Oscillatory physical phases preserve the nonzero first-generator norm trace. -/
theorem directTimeSymbol_upper_norm_origin_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Tendsto (fun z => ‖directTimeSymbol q t x true z‖) (𝓝[>] 0)
      (𝓝 ((1/2 : ℝ)*‖compatibilityMoment (globalSmallScatteringPotential q)‖)) := by
  simpa only [directTimeSymbol_norm] using
    (regularInverseFrequencyReflection_upper_origin_tendsto q).norm.const_mul (1/2 : ℝ)

private theorem direct_symbol_origin_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Tendsto (directSymbol q t x reverse) (𝓝[>] 0) (𝓝 0) := by
  have hp : Continuous (fun z : ℝ => (t,x,z)) := continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have hc : Continuous (directSymbol q t x reverse) := by
    cases reverse
    · have hh := (continuous_globalSmall_regularJump_parameters q).1.comp hp
      exact hh
    · have hh := (continuous_globalSmall_regularJump_parameters q).2.comp hp
      exact hh
  have hz : directSymbol q t x reverse 0 = 0 := by
    cases reverse
    · exact (regularJumpReflection_zero _ t x).1
    · exact (regularJumpReflection_zero _ t x).2
  simpa only [hz] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The literal symbol of the time difference-quotient error. -/
def directTimeSlopeErrorSymbol (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (reverse : Bool) (z : ℝ) : ℂ :=
  (s-t)⁻¹ • (directSymbol q s x reverse z-directSymbol q t x reverse z)-directTimeSymbol q t x reverse z

/-- Every upper time difference quotient retains the same origin error, even for arbitrarily small time increments. -/
theorem directTimeSlopeErrorSymbol_upper_norm_origin_tendsto (q : SchwartzMap ℝ ℂ) (t s x : ℝ) :
    Tendsto (fun z => ‖directTimeSlopeErrorSymbol q t s x true z‖) (𝓝[>] 0)
      (𝓝 ((1/2 : ℝ)*‖compatibilityMoment (globalSmallScatteringPotential q)‖)) := by
  let a : ℝ → ℂ := fun z => (s-t)⁻¹ • (directSymbol q s x true z-directSymbol q t x true z)
  have ha : Tendsto a (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_self,smul_zero] using
      ((direct_symbol_origin_zero q s x true).sub (direct_symbol_origin_zero q t x true)).const_smul (s-t)⁻¹
  have he : Tendsto (fun z => ‖a z-directTimeSymbol q t x true z‖-‖directTimeSymbol q t x true z‖)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm (a := fun z => ‖a z‖)
    · intro z
      simpa only [Real.norm_eq_abs,norm_neg,sub_neg_eq_add,sub_add_cancel] using
        abs_norm_sub_norm_le (a z-directTimeSymbol q t x true z) (-directTimeSymbol q t x true z)
    · simpa only [norm_zero] using ha.norm
  have hh := he.add (directTimeSymbol_upper_norm_origin_tendsto q t x)
  simpa only [sub_add_cancel,zero_add,directTimeSlopeErrorSymbol,a] using hh

/-- This error is the actual bounded-operator time difference quotient minus its only possible derivative. -/
theorem directMultiplier_time_slope_error_ae (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (reverse : Bool) (u : SoninL2) :
    ((slope (fun r => directMultiplier q r x reverse) t s-directTimeMultiplier q t x reverse) u : ℝ → ℂ) =ᵐ[volume]
      fun z => directTimeSlopeErrorSymbol q t s x reverse z*u z := by
  change (((s-t)⁻¹ • (directMultiplier q s x reverse u-directMultiplier q t x reverse u)-
    directTimeMultiplier q t x reverse u : SoninL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub ((s-t)⁻¹ • (directMultiplier q s x reverse u-directMultiplier q t x reverse u))
    (directTimeMultiplier q t x reverse u),
    Lp.coeFn_smul ((s-t)⁻¹) (directMultiplier q s x reverse u-directMultiplier q t x reverse u),
    Lp.coeFn_sub (directMultiplier q s x reverse u) (directMultiplier q t x reverse u),
    directMultiplier_ae q s x reverse u,directMultiplier_ae q t x reverse u,directTimeMultiplier_ae q t x reverse u]
    with z h0 h1 h2 h3 h4 h5
  simp only [Pi.sub_apply,Pi.smul_apply] at h0 h1 h2
  rw [h0,h1,h2,h3,h4,h5]
  simp only [directTimeSlopeErrorSymbol,Complex.real_smul,sub_mul,mul_sub,mul_assoc]

/-- A nonzero moment gives a uniform positive operator-norm obstruction to every upper time difference quotient. -/
theorem directMultiplier_upper_time_slope_error_lower_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) :
    (1/2 : ℝ)*‖compatibilityMoment (globalSmallScatteringPotential q)‖ ≤
      ‖slope (fun r => directMultiplier q r x true) t s-directTimeMultiplier q t x true‖ :=
  multiplier_norm_lower_of_origin_limit _ _ _ (directMultiplier_time_slope_error_ae q t s x true)
    (directTimeSlopeErrorSymbol_upper_norm_origin_tendsto q t s x)

end
end RHTower.FokasLenells
