import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeSymbols
import GaloisForLFunctions.RHTower.FokasLenellsTimeMultiplier
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# A sharp strong second-time differentiability criterion

The converse to dominated differentiation is proved here from actual L2
slope convergence: an almost-everywhere convergent subsequence identifies
the Hilbert-space derivative with the known pointwise derivative.
Together with the full-line weight theorem, this turns compatibility
into an exact criterion, not merely a sufficient domain condition.
-/

open MeasureTheory Complex Matrix Filter Topology
open scoped ENNReal NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem point_derivative_memLp_of_L2_derivative
    (f : ℝ → ℝ → ℂ) (hf : ∀ s, MemLp (f s) 2 volume) (t : ℝ) (g : ℝ → ℂ)
    (hp : ∀ z, HasDerivAt (fun s => f s z) (g z) t) (v : SoninL2)
    (hd : HasDerivAt (fun s => (hf s).toLp (f s)) v t) :
    MemLp g 2 volume := by
  let D (s z : ℝ) : ℂ := (s-t)⁻¹ • (f s z-f t z)
  have hD (s : ℝ) : MemLp (D s) 2 volume := ((hf s).sub (hf t)).const_smul (s-t)⁻¹
  have he (s : ℝ) : (hD s).toLp (D s) = slope (fun r => (hf r).toLp (f r)) t s := by
    change (((hf s).sub (hf t)).const_smul (s-t)⁻¹).toLp _ = _
    rw [MemLp.toLp_const_smul _ ((hf s).sub (hf t)), MemLp.toLp_sub]
    rfl
  have hlim : Tendsto (fun s => (hD s).toLp (D s)) (𝓝[≠] t) (𝓝 v) := by
    simpa only [he] using hd.tendsto_slope
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae'
  have hrep : ∀ᵐ z ∂volume, ∀ n : ℕ, (hD (ns n)).toLp (D (ns n)) z = D (ns n) z :=
    ae_all_iff.mpr (fun n => (hD (ns n)).coeFn_toLp)
  have heq : (v : ℝ → ℂ) =ᵐ[volume] g := by
    filter_upwards [hae,hrep] with z hz hr
    have hseq : Tendsto (fun n : ℕ => D (ns n) z) atTop (𝓝 (v z)) :=
      hz.congr' (Eventually.of_forall hr)
    have hpoint := (hp z).tendsto_slope.comp hns
    change Tendsto (fun n : ℕ => D (ns n) z) atTop (𝓝 (g z)) at hpoint
    exact tendsto_nhds_unique hseq hpoint
  exact MemLp.ae_eq heq (Lp.memLp v)

private theorem second_time_memLp_all (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool)
    (h : MemLp (directSecondTimeSymbol q t x reverse) 2 volume) (s : ℝ) :
    MemLp (directSecondTimeSymbol q s x reverse) 2 volume :=
  h.congr_norm (directSecondTimeSymbol_measurable q s x reverse).aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [directSecondTimeSymbol_norm, directSecondTimeSymbol_norm])

private theorem second_time_envelope_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool)
    (h : MemLp (directSecondTimeSymbol q t x reverse) 2 volume) :
    MemLp (fun z => (1/4 : ℝ)*‖regularSecondInverseReflection (globalSmallScatteringPotential q) reverse z‖) 2 volume :=
  MemLp.ae_eq (Eventually.of_forall (directSecondTimeSymbol_norm q t x reverse)) h.norm

private theorem second_time_strong_derivative (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool)
    (h : MemLp (directSecondTimeSymbol q t x reverse) 2 volume) :
    HasDerivAt (fun s => directTimeSymbolL2 q s x reverse)
      (h.toLp (directSecondTimeSymbol q t x reverse)) t := by
  exact hasDerivAt_toLp_two_of_dominated volume (fun s => directTimeSymbol q s x reverse)
    (fun s => directSecondTimeSymbol q s x reverse)
    (fun s => directTimeSymbol_memLp q s x reverse) (second_time_memLp_all q t x reverse h)
    (fun z => (1/4 : ℝ)*‖regularSecondInverseReflection (globalSmallScatteringPotential q) reverse z‖)
    (second_time_envelope_memLp q t x reverse h)
    (Eventually.of_forall fun z s => directTimeSymbol_time_hasDerivAt q s x reverse z)
    (Eventually.of_forall fun z s => (directSecondTimeSymbol_norm q s x reverse z).le) t

/-- Existence of a strong time derivative of the actual first-derivative L2 curve is equivalent to pointwise second-derivative integrability. -/
theorem directTimeSymbolL2_hasDerivAt_iff_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    (∃ v : SoninL2, HasDerivAt (fun s => directTimeSymbolL2 q s x reverse) v t) ↔
      MemLp (directSecondTimeSymbol q t x reverse) 2 volume := by
  constructor
  · rintro ⟨v,hv⟩
    exact point_derivative_memLp_of_L2_derivative (fun s => directTimeSymbol q s x reverse)
      (fun s => directTimeSymbol_memLp q s x reverse) t (directSecondTimeSymbol q t x reverse)
      (fun z => directTimeSymbol_time_hasDerivAt q t x reverse z) v hv
  · intro h
    exact ⟨h.toLp _,second_time_strong_derivative q t x reverse h⟩

/-- The lower actual scattering channel has a strong second time derivative for every small Schwartz profile. -/
theorem directTimeSymbolL2_lower_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    HasDerivAt (fun s => directTimeSymbolL2 q s x false)
      ((directSecondTimeSymbol_lower_memLp q t x).toLp (directSecondTimeSymbol q t x false)) t :=
  second_time_strong_derivative q t x false (directSecondTimeSymbol_lower_memLp q t x)

/-- The nonlinear compatibility moment is the exact strong second-time derivative gate for the upper actual channel. -/
theorem directTimeSymbolL2_upper_hasDerivAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    (∃ v : SoninL2, HasDerivAt (fun s => directTimeSymbolL2 q s x true) v t) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  rw [directTimeSymbolL2_hasDerivAt_iff_memLp, directSecondTimeSymbol_upper_memLp_iff]

/-- At every fixed physical point, differentiability of the upper first-time-derivative curve is equivalent to compatibility. -/
theorem directTimeSymbolL2_upper_differentiableAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => directTimeSymbolL2 q s x true) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · intro h
    exact (directTimeSymbolL2_upper_hasDerivAt_iff q t x).1 ⟨_,h.hasDerivAt⟩
  · intro hm
    obtain ⟨v,hv⟩ := (directTimeSymbolL2_upper_hasDerivAt_iff q t x).2 hm
    exact hv.differentiableAt

/-- The criterion applies directly to the second derivative of the original actual L2 scattering curve. -/
theorem directSymbolL2_upper_twice_differentiableAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    DifferentiableAt ℝ (deriv (fun s => directSymbolL2 q s x true)) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  have he : deriv (fun s => directSymbolL2 q s x true) = fun s => directTimeSymbolL2 q s x true :=
    funext fun s => (directSymbolL2_time_hasDerivAt q s x true).deriv
  rw [he]
  exact directTimeSymbolL2_upper_differentiableAt_iff q t x

/-- Small Gaussian profiles never acquire a strong second time derivative in the upper L2 channel. -/
theorem directSymbolL2_upper_Gaussian_not_twice_differentiableAt (a t x : ℝ) :
    ¬ DifferentiableAt ℝ (deriv (fun s => directSymbolL2 (compatibilityGaussian a) s x true)) t := by
  rw [directSymbolL2_upper_twice_differentiableAt_iff]
  exact compatibilityMoment_globalSmallGaussian_ne_zero a

/-- Compatible profiles with prescribed fifth traces have the genuine strong second time derivative. -/
theorem directTimeSymbolL2_upper_quinticGaussianProfile_hasDerivAt (a : ℝ) (c : ℂ) (t x : ℝ) :
    HasDerivAt (fun s => directTimeSymbolL2 (quinticGaussianProfile a c) s x true)
      ((directSecondTimeSymbol_upper_quinticGaussianProfile_memLp a c t x).toLp
        (directSecondTimeSymbol (quinticGaussianProfile a c) t x true)) t :=
  second_time_strong_derivative _ t x true (directSecondTimeSymbol_upper_quinticGaussianProfile_memLp a c t x)

private theorem second_time_toLp_continuous (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool)
    (h : MemLp (directSecondTimeSymbol q t x reverse) 2 volume) :
    Continuous (fun s => (second_time_memLp_all q t x reverse h s).toLp
      (directSecondTimeSymbol q s x reverse)) := by
  apply continuous_toLp_two_of_dominated volume
    (fun s => directSecondTimeSymbol q s x reverse) (second_time_memLp_all q t x reverse h)
    (fun z => (1/4 : ℝ)*‖regularSecondInverseReflection (globalSmallScatteringPotential q) reverse z‖)
    (second_time_envelope_memLp q t x reverse h)
  · intro s
    exact Eventually.of_forall fun z => (directSecondTimeSymbol_norm q s x reverse z).le
  · apply Eventually.of_forall
    intro z
    have hc : Continuous (fun s : ℝ => (s,x)) := continuous_id.prodMk continuous_const
    have hh := (continuous_directSecondTimeSymbol_parameters q reverse z).comp hc
    exact hh

private theorem first_time_curve_contDiff_one (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool)
    (h : MemLp (directSecondTimeSymbol q t x reverse) 2 volume) :
    ContDiff ℝ 1 (fun s => directTimeSymbolL2 q s x reverse) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (second_time_strong_derivative q s x reverse
    (second_time_memLp_all q t x reverse h s)).differentiableAt, ?_⟩
  have he : deriv (fun s => directTimeSymbolL2 q s x reverse) =
      fun s => (second_time_memLp_all q t x reverse h s).toLp (directSecondTimeSymbol q s x reverse) :=
    funext fun s => (second_time_strong_derivative q s x reverse (second_time_memLp_all q t x reverse h s)).deriv
  rw [he]
  exact second_time_toLp_continuous q t x reverse h

/-- Global C2 regularity of the actual scattering curve is equivalent to the actual second-derivative L2 condition at one time. -/
theorem directSymbolL2_time_contDiff_two_iff_memLp (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) :
    ContDiff ℝ 2 (fun t => directSymbolL2 q t x reverse) ↔
      MemLp (directSecondTimeSymbol q 0 x reverse) 2 volume := by
  have he : deriv (fun t => directSymbolL2 q t x reverse) = fun t => directTimeSymbolL2 q t x reverse :=
    funext fun t => (directSymbolL2_time_hasDerivAt q t x reverse).deriv
  constructor
  · intro h
    have hc : ContDiff ℝ 1 (deriv (fun t => directSymbolL2 q t x reverse)) :=
      (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) (fun t => directSymbolL2 q t x reverse) from h)).2.2
    rw [he] at hc
    have hd := (hc.differentiable (by simp)) 0
    exact (directTimeSymbolL2_hasDerivAt_iff_memLp q 0 x reverse).1 ⟨_,hd.hasDerivAt⟩
  · intro h
    change ContDiff ℝ (1+1) (fun t => directSymbolL2 q t x reverse)
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun t => (directSymbolL2_time_hasDerivAt q t x reverse).differentiableAt, by simp, ?_⟩
    rw [he]
    exact first_time_curve_contDiff_one q 0 x reverse h

/-- The lower actual scattering curve is globally C2 in time for arbitrary constructed small Schwartz data. -/
theorem directSymbolL2_lower_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 2 (fun t => directSymbolL2 q t x false) :=
  (directSymbolL2_time_contDiff_two_iff_memLp q x false).2 (directSecondTimeSymbol_lower_memLp q 0 x)

/-- Global C2 time regularity of the upper actual scattering curve holds exactly at compatibility. -/
theorem directSymbolL2_upper_time_contDiff_two_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 2 (fun t => directSymbolL2 q t x true) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  rw [directSymbolL2_time_contDiff_two_iff_memLp, directSecondTimeSymbol_upper_memLp_iff]

/-- The compatible prescribed-fifth-trace family has the genuine C2 upper time evolution. -/
theorem directSymbolL2_upper_quinticGaussianProfile_time_contDiff_two (a : ℝ) (c : ℂ) (x : ℝ) :
    ContDiff ℝ 2 (fun t => directSymbolL2 (quinticGaussianProfile a c) t x true) :=
  (directSymbolL2_upper_time_contDiff_two_iff _ x).2 (compatibilityMoment_globalSmall_quinticGaussianProfile a c)

private theorem weighted_second_time_memLp_all (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (reverse : Bool) (u : SoninL2)
    (h : MemLp (fun z => directSecondTimeSymbol q t x reverse z*u z) 2 volume) (s : ℝ) :
    MemLp (fun z => directSecondTimeSymbol q s x reverse z*u z) 2 volume :=
  h.congr_norm ((directSecondTimeSymbol_measurable q s x reverse).aestronglyMeasurable.mul
    (Lp.memLp u).aestronglyMeasurable)
    (Eventually.of_forall fun z => by rw [norm_mul,norm_mul,directSecondTimeSymbol_norm,directSecondTimeSymbol_norm])

private theorem weighted_second_time_strong_derivative (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (reverse : Bool) (u : SoninL2)
    (h : MemLp (fun z => directSecondTimeSymbol q t x reverse z*u z) 2 volume) :
    HasDerivAt (fun s => directTimeMultiplier q s x reverse u)
      (h.toLp (fun z => directSecondTimeSymbol q t x reverse z*u z)) t := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun s z => directTimeSymbol q s x reverse z*u z)
    (fun s z => directSecondTimeSymbol q s x reverse z*u z)
    (fun s => memLp_mul_of_bound (directTimeSymbol_measurable q s x reverse)
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q))
      (directTimeSymbol_bound q s x reverse) u)
    (weighted_second_time_memLp_all q t x reverse u h)
    (fun z => ‖directSecondTimeSymbol q t x reverse z*u z‖) h.norm
  · exact Eventually.of_forall fun z s => (directTimeSymbol_time_hasDerivAt q s x reverse z).mul_const _
  · exact Eventually.of_forall fun z s => by
      rw [norm_mul,norm_mul,directSecondTimeSymbol_norm,directSecondTimeSymbol_norm]

/-- On each L2 vector, the exact domain of the second strong multiplier derivative is multiplication by the actual second-time symbol. -/
theorem directTimeMultiplier_hasDerivAt_iff_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (reverse : Bool) (u : SoninL2) :
    (∃ v : SoninL2, HasDerivAt (fun s => directTimeMultiplier q s x reverse u) v t) ↔
      MemLp (fun z => directSecondTimeSymbol q t x reverse z*u z) 2 volume := by
  constructor
  · rintro ⟨v,hv⟩
    exact point_derivative_memLp_of_L2_derivative
      (fun s z => directTimeSymbol q s x reverse z*u z)
      (fun s => memLp_mul_of_bound (directTimeSymbol_measurable q s x reverse)
        (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q))
        (directTimeSymbol_bound q s x reverse) u) t _
      (fun z => (directTimeSymbol_time_hasDerivAt q t x reverse z).mul_const _) v hv
  · intro h
    exact ⟨h.toLp _,weighted_second_time_strong_derivative q t x reverse u h⟩

/-- The same criterion describes the actual iterated derivative of the original bounded multiplier orbit. -/
theorem directMultiplier_twice_differentiableAt_iff_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (reverse : Bool) (u : SoninL2) :
    DifferentiableAt ℝ (deriv (fun s => directMultiplier q s x reverse u)) t ↔
      MemLp (fun z => directSecondTimeSymbol q t x reverse z*u z) 2 volume := by
  have he : deriv (fun s => directMultiplier q s x reverse u) =
      fun s => directTimeMultiplier q s x reverse u :=
    funext fun s => (directMultiplier_time_hasDerivAt q s x reverse u).deriv
  rw [he,← directTimeMultiplier_hasDerivAt_iff_memLp]
  exact ⟨fun h => ⟨_,h.hasDerivAt⟩,fun ⟨_,h⟩ => h.differentiableAt⟩

end
end RHTower.FokasLenells
