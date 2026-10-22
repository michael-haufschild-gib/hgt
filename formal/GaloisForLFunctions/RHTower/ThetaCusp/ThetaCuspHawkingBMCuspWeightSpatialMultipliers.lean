import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularCuspWeight
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointAnalyticInverse
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-! Actual bounded spatial multipliers for cusp weight and its relative differential error. -/
open Set Filter Topology MeasureTheory
open scoped ComplexConjugate
namespace RHTower.D4BMJointWave
open D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem weight_ne_zero (N : ℝ) (hN : 0 < N) (z : UpperHalfPlane) :
    modularCuspWeight N z ≠ 0 := by
  intro hz
  have hb := (modularCuspWeight_re_bounds N hN z).1
  rw [hz,Complex.zero_re] at hb
  linarith [cuspWeightBase_one_le]

def cuspWeightSymbol (N : ℝ) (p : ℝ × UpperHalfPlane) : ℂ := modularCuspWeight N p.2

private theorem weight_symbol_measurable (N : ℝ) (hN : 0 < N) : Measurable (cuspWeightSymbol N) :=
  (modularCuspWeight_smooth N hN).continuous.measurable.comp measurable_snd

private theorem weight_bound_nonneg (N : ℝ) (hN : 0 < N) : 0 ≤ cuspWeightBase+N := by
  linarith [cuspWeightBase_one_le]

def cuspSpatialMultiply (N : ℝ) (hN : 0 < N) : SpatialSpace →L[ℂ] SpatialSpace :=
  lpBoundedMulCLM (weight_symbol_measurable N hN) (weight_bound_nonneg N hN)
    (fun p => modularCuspWeight_norm_bound N hN p.2)

theorem cuspSpatialMultiply_coe (N : ℝ) (hN : 0 < N) (u : SpatialSpace) :
    cuspSpatialMultiply N hN u =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      fun p => cuspWeightSymbol N p*u p :=
  lpBoundedMulCLM_coeFn (weight_symbol_measurable N hN) (weight_bound_nonneg N hN)
    (fun p => modularCuspWeight_norm_bound N hN p.2) u

theorem cuspSpatialMultiply_inner (N : ℝ) (hN : 0 < N) (u v : SpatialSpace) :
    inner ℂ (cuspSpatialMultiply N hN u) v = inner ℂ u (cuspSpatialMultiply N hN v) :=
  lpBoundedMulCLM_inner_real (weight_symbol_measurable N hN) (weight_bound_nonneg N hN)
    (fun p => modularCuspWeight_norm_bound N hN p.2) (fun p => modularCuspWeight_real N p.2) u v

/-- The complete vertical derivative relative to the weight, in the original product measure. -/
def cuspLogSlopeSymbol (N : ℝ) (p : ℝ × UpperHalfPlane) : ℂ :=
  angularWeight p.1 * ModularGroup.fd.indicator
    (fun z => weightedDeriv Complex.I (modularCuspWeight N) z / modularCuspWeight N z) p.2

private theorem angular_weight_continuous : Continuous angularWeight :=
  Complex.continuous_ofReal.comp (Real.continuous_cosh.inv₀ (fun t => (Real.cosh_pos t).ne'))

private theorem angular_weight_bound (t : ℝ) : ‖angularWeight t‖ ≤ 1 := by
  simp only [angularWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.cosh_pos t))]
  exact inv_le_one_of_one_le₀ (Real.one_le_cosh t)

private theorem slope_symbol_measurable (N : ℝ) (hN : 0 < N) : Measurable (cuspLogSlopeSymbol N) := by
  have hd := (weightedDeriv_continuous Complex.I _ (modularCuspWeight_smooth N hN)).measurable
  have hm := (modularCuspWeight_smooth N hN).continuous.measurable
  exact (angular_weight_continuous.measurable.comp measurable_fst).mul
    (((hd.div hm).indicator ModularGroup.isClosed_fd.measurableSet).comp measurable_snd)

/-- The relative differential error has one bound independent of the cusp truncation. -/
theorem cuspLogSlopeSymbol_bound (N : ℝ) (hN : 0 < N) (p : ℝ × UpperHalfPlane) :
    ‖cuspLogSlopeSymbol N p‖ ≤ (3/2:ℝ) := by
  have hd : ‖ModularGroup.fd.indicator
      (fun z => weightedDeriv Complex.I (modularCuspWeight N) z / modularCuspWeight N z) p.2‖ ≤
      (3/2:ℝ) := by
    by_cases hz : p.2 ∈ ModularGroup.fd
    · rw [Set.indicator_of_mem hz,norm_div]
      apply (div_le_iff₀ (norm_pos_iff.mpr (weight_ne_zero N hN p.2))).mpr
      exact modularCuspWeight_vertical_bound N hN p.2 hz
    · simp only [Set.indicator_of_notMem hz,norm_zero]
      norm_num
  unfold cuspLogSlopeSymbol
  rw [norm_mul]
  calc
    _ ≤ 1*(3/2:ℝ) := mul_le_mul (angular_weight_bound _) hd (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

private theorem slope_symbol_real (N : ℝ) (hN : 0 < N) (p : ℝ × UpperHalfPlane) :
    conj (cuspLogSlopeSymbol N p) = cuspLogSlopeSymbol N p := by
  unfold cuspLogSlopeSymbol
  by_cases hz : p.2 ∈ ModularGroup.fd
  · rw [Set.indicator_of_mem hz,map_mul,map_div₀,modularCuspWeight_real]
    have ha : conj (angularWeight p.1) = angularWeight p.1 := Complex.conj_ofReal _
    rw [ha,modularCuspWeight_weightedDeriv N hN p.2 hz]
    simp only [map_mul,Complex.conj_ofReal]
  · simp only [Set.indicator_of_notMem hz,mul_zero,map_zero]

def cuspSpatialLogSlope (N : ℝ) (hN : 0 < N) : SpatialSpace →L[ℂ] SpatialSpace :=
  lpBoundedMulCLM (slope_symbol_measurable N hN) (by norm_num : (0:ℝ) ≤ 3/2)
    (cuspLogSlopeSymbol_bound N hN)

theorem cuspSpatialLogSlope_coe (N : ℝ) (hN : 0 < N) (u : SpatialSpace) :
    cuspSpatialLogSlope N hN u =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      fun p => cuspLogSlopeSymbol N p*u p :=
  lpBoundedMulCLM_coeFn (slope_symbol_measurable N hN) (by norm_num : (0:ℝ) ≤ 3/2)
    (cuspLogSlopeSymbol_bound N hN) u

theorem cuspSpatialLogSlope_inner (N : ℝ) (hN : 0 < N) (u v : SpatialSpace) :
    inner ℂ (cuspSpatialLogSlope N hN u) v = inner ℂ u (cuspSpatialLogSlope N hN v) :=
  lpBoundedMulCLM_inner_real (slope_symbol_measurable N hN) (by norm_num : (0:ℝ) ≤ 3/2)
    (cuspLogSlopeSymbol_bound N hN) (slope_symbol_real N hN) u v

theorem cuspSpatialLogSlope_bound (N : ℝ) (hN : 0 < N) (u : SpatialSpace) :
    ‖cuspSpatialLogSlope N hN u‖ ≤ (3/2:ℝ)*‖u‖ := by
  apply (cuspSpatialLogSlope N hN).le_opNorm u |>.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  exact norm_lpBoundedMulCLM_le (slope_symbol_measurable N hN) (by norm_num : (0:ℝ) ≤ 3/2)
    (cuspLogSlopeSymbol_bound N hN)

/-- Weight and its retained relative gradient commute as actual L2 multipliers. -/
theorem cuspSpatialMultiply_logSlope_commute (N : ℝ) (hN : 0 < N) (u : SpatialSpace) :
    cuspSpatialMultiply N hN (cuspSpatialLogSlope N hN u) =
      cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN u) := by
  apply Lp.ext
  filter_upwards [cuspSpatialMultiply_coe N hN (cuspSpatialLogSlope N hN u),
    cuspSpatialLogSlope_coe N hN (cuspSpatialMultiply N hN u),
    cuspSpatialMultiply_coe N hN u,cuspSpatialLogSlope_coe N hN u] with p hM hR hm hr
  rw [hM,hR,hm,hr]
  ring

/-- Multiplying back by the same weight recovers the original full differential commutator. -/
theorem cuspLogSlopeSymbol_weight (N : ℝ) (hN : 0 < N) (p : ℝ × UpperHalfPlane)
    (hp : p.2 ∈ ModularGroup.fd) :
    cuspLogSlopeSymbol N p*cuspWeightSymbol N p =
      angularWeight p.1*weightedDeriv Complex.I (modularCuspWeight N) p.2 := by
  unfold cuspLogSlopeSymbol cuspWeightSymbol
  rw [Set.indicator_of_mem hp,mul_assoc,div_mul_cancel₀ _ (weight_ne_zero N hN p.2)]

end
end RHTower.D4BMJointWave
