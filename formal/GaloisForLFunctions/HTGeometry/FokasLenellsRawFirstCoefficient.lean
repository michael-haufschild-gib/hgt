import GaloisForLFunctions.HTGeometry.FokasLenellsRawFirstSlope

/-!
# Evaluation of the first genuine endpoint coefficient

The first divided kernel is the derivative of an explicit Schwartz
primitive. Decay at both infinities makes its endpoint integrals equal.
Thus the two original Jost endpoints have the same first spectral jet.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawLinearPrimitive (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  (I*q (-x)*v.2,I*q x*v.1)

theorem rawLinearPrimitive_hasDerivAt (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    HasDerivAt (rawLinearPrimitive q v) (rawDividedOperator q 0 x v) x := by
  have hq := ((q.smooth ⊤).differentiable (by simp)).differentiableAt (x := x) |>.hasDerivAt
  have hp := (((q.smooth ⊤).differentiable (by simp)).differentiableAt (x := -x) |>.hasDerivAt).scomp x (hasDerivAt_id x).neg
  have hh := ((hp.const_mul I).mul_const v.2).prodMk ((hq.const_mul I).mul_const v.1)
  convert! hh using 1
  simp only [rawDividedOperator_apply,zero_pow (by omega : 2 ≠ 0),mul_zero,neg_zero,
    FDNLS.staggerPhase,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,
    reflectedDerivative,_root_.neg_apply,RHTower.negSchwartz'_apply,SchwartzMap.derivCLM_apply,neg_one_smul]

private theorem rawLinearPrimitive_tendsto_top (q : SchwartzMap ℝ ℂ) (v : SpectralVector) :
    Tendsto (rawLinearPrimitive q v) atTop (𝓝 0) := by
  have ht : Tendsto (q : ℝ → ℂ) atTop (𝓝 0) := q.tendsto_cocompact.mono_left atTop_le_cocompact
  have hb : Tendsto (q : ℝ → ℂ) atBot (𝓝 0) := q.tendsto_cocompact.mono_left atBot_le_cocompact
  have hc : Continuous (fun p : ℂ × ℂ => ((I*p.1*v.2,I*p.2*v.1) : SpectralVector)) := by fun_prop
  have hh := (hc.tendsto (0,0)).comp ((hb.comp tendsto_neg_atTop_atBot).prodMk_nhds ht)
  convert! hh using 1
  simp only [mul_zero,zero_mul]
  rfl

private theorem rawLinearPrimitive_tendsto_bot (q : SchwartzMap ℝ ℂ) (v : SpectralVector) :
    Tendsto (rawLinearPrimitive q v) atBot (𝓝 0) := by
  have ht : Tendsto (q : ℝ → ℂ) atTop (𝓝 0) := q.tendsto_cocompact.mono_left atTop_le_cocompact
  have hb : Tendsto (q : ℝ → ℂ) atBot (𝓝 0) := q.tendsto_cocompact.mono_left atBot_le_cocompact
  have hc : Continuous (fun p : ℂ × ℂ => ((I*p.1*v.2,I*p.2*v.1) : SpectralVector)) := by fun_prop
  have hh := (hc.tendsto (0,0)).comp ((ht.comp tendsto_neg_atBot_atTop).prodMk_nhds hb)
  convert! hh using 1
  simp only [mul_zero,zero_mul]
  rfl

/-- Both first jets depend only on the initial profile at the common anchoring point. -/
def rawFirstCoefficient (q : SchwartzMap ℝ ℂ) (v : SpectralVector) : SpectralVector :=
  (-I*q 0*v.2,-I*q 0*v.1)

theorem rawFirstSlope_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    rawFirstSlope q 0 v left = rawFirstCoefficient q v := by
  let f : ℝ → SpectralVector := fun x => rawLinearPrimitive q v (if left then -x else x)
  have hd : ∀ x : ℝ, HasDerivAt f (rawOrientedDividedDerivative q 0 v left x) x := by
    intro x
    cases left
    · simpa only [f,Bool.false_eq_true,↓reduceIte,rawOrientedDividedDerivative,
        rawDividedDerivative,rawInteractionSolution_zero_frequency] using rawLinearPrimitive_hasDerivAt q v x
    · have hh := (rawLinearPrimitive_hasDerivAt q v (-x)).scomp x (hasDerivAt_id x).neg
      convert! hh using 1
      simp only [rawOrientedDividedDerivative,↓reduceIte,rawDividedDerivative,
        rawInteractionSolution_zero_frequency,neg_one_smul]
  have ht : Tendsto f atTop (𝓝 0) := by
    cases left
    · exact rawLinearPrimitive_tendsto_top q v
    · exact (rawLinearPrimitive_tendsto_bot q v).comp tendsto_neg_atTop_atBot
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ)) (fun x _ => hd x)
    (rawOrientedDividedDerivative_integrable q 0 v left).integrableOn ht
  change rawFirstSlope q 0 v left = 0-f 0 at hh
  rw [hh]
  simp only [f,neg_zero,ite_self,rawLinearPrimitive,zero_sub,rawFirstCoefficient,Prod.neg_mk,
    neg_mul]

/-- An explicitly evaluated derivative of the actual scattering endpoint, with no compatibility premise. -/
theorem rawAsymptoticVector_first_derivative (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    HasDerivAt (fun k : ℝ => rawAsymptoticVector q k v left) (rawFirstCoefficient q v) 0 := by
  simpa only [rawFirstSlope_zero] using rawAsymptoticVector_hasDerivAt_zero q v left

/-- The first spectral jets agree even though the two endpoint states differ away from zero. -/
theorem rawAsymptoticVector_first_derivative_sides (q : SchwartzMap ℝ ℂ) (v : SpectralVector) :
    deriv (fun k => rawAsymptoticVector q k v true) 0 = deriv (fun k => rawAsymptoticVector q k v false) 0 := by
  rw [(rawAsymptoticVector_first_derivative q v true).deriv,
    (rawAsymptoticVector_first_derivative q v false).deriv]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
