import GaloisForLFunctions.HTGeometry.FokasLenellsOriginCompatibility

/-!
# Exact low-order primitives for odd Schwartz scattering data

Odd projection removes the anchor and makes the zero-frequency kernel a
scalar derivative times one fixed off-diagonal matrix. The genuine mixed
and second primitives can therefore be evaluated before taking either
scattering endpoint.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem reflectedDerivative_oddInitialPart (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    reflectedDerivative (oddInitialPart q) x = -deriv (oddInitialPart q) x := by
  have hh := rawReflectedProfile_hasDerivAt (oddInitialPart q) x
  have he : (fun y : ℝ => oddInitialPart q (-y)) = fun y => -oddInitialPart q y := by
    funext y
    exact oddInitialPart_reflection q y
  rw [he] at hh
  exact hh.unique ((oddInitialPart q).hasDerivAt x).neg

theorem deriv_oddInitialPart_reflection (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (oddInitialPart q) (-x) = deriv (oddInitialPart q) x := by
  have hh := reflectedDerivative_oddInitialPart q x
  simp only [reflectedDerivative,_root_.neg_apply,RHTower.negSchwartz'_apply,
    SchwartzMap.derivCLM_apply] at hh
  exact neg_injective hh

/-- The nested mixed primitive becomes a local square for odd data. -/
theorem rawMixedPrimitive_oddInitialPart (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    rawMixedPrimitive (oddInitialPart q) x = -(oddInitialPart q x)^2/2 := by
  have hd (y : ℝ) : HasDerivAt (fun s : ℝ => -(oddInitialPart q s)^2/2)
      (rawMixedProfile (oddInitialPart q) y) y := by
    convert! (((oddInitialPart q).hasDerivAt y).pow 2).neg.div_const 2 using 1
    rw [rawMixedProfile_apply,reflectedDerivative_oddInitialPart]
    ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hd y) ((rawMixedProfile (oddInitialPart q)).integrable.intervalIntegrable (a := 0) (b := x))
  change (∫ y in (0 : ℝ)..x, rawMixedProfile (oddInitialPart q) y) = _
  simpa only [oddInitialPart_apply,neg_zero,sub_self,zero_div,zero_pow (by omega : 2 ≠ 0),sub_zero] using hh

/-- The true second coefficient is a scalar square times the initial vector. -/
theorem rawSecondSlope_oddInitialPart_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawSecondSlope (oddInitialPart q) 0 v x = ((oddInitialPart q x)^2/2) • v := by
  change rawSecondSlope (oddInitialPart q) 0 v x =
    (((oddInitialPart q x)^2/2)*v.1,((oddInitialPart q x)^2/2)*v.2)
  rw [rawSecondSlope_zero_eq]
  simp only [rawSecondPrimitive,rawMixedPrimitive_oddInitialPart,oddInitialPart_reflection]
  have hz : oddInitialPart q 0 = 0 := by simp
  rw [hz]
  apply Prod.ext <;> dsimp only <;> ring

/-- Both mixed endpoints vanish separately for odd data. -/
theorem rawMixedEndpoint_oddInitialPart (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawMixedEndpoint (oddInitialPart q) left = 0 := by
  have hq : Tendsto (fun x : ℝ => oddInitialPart q (if left then -x else x)) atTop (𝓝 0) := by
    cases left
    · exact (oddInitialPart q).tendsto_cocompact.mono_left atTop_le_cocompact
    · exact ((oddInitialPart q).tendsto_cocompact.mono_left atBot_le_cocompact).comp tendsto_neg_atTop_atBot
  have hh := (hq.pow 2).neg.div_const (2 : ℂ)
  simp only [zero_pow (by omega : 2 ≠ 0),neg_zero,zero_div] at hh
  have hj := rawMixedPrimitive_tendsto (oddInitialPart q) left
  simp only [rawMixedPrimitive_oddInitialPart] at hj
  exact tendsto_nhds_unique hj hh

/-- Odd data have no first endpoint coefficient. -/
theorem rawFirstCoefficientMatrix_oddInitialPart (q : SchwartzMap ℝ ℂ) :
    rawFirstCoefficientMatrix (oddInitialPart q) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rawFirstCoefficientMatrix]

/-- Odd data have no quadratic endpoint coefficient at either infinity. -/
theorem rawQuadraticEndpointMatrix_oddInitialPart (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawQuadraticEndpointMatrix (oddInitialPart q) left = 0 := by
  rw [rawQuadraticEndpointMatrix_eq,rawMixedEndpoint_oddInitialPart]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The actual third primitive is differentiable in the spatial coordinate. -/
theorem rawThirdSlope_hasDerivAt (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    HasDerivAt (rawThirdSlope q k v) (rawThirdIntegrand q k v x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((rawThirdIntegrand_integrable q k v).intervalIntegrable (a := 0) (b := x))
    (continuous_rawThirdIntegrand q k v).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_rawThirdIntegrand q k v).continuousAt

/-- The actual fourth primitive is differentiable in the spatial coordinate. -/
theorem rawFourthSlope_hasDerivAt (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    HasDerivAt (rawFourthSlope q k v) (rawFourthIntegrand q k v x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((rawFourthIntegrand_integrable q k v).intervalIntegrable (a := 0) (b := x))
    (continuous_rawFourthIntegrand q k v).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_rawFourthIntegrand q k v).continuousAt

/-- The second phase average has the exact zero-frequency value required by the fifth coefficient. -/
theorem rawSecondPhaseAverage_zero_frequency (x : ℝ) : rawSecondPhaseAverage 0 x = 1/2 := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)^2/2) (t : ℂ) t := by
    have hc : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
    convert! (hc.pow 2).div_const 2 using 1
    ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (Complex.continuous_ofReal.intervalIntegrable (μ := volume) 0 1)
  simp only [rawSecondPhaseAverage,rawPhaseAverage_zero_frequency,mul_one]
  simpa using hh

/-- Exact original quintic kernel at zero frequency. -/
theorem rawQuinticOperator_zero_apply (q : SchwartzMap ℝ ℂ) (x : ℝ) (v : SpectralVector) :
    rawQuinticOperator q 0 x v =
      (-2*I*(x : ℂ)^2*reflectedDerivative q x*v.2,
       -2*I*(x : ℂ)^2*deriv q x*v.1) := by
  rw [rawQuinticOperator_apply]
  simp only [zero_pow (by omega : 2 ≠ 0),mul_zero,neg_zero,
    rawSecondPhaseAverage_zero_frequency,SchwartzMap.derivCLM_apply]
  apply Prod.ext <;> dsimp only <;> ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
