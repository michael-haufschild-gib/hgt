import GaloisForLFunctions.HTGeometry.FokasLenellsRawMatrixTaylor

/-!
# An actual cubic expansion of the original scattering matrix

The exact endpoint expansions and the linear two-dimensional adjugate give
an exact scattering expansion. Its linear term cancels. The remaining
cubic factor converges at zero, so the displayed second and third
coefficients belong to the genuinely constructed scattering matrix.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawScatteringQuadraticCoefficient (q : SchwartzMap ℝ ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rawQuadraticEndpointMatrix q false+(rawQuadraticEndpointMatrix q true).adjugate-
    rawFirstCoefficientMatrix q*rawFirstCoefficientMatrix q

/-- All higher factors are retained: this is an exact remainder, not a truncated equation. -/
def rawScatteringCubicRemainder (q : SchwartzMap ℝ ℂ) (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rawCubicEndpointMatrix q k false+(rawCubicEndpointMatrix q k true).adjugate+
    rawFirstCoefficientMatrix q*(rawQuadraticEndpointMatrix q true).adjugate-
    rawQuadraticEndpointMatrix q false*rawFirstCoefficientMatrix q+
    (k : ℂ) • (rawFirstCoefficientMatrix q*(rawCubicEndpointMatrix q k true).adjugate-
      rawCubicEndpointMatrix q k false*rawFirstCoefficientMatrix q+
      rawQuadraticEndpointMatrix q false*(rawQuadraticEndpointMatrix q true).adjugate)+
    (k : ℂ)^2 • (rawQuadraticEndpointMatrix q false*(rawCubicEndpointMatrix q k true).adjugate+
      rawCubicEndpointMatrix q k false*(rawQuadraticEndpointMatrix q true).adjugate)+
    (k : ℂ)^3 • (rawCubicEndpointMatrix q k false*(rawCubicEndpointMatrix q k true).adjugate)

/-- The genuine cubic coefficient, expressed entirely in actual convergent endpoint integrals. -/
def rawScatteringCubicCoefficient (q : SchwartzMap ℝ ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rawCubicEndpointMatrix q 0 false+(rawCubicEndpointMatrix q 0 true).adjugate+
    rawFirstCoefficientMatrix q*(rawQuadraticEndpointMatrix q true).adjugate-
    rawQuadraticEndpointMatrix q false*rawFirstCoefficientMatrix q

theorem rawScatteringCubicRemainder_zero (q : SchwartzMap ℝ ℂ) :
    rawScatteringCubicRemainder q 0 = rawScatteringCubicCoefficient q := by
  simp only [rawScatteringCubicRemainder,rawScatteringCubicCoefficient,Complex.ofReal_zero,
    zero_smul,zero_pow (by omega : 2 ≠ 0),zero_pow (by omega : 3 ≠ 0),add_zero]

/-- The original scattering matrix has a rigorously justified cubic expansion for every Schwartz profile. -/
theorem rawScatteringMatrix_cubic_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    rawScatteringMatrix q k = 1+(k : ℂ)^2 • rawScatteringQuadraticCoefficient q+
      (k : ℂ)^3 • rawScatteringCubicRemainder q k := by
  rw [rawScatteringMatrix,rawAsymptoticMatrix_cubic_factor,rawAsymptoticMatrix_inverse_cubic_factor]
  unfold rawScatteringQuadraticCoefficient rawScatteringCubicRemainder
  simp only [sub_eq_add_neg,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,
    smul_add,smul_neg,mul_neg,one_mul,mul_one,smul_smul]
  module

private theorem continuousAt_rawCubicEndpointMatrix_zero (q : SchwartzMap ℝ ℂ) (left : Bool) :
    ContinuousAt (fun k => rawCubicEndpointMatrix q k left) 0 := rawCubicEndpointMatrix_tendsto_zero q left

/-- The actual cubic remainder tends to the stated coefficient; no Taylor-series hypothesis is supplied. -/
theorem rawScatteringCubicRemainder_tendsto_zero (q : SchwartzMap ℝ ℂ) :
    Tendsto (rawScatteringCubicRemainder q) (𝓝 0) (𝓝 (rawScatteringCubicCoefficient q)) := by
  have hR := continuousAt_rawCubicEndpointMatrix_zero q false
  have hL := continuousAt_rawCubicEndpointMatrix_zero q true
  have hc : ContinuousAt (rawScatteringCubicRemainder q) 0 := by
    unfold rawScatteringCubicRemainder
    fun_prop
  simpa only [rawScatteringCubicRemainder_zero] using hc.tendsto

/-- Removing the first two true coefficients leaves exactly the convergent cubic remainder. -/
theorem rawScatteringMatrix_sub_quadratic (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    rawScatteringMatrix q k-1-(k : ℂ)^2 • rawScatteringQuadraticCoefficient q =
      (k : ℂ)^3 • rawScatteringCubicRemainder q k := by
  rw [rawScatteringMatrix_cubic_factor]
  abel

/-- The punctured cubic quotient converges to the coefficient of the actual scattering matrix. -/
theorem rawScatteringMatrix_cubic_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℝ => ((k : ℂ)^3)⁻¹ •
      (rawScatteringMatrix q k-1-(k : ℂ)^2 • rawScatteringQuadraticCoefficient q))
      (𝓝[≠] 0) (𝓝 (rawScatteringCubicCoefficient q)) := by
  have hh : Tendsto (rawScatteringCubicRemainder q) (𝓝[≠] (0 : ℝ)) (𝓝 (rawScatteringCubicCoefficient q)) :=
    (rawScatteringCubicRemainder_tendsto_zero q).mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk0 : k ≠ 0 := hk
  have hkc : (k : ℂ)^3 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hk0)
  rw [rawScatteringMatrix_sub_quadratic,smul_smul,inv_mul_cancel₀ hkc,one_smul]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
