import GaloisForLFunctions.HTGeometry.FokasLenellsRawMatrixFifth

/-!
# Exact fifth-order expansion of the genuine scattering matrix

Multiplication of the two true endpoint expansions retains every higher
product in one continuous fifth remainder. The fourth and fifth coefficients
therefore belong to the actual spatial scattering matrix.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawScatteringFourthCoefficient (q : SchwartzMap ℝ ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rawQuarticEndpointMatrix q false+(rawQuarticEndpointMatrix q true).adjugate+
    rawFirstCoefficientMatrix q*(rawCubicEndpointMatrix q 0 true).adjugate-
    rawCubicEndpointMatrix q 0 false*rawFirstCoefficientMatrix q+
    rawQuadraticEndpointMatrix q false*(rawQuadraticEndpointMatrix q true).adjugate

/-- All products of total degree at least five remain in this exact remainder. -/
def rawScatteringFifthRemainder (q : SchwartzMap ℝ ℂ) (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let D := rawFirstCoefficientMatrix q
  let QR := rawQuadraticEndpointMatrix q false
  let QL := (rawQuadraticEndpointMatrix q true).adjugate
  let TR := rawCubicEndpointMatrix q 0 false
  let TL := (rawCubicEndpointMatrix q 0 true).adjugate
  let HR := rawQuarticEndpointMatrix q false
  let HL := (rawQuarticEndpointMatrix q true).adjugate
  let KR := rawQuinticEndpointMatrix q k false
  let KL := (rawQuinticEndpointMatrix q k true).adjugate
  KR+KL+D*HL-HR*D+QR*TL+TR*QL+
    (k : ℂ) • (D*KL-KR*D+QR*HL+HR*QL+TR*TL)+
    (k : ℂ)^2 • (QR*KL+KR*QL+TR*HL+HR*TL)+
    (k : ℂ)^3 • (TR*KL+KR*TL+HR*HL)+
    (k : ℂ)^4 • (HR*KL+KR*HL)+
    (k : ℂ)^5 • (KR*KL)

def rawScatteringFifthCoefficient (q : SchwartzMap ℝ ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rawScatteringFifthRemainder q 0

/-- The genuine scattering matrix has five exact orders, without a formal-series premise. -/
theorem rawScatteringMatrix_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    rawScatteringMatrix q k = 1+(k : ℂ)^2 • rawScatteringQuadraticCoefficient q+
      (k : ℂ)^3 • rawScatteringCubicCoefficient q+(k : ℂ)^4 • rawScatteringFourthCoefficient q+
      (k : ℂ)^5 • rawScatteringFifthRemainder q k := by
  rw [rawScatteringMatrix,rawAsymptoticMatrix_fifth_factor,rawAsymptoticMatrix_inverse_fifth_factor]
  unfold rawScatteringQuadraticCoefficient rawScatteringCubicCoefficient
    rawScatteringFourthCoefficient rawScatteringFifthRemainder
  simp only [sub_eq_add_neg,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,
    smul_add,smul_neg,mul_neg,one_mul,mul_one,smul_smul]
  module

private theorem continuousAt_rawQuinticEndpointMatrix_zero (q : SchwartzMap ℝ ℂ) (left : Bool) :
    ContinuousAt (fun k => rawQuinticEndpointMatrix q k left) 0 := rawQuinticEndpointMatrix_tendsto_zero q left

/-- The actual fifth remainder converges at zero; it is uniformly bounded nearby. -/
theorem rawScatteringFifthRemainder_tendsto_zero (q : SchwartzMap ℝ ℂ) :
    Tendsto (rawScatteringFifthRemainder q) (𝓝 0) (𝓝 (rawScatteringFifthCoefficient q)) := by
  have hR := continuousAt_rawQuinticEndpointMatrix_zero q false
  have hL := continuousAt_rawQuinticEndpointMatrix_zero q true
  have hc : ContinuousAt (rawScatteringFifthRemainder q) 0 := by
    unfold rawScatteringFifthRemainder
    fun_prop
  exact hc.tendsto

/-- The fifth quotient after subtracting the true preceding coefficients has an actual limit. -/
theorem rawScatteringMatrix_fifth_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℝ => ((k : ℂ)^5)⁻¹ •
      (rawScatteringMatrix q k-1-(k : ℂ)^2 • rawScatteringQuadraticCoefficient q-
        (k : ℂ)^3 • rawScatteringCubicCoefficient q-(k : ℂ)^4 • rawScatteringFourthCoefficient q))
      (𝓝[≠] 0) (𝓝 (rawScatteringFifthCoefficient q)) := by
  have hh : Tendsto (rawScatteringFifthRemainder q) (𝓝[≠] (0 : ℝ)) (𝓝 (rawScatteringFifthCoefficient q)) :=
    (rawScatteringFifthRemainder_tendsto_zero q).mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hkc : (k : ℂ)^5 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hk)
  have he : rawScatteringMatrix q k-1-(k : ℂ)^2 • rawScatteringQuadraticCoefficient q-
      (k : ℂ)^3 • rawScatteringCubicCoefficient q-(k : ℂ)^4 • rawScatteringFourthCoefficient q =
        (k : ℂ)^5 • rawScatteringFifthRemainder q k := by
    rw [rawScatteringMatrix_fifth_factor]
    abel
  rw [he,smul_smul,inv_mul_cancel₀ hkc,one_smul]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
