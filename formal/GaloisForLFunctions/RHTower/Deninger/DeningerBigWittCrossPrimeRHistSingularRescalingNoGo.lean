import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCrossPrimeHarmonicSingularGraphSource

open Filter Topology

namespace RHTower
noncomputable section

/-- Square-root rescaling of the trace-normalized finite prime-two source row. -/
def deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket
    (n : ℕ) : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  (Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1)) : ℂ) •
    deningerBigWittPrimeTwoRightEdgeNormalizedPacket n

/-- The singular algebraic one-leg trace of a square-root rescaled row is its
source square-root scale. -/
@[simp] theorem deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeSqrtNormalizedPacket
    (n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket n) =
      (Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1)) : ℂ) := by
  rw [deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket, map_smul,
    deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeNormalizedPacket,
    smul_eq_mul, mul_one]

private theorem sqrt_mass_mul_inv_mass_eq_inv_sqrt_mass (n : ℕ) :
    Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1)) *
        (deningerBigWittPrimeTwoRightEdgeMass (n + 1))⁻¹ =
      (Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1)))⁻¹ := by
  have hmass := deningerBigWittPrimeTwoRightEdgeMass_pos n
  let s : ℝ := Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1))
  have hs : s ≠ 0 := ne_of_gt (by
    simpa only [s] using Real.sqrt_pos.2 hmass)
  have hsq : s * s = deningerBigWittPrimeTwoRightEdgeMass (n + 1) := by
    simpa only [s, pow_two] using Real.sq_sqrt hmass.le
  change s * (deningerBigWittPrimeTwoRightEdgeMass (n + 1))⁻¹ = s⁻¹
  rw [← hsq]
  field_simp

/-- The square-root rescaling still disappears in the ambient cross-prime
Calderón--Witt `ℓ²` carrier. -/
theorem norm_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeSqrtNormalizedPacket_le
    (n : ℕ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket n)‖ ≤
      (Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1)))⁻¹ *
        ‖deningerBigWittCrossPrimePacketRawHorizon‖ := by
  rw [deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket, map_smul, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1)) *
        ‖deningerBigWittCrossPairFinitePacketAdmission
          (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n)‖ ≤
      Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1)) *
        ((deningerBigWittPrimeTwoRightEdgeMass (n + 1))⁻¹ *
          ‖deningerBigWittCrossPrimePacketRawHorizon‖) :=
      mul_le_mul_of_nonneg_left
        (norm_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeNormalizedPacket_le n)
        (Real.sqrt_nonneg _)
    _ = (Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1)))⁻¹ *
        ‖deningerBigWittCrossPrimePacketRawHorizon‖ := by
      rw [← mul_assoc, sqrt_mass_mul_inv_mass_eq_inv_sqrt_mass]

private theorem tendsto_inv_sqrt_deningerBigWittPrimeTwoRightEdgeMass_atTop :
    Tendsto (fun n => (Real.sqrt
      (deningerBigWittPrimeTwoRightEdgeMass (n + 1)))⁻¹) atTop (nhds 0) := by
  have hmass : Tendsto
      (fun n => deningerBigWittPrimeTwoRightEdgeMass (n + 1)) atTop atTop :=
    tendsto_deningerBigWittPrimeTwoRightEdgeMass_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  exact (Real.tendsto_sqrt_atTop.comp hmass).inv_tendsto_atTop

/-- Square-root rescaled finite source rows remain norm-dark in the ambient
carrier. -/
theorem tendsto_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeSqrtNormalizedPacket :
    Tendsto (fun n => deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket n))
      atTop (nhds 0) := by
  have hmaj : Tendsto (fun n =>
      (Real.sqrt (deningerBigWittPrimeTwoRightEdgeMass (n + 1)))⁻¹ *
        ‖deningerBigWittCrossPrimePacketRawHorizon‖) atTop (nhds 0) := by
    simpa [mul_comm] using
      tendsto_inv_sqrt_deningerBigWittPrimeTwoRightEdgeMass_atTop.const_mul
        ‖deningerBigWittCrossPrimePacketRawHorizon‖
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmaj
  exact Eventually.of_forall
    norm_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeSqrtNormalizedPacket_le

/-- The source-defined singular trace of those same ambiently dark rows grows
without bound. This rules out an RHist closure based only on ambient darkness
and a scale-sensitive singular readout. -/
theorem tendsto_re_deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeSqrtNormalizedPacket_atTop :
    Tendsto (fun n =>
      (deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket n)).re) atTop atTop := by
  have hmass : Tendsto
      (fun n => deningerBigWittPrimeTwoRightEdgeMass (n + 1)) atTop atTop :=
    tendsto_deningerBigWittPrimeTwoRightEdgeMass_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  simpa only [deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeSqrtNormalizedPacket,
    Complex.ofReal_re, Function.comp_def] using Real.tendsto_sqrt_atTop.comp hmass

/-- Arbitrarily small ambient source rows can carry arbitrarily large
source-defined singular trace. Hence a singular RHist observer needs a
normalization-invariant law beyond ambient darkness and finite price. -/
theorem exists_deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket_ambient_small_trace_large
    {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ n,
      ‖deningerBigWittCrossPairFinitePacketAdmission
          (deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket n)‖ < ε ∧
        B < (deningerBigWittCrossPairAlgebraicOneLegTrace
          (deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket n)).re := by
  have hnorm : Tendsto (fun n =>
      ‖deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittPrimeTwoRightEdgeSqrtNormalizedPacket n)‖) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp
      tendsto_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeSqrtNormalizedPacket
  exact ((hnorm.eventually_lt_const hε).and
    (tendsto_re_deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeSqrtNormalizedPacket_atTop
      |>.eventually_gt_atTop B)).exists

end
end RHTower
