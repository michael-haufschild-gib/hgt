import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitPrimeCellCoPoissonBudget
import GaloisForLFunctions.RHTower.GammaJordanXiTangentResponseGap

/-!
# Euler--Gamma Pythagorean budget of one Route-P prime cell

P-G48 leaves a positive trace-class complement after the primitive Gamma/co-Poisson current
cancels the running prime charge.  This module identifies that complement exactly with the fourth
power of the corpus's archimedean cyclic characteristic at the Julia-forced scattering rapidity.

This is a canonical value identity, but not yet physical clock provenance.  The forced rapidity is
nonlinear in the prime thermal data.  A Route-P producer must still prove that this forced Gamma
evaluation is carried by the actual completed source, rather than introduce it as a receiver.
-/

open Complex Filter Set Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Cayley coordinate measuring the fraction of running co-Poisson charge spent in Julia defect. -/
def thermalBernoulliCoPoissonCayley (q k T : ℝ) : ℝ :=
  (T - 1) / (T + thermalBernoulliRunningOdds q k)

theorem thermalBernoulliCoPoissonCayley_mem_Ioo_zero_one
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    thermalBernoulliCoPoissonCayley q k T ∈ Ioo 0 1 := by
  have ha : 0 < thermalBernoulliRunningOdds q k :=
    thermalBernoulliRunningOdds_pos hq
  rw [thermalBernoulliCoPoissonCayley]
  constructor
  · exact div_pos (sub_pos.mpr hT) (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith

/-- Julia defect is running charge times squared Cayley coordinate. -/
theorem thermalBernoulliBoundaryLayerDefectOdds_eq_runningOdds_mul_cayley_sq
    {q k T : ℝ} (hT : 1 < T) :
    thermalBernoulliMidpointDefectOdds q
        (thermalBernoulliBoundaryLayerEccentricity k T) T =
      thermalBernoulliRunningOdds q k *
        thermalBernoulliCoPoissonCayley q k T ^ 2 := by
  rw [thermalBernoulliBoundaryLayerDefectOdds_eq_wall hT,
    thermalBernoulliMidpointDefectOdds_one (lt_trans zero_lt_one hT).ne',
    thermalBernoulliCoPoissonCayley]
  field_simp

/-- Co-Poisson complement is running charge times complementary Julia coordinate. -/
theorem thermalBernoulliCoPoissonComplement_eq_runningOdds_mul_one_sub_cayley_sq
    {q k T : ℝ} (hT : 1 < T) :
    thermalBernoulliCoPoissonComplement q k T =
      thermalBernoulliRunningOdds q k *
        (1 - thermalBernoulliCoPoissonCayley q k T ^ 2) := by
  rw [thermalBernoulliCoPoissonComplement,
    thermalBernoulliBoundaryLayerDefectOdds_eq_runningOdds_mul_cayley_sq hT]
  ring

/-- The corpus's Gamma cyclic characteristic realizes the complementary Julia coordinate at the
uniquely forced scattering rapidity `artanh C`. -/
theorem semilocalArchimedeanCharacteristic_artanh_cayley_pow_four
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    RHTower.semilocalArchimedeanCharacteristic
        (Real.artanh (thermalBernoulliCoPoissonCayley q k T)) ^ 4 =
      1 - thermalBernoulliCoPoissonCayley q k T ^ 2 := by
  have hc := thermalBernoulliCoPoissonCayley_mem_Ioo_zero_one (k := k) hq hT
  have htanh := Real.tanh_artanh
    (show thermalBernoulliCoPoissonCayley q k T ∈ Ioo (-1 : ℝ) 1 by
      exact ⟨lt_trans (by norm_num) hc.1, hc.2⟩)
  have hunit := RHTower.semilocalArchimedeanCharacteristic_pow_four_add_tanh_sq
    (Real.artanh (thermalBernoulliCoPoissonCayley q k T))
  rw [htanh] at hunit
  linarith

/-- Exact Gamma representation of the P-G48 complement. -/
theorem thermalBernoulliCoPoissonComplement_eq_gammaCharacteristic
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    thermalBernoulliCoPoissonComplement q k T =
      thermalBernoulliRunningOdds q k *
        RHTower.semilocalArchimedeanCharacteristic
          (Real.artanh (thermalBernoulliCoPoissonCayley q k T)) ^ 4 := by
  rw [thermalBernoulliCoPoissonComplement_eq_runningOdds_mul_one_sub_cayley_sq hT,
    semilocalArchimedeanCharacteristic_artanh_cayley_pow_four hq hT]

/-- **Euler--Gamma Pythagorean budget.** Running source charge splits exactly into Julia defect
and Gamma cyclic complement. -/
theorem thermalBernoulliEulerGammaPythagoreanBudget
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    thermalBernoulliMidpointDefectOdds q
          (thermalBernoulliBoundaryLayerEccentricity k T) T +
        thermalBernoulliRunningOdds q k *
          RHTower.semilocalArchimedeanCharacteristic
            (Real.artanh (thermalBernoulliCoPoissonCayley q k T)) ^ 4 =
      thermalBernoulliRunningOdds q k := by
  rw [thermalBernoulliBoundaryLayerDefectOdds_eq_runningOdds_mul_cayley_sq hT,
    semilocalArchimedeanCharacteristic_artanh_cayley_pow_four hq hT]
  ring

/-- Literal three-channel Ward identity: primitive Gamma/co-Poisson term, Julia defect, and Gamma
cyclic complement sum exactly to zero on every finite prime cell. -/
theorem eulerGammaCoPoissonPrimitiveTerm_add_julia_add_gamma_eq_zero
    (p : Nat.Primes) {x epsilon T : ℝ} (hT : 1 < T) :
    RHTower.eulerGammaCoPoissonPrimitiveTerm p ((1 + x * epsilon : ℝ) : ℂ) +
        (thermalBernoulliMidpointDefectOdds ((p : ℝ) ^ (-1 : ℝ))
          (thermalBernoulliBoundaryLayerEccentricity
            (x * epsilon * Real.log (p : ℝ)) T) T : ℝ) +
        (thermalBernoulliRunningOdds ((p : ℝ) ^ (-1 : ℝ))
          (x * epsilon * Real.log (p : ℝ)) *
          RHTower.semilocalArchimedeanCharacteristic
            (Real.artanh (thermalBernoulliCoPoissonCayley
              ((p : ℝ) ^ (-1 : ℝ))
              (x * epsilon * Real.log (p : ℝ)) T)) ^ 4 : ℝ) = 0 := by
  have hq : 0 < (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  rw [eulerGammaCoPoissonPrimitiveTerm_prime_runningOdds]
  rw [show
    thermalBernoulliRunningOdds ((p : ℝ) ^ (-1 : ℝ))
          (x * epsilon * Real.log (p : ℝ)) *
        RHTower.semilocalArchimedeanCharacteristic
          (Real.artanh (thermalBernoulliCoPoissonCayley
            ((p : ℝ) ^ (-1 : ℝ))
            (x * epsilon * Real.log (p : ℝ)) T)) ^ 4 =
      thermalBernoulliCoPoissonComplement ((p : ℝ) ^ (-1 : ℝ))
        (x * epsilon * Real.log (p : ℝ)) T from
    (thermalBernoulliCoPoissonComplement_eq_gammaCharacteristic hq hT).symm]
  rw [thermalBernoulliCoPoissonComplement]
  push_cast
  ring

end

end RHTower.HedenmalmThetaSource
