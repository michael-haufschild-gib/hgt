import GaloisForLFunctions.OrderSixMetaplecticTheory.ThePhasedConjugateTwistCarriesAQuarterOfTheDoublePole
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheRatioPairsCarryTwistedSexticJacobiSums
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedDifferenceIsTheUnramifiedSquare

/-!
# The unramified conjugate twist carries half the double pole

STCC's selector separates the frequencies prime to `3`: on the support of `T`, the opposite translation phases
`φ(k) + φ(−k)` equal `2` on `3O` and `−1` elsewhere (`thetaSquare_translation_selector`). The conjugate cubic
character is even (`χ_q(−1) = 1`), so the same selector applies to the conjugate twist (`conjTwist_sub_phased`):

`L_{χ̄_q}(s) − L^φ_{χ̄_q}(s) = (3/2) Σ_{3 ∤ k} χ_q(k)⁻¹T(k)²(4π|ξ_k|)^{−s}`.

The conjugate twist has the double pole with leading coefficient `L` (`conjugateCubicTwist_double_pole`), its phased
version `L/4` (`phasedConjugateCubicTwist_double_pole`). Hence (`unramifiedConjugateCubicTwist_double_pole`):

**the part of the conjugate cubic twist on frequencies prime to `3` has the double pole with leading coefficient
`L/2` at every odd primary prime** — the ratio `1/2` of the untwisted theta square (`54π³r³` of `108π³r³`).
-/

noncomputable section

open MeasureTheory Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

theorem shiftPhase_omega_eq (h : O) : shiftPhase omega h = tracePhase (2 * (cuspFrequency h * ringComplex omega)) := by
  rw [shiftPhase]
  congr 1
  ring

theorem shiftPhase_omega_neg (h : O) :
    shiftPhase omega (-h) = tracePhase (-(2 * (cuspFrequency h * ringComplex omega))) := by
  rw [shiftPhase, cuspFrequency_neg]
  congr 1
  ring

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `χ_q(k)⁻¹T(k)²` on `k` prime to `3`. -/
def unramConjCoeff (h : O) : ℂ := if (3 : O) ∣ h then 0 else P.conjTwistCoeff h

theorem chi_res_neg (h : O) : P.chi (P.res (-h)) = P.chi (P.res h) := by
  rw [map_neg, show -P.res h = -1 * P.res h by ring, map_mul, P.chi_neg_one, one_mul]

theorem conjTwistCoeff_neg (h : O) : P.conjTwistCoeff (-h) = P.conjTwistCoeff h := by
  rw [conjTwistCoeff, conjTwistCoeff, P.chi_res_neg, rationalSourceResidualFourierCoefficient_neg]

theorem norm_chi_inv_le (u : P.Res) : ‖(P.chi u)⁻¹‖ ≤ 1 := by
  by_cases hu : u = 0
  · rw [hu, MulChar.map_zero, inv_zero, norm_zero]
    exact zero_le_one
  · rw [norm_inv, P.norm_chi_eq_one u hu, inv_one]

/-- The selector at one frequency. -/
theorem conjTwist_selector (h : O) :
    P.conjTwistCoeff h * (1 - (tracePhase (2 * (cuspFrequency h * ringComplex omega)) +
        tracePhase (-(2 * (cuspFrequency h * ringComplex omega)))) / 2) = (3 / 2 : ℂ) * P.unramConjCoeff h := by
  have hs := thetaSquare_translation_selector h
  rw [conjTwistCoeff, mul_assoc, hs]
  unfold unramConjCoeff conjTwistCoeff
  split_ifs <;> ring

/-- **The selector on the conjugate twist.** `L_{χ̄} − L^φ_{χ̄} = (3/2) L^{(3∤)}_{χ̄}`. -/
theorem conjTwist_sub_phased (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet P.conjTwistCoeff s - besselDirichlet P.phConjTwistCoeff s =
      (3 / 2 : ℂ) * besselDirichlet P.unramConjCoeff s := by
  let F : O → ℂ := fun h => if h = 0 then 0 else P.conjTwistCoeff h *
    ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  let C : O → ℂ := fun h => if h = 0 then 0 else P.phConjTwistCoeff h *
    ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  have hT := summable_thetaSqDirichlet_term s hs
  have hF : Summable F := by
    refine Summable.of_norm_bounded hT.norm fun h => ?_
    simp only [F]
    split_ifs with hh
    · simp
    · rw [conjTwistCoeff, norm_mul, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) (P.norm_chi_inv_le _)) (norm_nonneg _)
  have hC : Summable C := by
    refine Summable.of_norm_bounded hT.norm fun h => ?_
    simp only [C]
    split_ifs with hh
    · simp
    · rw [phConjTwistCoeff, conjTwistCoeff, norm_mul, norm_mul, norm_mul, norm_mul, norm_shiftPhase, one_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) (P.norm_chi_inv_le _)) (norm_nonneg _)
  have hneg : Summable (fun h => C (-h)) := hC.comp_injective neg_injective
  have he : (∑' h, C (-h)) = ∑' h, C h := (Equiv.neg O).tsum_eq C
  change (∑' h, F h) - (∑' h, C h) = _
  calc
    _ = (∑' h, F h) - ((∑' h, C h) + ∑' h, C (-h)) / 2 := by rw [he]; ring
    _ = ∑' h, (F h - (C h + C (-h)) / 2) := by
      rw [← hC.tsum_add hneg, ← tsum_div_const, hF.tsum_sub ((hC.add hneg).div_const 2)]
    _ = ∑' h : O, (3 / 2 : ℂ) * (if h = 0 then 0 else P.unramConjCoeff h *
        ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) := by
      refine tsum_congr fun h => ?_
      by_cases hh : h = 0
      · simp [F, C, hh]
      · simp only [F, C, hh, neg_ne_zero.mpr hh, if_false, cuspFrequency_neg, norm_neg, phConjTwistCoeff,
          P.conjTwistCoeff_neg]
        rw [shiftPhase_omega_neg, shiftPhase_omega_eq]
        have hp := P.conjTwist_selector h
        linear_combination (((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) * hp
    _ = _ := by rw [tsum_mul_left]; rfl

/-- **The unramified conjugate cubic twist has the double pole with half the leading coefficient.** For every odd
primary prime `q`, `(s − 4/3)²M(s)Σ_{3∤k} χ_q(k)⁻¹T(k)²(4π|ξ_k|)^{−s} → L/2 ≠ 0`, where `L` is the leading
coefficient of the conjugate cubic twist. -/
theorem unramifiedConjugateCubicTwist_double_pole (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * besselDirichlet P.unramConjCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 ((P.gaussAt 1)⁻¹ * P.conjLimit / 2)) ∧
      (P.gaussAt 1)⁻¹ * P.conjLimit / 2 ≠ 0 := by
  obtain ⟨Λc, hc_eq, hc_d, hc_n, hc_l, hc_ne⟩ := P.conjugateCubicTwist_double_pole h2
  obtain ⟨Λφ, hφ_eq, hφ_d, hφ_n, hφ_l, -⟩ := P.phasedConjugateCubicTwist_double_pole h2
  refine ⟨fun s => (2 / 3 : ℂ) * (Λc s - Λφ s), fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_,
    div_ne_zero hc_ne (by norm_num)⟩
  · show (2 / 3 : ℂ) * (Λc s - Λφ s) = _
    rw [hc_eq s hs4 hs hi, hφ_eq s hs4 hs hi, ← mul_sub, P.conjTwist_sub_phased s hs4]
    ring
  · exact ((hc_d s hs1 hs hi).sub (hφ_d s hs1 hs hi)).const_mul _
  · filter_upwards [hc_n, hφ_n] with s h1 h2'
    exact (h1.sub h2').const_mul _
  · have h := (hc_l.sub hφ_l).const_mul (2 / 3 : ℂ)
    rw [P.phConjLimit_eq] at h
    have he : (2 / 3 : ℂ) * ((P.gaussAt 1)⁻¹ * P.conjLimit - (P.gaussAt 1)⁻¹ * (P.conjLimit / 4)) =
        (P.gaussAt 1)⁻¹ * P.conjLimit / 2 := by ring
    rw [he] at h
    exact h.congr fun s => by ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
