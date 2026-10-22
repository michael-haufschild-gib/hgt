import GaloisForLFunctions.RHTower.FiniteOfflineCauchyL2
import GaloisForLFunctions.RHTower.XiShiftLoewnerFlow
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyTransport
import GaloisForLFunctions.RHTower.CCM.CCMRectangularDirichletLandau
import GaloisForLFunctions.RHTower.XiShiftDivisorPrimeSymbol
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCriticalChordMeasure

open MeasureTheory Set Complex Filter
open scoped BigOperators

noncomputable section

namespace RHTower

/-- A certificate that the complete strict-right Xi divisor is finite, indexed with every
analytic multiplicity copy. -/
structure FiniteXiRightDivisor where
  card : ℕ
  index : Fin card ≃ XiRightZeroCopy

def FiniteXiRightDivisor.depth (D : FiniteXiRightDivisor) (j : Fin D.card) : ℝ :=
  (xiRightCenteredZero (D.index j)).re

def FiniteXiRightDivisor.ordinate (D : FiniteXiRightDivisor) (j : Fin D.card) : ℝ :=
  (xiRightCenteredZero (D.index j)).im

def FiniteXiRightDivisor.profile (D : FiniteXiRightDivisor) (t : ℝ) : ℂ :=
  finiteOfflineProfile D.depth D.ordinate (fun _ => 1) t

def FiniteXiRightDivisor.energy (D : FiniteXiRightDivisor) : ℝ :=
  finiteOfflineCauchyEnergy D.depth D.ordinate (fun _ => 1)

def FiniteXiRightDivisor.boundaryContact (D : FiniteXiRightDivisor) : ℂ :=
  ∑ j, 2 * (xiRightCenteredZero (D.index j))⁻¹

def FiniteXiRightDivisor.profileLaplace
    (D : FiniteXiRightDivisor) (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (-w * t) * D.profile t

/-- Source-side infinitesimal Toeplitz curvature kernel `D⁺D` in the reflected
Paley--Wiener coordinate. -/
def FiniteXiRightDivisor.curvatureKernel
    (D : FiniteXiRightDivisor) (y z : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ),
    (starRingEnd ℂ) (D.profile (x + y)) * D.profile (x + z)

theorem FiniteXiRightDivisor.depth_pos (D : FiniteXiRightDivisor) (j : Fin D.card) :
    0 < D.depth j :=
  xiRightCenteredZero_re_pos (D.index j)

theorem FiniteXiRightDivisor.depth_lt_half (D : FiniteXiRightDivisor) (j : Fin D.card) :
    D.depth j < (1 / 2 : ℝ) := by
  exact (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half (D.index j))).2

theorem FiniteXiRightDivisor.profile_eq (D : FiniteXiRightDivisor) (t : ℝ) :
    D.profile t =
      2 * ∑ j, Complex.exp
        (-((D.depth j : ℝ) : ℂ) * t -
          Complex.I * (D.ordinate j : ℂ) * t) := by
  rw [FiniteXiRightDivisor.profile, finiteOfflineProfile, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [finiteOfflineMode]

theorem FiniteXiRightDivisor.centeredZero_eq (D : FiniteXiRightDivisor)
    (j : Fin D.card) :
    xiRightCenteredZero (D.index j) =
      (D.depth j : ℂ) + Complex.I * (D.ordinate j : ℂ) := by
  apply Complex.ext <;> simp [FiniteXiRightDivisor.depth,
    FiniteXiRightDivisor.ordinate]

theorem FiniteXiRightDivisor.profileLaplace_eq_cauchySum
    (D : FiniteXiRightDivisor) {w : ℂ} (hw : 0 ≤ w.re) :
    D.profileLaplace w =
      ∑ j, 2 * (w + xiRightCenteredZero (D.index j))⁻¹ := by
  rw [FiniteXiRightDivisor.profileLaplace]
  have hint (j : Fin D.card) : IntegrableOn
      (fun t : ℝ =>
        Complex.exp (-w * t) *
          (2 * Complex.exp
            (-((D.depth j : ℝ) : ℂ) * t -
              Complex.I * (D.ordinate j : ℂ) * t))) (Ioi 0) := by
    have hreal :
        ((-(w + ((D.depth j : ℝ) : ℂ) +
          Complex.I * (D.ordinate j : ℂ))).re) < 0 := by
      simp only [neg_re, add_re, ofReal_re, mul_re, I_re, I_im,
        ofReal_im, zero_mul, one_mul, sub_zero]
      linarith [D.depth_pos j]
    have hexp : IntegrableOn (fun t : ℝ => Complex.exp
        (-(w + ((D.depth j : ℝ) : ℂ) +
          Complex.I * (D.ordinate j : ℂ)) * t)) (Ioi 0) := by
      apply integrableOn_exp_mul_complex_Ioi
      exact hreal
    have heq : (fun t : ℝ =>
        Complex.exp (-w * t) *
          (2 * Complex.exp
            (-((D.depth j : ℝ) : ℂ) * t -
              Complex.I * (D.ordinate j : ℂ) * t))) =
        fun t : ℝ => 2 * Complex.exp
          (-(w + ((D.depth j : ℝ) : ℂ) +
            Complex.I * (D.ordinate j : ℂ)) * t) := by
      funext t
      calc
        Complex.exp (-w * t) *
              (2 * Complex.exp
                (-((D.depth j : ℝ) : ℂ) * t -
                  Complex.I * (D.ordinate j : ℂ) * t)) =
            2 * (Complex.exp (-w * t) * Complex.exp
              (-((D.depth j : ℝ) : ℂ) * t -
                Complex.I * (D.ordinate j : ℂ) * t)) := by ring
        _ = 2 * Complex.exp
            ((-w * t) + (-((D.depth j : ℝ) : ℂ) * t -
              Complex.I * (D.ordinate j : ℂ) * t)) := by
              rw [Complex.exp_add]
        _ = 2 * Complex.exp
            (-(w + ((D.depth j : ℝ) : ℂ) +
              Complex.I * (D.ordinate j : ℂ)) * t) := by
              congr 2
              ring
    rw [heq]
    exact hexp.const_mul 2
  rw [show (fun t : ℝ => Complex.exp (-w * t) * D.profile t) =
      fun t : ℝ => ∑ j, Complex.exp (-w * t) *
        (2 * Complex.exp
          (-((D.depth j : ℝ) : ℂ) * t -
            Complex.I * (D.ordinate j : ℂ) * t)) by
    funext t
    rw [D.profile_eq, Finset.mul_sum, Finset.mul_sum]]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [show (fun t : ℝ =>
        Complex.exp (-w * t) *
          (2 * Complex.exp
            (-((D.depth j : ℝ) : ℂ) * t -
              Complex.I * (D.ordinate j : ℂ) * t))) =
        fun t : ℝ => 2 * Complex.exp
          (-(w + xiRightCenteredZero (D.index j)) * t) by
      funext t
      rw [D.centeredZero_eq j]
      calc
        Complex.exp (-w * t) *
              (2 * Complex.exp
                (-((D.depth j : ℝ) : ℂ) * t -
                  Complex.I * (D.ordinate j : ℂ) * t)) =
            2 * (Complex.exp (-w * t) * Complex.exp
              (-((D.depth j : ℝ) : ℂ) * t -
                Complex.I * (D.ordinate j : ℂ) * t)) := by ring
        _ = 2 * Complex.exp
            ((-w * t) + (-((D.depth j : ℝ) : ℂ) * t -
              Complex.I * (D.ordinate j : ℂ) * t)) := by
              rw [Complex.exp_add]
        _ = 2 * Complex.exp
            (-(w + (((D.depth j : ℝ) : ℂ) +
              Complex.I * (D.ordinate j : ℂ))) * t) := by
              congr 2
              ring]
    rw [integral_const_mul,
      integral_exp_mul_complex_Ioi (c := 0) (by
        simp only [neg_re, add_re]
        rw [D.centeredZero_eq j]
        simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
          zero_mul, one_mul, sub_zero]
        linarith [D.depth_pos j])]
    simp
    calc
      -1 / (-xiRightCenteredZero (D.index j) + -w) =
          -1 / (-(w + xiRightCenteredZero (D.index j))) := by
            congr 1
            ring
      _ = (w + xiRightCenteredZero (D.index j))⁻¹ := by
        rw [div_neg]
        ring
  · intro j hj
    exact hint j

/-- The actual shifted completed-Xi quotient has first aperture derivative `-2 Xi'/Xi`. -/
theorem hasDerivAt_xiShiftTheta_zero_logDeriv {W : ℂ} (hW : xiCent W ≠ 0) :
    HasDerivAt (fun ω : ℝ => xiShiftTheta ω W)
      (-2 * logDeriv xiCent W) 0 := by
  have h := hasDerivAt_xiShiftTheta (W := W) (ω := 0)
    (by simpa using hW) (by simpa using hW)
  convert h using 1
  simp [xiShiftGen, xiShiftTheta, hW]
  ring

theorem FiniteXiRightDivisor.energy_eq_integral (D : FiniteXiRightDivisor) :
    ∫ t in Ioi (0 : ℝ), ‖D.profile t‖ ^ (2 : ℕ) = D.energy := by
  exact integral_norm_sq_finiteOfflineProfile (fun _ => 1) D.depth_pos

theorem FiniteXiRightDivisor.curvatureKernel_zero_zero_re_eq_energy
    (D : FiniteXiRightDivisor) :
    (D.curvatureKernel 0 0).re = D.energy := by
  rw [FiniteXiRightDivisor.curvatureKernel]
  simp only [add_zero]
  have hint : IntegrableOn (fun t =>
      (starRingEnd ℂ) (D.profile t) * D.profile t) (Ioi 0) := by
    simpa [FiniteXiRightDivisor.profile] using
      finiteOfflineProfile_gramIntegrableOn (fun _ => 1) D.depth_pos
  rw [← D.energy_eq_integral]
  have hre :
      (∫ t in Ioi (0 : ℝ),
          ((starRingEnd ℂ) (D.profile t) * D.profile t).re) =
        (∫ t in Ioi (0 : ℝ),
          (starRingEnd ℂ) (D.profile t) * D.profile t).re :=
    integral_re hint
  rw [← hre]
  apply integral_congr_ae
  filter_upwards with t
  rw [← Complex.normSq_eq_norm_sq]
  have h := Complex.normSq_eq_conj_mul_self (z := D.profile t)
  exact_mod_cast (congrArg Complex.re h).symm

theorem FiniteXiRightDivisor.energy_gt_four_card
    (D : FiniteXiRightDivisor) (hcard : 0 < D.card) :
    (4 : ℝ) * D.card < D.energy := by
  exact finiteOfflineCauchyEnergy_gt_four_card hcard D.depth_pos D.depth_lt_half (by simp)

def FiniteXiRightDivisor.modeResponse (D : FiniteXiRightDivisor)
    (j : Fin D.card) (w : ℂ) : ℂ :=
  xiCenteredAntiCausalWardModeResponse (D.index j) w

theorem FiniteXiRightDivisor.wardResponse_eq_sum_modes
    (D : FiniteXiRightDivisor) {w : ℂ} (hw : 0 < w.re) :
    continuedXiCenteredAntiCausalWardResponse w =
      ∑ j, D.modeResponse j w := by
  letI : Fintype XiRightZeroCopy := Fintype.ofEquiv (Fin D.card) D.index
  rw [continuedXiCenteredAntiCausalWardResponse_eq_tsum_modes hw, tsum_fintype]
  exact (Equiv.sum_comp D.index
    (fun q : XiRightZeroCopy => xiCenteredAntiCausalWardModeResponse q w)).symm

theorem FiniteXiRightDivisor.profileLaplace_eq_ward_add_boundary
    (D : FiniteXiRightDivisor) {w : ℂ} (hw : 0 < w.re) :
    D.profileLaplace w =
      continuedXiCenteredAntiCausalWardResponse w + D.boundaryContact := by
  rw [D.profileLaplace_eq_cauchySum hw.le, D.wardResponse_eq_sum_modes hw,
    FiniteXiRightDivisor.boundaryContact]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteXiRightDivisor.modeResponse,
    xiCenteredAntiCausalWardModeResponse]
  ring

/-- The first two infinitesimal Suzuki Euler grades are exactly `2Λ` and
`4(Λ * Λ)` at every arithmetic label. -/
theorem finiteXiSuzukiEulerTangents :
    ∀ n : ℕ,
      suzukiShiftedCoefficientComplexFirstJet n 0 =
        2 * ArithmeticFunction.vonMangoldt n ∧
      HasDerivAt (suzukiShiftedCoefficientComplexFirstJet n)
        (4 * ((ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) n)) 0 := by
  intro n
  exact ⟨suzukiShiftedCoefficientComplexFirstJet_zero n,
    hasDerivAt_suzukiShiftedCoefficientComplexFirstJet_zero n⟩

theorem finiteXiRightDivisor_capstone :
    ∀ D : FiniteXiRightDivisor,
      (∀ j, 0 < D.depth j ∧ D.depth j < (1 / 2 : ℝ)) ∧
      (∀ t : ℝ, D.profile t =
        2 * ∑ j, Complex.exp
          (-((D.depth j : ℝ) : ℂ) * t -
            Complex.I * (D.ordinate j : ℂ) * t)) ∧
      (∫ t in Ioi (0 : ℝ), ‖D.profile t‖ ^ (2 : ℕ) = D.energy) ∧
      ((D.curvatureKernel 0 0).re = D.energy) ∧
      (0 < D.card → (4 : ℝ) * D.card < D.energy) ∧
      (∀ W : ℂ, xiCent W ≠ 0 →
        HasDerivAt (fun ω : ℝ => xiShiftTheta ω W)
          (-2 * logDeriv xiCent W) 0) ∧
      (∀ s : ℂ, 1 < s.re →
        logDeriv xi s - logDeriv archFactor s =
          -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) ∧
      (∀ w : ℂ, 0 < w.re →
        D.profileLaplace w =
          continuedXiCenteredAntiCausalWardResponse w + D.boundaryContact) ∧
      (∀ w : ℂ, 0 < w.re →
        continuedXiCenteredAntiCausalWardResponse w =
          ∑ j, D.modeResponse j w) ∧
      (∀ n : ℕ,
        suzukiShiftedCoefficientComplexFirstJet n 0 =
          2 * ArithmeticFunction.vonMangoldt n ∧
        HasDerivAt (suzukiShiftedCoefficientComplexFirstJet n)
          (4 * ((ArithmeticFunction.vonMangoldt *
            ArithmeticFunction.vonMangoldt) n)) 0) := by
  intro D
  exact ⟨fun j => ⟨D.depth_pos j, D.depth_lt_half j⟩,
    D.profile_eq, D.energy_eq_integral,
    D.curvatureKernel_zero_zero_re_eq_energy,
    D.energy_gt_four_card,
    fun W hW => hasDerivAt_xiShiftTheta_zero_logDeriv hW,
    fun s hs => logDeriv_xi_sub_archFactor_eq_neg_vonMangoldtLSeries hs,
    fun w hw => D.profileLaplace_eq_ward_add_boundary hw,
    fun w hw => D.wardResponse_eq_sum_modes hw,
    finiteXiSuzukiEulerTangents⟩

end RHTower
