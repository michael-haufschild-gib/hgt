import GaloisForLFunctions.WindowTowerOfSpecZ.TheOddWeilFormHasAFloorAtApertureLogTwo
import GaloisForLFunctions.WindowTowerOfSpecZ.TheEvenWeilFormHasAFloorAtApertureLogTwo
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGroundEnergyOfAnApertureIsTheFloorOfWeilsFormOnTheWindowsInsideIt

/-!
# A positive Weil floor on the full two-prime window at every block size

This module combines the unconditional odd floor (`10⁻¹⁰`, proved in
`TheOddWeilFormHasAFloorAtApertureLogTwo`) and even floor (`10⁻¹³`, proved in
`TheEvenWeilFormHasAFloorAtApertureLogTwo`) at aperture `A = log 2` by orthogonal parity
splitting, transfers the resulting `10⁻¹³` floor to complex tests, to the closed Suzuki–CCM
ground energy `ccmRestrictedWeilGroundEnergy ⟨log 2, _⟩`, and to the step packets, block
matrices, and neutral windows of every two-prime window `(R, R + J]` of ratio `(R + J) / R < 4`
at every block size `R ≥ 1` and cutoff `Q ≥ 3`. It also pairs the lower bound with the smooth
degree-18 upper-bound witness `twoPrimeScaleTest` to bracket the ground energy in
`[10⁻¹³, 10⁻⁹)` and record the strict negativity of the degree-14 local Gamma lower form on
`[-log 2, log 2]`.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology Finset Matrix Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open ArithmeticCriticalityTheory ArithmeticPositivityTheory SquareRootThreshold
open SpacingScaleHarmonicAnalysis AbsoluteGeometryOfSpecZ
open HTGeometry MixingArithmeticOfTheFloorTrees
open GreenCalculusOfThePrimeFreeWindow

/-! ### 1. Parity combination and continuum Weil floor at aperture `log 2` -/

/-- The Suzuki positive aperture `A = log 2` of the full two-prime window. -/
def suzukiApertureLogTwo : SuzukiPositiveAperture :=
  ⟨Real.log 2, Real.log_pos one_lt_two⟩

/-- On odd `C²` tests supported in `[-log 2, log 2]`, Weil's form has the floor `10⁻¹⁰`. -/
theorem oddWeilFloor_apertureLogTwo : OddWeilFloor (Real.log 2) (1 / 10 ^ 10) :=
  fun _ hF hs ho => weilQuad_ge_odd_at_aperture_log_two hF hs ho

/-- On even `C²` tests supported in `[-log 2, log 2]`, Weil's form has the floor `10⁻¹³`. -/
theorem evenWeilFloor_apertureLogTwo : EvenWeilFloor (Real.log 2) (1 / 10 ^ 13) :=
  fun _ hF hs he => weilQuad_ge_even_at_aperture_log_two hF hs he

/-- Orthogonal parity splitting combines the even (`10⁻¹³`) and odd (`10⁻¹⁰`) floors into an
unconditional `10⁻¹³` floor on all real `C²` tests supported in `[-log 2, log 2]`. -/
theorem weilFloor_apertureLogTwo : WeilFloor (Real.log 2) (1 / 10 ^ 13) :=
  WeilFloor.of_even_of_odd evenWeilFloor_apertureLogTwo
    (oddWeilFloor_apertureLogTwo.mono (by norm_num))

/-- Every real `C²` test supported in `[-log 2, log 2]` satisfies
`(1 / 10 ^ 13) * ∫ F² ≤ weilQuad F`. -/
theorem weilQuad_ge_at_aperture_log_two {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-Real.log 2) (Real.log 2)) :
    (1 / 10 ^ 13 : ℝ) * (∫ x, F x ^ 2) ≤ weilQuad F :=
  weilFloor_apertureLogTwo F hF hs

/-- Every real `C²` test vanishing outside `[-log 2, log 2]` has `fullZeroForm F ≥ 10⁻¹³ ∫ F²`. -/
theorem fullZeroForm_ge_at_aperture_log_two {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : ∀ x, Real.log 2 < |x| → F x = 0) :
    (1 / 10 ^ 13 : ℝ) * (∫ x, F x ^ 2) ≤ fullZeroForm F := by
  rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hcs]
  exact weilFloor_apertureLogTwo F hF (tsupport_subset_Icc_of_forall_eq_zero hs)

/-- Complexification transfers the `10⁻¹³` floor to all complex `C²` tests supported in
`[-log 2, log 2]`, with no parity restriction. -/
theorem zetaZeroConfig_re_W_ge_at_aperture_log_two {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-Real.log 2) (Real.log 2)) :
    (1 / 10 ^ 13 : ℝ) * (∫ x, ‖f x‖ ^ 2) ≤ (zetaZeroConfig.W f f).re :=
  zetaZeroConfig_re_W_ge_of_window
    (fun _ hF hcs hs => fullZeroForm_ge_at_aperture_log_two hF hcs hs) hf hs

/-! ### 2. Ground energy bracket `[10⁻¹³, 10⁻⁹)` and degree-14 Gamma insufficiency -/

/-- The closed Weil form retains the `10⁻¹³` floor at every aperture `A ≤ log 2`. -/
theorem one_div_ten_pow_13_le_groundEnergy_of_aperture_le_log_two
    {A : SuzukiPositiveAperture} (hA : A.1 ≤ Real.log 2) :
    (1 / 10 ^ 13 : ℝ) ≤ ccmRestrictedWeilGroundEnergy A := by
  apply WeilFloor.le_groundEnergy
  intro F hF hs
  exact weilFloor_apertureLogTwo F hF (hs.trans fun x hx =>
    ⟨by linarith only [hx.1, hA], by linarith only [hx.2, hA]⟩)

/-- Lower bound `10⁻¹³ ≤ ccmRestrictedWeilGroundEnergy ⟨log 2, _⟩`. -/
theorem one_div_ten_pow_13_le_groundEnergy_apertureLogTwo :
    (1 / 10 ^ 13 : ℝ) ≤ ccmRestrictedWeilGroundEnergy suzukiApertureLogTwo :=
  one_div_ten_pow_13_le_groundEnergy_of_aperture_le_log_two le_rfl

/-- Strict upper bound `ccmRestrictedWeilGroundEnergy ⟨log 2, _⟩ < 10⁻⁹`, certified by the
rescaled smooth degree-18 witness `twoPrimeScaleTest (1 - 10⁻²⁰)` supported strictly inside
`(-log 2, log 2)`. -/
theorem groundEnergy_apertureLogTwo_lt_one_div_ten_pow_9 :
    ccmRestrictedWeilGroundEnergy suzukiApertureLogTwo < 1 / 10 ^ 9 := by
  by_contra hge
  push_neg at hge
  have hexp : Real.exp (2 * suzukiApertureLogTwo.1) ≤ (4 : ℕ) := by
    change Real.exp (2 * Real.log 2) ≤ (4 : ℝ)
    have h2 : 2 * Real.log 2 = Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h2, Real.exp_log (by norm_num)]
  have hstep : StepFloor 4 (Real.log 2) (1 / 10 ^ 9) :=
    stepFloor_of_le_groundEnergy (A := suzukiApertureLogTwo) hexp hge
  set s : ℝ := 1 - 1 / 10 ^ 20
  have hs0 : 0 < s := by dsimp [s]; norm_num
  have hs1 : s < 1 := by dsimp [s]; norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hwf : WeilFloor (s * Real.log 2) (1 / 10 ^ 9) :=
    WeilFloor.of_stepFloor hexp hstep (mul_pos hs0 hlog2) (by nlinarith)
  have hge_test := hwf (twoPrimeScaleTest s) (contDiff_twoPrimeScaleTest s)
    (tsupport_twoPrimeScaleTest hs0)
  have hlt_test := weilQuad_twoPrimeScaleTest_lt (le_rfl : 1 - 1 / 10 ^ 20 ≤ s) hs1.le
  linarith

/-- Two-sided bracket `10⁻¹³ ≤ ccmRestrictedWeilGroundEnergy ⟨log 2, _⟩ < 10⁻⁹` for the
bottom of the spectrum of the restricted Weil operator on `[-log 2, log 2]`. -/
theorem groundEnergy_apertureLogTwo_bounds :
    (1 / 10 ^ 13 : ℝ) ≤ ccmRestrictedWeilGroundEnergy suzukiApertureLogTwo ∧
      ccmRestrictedWeilGroundEnergy suzukiApertureLogTwo < 1 / 10 ^ 9 :=
  ⟨one_div_ten_pow_13_le_groundEnergy_apertureLogTwo,
    groundEnergy_apertureLogTwo_lt_one_div_ten_pow_9⟩

/-- The degree-14 local Gamma lower polynomial used at `A = 1881 / 5000` is strictly insufficient
at `A = log 2`: there exists an even `C²` test supported in `[-log 2, log 2]` of positive mass
on which `twoPrimeDegree14GammaForm` is strictly negative while `weilQuad` is strictly positive. -/
theorem exists_contDiff_twoPrimeDegree14GammaForm_lt_zero :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧
      tsupport F ⊆ Icc (-Real.log 2) (Real.log 2) ∧
      (∀ x, F (-x) = F x) ∧
      0 < (∫ x, F x ^ 2) ∧
      twoPrimeDegree14GammaForm F < 0 ∧
      (1 / 10 ^ 13 : ℝ) * (∫ x, F x ^ 2) ≤ weilQuad F :=
  ⟨twoPrimeUpperTest, contDiff_twoPrimeUpperTest, tsupport_twoPrimeUpperTest,
    twoPrimeScaleTest_even 1, integral_sq_twoPrimeUpperTest_pos,
    twoPrimeDegree14GammaForm_twoPrimeUpperTest_lt_zero,
    weilQuad_ge_at_aperture_log_two contDiff_twoPrimeUpperTest tsupport_twoPrimeUpperTest⟩

/-! ### 3. Step packets, block matrices, and neutral windows of two-prime windows -/

/-- Every integer window `(R, R + J]` with `R + J < 4 * R` has logarithmic length strictly
below `2 * log 2 = log 4`. -/
theorem log_window_lt_two_mul_log_two {R J : ℕ} (hR : 1 ≤ R) (hJ : R + J < 4 * R) :
    Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * Real.log 2 := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hpos : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
  have hlt : ((R + J : ℕ) : ℝ) < 4 * R := by exact_mod_cast hJ
  have h1 := Real.log_lt_log hpos hlt
  rw [Real.log_mul (by norm_num) hR'.ne'] at h1
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

/-- Step packets of every window `(R, R + J]` with `R + J < 4 * R` have the uniform `10⁻¹³`
floor at every block size `R ≥ 1` and for every prime cutoff `Q ≥ 3`. -/
theorem packetForm_stepPacket_ge_of_two_prime_window {R J Q : ℕ}
    (hR : 1 ≤ R) (hJ : R + J < 4 * R) (hQ : 3 ≤ Q) (σ : ℕ → ℝ) :
    (1 / 10 ^ 13 : ℝ) * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ) := by
  have hlen : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * suzukiApertureLogTwo.1 :=
    log_window_lt_two_mul_log_two hR hJ
  have hcut : R + J < (Q + 1) * R :=
    lt_of_lt_of_le hJ (Nat.mul_le_mul_right R (by omega))
  have hμ := one_div_ten_pow_13_le_groundEnergy_apertureLogTwo
  have hfloor := groundEnergy_mul_le_packetForm_stepPacket (A := suzukiApertureLogTwo)
    hR hlen hcut σ
  exact (mul_le_mul_of_nonneg_right hμ (Finset.sum_nonneg fun j _ => sq_nonneg _)).trans hfloor

/-- Every block matrix of a window `(R, R + J]` with `R + J < 4 * R` (`Q ≥ 3`) is uniformly
positive definite with floor `10⁻¹³` at every block size `R ≥ 1`. -/
theorem sum_blockMatrix_ge_of_two_prime_window {R J Q : ℕ}
    (hR : 1 ≤ R) (hJ : R + J < 4 * R) (hQ : 3 ≤ Q) (σ : ℕ → ℝ) :
    (1 / 10 ^ 13 : ℝ) * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) := by
  rw [← packetForm_stepPacket_eq_sum_blockMatrix hR Q J σ]
  exact packetForm_stepPacket_ge_of_two_prime_window hR hJ hQ σ

/-- Every neutral window `neutralWindow Q R J` with `R + J < 4 * R` and `Q ≥ 3` is at least
`10⁻¹³` on its charge-free packets, at every block size `R ≥ 1`. -/
theorem neutralWindow_floor_two_prime_window {Q R J : ℕ}
    (hQ : 3 ≤ Q) (hR : 1 ≤ R) (hJ : R + J < 4 * R) (z : Fin J → ℝ) (hz : ∑ i, z i = 0) :
    (1 / 10 ^ 13 : ℝ) * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z) :=
  neutralWindow_floor_of_le_groundEnergy (A := suzukiApertureLogTwo) hR
    (log_window_lt_two_mul_log_two hR hJ)
    (lt_of_lt_of_le hJ (Nat.mul_le_mul_right R (by omega)))
    one_div_ten_pow_13_le_groundEnergy_apertureLogTwo z hz

/-- Every neutral window `neutralWindow Q R J` with `R + J < 4 * R` and `Q ≥ 3` has the uniform
spectral gap `10⁻¹³` at every block size `R ≥ 1`. -/
theorem hasGap_neutralWindow_two_prime_window {Q R J : ℕ}
    (hQ : 3 ≤ Q) (hR : 1 ≤ R) (hJ : R + J < 4 * R) :
    HasGap (neutralWindow Q R J) (1 / 10 ^ 13) :=
  hasGap_neutralWindow_of_le_groundEnergy (A := suzukiApertureLogTwo) hR
    (log_window_lt_two_mul_log_two hR hJ)
    (lt_of_lt_of_le hJ (Nat.mul_le_mul_right R (by omega)))
    one_div_ten_pow_13_le_groundEnergy_apertureLogTwo

/-- Every neutral window `neutralWindow Q R J` with `R ≤ J` and `R + J < 4 * R` (`Q ≥ 3`) holds
exactly one bound state (`hermNegIndex = 1`) at every block size `R ≥ 1`. -/
theorem hermNegIndex_neutralWindow_two_prime_window {Q R J : ℕ}
    (hQ : 3 ≤ Q) (hR : 1 ≤ R) (hRJ : R ≤ J) (hJ : R + J < 4 * R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 :=
  hermNegIndex_neutralWindow_eq_one_of_hasGap hR hRJ (by norm_num)
    (hasGap_neutralWindow_two_prime_window hQ hR hJ)

end GaloisForLFunctions.WindowTowerOfSpecZ
