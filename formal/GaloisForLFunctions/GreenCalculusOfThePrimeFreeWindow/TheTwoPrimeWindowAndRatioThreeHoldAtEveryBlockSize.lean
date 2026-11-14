import GaloisForLFunctions.WindowTowerOfSpecZ.TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheThreeRemainingExcessesOfTheRatioThreeLadder

/-!
# The two-prime window and the ratio-three window hold at every block size

The `10⁻¹³` floor of Weil's form at aperture `A = log 2` proved in
`TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize` controls every overlap step inside
`[-log 2, log 2]` (`2(R + a) + b < 4 R`, `Q ≥ 3`), proves the ratio-three window theorem
unconditionally at every block size `R ≥ 1` and for every prime cutoff `Q ≥ 2`, and zeroes out
the iterated Schur excess ladder through the fourth step:

* **Two-prime overlap steps (`2(R + a) + b < 4 R`, `Q ≥ 3`)** (`greenForm_two_prime_window`,
  `overlapSchurLevel_nonneg_two_prime_window`, `windowExcess_eq_zero_two_prime_window`,
  `hermNegIndex_dressedMiddle_two_prime_window`, `dressedMiddle_wells_bound_two_prime_window`,
  `weilSchur_nonneg_two_prime_window`,
  `exists_stepPacket_two_prime_window_lt_one_div_ten_pow_9`): on every overlap step inside the
  ratio-four horizon at cutoff `Q ≥ 3`, the Green inequality holds with reserve `10⁻¹³`, the
  Schur complement is nonnegative down to level `-10⁻¹³`, the dressed middle holds one bound
  state, Weil's Schur complement is nonnegative for `Q ≥ 4`, and some window inside the
  ratio-four horizon carries a step packet with Rayleigh quotient `< 10⁻⁹`.
* **The ratio-three window at every block size (`R ≤ J ≤ 2 R`, `Q ≥ 2`)**
  (`neutralWindow_floor_ratio_three`, `hasGap_neutralWindow_ratio_three`,
  `hermNegIndex_neutralWindow_ratio_three`, `greenForm_ratio_three`,
  `overlapSchurLevel_nonneg_ratio_three`, `windowExcess_eq_zero_ratio_three`,
  `hermNegIndex_dressedMiddle_ratio_three`, `dressedMiddle_wells_bound_ratio_three`): because
  `neutralWindow Q R J = neutralWindow 3 R J` whenever `J ≤ 2 R` and `Q ≥ 2`, and `R + J ≤ 3 R < 4 R`,
  every ratio-three neutral window has the uniform spectral gap `10⁻¹³` on charge-free packets
  and holds **one** bound state (`hermNegIndex = 1`) at every block size `R ≥ 1` and for every
  `Q ≥ 2`.
* **The ratio-squaring excess ladder through step 4 (`2.06 → 2.1218 → 2.25 → 2.53 → 3.209`)**
  (`schurStepExcess_eq_zero_of_sq_div_two_lt_four`,
  `schurStepExcess_eq_zero_of_sq_div_two_le_three`, `schurStepExcess_secondStep`,
  `schurStepExcess_thirdStep`, `schurStepExcess_fourthStep`, `levelAt_two_eq_zero`,
  `levelAt_three_eq_zero`, `levelAt_eq_zero_of_le_three`, `levelAt_four_eq_fourthStep`,
  `levelAt_four_eq_zero`, `levelAt_eq_zero_of_le_four`, `hermNegIndex_fourthStep_eq_one`,
  `globalTowerLevel_eq_zero_of_le_three`): every step with `ρ² / 2 ≤ 3` has zero Schur excess
  down to level `-10⁻¹³` for all `Q ≥ 2`, and every step with `ρ² / 2 < 4` has zero Schur
  excess down to level `-10⁻¹³` for all `Q ≥ 3`. Consequently `levelAt Q k = 0` for all
  `Q ≥ 2, k ≤ 3`, `levelAt Q k = 0` for all `Q ≥ 3, k ≤ 4`, and `globalTowerLevel k = 0` for all
  `k ≤ 3`.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
open GaloisForLFunctions.WindowTowerOfSpecZ

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### 1. Two-prime overlap steps (`2(R + a) + b < 4 R`, `Q ≥ 3`) at every block size -/

/-- **Two-prime overlap step in Green form, with `10⁻¹³` reserve.** On the two ends of every
window `(R, 2(R + a) + b]` with `2(R + a) + b < 4 R` (`Q ≥ 3`, `R ≥ 1`), the attraction through
the positive part of the Green matrix of the dyadic middle, plus `10⁻¹³` times the mass of the
ends, is at most the neutral form of the ends plus the repulsion through the bound state of the
middle. -/
theorem greenForm_two_prime_window {Q R a b : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b < 4 * R) (e : Fin a ⊕ Fin b → ℝ) :
    (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) +
        1 / 10 ^ 13 * (e ⬝ᵥ e) ≤
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) := by
  have htot : R + (a + (R + a) + b) < 4 * R := by omega
  exact greenForm_add_excess_le_of_floor (by omega) (by norm_num)
    (neutralWindow_floor_two_prime_window hQ hR htot) e

/-- For every overlap window `(R, 2(R + a) + b]` with `2(R + a) + b < 4 R` (`Q ≥ 3`, `R ≥ 1`),
the Schur complement of the dyadic middle is nonnegative at every level
`C ∈ [-10⁻¹³, bindingEnergy (R + a))`. -/
theorem overlapSchurLevel_nonneg_two_prime_window {Q R a b : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b < 4 * R) {C : ℝ} (hC : -(1 / 10 ^ 13) ≤ C)
    (hCμ : C < bindingEnergy (R + a)) (e : Fin a ⊕ Fin b → ℝ) :
    0 ≤ e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e) := by
  have htot : R + (a + (R + a) + b) < 4 * R := by omega
  exact overlapSchurLevel_nonneg_of_floor hR (by norm_num) (by norm_num)
    (neutralWindow_floor_two_prime_window hQ hR htot) hC hCμ e

/-- The exact Schur excess of every overlap window `(R, 2(R + a) + b]` with
`2(R + a) + b < 4 R` (`Q ≥ 3`, `R ≥ 1`) vanishes at every level
`C ∈ [-10⁻¹³, bindingEnergy (R + a))`. -/
theorem windowExcess_eq_zero_two_prime_window {Q R a b : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b < 4 * R) {C : ℝ} (hC : -(1 / 10 ^ 13) ≤ C)
    (hCμ : C < bindingEnergy (R + a)) : windowExcess Q R a b C = 0 := by
  have htot : R + (a + (R + a) + b) < 4 * R := by omega
  exact windowExcess_eq_zero_of_floor hR (by norm_num) (by norm_num)
    (neutralWindow_floor_two_prime_window hQ hR htot) hC hCμ

/-- On every overlap window `(R, 2(R + a) + b]` with `2(R + a) + b < 4 R` (`Q ≥ 3`, `R ≥ 1`),
the dyadic middle dressed by the attraction of both ends holds one bound state. -/
theorem hermNegIndex_dressedMiddle_two_prime_window {Q R a b : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b < 4 * R) :
    hermNegIndex ((dressedMiddle Q R a b).map (↑) :
      Matrix (Fin (R + a)) (Fin (R + a)) ℂ) = 1 := by
  rw [← hermNegIndex_neutralWindow_eq_dressedMiddle hR (by omega) (by omega)]
  exact hermNegIndex_neutralWindow_two_prime_window hQ hR (by omega) (by omega)

/-- **Hodge index inequality of the dressed middle on the two-prime window**: two nonnegative
packets of the dyadic middle without a common block, the first of negative dressed energy,
satisfy the reverse Cauchy–Schwarz inequality of the dressed form whenever
`2(R + a) + b < 4 R` (`Q ≥ 3`, `R ≥ 1`). -/
theorem dressedMiddle_wells_bound_two_prime_window {Q R a b : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b < 4 * R) (x y : Fin (R + a) → ℝ)
    (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k) (hxy : ∀ k, x k * y k = 0)
    (hneg : bilin (dressedMiddle Q R a b) x x < 0) :
    bilin (dressedMiddle Q R a b) x x * bilin (dressedMiddle Q R a b) y y ≤
      bilin (dressedMiddle Q R a b) x y ^ 2 :=
  (hermNegIndex_neutralWindow_eq_one_iff_dressedMiddle_wells_bound hR (by omega) (by omega)).mp
    (hermNegIndex_neutralWindow_two_prime_window hQ hR (by omega) (by omega)) x y hx hy hxy hneg

/-- For every cutoff `Q ≥ 4` and every overlap window `(R, 2(R + a) + b]` with
`2(R + a) + b < 4 R` (`R ≥ 1`), Weil's Schur complement on the two ends is positive
semidefinite. -/
theorem weilSchur_nonneg_two_prime_window {Q R a b : ℕ} (hQ : 4 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b < 4 * R) (e : Fin a ⊕ Fin b → ℝ) :
    0 ≤ e ⬝ᵥ (weilSchur Q R a b *ᵥ e) := by
  have hexp : Real.exp (2 * suzukiApertureLogTwo.1) ≤ (Q : ℝ) := by
    change Real.exp (2 * Real.log 2) ≤ (Q : ℝ)
    have h2 : 2 * Real.log 2 = Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h2, Real.exp_log (by norm_num)]
    exact_mod_cast hQ
  have hge : 0 ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy suzukiApertureLogTwo :=
    le_trans (by norm_num) one_div_ten_pow_13_le_groundEnergy_apertureLogTwo
  have htot : R + (a + (R + a) + b) < 4 * R := by omega
  exact (groundEnergy_nonneg_iff_forall_weilSchur_nonneg (by omega) hexp).mp hge R a b hR
    (log_window_lt_two_mul_log_two hR htot) e

/-- For every cutoff `Q ≥ 4`, some two-prime window `(R, R + J]` with `1 ≤ R` and
`R + J < 4 * R` carries a step packet with Rayleigh quotient strictly below `10⁻⁹`. -/
theorem exists_stepPacket_two_prime_window_lt_one_div_ten_pow_9 {Q : ℕ} (hQ : 4 ≤ Q) :
    ∃ R J : ℕ, 1 ≤ R ∧ R + J < 4 * R ∧
      ∃ σ : ℕ → ℝ, packetForm Q (stepPacket R J σ) < (1 / 10 ^ 9 : ℝ) * ∑ j ∈ range J, σ j ^ 2 := by
  have hexp4 : Real.exp (2 * suzukiApertureLogTwo.1) ≤ (4 : ℕ) := by
    change Real.exp (2 * Real.log 2) ≤ (4 : ℝ)
    have h2 : 2 * Real.log 2 = Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h2, Real.exp_log (by norm_num)]
  have hexpQ : Real.exp (2 * suzukiApertureLogTwo.1) ≤ (Q : ℕ) :=
    hexp4.trans (by exact_mod_cast hQ)
  obtain ⟨R, J, hR, hlog, σ, hσ⟩ := exists_stepPacket_lt_of_groundEnergy_lt hexpQ
    groundEnergy_apertureLogTwo_lt_one_div_ten_pow_9
  exact ⟨R, J, hR, window_lt_of_log_lt hR hlog hexp4, σ, hσ⟩

/-! ### 2. The ratio-three window at every block size (`R ≤ J ≤ 2 R`, `Q ≥ 2`) -/

/-- **Every ratio-three neutral window is at least `10⁻¹³` on its charge-free packets**, at
every block size `R ≥ 1` and for every prime cutoff `Q ≥ 2`. -/
theorem neutralWindow_floor_ratio_three {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hJ : J ≤ 2 * R) (z : Fin J → ℝ) (hz : ∑ i, z i = 0) :
    (1 / 10 ^ 13 : ℝ) * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z) := by
  rw [neutralWindow_eq_two_of_le_two_mul hQ hJ,
    ← neutralWindow_eq_two_of_le_two_mul (Q := 3) (by norm_num) hJ]
  exact neutralWindow_floor_two_prime_window (by norm_num) hR (by omega) z hz

/-- **Every ratio-three neutral window (`J ≤ 2 R`, `Q ≥ 2`) has the uniform spectral gap `10⁻¹³`**
at every block size `R ≥ 1`. -/
theorem hasGap_neutralWindow_ratio_three {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hJ : J ≤ 2 * R) : HasGap (neutralWindow Q R J) (1 / 10 ^ 13) := by
  rw [neutralWindow_eq_two_of_le_two_mul hQ hJ,
    ← neutralWindow_eq_two_of_le_two_mul (Q := 3) (by norm_num) hJ]
  exact hasGap_neutralWindow_two_prime_window (by norm_num) hR (by omega)

/-- **Unconditional ratio-three theorem at every block size (`§2.4`).** Every neutral window
`neutralWindow Q R J` with `R ≤ J ≤ 2 R` (including `(R, 3 R]`) holds **one** bound state
(`hermNegIndex = 1`) at every block size `R ≥ 1` and for every prime cutoff `Q ≥ 2`. -/
theorem hermNegIndex_neutralWindow_ratio_three {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hRJ : R ≤ J) (hJ : J ≤ 2 * R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 :=
  hermNegIndex_neutralWindow_eq_one_of_hasGap hR hRJ (by norm_num)
    (hasGap_neutralWindow_ratio_three hQ hR hJ)

/-- **Ratio-three overlap step in Green form, with `10⁻¹³` reserve.** On the two ends of every
window `(R, 2(R + a) + b]` with `2(R + a) + b ≤ 3 R` (`Q ≥ 2`, `R ≥ 1`), the Green inequality
holds with reserve `10⁻¹³`. -/
theorem greenForm_ratio_three {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b ≤ 3 * R) (e : Fin a ⊕ Fin b → ℝ) :
    (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) +
        1 / 10 ^ 13 * (e ⬝ᵥ e) ≤
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) :=
  greenForm_add_excess_le_of_floor (by omega) (by norm_num)
    (neutralWindow_floor_ratio_three hQ hR (by omega)) e

/-- For every overlap window `(R, 2(R + a) + b]` with `2(R + a) + b ≤ 3 R` (`Q ≥ 2`, `R ≥ 1`),
the Schur complement of the dyadic middle is nonnegative at every level
`C ∈ [-10⁻¹³, bindingEnergy (R + a))`. -/
theorem overlapSchurLevel_nonneg_ratio_three {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b ≤ 3 * R) {C : ℝ} (hC : -(1 / 10 ^ 13) ≤ C)
    (hCμ : C < bindingEnergy (R + a)) (e : Fin a ⊕ Fin b → ℝ) :
    0 ≤ e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e) :=
  overlapSchurLevel_nonneg_of_floor hR (by norm_num) (by norm_num)
    (neutralWindow_floor_ratio_three hQ hR (by omega)) hC hCμ e

/-- The exact Schur excess of every overlap window `(R, 2(R + a) + b]` with
`2(R + a) + b ≤ 3 R` (`Q ≥ 2`, `R ≥ 1`) vanishes at every level
`C ∈ [-10⁻¹³, bindingEnergy (R + a))`. -/
theorem windowExcess_eq_zero_ratio_three {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b ≤ 3 * R) {C : ℝ} (hC : -(1 / 10 ^ 13) ≤ C)
    (hCμ : C < bindingEnergy (R + a)) : windowExcess Q R a b C = 0 :=
  windowExcess_eq_zero_of_floor hR (by norm_num) (by norm_num)
    (neutralWindow_floor_ratio_three hQ hR (by omega)) hC hCμ

/-- On every overlap window `(R, 2(R + a) + b]` with `2(R + a) + b ≤ 3 R` (`Q ≥ 2`, `R ≥ 1`),
the dyadic middle dressed by the attraction of both ends holds one bound state. -/
theorem hermNegIndex_dressedMiddle_ratio_three {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b ≤ 3 * R) :
    hermNegIndex ((dressedMiddle Q R a b).map (↑) :
      Matrix (Fin (R + a)) (Fin (R + a)) ℂ) = 1 := by
  rw [← hermNegIndex_neutralWindow_eq_dressedMiddle hR (by omega) (by omega)]
  exact hermNegIndex_neutralWindow_ratio_three hQ hR (by omega) (by omega)

/-- **Hodge index inequality of the dressed middle up to ratio three**: two nonnegative packets
of the dyadic middle without a common block, the first of negative dressed energy, satisfy the
reverse Cauchy–Schwarz inequality of the dressed form whenever `2(R + a) + b ≤ 3 R`
(`Q ≥ 2`, `R ≥ 1`). -/
theorem dressedMiddle_wells_bound_ratio_three {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hwin : 2 * (R + a) + b ≤ 3 * R) (x y : Fin (R + a) → ℝ)
    (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k) (hxy : ∀ k, x k * y k = 0)
    (hneg : bilin (dressedMiddle Q R a b) x x < 0) :
    bilin (dressedMiddle Q R a b) x x * bilin (dressedMiddle Q R a b) y y ≤
      bilin (dressedMiddle Q R a b) x y ^ 2 :=
  (hermNegIndex_neutralWindow_eq_one_iff_dressedMiddle_wells_bound hR (by omega) (by omega)).mp
    (hermNegIndex_neutralWindow_ratio_three hQ hR (by omega) (by omega)) x y hx hy hxy hneg

/-! ### 3. Vanishing of `schurStepExcess`, `levelAt`, and `globalTowerLevel` along the ladder -/

/-- Every ratio-squaring step with `ρ² / 2 < 4` has zero Schur excess down to level `-10⁻¹³`
for every prime cutoff `Q ≥ 3`. -/
theorem schurStepExcess_eq_zero_of_sq_div_two_lt_four {Q : ℕ} (hQ : 3 ≤ Q)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ^ 2 / 2 < 4)
    {C : ℝ} (hC : -(1 / 10 ^ 13) ≤ C) (hC2 : C < -neutralBlock 1 1 1) :
    schurStepExcess Q ρ C = 0 := by
  have hQ' : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : Real.log (ρ ^ 2 / 2) < 2 * suzukiApertureLogTwo.1 := by
    change Real.log (ρ ^ 2 / 2) < 2 * Real.log 2
    have hpos : 0 < ρ ^ 2 / 2 := by positivity
    have h1 := Real.log_lt_log hpos hρ
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  exact schurStepExcess_eq_zero_of_le_groundEnergy (A := suzukiApertureLogTwo)
    (by norm_num) (by norm_num) one_div_ten_pow_13_le_groundEnergy_apertureLogTwo
    hlog (by linarith) hC hC2

/-- Every ratio-squaring step with `ρ² / 2 ≤ 3` has zero Schur excess down to level `-10⁻¹³`
for every prime cutoff `Q ≥ 2`. -/
theorem schurStepExcess_eq_zero_of_sq_div_two_le_three {Q : ℕ} (hQ : 2 ≤ Q)
    {ρ : ℝ} (hρ : ρ ^ 2 / 2 ≤ 3)
    {C : ℝ} (hC : -(1 / 10 ^ 13) ≤ C) (hC2 : C < -neutralBlock 1 1 1) :
    schurStepExcess Q ρ C = 0 := by
  refine le_antisymm (csSup_le ⟨0, Or.inl rfl⟩ ?_) (schurStepExcess_nonneg Q ρ C)
  rintro y (rfl | ⟨R, a, b, hstep, rfl⟩)
  · exact le_rfl
  · have hR := hstep.1
    have hwhole := ratioStep_whole_le hstep
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have h3R : ((2 * (R + a) + b : ℕ) : ℝ) ≤ ((3 * R : ℕ) : ℝ) := by
      push_cast
      exact hwhole.trans (mul_le_mul_of_nonneg_right hρ hR0)
    have hnat : 2 * (R + a) + b ≤ 3 * R := Nat.cast_le.mp h3R
    exact (windowExcess_eq_zero_ratio_three hQ hR hnat hC
      (lt_of_lt_of_le hC2 (groundPair_spec (by omega)).2.2)).le

/-- The excess of the second step (`10609 / 5000 = 2.1218 ↦ 2.251... ≤ 3`) vanishes at every
level `C ∈ [-10⁻¹³, -neutralBlock 1 1 1)` for every `Q ≥ 2`. -/
theorem schurStepExcess_secondStep {Q : ℕ} (hQ : 2 ≤ Q) {C : ℝ} (hC : -(1 / 10 ^ 13) ≤ C)
    (hC2 : C < -neutralBlock 1 1 1) : schurStepExcess Q (10609 / 5000) C = 0 :=
  schurStepExcess_eq_zero_of_sq_div_two_le_three hQ (by norm_num) hC hC2

/-- The excess of the third step (`112550881 / 50000000 ↦ 2.5335... ≤ 3`) vanishes at every
level `C ∈ [-10⁻¹³, -neutralBlock 1 1 1)` for every `Q ≥ 2`. -/
theorem schurStepExcess_thirdStep {Q : ℕ} (hQ : 2 ≤ Q) {C : ℝ} (hC : -(1 / 10 ^ 13) ≤ C)
    (hC2 : C < -neutralBlock 1 1 1) : schurStepExcess Q (112550881 / 50000000) C = 0 :=
  schurStepExcess_eq_zero_of_sq_div_two_le_three hQ (by norm_num) hC hC2

/-- The excess of the fourth step (`(103^8 / (100^8 / 2)) ↦ 3.20989... < 4`) vanishes at every
level `C ∈ [-10⁻¹³, -neutralBlock 1 1 1)` for every `Q ≥ 3`. -/
theorem schurStepExcess_fourthStep {Q : ℕ} (hQ : 3 ≤ Q) {C : ℝ} (hC : -(1 / 10 ^ 13) ≤ C)
    (hC2 : C < -neutralBlock 1 1 1) :
    schurStepExcess Q ((103 : ℝ) ^ 8 / (100 ^ 8 / 2)) C = 0 :=
  schurStepExcess_eq_zero_of_sq_div_two_lt_four hQ (by norm_num) (by norm_num) hC hC2

/-- The cumulative level after two ratio-squaring steps is zero for every `Q ≥ 2`. -/
theorem levelAt_two_eq_zero {Q : ℕ} (hQ : 2 ≤ Q) : levelAt Q 2 = 0 := by
  rw [levelAt_two hQ]
  exact schurStepExcess_secondStep hQ (by norm_num)
    (by rw [neutralBlock_one_one, neg_neg]; linarith [dyadicDepth_mem.1])

/-- The cumulative level after three ratio-squaring steps (`iteratedRatio 3 ≈ 2.5335`) is zero
for every `Q ≥ 2`. -/
theorem levelAt_three_eq_zero {Q : ℕ} (hQ : 2 ≤ Q) : levelAt Q 3 = 0 := by
  show levelAt Q 2 + schurStepExcess Q (iteratedRatio 2) (levelAt Q 2) = 0
  rw [levelAt_two_eq_zero hQ, zero_add, iteratedRatio_exact_milestones.2.2.1]
  exact schurStepExcess_thirdStep hQ (by norm_num)
    (by rw [neutralBlock_one_one, neg_neg]; linarith [dyadicDepth_mem.1])

/-- For every `Q ≥ 2` and `k ≤ 3`, `levelAt Q k = 0`. -/
theorem levelAt_eq_zero_of_le_three {Q k : ℕ} (hQ : 2 ≤ Q) (hk : k ≤ 3) : levelAt Q k = 0 :=
  le_antisymm ((levelAt_mono Q hk).trans (levelAt_three_eq_zero hQ).le) (levelAt_nonneg Q k)

/-- After three lossless steps, the four-step level `levelAt Q 4` (`Q ≥ 2`) reduces to the
single fourth-step excess `schurStepExcess Q (103^8 / (100^8 / 2)) 0`. -/
theorem levelAt_four_eq_fourthStep {Q : ℕ} (hQ : 2 ≤ Q) :
    levelAt Q 4 = schurStepExcess Q ((103 : ℝ) ^ 8 / (100 ^ 8 / 2)) 0 := by
  show levelAt Q 3 + schurStepExcess Q (iteratedRatio 3) (levelAt Q 3) = _
  rw [levelAt_three_eq_zero hQ, zero_add, iteratedRatio_exact_milestones.2.2.2.1]

/-- For every cutoff `Q ≥ 3`, the four-step cumulative level `levelAt Q 4` vanishes. -/
theorem levelAt_four_eq_zero {Q : ℕ} (hQ : 3 ≤ Q) : levelAt Q 4 = 0 := by
  rw [levelAt_four_eq_fourthStep (by omega)]
  exact schurStepExcess_fourthStep hQ (by norm_num)
    (by rw [neutralBlock_one_one, neg_neg]; linarith [dyadicDepth_mem.1])

/-- For every `Q ≥ 3` and `k ≤ 4`, `levelAt Q k = 0`. -/
theorem levelAt_eq_zero_of_le_four {Q k : ℕ} (hQ : 3 ≤ Q) (hk : k ≤ 4) : levelAt Q k = 0 :=
  le_antisymm ((levelAt_mono Q hk).trans (levelAt_four_eq_zero hQ).le) (levelAt_nonneg Q k)

/-- At the fourth ratio-squaring milestone (`iteratedRatio 4 > 3.209`), every neutral window
`neutralWindow Q R J` with `R ≤ J` and `(R + J) ≤ iteratedRatio 4 * R` (`Q ≥ 3`) holds one
bound state at every block size `R ≥ 1`. -/
theorem hermNegIndex_fourthStep_eq_one {Q R J : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R)
    (hRJ : R ≤ J) (hJ : ((R + J : ℕ) : ℝ) ≤ iteratedRatio 4 * R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 := by
  have hk3 : levelAt Q 3 < -neutralBlock 1 1 1 := by
    rw [levelAt_three_eq_zero (by omega), neutralBlock_one_one, neg_neg]
    linarith [dyadicDepth_mem.1]
  have hle := hermNegIndex_le_one_of_levelAt (by omega : 2 ≤ Q) 3 hk3 hR hRJ hJ
  rw [levelAt_four_eq_zero hQ, Matrix.diagonal_zero, add_zero] at hle
  exact le_antisymm hle (one_le_hermNegIndex_neutralWindow Q hR hRJ)

/-- For every `k ≤ 3`, the global quantization level `globalTowerLevel k` vanishes
unconditionally. -/
theorem globalTowerLevel_eq_zero_of_le_three {k : ℕ} (hk : k ≤ 3) : globalTowerLevel k = 0 := by
  unfold globalTowerLevel
  rcases le_or_gt k 2 with hk2 | hk3
  · exact levelAt_eq_zero_of_le_three (two_le_towerCutoff k) (by omega)
  · have hk_eq : k = 3 := by omega
    subst hk_eq
    have hcut : 3 ≤ towerCutoff 3 := by
      unfold towerCutoff iteratedNum iteratedDen
      norm_num
    exact levelAt_four_eq_zero hcut

theorem globalTowerLevel_zero : globalTowerLevel 0 = 0 :=
  globalTowerLevel_eq_zero_of_le_three (by omega)

theorem globalTowerLevel_one : globalTowerLevel 1 = 0 :=
  globalTowerLevel_eq_zero_of_le_three (by omega)

theorem globalTowerLevel_two : globalTowerLevel 2 = 0 :=
  globalTowerLevel_eq_zero_of_le_three (by omega)

theorem globalTowerLevel_three : globalTowerLevel 3 = 0 :=
  globalTowerLevel_eq_zero_of_le_three le_rfl

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
