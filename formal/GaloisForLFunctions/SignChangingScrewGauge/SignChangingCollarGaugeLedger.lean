import GaloisForLFunctions.ArithmeticCriticalityTheory.GroundStateRepresentationAlgebra
import GaloisForLFunctions.ArithmeticCriticalityTheory.FiniteJumpFormAllegrettoPiepenbrink
import GaloisForLFunctions.RHTower.Suzuki.SuzukiExplicitScrewRegularKernel
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sign-Changing Collar Gauges: Unconditional Energy Ledger, Prime-Shift Cancellation, and Collar Conservation

This module establishes the first leg of Mechanism 3 of Project Argon
(`docs/reports/review-2110/argon.md`, §1.4):

1. **Unconditional Sign-Changing Collar Gauge Decay & Commutator Summation by Parts**
   (`hasCompactSupport_of_support_le`, `exists_abs_le_exp_of_support_le`,
   `integral_mul_mul_shiftCommutator_eq_gaugeJumpProfile`):
   Every continuous collar gauge `P` vanishing for `R ≤ |y|` has compact support and exponential
   decay `|P y| ≤ C e^{−k|y|}` at every rate `k > 0`, and satisfies the commutator summation-by-parts
   identity `∫ x, F x * P x * shiftCommutator P F t x = gaugeJumpProfile P F t` without any
   nonnegativity (`0 ≤ P`) or upper-bound (`P ≤ 1`) hypothesis on the outer collar `r < |y| < R`.

2. **Sign-Changing Prime-Shift Cancellation vs. Nonnegative Subsolution Obstruction**
   (`profilePrimeSum_nonneg_of_nonneg`, `profilePrimeSum_zero_eq_two_term_of_collar`,
   `profilePrimeSum_zero_neg_and_weilOperator_gain_of_neg_collar`):
   Whereas every nonnegative gauge `P ≥ 0` satisfies `0 ≤ profilePrimeSum P x` (driving
   `-poleFreeWeilOperator P x` negative at prime translates), an even sign-changing collar gauge
   with `P (Real.log 2) < 0` and `P (Real.log n) = 0` (`n ≥ 3`) makes
   `profilePrimeSum P 0 = 2 * vonMangoldtAtom 2 * P (Real.log 2) < 0` and strictly boosts
   `-poleFreeWeilOperator P 0 c_arch` above its prime-free baseline.

3. **Collar Conservation Law on `supp F`**
   (`gaugeJumpProfile_sub_shiftPotential_eq_neg_two_mul_autoCorr`,
   `signedCollar_netShiftEnergy_invariance`):
   For any continuous gauge `P` (sign-changing or not) with `P = 1` on `supp F` and any shift `L`,
   `gaugeJumpProfile P F L - ∫ x, F x ^ 2 * P x * (P (x + L) + P (x - L)) = -2 * autoCorr F L`.
   Consequently, any collar modification of `P` outside `supp F` transfers weight 1-for-1 between
   collar-exit jumps (`x ∈ supp F`, `x ± L ∉ supp F`) and the shift potential.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.SignChangingScrewGauge

/-! ### Core collar-gauge and Weil-operator definitions -/

/-- The archimedean Lévy jump density `ω(t) = e^{−t/2} / (1 − e^{−2t})`. -/
def archLevyDensity (t : ℝ) : ℝ := Real.exp (-t / 2) / (1 - Real.exp (-2 * t))

/-- The prime-power von Mangoldt weight `Λ(n) / √n` for `n ≥ 2` (`0` for `n < 2`). -/
def vonMangoldtAtom (n : ℕ) : ℝ :=
  if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0

theorem vonMangoldtAtom_nonneg (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs with h
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-- The signed shift jump density `P(x) P(x + t) (F(x) − F(x + t))²`. -/
def signedShiftJump (P F : ℝ → ℝ) (t x : ℝ) : ℝ := P x * P (x + t) * (F x - F (x + t)) ^ 2

/-- The shift commutator `P(x + t)(F(x) − F(x + t)) + P(x − t)(F(x) − F(x − t))`. -/
def shiftCommutator (P F : ℝ → ℝ) (t x : ℝ) : ℝ :=
  P (x + t) * (F x - F (x + t)) + P (x - t) * (F x - F (x - t))

/-- The gauge jump profile `∫_ℝ P(x) P(x + t) (F(x) − F(x + t))² dx` at shift `t`. -/
def gaugeJumpProfile (P F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, signedShiftJump P F t x

/-- The total signed jump energy `J_P(F)` combining archimedean and prime-power shifts. -/
def signedJumpEnergy (P F : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) +
    ∑' n : ℕ, vonMangoldtAtom n * gaugeJumpProfile P F (Real.log n)

/-- The archimedean generator term `∫_{u > 0} ω(u) (P(x + u) + P(x − u) − 2 P(x)) du`. -/
def profileArchTerm (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), archLevyDensity u * (P (x + u) + P (x - u) - 2 * P x)

/-- The prime-power shift sum `∑_{n} (Λ(n)/√n) (P(x + log n) + P(x − log n))`. -/
def profilePrimeSum (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * (P (x + Real.log n) + P (x - Real.log n))

/-- The pole-free Weil operator `(1/2) profileArchTerm P x + (1/2) profilePrimeSum P x + c_arch`. -/
def poleFreeWeilOperator (P : ℝ → ℝ) (x : ℝ) (c_arch : ℝ) : ℝ :=
  (1 / 2) * profileArchTerm P x + (1 / 2) * profilePrimeSum P x + c_arch

/-- The gauge remainder `∫ F(x)² P(x) (−poleFreeWeilOperator P x c_arch + profilePrimeSum P x) dx`. -/
def gaugeRemainder (P F : ℝ → ℝ) (c_arch : ℝ) : ℝ :=
  ∫ x, F x ^ 2 * P x * (-poleFreeWeilOperator P x c_arch + profilePrimeSum P x)

/-- The autocorrelation `∫_ℝ F(x) F(x + L) dx` at shift `L`. -/
def autoCorr (F : ℝ → ℝ) (L : ℝ) : ℝ := ∫ x, F x * F (x + L)

/-- The odd pole moment `∫_ℝ F(x) sinh(x / 2) dx`. -/
def oddPoleMoment (F : ℝ → ℝ) : ℝ := ∫ x, F x * Real.sinh (x / 2)

/-- The even pole moment `∫_ℝ F(x) cosh(x / 2) dx`. -/
def evenPoleMoment (F : ℝ → ℝ) : ℝ := ∫ x, F x * Real.cosh (x / 2)

/-- The odd pole charge `2 (∫_ℝ F(x) sinh(x / 2) dx)²`. -/
def poleCharge (F : ℝ → ℝ) : ℝ := 2 * oddPoleMoment F ^ 2

/-! ### Compact support and exponential decay bounds for arbitrary sign-changing collar gauges -/

/-- Any function vanishing for `R ≤ |y|` has compact support contained in `[−|R|, |R|]`. -/
theorem hasCompactSupport_of_support_le {P : ℝ → ℝ} {R : ℝ} (hPR : ∀ y, R ≤ |y| → P y = 0) :
    HasCompactSupport P :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -|R|) (b := |R|)) fun y hy => by
    rw [Function.mem_support] at hy
    exact abs_le.mp (not_lt.mp fun h => hy (hPR y ((le_abs_self R).trans h.le)))

/-- Any continuous function `P` vanishing for `R ≤ |y|` satisfies an exponential decay bound
`|P y| ≤ C e^{−k|y|}` at every rate `k > 0`, without any nonnegativity or `P ≤ 1` assumption. -/
theorem exists_abs_le_exp_of_support_le {P : ℝ → ℝ} {R : ℝ} (hP : Continuous P)
    (hPR : ∀ y, R ≤ |y| → P y = 0) {k : ℝ} (hk : 0 < k) :
    ∃ C ≥ 0, ∀ y, |P y| ≤ C * Real.exp (-(k * |y|)) := by
  have hPcs : HasCompactSupport P := hasCompactSupport_of_support_le hPR
  obtain ⟨B, hB⟩ := hPcs.exists_bound_of_continuous hP
  set B₀ : ℝ := max B 0
  have hB₀ : 0 ≤ B₀ := le_max_right B 0
  have hPB₀ : ∀ y, |P y| ≤ B₀ := fun y => by
    have hy := hB y
    rw [Real.norm_eq_abs] at hy
    exact hy.trans (le_max_left B 0)
  refine ⟨B₀ * Real.exp (k * |R|), mul_nonneg hB₀ (Real.exp_pos _).le, fun y => ?_⟩
  by_cases hy : |y| < R
  · have hyR : |y| ≤ |R| := hy.le.trans (le_abs_self R)
    have hexp : 1 ≤ Real.exp (k * |R|) * Real.exp (-(k * |y|)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc |P y| ≤ B₀ * 1 := by linarith [hPB₀ y]
      _ ≤ B₀ * (Real.exp (k * |R|) * Real.exp (-(k * |y|))) :=
          mul_le_mul_of_nonneg_left hexp hB₀
      _ = B₀ * Real.exp (k * |R|) * Real.exp (-(k * |y|)) := by ring
  · rw [hPR y (not_lt.mp hy), abs_zero]
    positivity

/-! ### Unconditional summation by parts of the shift commutator for sign-changing gauges -/

/-- **Unconditional Commutator Summation by Parts.**
For any continuous gauge `P` (with no `0 ≤ P` or `P ≤ 1` restriction) and any continuous
compactly supported `F`, `∫ x, F x * P x * shiftCommutator P F t x = gaugeJumpProfile P F t`. -/
theorem integral_mul_mul_shiftCommutator_eq_gaugeJumpProfile {P F : ℝ → ℝ}
    (hP : Continuous P) (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    (∫ x, F x * P x * shiftCommutator P F t x) = gaugeJumpProfile P F t := by
  set f : ℝ → ℝ := fun x => F x * P x * P (x + t) * (F x - F (x + t)) with hf_def
  set g : ℝ → ℝ := fun y => F y * P y * P (y - t) * (F y - F (y - t)) with hg_def
  have hf : Integrable f := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hF.mul hP).mul (hP.comp (continuous_id.add continuous_const))).mul
        (hF.sub (hF.comp (continuous_id.add continuous_const)))
    · exact hFc.mul_right.mul_right.mul_right
  have hg : Integrable g := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hF.mul hP).mul (hP.comp (continuous_id.sub continuous_const))).mul
        (hF.sub (hF.comp (continuous_id.sub continuous_const)))
    · exact hFc.mul_right.mul_right.mul_right
  have h1 : (∫ x, F x * P x * shiftCommutator P F t x) = ∫ x, (f x + g x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [shiftCommutator, hf_def, hg_def]
    ring
  have h2 : gaugeJumpProfile P F t = ∫ x, (f x + g (x + t)) := by
    unfold gaugeJumpProfile
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [signedShiftJump, hf_def, hg_def, add_sub_cancel_right]
    ring
  rw [h1, h2, integral_add hf hg, integral_add hf (hg.comp_add_right t),
    integral_add_right_eq_self g t]

/-! ### Prime-shift subsolution escape via sign-changing collars -/

/-- For any nonnegative gauge `P ≥ 0`, `profilePrimeSum P x ≥ 0` everywhere, so no prime-shift
cancellation can occur in a nonnegative gauge. -/
theorem profilePrimeSum_nonneg_of_nonneg {P : ℝ → ℝ} (hP0 : ∀ y, 0 ≤ P y) (x : ℝ) :
    0 ≤ profilePrimeSum P x :=
  tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n)
    (add_nonneg (hP0 (x + Real.log n)) (hP0 (x - Real.log n)))

/-- On a collar window where all prime-power shifts `n ≥ 3` lie outside the support of `P`
(e.g. `R ≤ log 3`), the prime sum at the origin `profilePrimeSum P 0` reduces exactly to the
`n = 2` collar value `vonMangoldtAtom 2 * (P (log 2) + P (−log 2))`. -/
theorem profilePrimeSum_zero_eq_two_term_of_collar {P : ℝ → ℝ}
    (hP3 : ∀ n : ℕ, 3 ≤ n → P (Real.log n) = 0 ∧ P (-Real.log n) = 0) :
    profilePrimeSum P 0 = vonMangoldtAtom 2 * (P (Real.log 2) + P (-Real.log 2)) := by
  unfold profilePrimeSum
  rw [tsum_eq_single 2]
  · simp
  · intro n hn
    by_cases h2 : n < 2
    · have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl <;> simp [vonMangoldtAtom]
    · have h3 : 3 ≤ n := by omega
      obtain ⟨hp, hm⟩ := hP3 n h3
      simp [hp, hm]

/-- For an even gauge `P` vanishing at `log n` for `n ≥ 3`,
`profilePrimeSum P 0 = 2 * vonMangoldtAtom 2 * P (log 2)`.
In particular, choosing a negative collar value `P (log 2) < 0` makes `profilePrimeSum P 0 < 0`
and strictly increases `-poleFreeWeilOperator P 0 c_arch` above its prime-free baseline
`-(1/2) * profileArchTerm P 0 - c_arch`. -/
theorem profilePrimeSum_zero_neg_and_weilOperator_gain_of_neg_collar {P : ℝ → ℝ} (c_arch : ℝ)
    (heven : ∀ y, P (-y) = P y)
    (hP3 : ∀ n : ℕ, 3 ≤ n → P (Real.log n) = 0)
    (hneg : P (Real.log 2) < 0) :
    profilePrimeSum P 0 = 2 * vonMangoldtAtom 2 * P (Real.log 2) ∧
      profilePrimeSum P 0 < 0 ∧
      -(1 / 2) * profileArchTerm P 0 - c_arch < -poleFreeWeilOperator P 0 c_arch := by
  have hsum : profilePrimeSum P 0 = 2 * vonMangoldtAtom 2 * P (Real.log 2) := by
    rw [profilePrimeSum_zero_eq_two_term_of_collar fun n hn => ⟨hP3 n hn, by rw [heven, hP3 n hn]⟩,
      heven]
    ring
  have hatom2 : 0 < vonMangoldtAtom 2 := by
    unfold vonMangoldtAtom
    rw [if_pos (by decide)]
    have hvm : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    rw [hvm]
    exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  have hlt : profilePrimeSum P 0 < 0 := by
    rw [hsum]
    nlinarith
  refine ⟨hsum, hlt, ?_⟩
  unfold poleFreeWeilOperator
  linarith

/-! ### Collar conservation law at every shift -/

/-- **Collar Conservation Law at a Single Shift.**
For any continuous gauge `P` (sign-changing or not) with `P = 1` on `supp F`, the jump profile
minus the shift potential at lag `L` equals `-2 * autoCorr F L`, independent of the collar values
of `P` outside `supp F`. -/
theorem gaugeJumpProfile_sub_shiftPotential_eq_neg_two_mul_autoCorr {P F : ℝ → ℝ}
    (hP : Continuous P) (hF : Continuous F) (hFc : HasCompactSupport F)
    (hFP : ∀ x, F x ≠ 0 → P x = 1) (L : ℝ) :
    gaugeJumpProfile P F L - ∫ x, F x ^ 2 * P x * (P (x + L) + P (x - L)) =
      -2 * autoCorr F L := by
  have hcross : ∀ x, P x * P (x + L) * (F x * F (x + L)) = F x * F (x + L) := fun x => by
    by_cases hx : F x = 0
    · simp [hx]
    · by_cases hxL : F (x + L) = 0
      · simp [hxL]
      · rw [hFP x hx, hFP (x + L) hxL, one_mul, one_mul]
  set u₁ : ℝ → ℝ := fun x => F x ^ 2 * P x * P (x + L) with hu₁
  set u₂ : ℝ → ℝ := fun y => F y ^ 2 * P y * P (y - L) with hu₂
  set u₃ : ℝ → ℝ := fun x => F x * F (x + L) with hu₃
  have hpt : ∀ x, signedShiftJump P F L x = u₁ x + u₂ (x + L) - 2 * u₃ x := fun x => by
    simp only [signedShiftJump, hu₁, hu₂, hu₃, add_sub_cancel_right]
    linear_combination -2 * hcross x
  have hFc2 : HasCompactSupport (fun x => F x ^ 2) :=
    hFc.comp_left (g := fun y : ℝ => y ^ 2) (by ring)
  have hI1 : Integrable u₁ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hFc2.mul_right.mul_right
    exact ((hF.pow 2).mul hP).mul (hP.comp (continuous_id.add continuous_const))
  have hI2 : Integrable u₂ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hFc2.mul_right.mul_right
    exact ((hF.pow 2).mul hP).mul (hP.comp (continuous_id.sub continuous_const))
  have hI2L : Integrable (fun x => u₂ (x + L)) := hI2.comp_add_right L
  have hI12 : Integrable (fun x => u₁ x + u₂ (x + L)) := hI1.add hI2L
  have hI3 : Integrable u₃ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hFc.mul_right
    exact hF.mul (hF.comp (continuous_id.add continuous_const))
  have hJ : gaugeJumpProfile P F L = (∫ x, u₁ x) + (∫ y, u₂ y) - 2 * autoCorr F L := by
    unfold gaugeJumpProfile autoCorr
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_sub hI12 (hI3.const_mul 2),
      integral_add hI1 hI2L,
      integral_add_right_eq_self u₂ L,
      integral_const_mul]
  have hpot : (∫ x, F x ^ 2 * P x * (P (x + L) + P (x - L))) =
      (∫ x, u₁ x) + (∫ x, u₂ x) := by
    rw [← integral_add hI1 hI2]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hu₁, hu₂]; ring)
  linarith

/-- **Collar Gauge Invariance of Net Shift Energy.**
For any two continuous gauges `P₁, P₂` (regardless of sign changes on the collar outside `supp F`)
that both equal `1` on `supp F`, the net shift energy `gaugeJumpProfile Pᵢ F L - ∫ F² Pᵢ (Pᵢ(·+L) + Pᵢ(·-L))`
is identical for `P₁` and `P₂` at every lag `L`. -/
theorem signedCollar_netShiftEnergy_invariance {P₁ P₂ F : ℝ → ℝ}
    (hP₁ : Continuous P₁) (hP₂ : Continuous P₂)
    (hF : Continuous F) (hFc : HasCompactSupport F)
    (hFP₁ : ∀ x, F x ≠ 0 → P₁ x = 1) (hFP₂ : ∀ x, F x ≠ 0 → P₂ x = 1) (L : ℝ) :
    gaugeJumpProfile P₁ F L - ∫ x, F x ^ 2 * P₁ x * (P₁ (x + L) + P₁ (x - L)) =
      gaugeJumpProfile P₂ F L - ∫ x, F x ^ 2 * P₂ x * (P₂ (x + L) + P₂ (x - L)) := by
  rw [gaugeJumpProfile_sub_shiftPotential_eq_neg_two_mul_autoCorr hP₁ hF hFc hFP₁ L,
    gaugeJumpProfile_sub_shiftPotential_eq_neg_two_mul_autoCorr hP₂ hF hFc hFP₂ L]

end GaloisForLFunctions.SignChangingScrewGauge

end
