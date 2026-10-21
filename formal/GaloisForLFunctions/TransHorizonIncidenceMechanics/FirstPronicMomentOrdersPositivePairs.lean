import GaloisForLFunctions.TransHorizonIncidenceMechanics.FirstPronicMomentIsTheVonMangoldtPairing

/-!
# The first pronic moment orders every pair with a positive member

A nonnegative weight has nonnegative Ramanujan coefficients, so a nonnegative weight `c₊` with the
amplitudes of `c` has `W_{c₊} = |W_c|`. By the first-moment law `M(c) = −Σ_e Λ(e) W_c(e)`,

`M(c) − M(c₊) = Σ_e Λ(e) (|W_c(e)| − W_c(e)) ≥ 0`,

and the gap is positive exactly when `W_c` is negative at some prime power. So **the first pronic
moment orders every amplitude pair with a positive member**, and a pair that it cannot separate
must have `W_c ≥ 0` on all prime powers: the parity of such a pair lives entirely on composite
moduli. For the Liouville pair the gap is `2 m_λ Σ_{Ω(e) odd} Λ(e) e^{-1-ε} > 0`.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The first pronic moment `M(c) = Σ_n A_c(n)/(n(n+1))`, centred at the mean `Σ c(d)/d`. -/
def firstPronicMoment (c : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, weightCenteredPrefix c (∑' d : ℕ, c d / d) n / ((n : ℝ) * ((n : ℝ) + 1))

/-- Ramanujan coefficients of the damped class: `|W_c(e)| ≤ K Z e^{-1-ε}`, `Z = Σ k^{-1-ε}`. -/
theorem abs_weightRamanujanCoeff_le_of_dampedClass {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (e : ℕ) :
    |weightRamanujanCoeff c e| ≤
      K * (∑' k : ℕ, dampedSignWeight unitSign ε k / k) * ((e : ℝ) ^ (-ε) / e) := by
  have hK := nonneg_of_dampedClass hc
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [weightRamanujanCoeff]
  · have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hZ := summable_unit_weight hε
    have hu : ∀ n : ℕ, dampedSignWeight unitSign ε n / n = (n : ℝ) ^ (-ε) / n := fun n => by
      rw [dampedSignWeight, unitSign, one_mul]
    have hterm : ∀ k : ℕ, ‖c (e * k) / ((e * k : ℕ) : ℝ)‖ ≤
        K * ((e : ℝ) ^ (-ε) / e) * (dampedSignWeight unitSign ε k / k) := fun k => by
      have hprod := dampedSignWeight_mul_div (s := unitSign) (ε := ε)
        (fun _ _ => by simp [unitSign]) e k
      rw [hu, hu, hu] at hprod
      rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, hu, mul_assoc, ← hprod]
      calc |c (e * k)| / ((e * k : ℕ) : ℝ) ≤ K * ((e * k : ℕ) : ℝ) ^ (-ε) / ((e * k : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right (hc _) (Nat.cast_nonneg _)
        _ = K * (((e * k : ℕ) : ℝ) ^ (-ε) / ((e * k : ℕ) : ℝ)) := by ring
    have hbound := tsum_of_norm_bounded ((hZ.mul_left (K * ((e : ℝ) ^ (-ε) / e))).hasSum) hterm
    rw [Real.norm_eq_abs, tsum_mul_left] at hbound
    unfold weightRamanujanCoeff
    linarith

theorem summable_vonMangoldt_mul_weightRamanujanCoeff {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) :
    Summable (fun e : ℕ => Λ e * weightRamanujanCoeff c e) := by
  have hK := nonneg_of_dampedClass hc
  set Z := ∑' k : ℕ, dampedSignWeight unitSign ε k / k
  have hZ := (unitDampedMass_pos hε).le
  have hlog1 := summable_abs_mul_log_div_of_dampedClass hε
    (show DampedClass 1 ε (dampedSignWeight unitSign ε) from fun d => by
      rw [dampedSignWeight, unitSign, one_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)])
  refine (hlog1.mul_left (K * Z)).of_norm_bounded fun e => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    dampedSignWeight, unitSign, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _)]
  have hW := abs_weightRamanujanCoeff_le_of_dampedClass hε hc e
  have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := e)
  have hp : 0 ≤ K * Z * ((e : ℝ) ^ (-ε) / e) := by positivity
  calc Λ e * |weightRamanujanCoeff c e| ≤ Real.log e * (K * Z * ((e : ℝ) ^ (-ε) / e)) :=
        mul_le_mul hΛ hW (abs_nonneg _) (Real.log_natCast_nonneg e)
    _ = K * Z * ((e : ℝ) ^ (-ε) * Real.log e / e) := by ring

/-- **The first pronic moment orders every pair with a positive member.** If `c₊ ≥ 0` has the
Ramanujan amplitudes of `c`, both in damped classes, then
`M(c) − M(c₊) = Σ_e Λ(e)(|W_c(e)| − W_c(e)) ≥ 0`, with strict inequality iff `W_c(e) < 0` at a
prime power `e`. -/
theorem firstPronicMoment_sub_of_positive_twin {K Kp ε : ℝ} (hε : 0 < ε) {c cp : ℕ → ℝ}
    (hc : DampedClass K ε c) (hcp : DampedClass Kp ε cp) (hpos : ∀ d, 0 ≤ cp d)
    (hamp : ∀ e, |weightRamanujanCoeff cp e| = |weightRamanujanCoeff c e|) :
    firstPronicMoment c - firstPronicMoment cp =
        ∑' e : ℕ, Λ e * (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e) ∧
      (firstPronicMoment cp < firstPronicMoment c ↔
        ∃ e : ℕ, Λ e ≠ 0 ∧ weightRamanujanCoeff c e < 0) := by
  have hWp : ∀ e, weightRamanujanCoeff cp e = |weightRamanujanCoeff c e| := fun e => by
    rw [← hamp e, abs_of_nonneg (weightRamanujanCoeff_nonneg hpos e)]
  have hs := summable_vonMangoldt_mul_weightRamanujanCoeff hε hc
  have hsp := summable_vonMangoldt_mul_weightRamanujanCoeff hε hcp
  have hgap : firstPronicMoment c - firstPronicMoment cp =
      ∑' e : ℕ, Λ e * (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e) := by
    unfold firstPronicMoment
    rw [(hasSum_firstPronicMoment hε hc).tsum_eq, (hasSum_firstPronicMoment hε hcp).tsum_eq,
      neg_sub_neg, ← hsp.tsum_sub hs]
    exact tsum_congr fun e => by rw [hWp]; ring
  refine ⟨hgap, ?_⟩
  have hnn : ∀ e : ℕ, 0 ≤ Λ e * (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e) :=
    fun e => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr (le_abs_self _))
  have hsumgap : Summable (fun e : ℕ =>
      Λ e * (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e)) :=
    (hsp.sub hs).congr fun e => by rw [hWp]; ring
  rw [← sub_pos, hgap]
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have hzero : ∀ e : ℕ, Λ e * (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e) = 0 :=
      fun e => by
        by_cases hΛ : Λ e = 0
        · rw [hΛ, zero_mul]
        · rw [abs_of_nonneg (hall e hΛ), sub_self, mul_zero]
    rw [tsum_congr hzero, tsum_zero] at h
    exact lt_irrefl _ h
  · rintro ⟨e, hΛ, hneg⟩
    refine hsumgap.tsum_pos hnn e ?_
    have hΛpos : 0 < Λ e := lt_of_le_of_ne ArithmeticFunction.vonMangoldt_nonneg (Ne.symm hΛ)
    rw [abs_of_neg hneg]
    nlinarith

/-- **The Liouville pair is ordered strictly** by the first pronic moment, at every `ε > 0`. -/
theorem firstPronicMoment_liouvilleTwin_lt {ε : ℝ} (hε : 0 < ε) :
    firstPronicMoment (liouvilleTwin ε) <
      firstPronicMoment (dampedSignWeight RHTower.liouvilleR ε) := by
  have hclassL : DampedClass 1 ε (dampedSignWeight RHTower.liouvilleR ε) := fun d => by
    rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _), one_mul]
    rcases eq_or_ne d 0 with rfl | hd
    · simp [RHTower.liouvilleR, Real.zero_rpow (show -ε ≠ 0 by linarith)]
    · rw [abs_liouvilleR hd, one_mul]
  have hκ : 0 ≤ |∑' k : ℕ, dampedSignWeight RHTower.liouvilleR ε k / k| /
      ∑' k : ℕ, dampedSignWeight unitSign ε k / k :=
    div_nonneg (abs_nonneg _) (unitDampedMass_pos hε).le
  have hclassP : DampedClass (|∑' k : ℕ, dampedSignWeight RHTower.liouvilleR ε k / k| /
      ∑' k : ℕ, dampedSignWeight unitSign ε k / k) ε (liouvilleTwin ε) := fun d => by
    rw [abs_of_nonneg (liouvilleTwin_nonneg hε d), liouvilleTwin, dampedSignWeight, unitSign,
      one_mul]
  refine ((firstPronicMoment_sub_of_positive_twin hε hclassL hclassP (liouvilleTwin_nonneg hε)
    (abs_weightRamanujanCoeff_liouvilleTwin hε)).2).mpr ⟨2, ?_, ?_⟩
  · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact (Real.log_pos (by norm_num)).ne'
  · -- `W_λ(2) = −2^{-1-ε} m_λ < 0`
    unfold weightRamanujanCoeff
    simp_rw [dampedSignWeight_mul_div liouvilleR_mul 2]
    rw [tsum_mul_left]
    have hL2 : RHTower.liouvilleR 2 = -1 := by
      simp [RHTower.liouvilleR, ArithmeticFunction.liouville_apply (show (2 : ℕ) ≠ 0 by norm_num),
        ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
    have hm := liouvilleDampedMass_pos hε
    rw [dampedSignWeight, hL2]
    have : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ (-ε) / ((2 : ℕ) : ℝ) := by positivity
    nlinarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
