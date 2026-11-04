import GaloisForLFunctions.BezoutValuationIncidence.Sieve.KernelVariation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Variation of the literal logarithmic offset kernels

The square-root Jacobian is monotone and bounded away from the excluded
origin. The nonnegative logarithmic argument is antitone. Clamping at the
kernel support endpoint makes the variation independent of its scale;
an initial-segment cutoff adds only one supremum cost.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence


/-- Truncating a bounded kernel by an initial segment adds at most one supremum cost. -/
theorem cutoff_variation {f : ℕ → ℝ} {M K : ℝ} (hM : 0 ≤ M)
    {A B : ℕ} (hAB : A ≤ B) (hf : ∀ n ∈ Icc A B, |f n| ≤ M)
    (hfv : discreteVariation f A B ≤ K) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n m, A ≤ n → n ≤ m → m ≤ B → P m → P n) :
    discreteVariation (fun n => if P n then f n else 0) A B ≤ K + M := by
  let v : ℕ → ℝ := fun n => if P n then 1 else 0
  have hv : ∀ n ∈ Icc A B, |v n| ≤ 1 := by
    intro n _
    dsimp only [v]
    split_ifs <;> norm_num
  have hvanti : ∀ n m, A ≤ n → n ≤ m → m ≤ B → v m ≤ v n := by
    intro n m hn hnm hm
    dsimp only [v]
    by_cases hp : P m
    · rw [if_pos hp, if_pos (hP n m hn hnm hm hp)]
    · rw [if_neg hp]
      split_ifs <;> norm_num
  have hvv : discreteVariation v A B ≤ 1 := by
    rw [antitone_variation hAB hvanti]
    have hleft : v A ≤ 1 := (le_abs_self _).trans (hv A (mem_Icc.mpr ⟨le_rfl, hAB⟩))
    have hright : 0 ≤ v B := by dsimp only [v]; split_ifs <;> norm_num
    linarith only [hleft, hright]
  have he : (fun n => if P n then f n else 0) = (fun n => f n * v n) := by
    funext n
    dsimp only [v]
    split_ifs <;> simp only [mul_one, mul_zero]
  rw [he]
  refine (product_variation hf hv).trans ?_
  have h := add_le_add (mul_le_mul_of_nonneg_left hvv hM)
    (mul_le_mul_of_nonneg_left hfv zero_le_one)
  simpa only [mul_one, one_mul, add_comm] using h

#print axioms cutoff_variation

/-- The positive-offset square-root factor increases and stays below one. -/
theorem positive_root_ratio_mono {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hxy : x ≤ y) :
    Real.sqrt (x / (x + a)) ≤ Real.sqrt (y / (y + a)) := by
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by linarith only [ha, hx]) (by linarith only [ha, hx, hxy])]
  nlinarith only [mul_le_mul_of_nonneg_right hxy ha]

theorem positive_root_ratio_le {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) :
    Real.sqrt (x / (x + a)) ≤ 2 := by
  have h : x / (x + a) ≤ 1 := (div_le_one (by linarith only [ha, hx])).mpr (by linarith only [ha])
  have hroot := Real.sqrt_le_sqrt h
  rw [Real.sqrt_one] at hroot
  exact hroot.trans (by norm_num)

/-- The negative-offset square-root factor decreases away from the excluded origin. -/
theorem negative_root_ratio_anti {a x y : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxy : x ≤ y) :
    Real.sqrt (y / (y - a)) ≤ Real.sqrt (x / (x - a)) := by
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by linarith only [hx, hxy]) (sub_pos.mpr hx)]
  nlinarith only [mul_le_mul_of_nonneg_right hxy ha]

theorem negative_root_ratio_le {a x : ℝ} (hx : 0 < x) (ha : 2 * a ≤ x) :
    Real.sqrt (x / (x - a)) ≤ 2 := by
  have hden : 0 < x - a := by linarith only [ha, hx]
  have h : x / (x - a) ≤ 4 := (div_le_iff₀ hden).mpr (by linarith only [ha, hx])
  have hroot := Real.sqrt_le_sqrt h
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsqrt] at hroot
  exact hroot

/-- Positive logarithmic offsets have scale-independent variation. -/
theorem positive_log_kernel_variation {f : ℝ → ℝ} {M K a C : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hf1 : ∀ x, 1 ≤ x → f x = 0) (hfM : ∀ x, |f x| ≤ M)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    discreteVariation (fun n => Real.sqrt ((n : ℝ) / ((n : ℝ) + a)) *
      f (C * Real.log (1 + a / (n : ℝ)))) A B ≤ 2 * K + 2 * M := by
  let r : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) / ((n : ℝ) + a))
  let u : ℕ → ℝ := fun n => C * Real.log (1 + a / (n : ℝ))
  have hn0 (n : ℕ) (hn : A ≤ n) : (0 : ℝ) < n := by exact_mod_cast hA.trans hn
  have hr : ∀ n ∈ Icc A B, |r n| ≤ 2 := by
    intro n hn
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact positive_root_ratio_le ha (hn0 n (mem_Icc.mp hn).1)
  have hrmono : ∀ n m, A ≤ n → n ≤ m → m ≤ B → r n ≤ r m :=
    fun n m hn hnm _ => positive_root_ratio_mono (y := (m : ℝ)) ha
      (hn0 n hn) (by exact_mod_cast hnm)
  have hrv : discreteVariation r A B ≤ 2 := by
    rw [monotone_variation hAB hrmono]
    have hB := (le_abs_self _).trans (hr B (mem_Icc.mpr ⟨hAB, le_rfl⟩))
    have hA' : 0 ≤ r A := Real.sqrt_nonneg _
    linarith only [hB, hA']
  have hu : ∀ n m, A ≤ n → n ≤ m → m ≤ B → u m ≤ u n := by
    intro n m hn hnm _
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.log_le_log (x := 1 + a / (m : ℝ))
      (by have := div_nonneg ha (Nat.cast_nonneg m); linarith only [this])
    exact add_le_add le_rfl (div_le_div_of_nonneg_left ha (hn0 n hn)
      (by exact_mod_cast hnm : (n : ℝ) ≤ (m : ℝ)))
  have huB : 0 ≤ u B := mul_nonneg hC (Real.log_nonneg (by
    have h := div_nonneg ha (Nat.cast_nonneg B)
    linarith only [h]))
  have hfv := clamped_antitone_variation hK hf hf1 hAB hu huB
  have h := product_variation hr (fun n (_ : n ∈ Icc A B) => hfM (u n))
  refine h.trans ?_
  have hb := add_le_add (mul_le_mul_of_nonneg_left hfv zero_le_two)
    (mul_le_mul_of_nonneg_left hrv hM)
  simpa only [mul_comm M 2] using hb

#print axioms positive_log_kernel_variation

/-- Negative logarithmic offsets have the same variation bound away from zero. -/
theorem negative_log_kernel_variation {f : ℝ → ℝ} {M K a C : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hf1 : ∀ x, 1 ≤ x → f x = 0) (hfM : ∀ x, |f x| ≤ M)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (haway : 2 * a ≤ (A : ℝ)) :
    discreteVariation (fun n => Real.sqrt ((n : ℝ) / ((n : ℝ) - a)) *
      f (C * (-Real.log (1 - a / (n : ℝ))))) A B ≤ 2 * K + 2 * M := by
  let r : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) / ((n : ℝ) - a))
  let u : ℕ → ℝ := fun n => C * (-Real.log (1 - a / (n : ℝ)))
  have hn0 (n : ℕ) (hn : A ≤ n) : (0 : ℝ) < n := by exact_mod_cast hA.trans hn
  have hnaway (n : ℕ) (hn : A ≤ n) : 2 * a ≤ (n : ℝ) :=
    haway.trans (by exact_mod_cast hn)
  have harg (n : ℕ) (hn : A ≤ n) : 0 < 1 - a / (n : ℝ) := by
    have hratio : a / (n : ℝ) ≤ 1 / 2 :=
      (div_le_iff₀ (hn0 n hn)).mpr (by linarith only [hnaway n hn])
    linarith only [hratio]
  have hr : ∀ n ∈ Icc A B, |r n| ≤ 2 := by
    intro n hn
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact negative_root_ratio_le (hn0 n (mem_Icc.mp hn).1) (hnaway n (mem_Icc.mp hn).1)
  have hranti : ∀ n m, A ≤ n → n ≤ m → m ≤ B → r m ≤ r n := by
    intro n m hn hnm _
    apply negative_root_ratio_anti ha
    · linarith only [hnaway n hn, hn0 n hn]
    · exact_mod_cast hnm
  have hrv : discreteVariation r A B ≤ 2 := by
    rw [antitone_variation hAB hranti]
    have hA' := (le_abs_self _).trans (hr A (mem_Icc.mpr ⟨le_rfl, hAB⟩))
    have hB : 0 ≤ r B := Real.sqrt_nonneg _
    linarith only [hA', hB]
  have hu : ∀ n m, A ≤ n → n ≤ m → m ≤ B → u m ≤ u n := by
    intro n m hn hnm _
    apply mul_le_mul_of_nonneg_left _ hC
    apply neg_le_neg
    apply Real.log_le_log (harg n hn)
    exact sub_le_sub_left (div_le_div_of_nonneg_left ha (hn0 n hn) (by exact_mod_cast hnm)) 1
  have huB : 0 ≤ u B := by
    apply mul_nonneg hC
    apply neg_nonneg.mpr
    apply Real.log_nonpos (harg B hAB).le
    have h := div_nonneg ha (Nat.cast_nonneg B)
    linarith only [h]
  have hfv := clamped_antitone_variation hK hf hf1 hAB hu huB
  have h := product_variation hr (fun n (_ : n ∈ Icc A B) => hfM (u n))
  refine h.trans ?_
  have hb := add_le_add (mul_le_mul_of_nonneg_left hfv zero_le_two)
    (mul_le_mul_of_nonneg_left hrv hM)
  simpa only [mul_comm M 2] using hb

#print axioms negative_log_kernel_variation

/-- Pointwise equality on the closed interval preserves discrete variation. -/
theorem discreteVariation_congr {f g : ℕ → ℝ} {A B : ℕ}
    (hfg : ∀ n ∈ Icc A B, f n = g n) : discreteVariation f A B = discreteVariation g A B := by
  apply sum_congr rfl
  intro n hn
  have hn0 : n ∈ Icc A B := mem_Icc.mpr ⟨(mem_Ico.mp hn).1, (mem_Ico.mp hn).2.le⟩
  have hn1 : n + 1 ∈ Icc A B := mem_Icc.mpr ⟨by have := (mem_Ico.mp hn).1; omega,
    by have := (mem_Ico.mp hn).2; omega⟩
  rw [hfg n hn0, hfg (n + 1) hn1]

#print axioms discreteVariation_congr

end GaloisForLFunctions.BezoutValuationIncidence
