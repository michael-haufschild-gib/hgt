import GaloisForLFunctions.BiScaleUncertainty.SixthSievePhaseRecovery
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The sixth-root exponent is sharp in the metric of actual translated signals. -/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open BezoutValuationIncidence
set_option autoImplicit false

private theorem translatedMoment_abs_le (N : ℕ) (c : ℕ → ℝ) (m : ℕ) (B : ℝ)
    (h : ∀ n, |sieveSeq N c n| ≤ B) (v : Fin m → ℕ) :
    |translatedMoment N c v| ≤ B^m := by
  have hterm (n : ℕ) : |∏ i, sieveSeq N c (n+v i)| ≤ B^m := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _ : Fin m, B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => h (n+v i))
      _ = _ := by simp
  have hs : |∑ n ∈ Finset.range N.factorial, ∏ i, sieveSeq N c (n+v i)| ≤
      (N.factorial : ℝ) * B^m := by
    calc
      _ ≤ ∑ n ∈ Finset.range N.factorial, |∏ i, sieveSeq N c (n+v i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range N.factorial, B^m := Finset.sum_le_sum fun n _ => hterm n
      _ = _ := by simp
  have hp : 0 < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  rw [translatedMoment, abs_div, abs_of_nonneg hp.le]
  exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hs)

private theorem zero_evenPair_signal (N n : ℕ) :
    sieveSeq (N+10) (evenPairReal 0 0) n = 0 := by
  simp [sieveSeq_evenPairReal]

private theorem zero_evenPair_moment (N m : ℕ) (hm : 0 < m) (h : Fin m → ℕ) :
    translatedMoment (N+10) (evenPairReal 0 0) h = 0 := by
  simp [translatedMoment, zero_evenPair_signal, Nat.ne_of_gt hm]

private theorem single_mode_signal_bounds (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    δ/2 ≤ |sieveSeq (N+10) (evenPairReal (δ/2) 0) n| ∧
      |sieveSeq (N+10) (evenPairReal (δ/2) 0) n| ≤ δ := by
  rw [sieveSeq_evenPairReal]
  simp only [zero_mul, add_zero, residueRow]
  split_ifs <;> norm_num [abs_mul, abs_div, abs_of_nonneg hδ] <;> linarith

/-- An existing one-mode family is small in all raw data but separated from zero after every shift. -/
theorem physical_translation_sharp_witness (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ n, |sieveSeq (N+10) (evenPairReal (δ/2) 0) n| ≤ δ) ∧
    (∀ h : Fin 5 → ℕ,
      |translatedMoment (N+10) (evenPairReal (δ/2) 0) h -
        translatedMoment (N+10) (evenPairReal 0 0) h| ≤ δ^6) ∧
    (∀ h : Fin 6 → ℕ,
      |translatedMoment (N+10) (evenPairReal (δ/2) 0) h -
        translatedMoment (N+10) (evenPairReal 0 0) h| ≤ δ^6) ∧
    (∀ t n : ℕ, δ/2 ≤ |sieveSeq (N+10) (evenPairReal 0 0) n -
      sieveSeq (N+10) (evenPairReal (δ/2) 0) (n+t)|) := by
  refine ⟨fun n => (single_mode_signal_bounds N δ hδ n).2, ?_, ?_, ?_⟩
  · intro h
    rw [evenPair_odd_zero N (δ/2) 0 2, evenPair_odd_zero N 0 0 2]
    simpa using pow_nonneg hδ 6
  · intro h
    rw [zero_evenPair_moment N 6 (by norm_num), sub_zero]
    exact translatedMoment_abs_le (N+10) _ 6 δ
      (fun n => (single_mode_signal_bounds N δ hδ n).2) h
  · intro t n
    rw [zero_evenPair_signal, zero_sub, abs_neg]
    exact (single_mode_signal_bounds N δ hδ (n+t)).1

/-- Every positive-radius neighborhood of zero already obstructs a stronger exponent. -/
theorem no_improved_physical_exponent_near_zero (N : ℕ) (α : ℝ) (hα : 1/6 < α)
    (R : ℝ) (hR : 0 < R) :
    ¬∃ C : ℝ, ∀ (c e : ℕ → ℝ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      (∀ n, |sieveSeq (N+10) c n| ≤ R) →
      (∀ n, |sieveSeq (N+10) e n| ≤ R) →
      (∀ h : Fin 5 → ℕ,
        |translatedMoment (N+10) c h - translatedMoment (N+10) e h| ≤ ε) →
      (∀ h : Fin 6 → ℕ,
        |translatedMoment (N+10) c h - translatedMoment (N+10) e h| ≤ ε) →
      ∃ t : ℕ, ∀ n : ℕ,
        |sieveSeq (N+10) e n - sieveSeq (N+10) c (n+t)| ≤ C*ε^α := by
  rintro ⟨C, hC⟩
  have hgap : 0 < 6*α-1 := by linarith
  let x : ℝ := (|2*C|+1)/(6*α-1) + R⁻¹
  let δ : ℝ := Real.exp (-x)
  have hx : 0 < x := by dsimp [x]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hδR : δ ≤ R := by
    have hRx : R⁻¹ ≤ x := by
      have hb : 0 ≤ (|2*C|+1)/(6*α-1) := by positivity
      dsimp [x]
      linarith
    have hRe : R⁻¹ ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hmul := mul_le_mul_of_nonneg_left hRe hR.le
    rw [mul_inv_cancel₀ hR.ne'] at hmul
    change Real.exp (-x) ≤ R
    rw [Real.exp_neg, ← one_div]
    exact (div_le_iff₀ (Real.exp_pos x)).mpr hmul
  have hδ6 : δ^6 ≤ 1 := by simpa using pow_le_pow_left₀ hδ.le hδ1 6
  have hw := physical_translation_sharp_witness N δ hδ.le
  obtain ⟨t, ht⟩ := hC (evenPairReal (δ/2) 0) (evenPairReal 0 0) (δ^6)
    (pow_nonneg hδ.le _) hδ6
    (fun n => (hw.1 n).trans hδR)
    (fun n => by simpa [zero_evenPair_signal] using hR.le) hw.2.1 hw.2.2.1
  have hb : δ/2 ≤ C*(δ^6)^α := (hw.2.2.2 t 0).trans (ht 0)
  rw [← Real.rpow_natCast_mul hδ.le 6 α] at hb
  have hp : 0 < δ^(6*α) := by positivity
  have hratio : δ^(1-6*α) ≤ 2*C := by
    rw [Real.rpow_sub hδ, Real.rpow_one]
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hb]
  have he : δ^(1-6*α) = Real.exp (|2*C|+1+R⁻¹*(6*α-1)) := by
    rw [Real.rpow_def_of_pos hδ]
    change Real.exp (Real.log (Real.exp (-x))*(1-6*α)) = _
    rw [Real.log_exp]
    congr 1
    dsimp [x]
    field_simp [hgap.ne', hR.ne']
    ring
  rw [he] at hratio
  have hnonneg : 0 ≤ R⁻¹*(6*α-1) := mul_nonneg (inv_nonneg.mpr hR.le) hgap.le
  linarith [Real.add_one_le_exp (|2*C|+1+R⁻¹*(6*α-1)), le_abs_self (2*C)]

/-- A uniform raw-data exponent cannot exceed one sixth. -/
theorem no_improved_physical_exponent (N : ℕ) (α : ℝ) (hα : 1/6 < α) :
    ¬∃ C : ℝ, ∀ (c e : ℕ → ℝ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      (∀ h : Fin 5 → ℕ,
        |translatedMoment (N+10) c h - translatedMoment (N+10) e h| ≤ ε) →
      (∀ h : Fin 6 → ℕ,
        |translatedMoment (N+10) c h - translatedMoment (N+10) e h| ≤ ε) →
      ∃ t : ℕ, ∀ n : ℕ,
        |sieveSeq (N+10) e n - sieveSeq (N+10) c (n+t)| ≤ C*ε^α := by
  rintro ⟨C, hC⟩
  exact no_improved_physical_exponent_near_zero N α hα 1 (by norm_num)
    ⟨C, fun c e ε hε hε1 _ _ h5 h6 => hC c e ε hε hε1 h5 h6⟩

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
