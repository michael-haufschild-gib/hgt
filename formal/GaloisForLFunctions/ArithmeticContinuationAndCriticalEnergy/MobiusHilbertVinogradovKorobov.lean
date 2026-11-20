import GaloisForLFunctions.RHTower.EulerDeletionFirstTailExponentLaw
import GaloisForLFunctions.BezoutValuationIncidence.VinogradovKorobovCofinalMobiusDiscrepancy
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverGrowthBelowHalfDampingAgainstThePeriodEnergy

/-!
# Vinogradov–Korobov cancellation in the Möbius Hilbert form

Abel summation and weighted Cauchy–Schwarz control the signed Hilbert form by
Mertens squares. Splitting those squares at the square root of an outer horizon
retains a Vinogradov–Korobov saving uniformly over every smaller cutoff.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
noncomputable section

private def mertensCell (n : ℕ) : ℝ := shiftedMertensReal n ^ 2 / (n : ℝ) ^ 2

private theorem mertensCell_nonneg (n : ℕ) : 0 ≤ mertensCell n := by
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem mertensCell_le_one {n : ℕ} (hn : 1 ≤ n) : mertensCell n ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mertensCell, div_le_iff₀ (sq_pos_of_pos hn0), one_mul, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_shiftedMertensReal_le n) 2

private theorem hilbert_le_mertens_cells {N : ℕ} (hN : 1 ≤ N) :
    finiteMobiusGammaHankelEnergy N 1 ≤
      (N : ℝ) * mertensCell N + 2 * ∑ n ∈ Icc 1 N, mertensCell n := by
  have h := finiteMobiusGammaHankelEnergy_le_mertens hN (r := 1) (by norm_num)
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  norm_num [Real.Gamma_add_one] at h
  have hend : 2 * shiftedMertensReal N ^ 2 * ((N : ℝ)⁻¹ * (1 / 2)) =
      (N : ℝ) * mertensCell N := by
    dsimp only [mertensCell]
    field_simp
  have hsum : (∑ k ∈ range N, shiftedMertensReal (k + 1) ^ 2 *
      (((k : ℝ) + 1) ^ 2)⁻¹) = ∑ n ∈ Icc 1 N, mertensCell n := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply sum_congr rfl
    intro k _
    simp only [mertensCell, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, add_comm]
  rw [hend, hsum] at h
  exact h

/-- A normalized Mertens square above √T inherits the saving at the outer horizon. -/
private theorem mertensCell_le_vk {B : ℝ} {n T : ℕ}
    (hn : 1 ≤ n) (hnT : n ≤ T) (hsq : T < n * n) (hT : 3 ≤ Real.log T)
    (hM : |shiftedMertensReal n| ≤
      B * n * Real.exp (-(vkKappa * vkScale n / 24))) :
    mertensCell n ≤ B ^ 2 * Real.exp (-(vkKappa * vkScale T / 27)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale := vkScale_comparable_of_sq_gt hn hnT hsq hT
  have hκ := vkKappa_pos
  have hsave : Real.exp (-(2 * (vkKappa * vkScale n / 24))) ≤
      Real.exp (-(vkKappa * vkScale T / 27)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hscale hκ.le]
  calc
    mertensCell n ≤ (B * n * Real.exp (-(vkKappa * vkScale n / 24))) ^ 2 /
        (n : ℝ) ^ 2 := by
      rw [mertensCell, ← sq_abs]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) hM 2) (sq_nonneg _)
    _ = B ^ 2 * Real.exp (-(2 * (vkKappa * vkScale n / 24))) := by
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
      push_cast
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (sq_nonneg B)

private theorem sum_mertensCell_le {B : ℝ} {T : ℕ}
    (hcell : ∀ n, 1 ≤ n → n ≤ T → T < n * n →
      mertensCell n ≤ B ^ 2 * Real.exp (-(vkKappa * vkScale T / 27))) :
    ∑ n ∈ Icc 1 T, mertensCell n ≤
      (T : ℝ) ^ (1 / 2 : ℝ) +
        B ^ 2 * T * Real.exp (-(vkKappa * vkScale T / 27)) := by
  have hlo : ∑ n ∈ Icc 1 T with n * n ≤ T, mertensCell n ≤
      (T : ℝ) ^ (1 / 2 : ℝ) := by
    have hsub : (Icc 1 T).filter (fun n => n * n ≤ T) ⊆ Icc 1 (Nat.sqrt T) := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      exact ⟨hn.1.1, Nat.le_sqrt.mpr hn.2⟩
    calc
      _ ≤ ∑ n ∈ Icc 1 T with n * n ≤ T, (1 : ℝ) :=
        sum_le_sum fun n hn => mertensCell_le_one (mem_Icc.mp (mem_filter.mp hn).1).1
      _ ≤ ∑ n ∈ Icc 1 (Nat.sqrt T), (1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le_one)
      _ = (Nat.sqrt T : ℝ) := by simp
      _ ≤ (T : ℝ) ^ (1 / 2 : ℝ) := by
        simpa only [Real.rpow_one] using natSqrt_rpow_le (a := 1) zero_le_one T
  have hhi : ∑ n ∈ Icc 1 T with ¬ n * n ≤ T, mertensCell n ≤
      B ^ 2 * T * Real.exp (-(vkKappa * vkScale T / 27)) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 T with ¬ n * n ≤ T,
          B ^ 2 * Real.exp (-(vkKappa * vkScale T / 27)) := by
        apply sum_le_sum
        intro n hn
        simp only [mem_filter, mem_Icc, not_le] at hn
        exact hcell n hn.1.1 hn.1.2 hn.2
      _ ≤ ∑ _n ∈ Icc 1 T, B ^ 2 * Real.exp (-(vkKappa * vkScale T / 27)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = _ := by simp; ring
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 T) (fun n => n * n ≤ T) mertensCell
  linarith

/-- The terminal normalized Mertens square and the positive sum of
prefix squares share one bound at all cutoffs below the outer horizon. -/
theorem exists_uniform_mertens_square_envelope_vk :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℕ in atTop, ∀ N : ℕ, N ≤ T →
      (N : ℝ) * (shiftedMertensReal N ^ 2 / (N : ℝ) ^ 2) +
        2 * ∑ n ∈ Icc 1 N, shiftedMertensReal n ^ 2 / (n : ℝ) ^ 2 ≤
          C * T * Real.exp (-(vkKappa * vkScale T / 27)) := by
  obtain ⟨B, _, hev⟩ := exists_abs_mertensM_le_vk_rate
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  have hκ := vkKappa_pos
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := (tendsto_vkScale_div_log.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds (show (0 : ℝ) < 27 / (2 * vkKappa) by positivity))
  refine ⟨3 + 3 * B ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (n₀ * n₀), eventually_ge_atTop 1,
    hlog.eventually_ge_atTop 3, hratio] with T hTn hT1 hTlog hTr
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  have hs : vkKappa * vkScale T / 27 ≤ Real.log T / 2 := by
    simp only [Function.comp_apply] at hTr
    rw [div_le_iff₀ (by linarith)] at hTr
    have hh := mul_le_mul_of_nonneg_left hTr hκ.le
    have heq : vkKappa * (27 / (2 * vkKappa) * Real.log T) =
        27 * Real.log T / 2 := by field_simp
    rw [heq] at hh
    linarith
  let G : ℝ := T * Real.exp (-(vkKappa * vkScale T / 27))
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have hGroot : (T : ℝ) ^ (1 / 2 : ℝ) ≤ G := by
    rw [Real.rpow_def_of_pos hT0]
    dsimp only [G]
    conv_rhs => lhs; rw [← Real.exp_log hT0]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hcell : ∀ n, 1 ≤ n → n ≤ T → T < n * n →
      mertensCell n ≤ B ^ 2 * Real.exp (-(vkKappa * vkScale T / 27)) := by
    intro n hn hnT hsq
    have hlarge : n₀ ≤ n := by
      by_contra h
      have hn' := not_le.mp h
      nlinarith
    apply mertensCell_le_vk hn hnT hsq hTlog
    simpa only [RHTower.DeletionFirstTail.mertensM_eq_shiftedMertensReal] using hn₀ n hlarge
  have hsum : ∑ n ∈ Icc 1 T, mertensCell n ≤ (1 + B ^ 2) * G := by
    have h := sum_mertensCell_le hcell
    have hid : B ^ 2 * T * Real.exp (-(vkKappa * vkScale T / 27)) = B ^ 2 * G := by
      dsimp only [G]; ring
    rw [hid] at h
    nlinarith only [h, hGroot]
  intro N hNT
  change (N : ℝ) * mertensCell N + 2 * ∑ n ∈ Icc 1 N, mertensCell n ≤ _
  by_cases hN : N = 0
  · subst N
    simp only [Nat.cast_zero,zero_mul,Finset.Icc_eq_empty_of_lt (by decide : (0:ℕ) < 1),
      sum_empty,mul_zero,add_zero]
    positivity
  have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN
  have hend : (N : ℝ) * mertensCell N ≤ (1 + B ^ 2) * G := by
    by_cases hsq : N * N ≤ T
    · have hroot : (N : ℝ) ≤ (T : ℝ) ^ (1 / 2 : ℝ) := by
        calc
          (N : ℝ) ≤ (Nat.sqrt T : ℝ) := by exact_mod_cast Nat.le_sqrt.mpr hsq
          _ ≤ _ := by simpa only [Real.rpow_one] using natSqrt_rpow_le (a := 1) zero_le_one T
      have hc := mul_le_mul_of_nonneg_left (mertensCell_le_one hN1) (Nat.cast_nonneg N)
      nlinarith only [hc, hroot, hGroot, mul_nonneg (sq_nonneg B) hG0]
    · calc
        (N : ℝ) * mertensCell N ≤
            N * (B ^ 2 * Real.exp (-(vkKappa * vkScale T / 27))) :=
          mul_le_mul_of_nonneg_left (hcell N hN1 hNT (not_le.mp hsq)) (Nat.cast_nonneg N)
        _ ≤ T * (B ^ 2 * Real.exp (-(vkKappa * vkScale T / 27))) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hNT)
          positivity
        _ = B ^ 2 * G := by dsimp only [G]; ring
        _ ≤ (1 + B ^ 2) * G := by nlinarith only [hG0]
  have hsumN : ∑ n ∈ Icc 1 N, mertensCell n ≤ (1 + B ^ 2) * G := by
    refine (sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => mertensCell_nonneg n)).trans hsum
    intro n hn
    exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hNT⟩
  calc
    _ ≤ (3 + 3 * B ^ 2) * G := by nlinarith only [hend, hsumN]
    _ = _ := by dsimp only [G]; ring

/-- The actual undamped Hilbert form has a Vinogradov–Korobov saving, uniformly
in every cutoff below the outer horizon. No monotonicity of the signed form is used. -/
theorem exists_uniform_mobiusHilbert_le_vinogradovKorobov :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℕ in atTop, ∀ N : ℕ, N ≤ T →
      0 ≤ finiteMobiusGammaHankelEnergy N 1 ∧
      finiteMobiusGammaHankelEnergy N 1 ≤
        C * T * Real.exp (-(vkKappa * vkScale T / 27)) := by
  obtain ⟨C,hC,h⟩ := exists_uniform_mertens_square_envelope_vk
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T hT N hNT
  refine ⟨finiteMobiusGammaHankelEnergy_nonneg N (by norm_num), ?_⟩
  by_cases hN : N = 0
  · subst N
    simp only [finiteMobiusGammaHankelEnergy,finiteGammaHankelEnergy,sum_range_zero,mul_zero]
    positivity
  exact (hilbert_le_mertens_cells (Nat.pos_of_ne_zero hN)).trans (hT N hNT)

#print axioms exists_uniform_mertens_square_envelope_vk
#print axioms exists_uniform_mobiusHilbert_le_vinogradovKorobov

end
end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
