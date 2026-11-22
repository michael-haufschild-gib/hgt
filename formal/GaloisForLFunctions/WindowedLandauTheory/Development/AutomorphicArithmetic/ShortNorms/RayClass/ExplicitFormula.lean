import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.ExceptionalContour
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.TruncatedPerron

/-! The sharp ray class explicit formula with exponentially small remainder. -/

open Complex ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Hk
open scoped Classical

namespace GlobalTheory.Hk.PsiExc

open Finset

theorem norm_psi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {u : ℝ} (hu : 0 ≤ u) : ‖𝓕.psi χ u‖ ≤ 12 * u := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => LogDeriv.norm_lamChi_le 𝓕 χ n).trans ?_)
  rw [← Finset.mul_sum]
  have hi : Icc 1 ⌊u⌋₊ = Ioc 0 ⌊u⌋₊ := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hi, ← Chebyshev.psi]
  have h := Chebyshev.psi_le_const_mul_self hu
  have hlog : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    change (2 : ℝ) * Real.log 2 ≤ 2
    linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  nlinarith only [h, mul_le_mul_of_nonneg_right hlog hu]

theorem pow_four_mul_exp_le {δ W : ℝ} (hδ : 0 < δ) (hW : 0 ≤ W) :
    W ^ 4 * Real.exp (-(δ * W)) ≤ 24 * (2 / δ) ^ 4 * Real.exp (-(δ / 2) * W) := by
  have h := Real.pow_div_factorial_le_exp (δ / 2 * W) (by positivity) 4
  have e : Real.exp (-(δ / 2) * W) = Real.exp (δ / 2 * W) * Real.exp (-(δ * W)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e, ← mul_assoc]
  gcongr
  have e2 : W ^ 4 = 24 * (2 / δ) ^ 4 * ((δ / 2 * W) ^ 4 / (Nat.factorial 4 : ℕ)) := by
    simp only [Nat.factorial]
    field_simp
    norm_num
  rw [e2]
  gcongr

theorem const_le {c₀ C l W : ℝ} (hc₀ : 0 < c₀) (hC : 0 < C) (hl1 : 1 ≤ l) (hl : l ≤ 3 * W)
    (hW1 : 1 ≤ W) : C * l ^ 2 + 2 / (c₀ / (8 * l)) ≤ (9 * C + 48 / c₀) * W ^ 4 := by
  have h1 : l ^ 2 ≤ (3 * W) ^ 2 := by gcongr
  have h2 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW1 (by norm_num)
  have h3 : W ≤ W ^ 4 := le_self_pow₀ hW1 (by norm_num)
  have h4 : 2 / (c₀ / (8 * l)) = 48 / c₀ * (l / 3) := by field_simp; norm_num
  have h5 : 48 / c₀ * (l / 3) ≤ 48 / c₀ * W ^ 4 := by gcongr; linarith
  have h6 : C * l ^ 2 ≤ C * (9 * W ^ 4) := by gcongr; linarith
  rw [h4]
  linarith

theorem rpow_le {c₀ u l W : ℝ} (hc₀ : 0 < c₀) (hu0 : 0 < u) (hl1 : 1 ≤ l) (hl : l ≤ 3 * W)
    (hW0 : 0 ≤ W) (hW2 : W ^ 2 = Real.log u) :
    u ^ (1 - 2 * (c₀ / (8 * l))) ≤ u / Real.exp (c₀ / 32 * W) / Real.exp (c₀ / 32 * W) := by
  rw [Real.rpow_sub hu0, Real.rpow_one, div_div, ← Real.exp_add, Real.rpow_def_of_pos hu0,
    ← hW2]
  gcongr
  have e : W ^ 2 * (2 * (c₀ / (8 * l))) = c₀ / 4 * W * W / l := by field_simp; ring
  rw [e, le_div_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left hl (mul_nonneg hc₀.le hW0)
  nlinarith [mul_nonneg (mul_nonneg hc₀.le hW0) hW0]

theorem total_le {δ P K M Y u T W : ℝ} (hδ0 : 0 < δ) (hP : 0 < P) (hK0 : 0 < K) (hM0 : 0 ≤ M)
    (hu0 : 0 < u) (hW1 : 1 ≤ W) (hW2 : W ^ 2 = Real.log u) (hT : T = Real.exp (δ * W))
    (hT2 : 2 ≤ T) (hTu : T ≤ u) (hM : M ≤ K * W ^ 4) (hpow : Y ≤ u / T / T) :
    P * (u * Real.log u ^ 2 / T + Real.log u) + (18 * (M * u / T) + 4 * (T * M * Y) + 2 * Y) ≤
      (30 + (2 * P + 22 * K + 2) * (24 * (2 / δ) ^ 4)) * u * Real.exp (-(δ / 2) * W) := by
  have hW0 : 0 ≤ W := by linarith
  have hE := Real.exp_pos (-(δ / 2) * W)
  have hT0 : 0 < T := by linarith
  have hR1 : 1 ≤ u / T := (one_le_div hT0).2 hTu
  have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW1
  have t1 : M * u / T ≤ K * (W ^ 4 * (u / T)) := by
    rw [mul_div_assoc, ← mul_assoc]; gcongr
  have t2 : T * M * Y ≤ K * (W ^ 4 * (u / T)) := by
    calc T * M * Y ≤ T * (K * W ^ 4) * (u / T / T) := by
          rcases le_total 0 Y with hY | hY
          · gcongr
          · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hY).trans (by positivity)
      _ = _ := by field_simp
  have t3 : Y ≤ W ^ 4 * (u / T) := by
    refine hpow.trans ((div_le_self (by positivity) (by linarith)).trans ?_)
    nlinarith
  have t4 : u * Real.log u ^ 2 / T + Real.log u ≤ 2 * (W ^ 4 * (u / T)) := by
    have h2 : W ^ 2 ≤ W ^ 4 := pow_le_pow_right₀ hW1 (by norm_num)
    have e : u * Real.log u ^ 2 / T = W ^ 4 * (u / T) := by rw [← hW2]; ring
    rw [e, ← hW2]
    nlinarith
  have t5 : W ^ 4 * (u / T) ≤ 24 * (2 / δ) ^ 4 * (u * Real.exp (-(δ / 2) * W)) := by
    have := mul_le_mul_of_nonneg_left (pow_four_mul_exp_le hδ0 hW0) hu0.le
    rw [Real.exp_neg, ← hT] at this
    calc _ = u * (W ^ 4 * T⁻¹) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have t6 := mul_le_mul_of_nonneg_left t4 hP.le
  have t7 := mul_le_mul_of_nonneg_left t5 (by positivity : 0 ≤ 2 * P + 22 * K + 2)
  have t8 := mul_pos hu0 hE
  generalize W ^ 4 * (u / T) = R at *
  calc _ ≤ (2 * P + 22 * K + 2) * R := by linarith
    _ ≤ _ := by linarith

theorem psi_exceptional : ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 20 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (Z : Finset ℝ) (u : ℝ), 𝓕.ExcZ χ c₀ Z → 2 ≤ u → Real.log 𝓕.B ≤ Real.sqrt (Real.log u) → ‖𝓕.psi χ u - (if χ = 1 then (u : ℂ) else 0) + ∑ β ∈ Z, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  intro c₀ hc₀ hc₁
  obtain ⟨C, hC, H⟩ := GlobalTheory.Hk.LogDerivHalf.logDeriv_sub_exceptional_le c₀ hc₀ hc₁
  obtain ⟨P, hP, HP⟩ := GlobalTheory.PerronCoeff.truncated_perron_of_le_two_vonMangoldt
  set δ := c₀ / 32 with hδ
  have hδ0 : 0 < δ := by positivity
  set K := 9 * C + 48 / c₀ with hK
  have hK0 : 0 < K := by positivity
  refine ⟨δ / 2, 30 + (2 * P + 22 * K + 2) * (24 * (2 / δ) ^ 4), by positivity, by positivity, ?_⟩
  intro 𝓕 χ Z u hZ hu hB
  have hu0 : 0 < u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hW2 : Real.sqrt (Real.log u) ^ 2 = Real.log u := Real.sq_sqrt hlog
  have hW0 : 0 ≤ Real.sqrt (Real.log u) := Real.sqrt_nonneg _
  generalize Real.sqrt (Real.log u) = W at *
  have hE := Real.exp_pos (-(δ / 2) * W)
  have hQ : 0 ≤ (2 * P + 22 * K + 2) * (24 * (2 / δ) ^ 4) := by positivity
  rcases le_total (δ * W) 1 with h | h
  · have n1 := norm_psi_le 𝓕 χ hu0.le
    have n2 : ‖(if χ = 1 then (u : ℂ) else 0)‖ ≤ u := by
      split_ifs
      · simp [abs_of_pos hu0]
      · simp [hu0.le]
    have n3 : ‖∑ β ∈ Z, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * u :=
      norm_sum_le_of_card hZ.1 (by positivity) fun β hβ => by
        have h1 := (hZ.2.1 β hβ).1
        have h2 : c₀ / 𝓕.ell 0 ≤ c₀ := div_le_self hc₀.le (one_le_ell 𝓕 0)
        simpa using norm_term_le (u := u) (β := β) (σ := 1) (by linarith) (by linarith)
          (hZ.2.1 β hβ).2.1.le
    have n4 := norm_sub_le (𝓕.psi χ u) (if χ = 1 then (u : ℂ) else 0)
    refine (norm_add_le _ _).trans ?_
    have n5 := Real.add_one_le_exp (-(δ / 2) * W)
    have n6 : 1 / 2 ≤ Real.exp (-(δ / 2) * W) := by linarith
    have n7 := mul_le_mul_of_nonneg_left n6 hu0.le
    have n8 := mul_nonneg hQ (mul_pos hu0 hE).le
    nlinarith
  have hδ1 : δ ≤ 1 := by linarith
  have hW1 : 1 ≤ W := by nlinarith
  set T := Real.exp (δ * W) with hT
  have hT2 : 2 ≤ T := by
    have := Real.add_one_le_exp (δ * W)
    linarith
  have hTu : T ≤ u := by
    rw [hT, ← Real.le_log_iff_exp_le hu0, ← hW2]
    nlinarith
  have hl1 := one_le_ell 𝓕 T
  have hl : 𝓕.ell T ≤ 3 * W := by
    have hB4 := 𝓕.B_ge
    have e : 𝓕.ell T ≤ Real.log (𝓕.B * (2 * T)) := by
      refine Real.log_le_log (by positivity) ?_
      rw [abs_of_pos (by linarith)]
      gcongr
      linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      hT, Real.log_exp] at e
    have := Real.log_two_lt_d9
    nlinarith
  have A := HP (𝓕.lamChi χ) u T (LogDeriv.norm_lamChi_le 𝓕 χ) hT2 hTu
  have B := contour 𝓕 χ Z c₀ C u T _ hc₀ hc₁ hC hZ hu (by linarith) rfl (H 𝓕 χ Z hZ)
  have gen : ∀ a v m z : ℂ, ‖a - m + z‖ ≤ ‖a - v‖ + ‖v - m + z‖ := fun a v m z => by
    refine le_trans (le_of_eq ?_) (norm_add_le _ _)
    congr 1; ring
  refine ((gen _ _ _ _).trans (add_le_add A B)).trans ?_
  exact total_le hδ0 hP hK0 (by positivity) hu0 hW1 hW2 hT hT2 hTu (const_le hc₀ hC hl1 hl hW1)
    (rpow_le hc₀ hu0 hl1 hl hW0 hW2)

end GlobalTheory.Hk.PsiExc
