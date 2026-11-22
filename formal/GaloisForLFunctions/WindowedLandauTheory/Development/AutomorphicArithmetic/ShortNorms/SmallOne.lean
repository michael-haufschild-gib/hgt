import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.Statement
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.RelativePrimeNumberTheorem

/-! A fixed polynomial bound for a prime congruent to one. -/

open Finset QH.PrimeProgressions

namespace UpperTheory.T3

private theorem mainAP_one_pos {q : ℕ} [NeZero q] (hq : 8 ≤ q)
    (e : Option (DirichletCharacter ℂ q × ℝ)) (he : ∀ p, e = some p → IsExcPair p.1 p.2)
    {X : ℝ} (hX : 16 ≤ X) : 0 < mainAP e 1 X := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hXlog : 0 < Real.log X := Real.log_pos (by linarith only [hX])
  rcases e with _ | ⟨χ, β⟩
  · change 0 < liX X / (q.totient : ℝ)
    have h := liX_lower (show 4 ≤ X by linarith only [hX])
    exact div_pos ((by positivity : 0 < X / (2 * Real.log X)).trans_le h) hφ
  · obtain ⟨-, -, -, hβ, hβ₁⟩ := he (χ, β) rfl
    have hq' : (8 : ℝ) ≤ q := by exact_mod_cast hq
    have hlog := one_le_log_of_three_le (show (3 : ℝ) ≤ q by linarith only [hq'])
    have hbound : 1 / (8 * Real.log q) ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [hlog])
    have hβ₀ : 1 / 2 ≤ β := by linarith only [hβ, hbound]
    let η := min 1 ((1 - β) * Real.log X)
    have hη : 0 < η := lt_min one_pos (mul_pos (sub_pos.mpr hβ₁) hXlog)
    have h := main_lower (θ := 1) (η := η) (l := Real.log X) (by norm_num) hβ₀ hβ₁.le hX le_rfl
      hη.le (min_le_left _ _) (Or.inr (min_le_right _ _))
    rw [one_mul] at h
    simp only [mainAP, Nat.cast_one, map_one, Complex.one_re, one_mul]
    exact div_pos ((by positivity : 0 < X * η / (2 * Real.log X)).trans_le h) hφ

/-- Every modulus `M ≥ 2` has a prime congruent to one below a fixed power of `M`. -/
theorem small_one : SmallOne := by
  obtain ⟨c, A, C, hc, hP⟩ := pnt_progressions_relative_holds
  let B := |A| + 1
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [abs_nonneg A]
  have hA : A ≤ B := by dsimp only [B]; linarith only [le_abs_self A]
  let u := Real.log (4 * B)
  have hu : 0 < u := Real.log_pos (by linarith only [hB])
  let K := max (max C 4) ((u + u ^ 2 + 1) / c)
  have hK₄ : 4 ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hCK : C ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hcK : u + u ^ 2 + 1 ≤ c * K := by
    have hK := (div_le_iff₀ hc).mp (le_max_right (max C 4) ((u + u ^ 2 + 1) / c))
    simpa only [mul_comm c] using hK
  refine ⟨4 * K, by linarith only [hK₄], fun M hM => ?_⟩
  let q := M * 8
  have hqpos : 0 < q := Nat.mul_pos (by omega) (by norm_num)
  letI : NeZero q := ⟨hqpos.ne'⟩
  have h8 : 8 ∣ q := ⟨M, Nat.mul_comm M 8⟩
  have hq : 8 ≤ q := Nat.le_of_dvd hqpos h8
  have hqr : (8 : ℝ) ≤ q := by exact_mod_cast hq
  have hq₀ : (0 : ℝ) < q := by linarith only [hqr]
  have hlq := one_le_log_of_three_le (show (3 : ℝ) ≤ q by linarith only [hqr])
  let X := (q : ℝ) ^ K
  have hqX : (q : ℝ) ^ (2 : ℝ) ≤ X := Real.rpow_le_rpow_of_exponent_le
    (by linarith only [hqr]) (by linarith only [hK₄])
  have hX : 16 ≤ X := by
    rw [Real.rpow_two] at hqX
    exact (by norm_num : (16 : ℝ) ≤ 8 ^ 2).trans
      ((pow_le_pow_left₀ (by norm_num) hqr 2).trans hqX)
  have hlogX : Real.log X = K * Real.log q := Real.log_rpow hq₀ K
  have hC : C * Real.log q ≤ Real.log X := by
    rw [hlogX]
    exact mul_le_mul_of_nonneg_right hCK (by linarith only [hlq])
  obtain ⟨e, he, -, herr⟩ := hP q h8
  have hmain := mainAP_one_pos hq e he hX
  have h₁ : Real.exp (-(c * Real.log X / Real.log q)) ≤ Real.exp (-u) := by
    rw [hlogX, ← mul_assoc, mul_div_cancel_right₀ _ (by linarith only [hlq] : Real.log q ≠ 0)]
    exact Real.exp_le_exp.mpr (by nlinarith only [hcK, sq_nonneg u])
  have h₂ : Real.exp (-Real.sqrt (c * Real.log X)) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.mpr
    refine neg_le_neg (Real.le_sqrt_of_sq_le ?_)
    rw [hlogX, ← mul_assoc]
    have h := le_mul_of_one_le_right (mul_nonneg hc.le (by linarith only [hK₄])) hlq
    nlinarith only [h, hcK, hu]
  have hsmall : A * (Real.exp (-(c * Real.log X / Real.log q)) + Real.exp (-Real.sqrt (c * Real.log X))) < 1 := by
    calc
      _ ≤ B * (Real.exp (-(c * Real.log X / Real.log q)) + Real.exp (-Real.sqrt (c * Real.log X))) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ ≤ B * (Real.exp (-u) + Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by linarith only [hB])
      _ = 1 / 2 := by
        dsimp only [u]
        rw [Real.exp_neg, Real.exp_log (by linarith only [hB])]
        field_simp [show B ≠ 0 by linarith only [hB]]
        ring
      _ < _ := by norm_num
  have hp : 0 < piAP X q 1 := by
    by_contra! hp
    have hz : piAP X q 1 = 0 := Nat.eq_zero_of_le_zero hp
    have h := herr X 1 (by linarith only [hX]) hC (Nat.coprime_one_left q)
    rw [hz, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hmain] at h
    exact (lt_irrefl _)
      (h.trans_lt ((mul_lt_mul_of_pos_right hsmall hmain).trans_eq (one_mul _)))
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hp
  obtain ⟨hpI, hpP, hpmod⟩ := mem_filter.mp hp
  refine ⟨p, hpP, ?_, ?_⟩
  · change p % (M * 8) = 1 % (M * 8) at hpmod
    rw [← Nat.mod_mul_right_mod p M 8, hpmod, Nat.mod_mul_right_mod, Nat.mod_eq_of_lt (by omega : 1 < M)]
  · have hpX : (p : ℝ) ≤ X := (Nat.cast_le.mpr (mem_Icc.mp hpI).2).trans
      (Nat.floor_le (by linarith only [hX]))
    have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hqM : (q : ℝ) ≤ (M : ℝ) ^ (4 : ℝ) := by
      have h₃ : (8 : ℝ) ≤ (M : ℝ) ^ 3 := calc
        8 = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hMr 3
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_succ]
      dsimp only [q]
      push_cast
      rw [mul_comm (M : ℝ)]
      exact mul_le_mul_of_nonneg_right h₃ (Nat.cast_nonneg M)
    refine hpX.trans ?_
    rw [Real.rpow_mul (Nat.cast_nonneg M)]
    exact Real.rpow_le_rpow hq₀.le hqM (by linarith only [hK₄])

end UpperTheory.T3
