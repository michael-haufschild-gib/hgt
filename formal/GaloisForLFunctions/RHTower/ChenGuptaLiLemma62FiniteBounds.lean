import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FunctionalGrowth

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

structure CGLLemma62NonnegativePoint where
  value : ℂ
  nonnegative : 0 ≤ value.re

private theorem cglLemma62_norm_dirichletTerm_le_one
    (B : CGLLemma62InducedCharacter) (s : CGLLemma62NonnegativePoint) (n : ℕ) :
    ‖LSeries.term (↗(B.character⁻¹)) s.value n‖ ≤ 1 := by
  letI : NeZero B.ambient.value := ⟨Nat.ne_of_gt B.ambient.positive⟩
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    norm_num
  · rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hpow : 1 ≤ (n : ℝ) ^ s.value.re :=
      Real.one_le_rpow hn1 s.nonnegative
    have hpos : 0 < (n : ℝ) ^ s.value.re :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
    rw [div_le_one hpos]
    calc
      ‖B.character⁻¹ ((n : ℕ) : ZMod B.ambient.value)‖ ≤ 1 :=
        norm_dirichletCharacter_le_one B.character⁻¹ _
      _ ≤ (n : ℝ) ^ s.value.re := hpow

theorem cglLemma62_dirichletHead_norm_le
    (B : CGLLemma62InducedCharacter) (M : ℕ) (s : CGLLemma62NonnegativePoint) :
    ‖cglLemma62DirichletHead B.character⁻¹ M s.value‖ ≤ M + 1 := by
  unfold cglLemma62DirichletHead
  calc
    ‖∑ n ∈ Finset.range (M + 1), LSeries.term (↗(B.character⁻¹)) s.value n‖ ≤
        ∑ n ∈ Finset.range (M + 1), ‖LSeries.term (↗(B.character⁻¹)) s.value n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range (M + 1), (1 : ℝ) := by
      gcongr with n hn
      exact cglLemma62_norm_dirichletTerm_le_one B s n
    _ = M + 1 := by
      simp

def cglLemma62EulerCorrectionBudget (B : CGLLemma62InducedCharacter) : ℝ :=
  ∏ p ∈ B.ambient.value.primeFactors,
    (1 + (p : ℝ)) / (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))

private theorem cglLemma62EulerCorrection_budget_factor_pos
    (B : CGLLemma62InducedCharacter) (p : ↑B.ambient.value.primeFactors) :
    0 < (1 + (p.1 : ℝ)) / (1 - (p.1 : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpowlt : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)
  positivity

private theorem cglLemma62EulerCorrection_left_factor_bound
    (B : CGLLemma62InducedCharacter) (z : CGLLemma62HighStripPoint)
    (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤ 1 + p.1 := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpone : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.one_le
  have hppos : (0 : ℝ) < p.1 := by exact_mod_cast hp.pos
  have hpow : ‖(p.1 : ℂ) ^ (-z.value)‖ ≤ p.1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    change (p.1 : ℝ) ^ (-z.value.re) ≤ p.1
    calc
      (p.1 : ℝ) ^ (-z.value.re) ≤ (p.1 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hpone
        linarith [z.lower]
      _ = p.1 := Real.rpow_one _
  have hmul : ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤ p.1 := by
    rw [norm_mul]
    simpa using mul_le_mul (B.primitive.character.norm_le_one p.1) hpow
      (norm_nonneg _) (by norm_num)
  calc
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
        ‖(1 : ℂ)‖ + ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ :=
          norm_sub_le _ _
    _ = 1 + ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ := by norm_num
    _ ≤ 1 + p.1 := by gcongr

private theorem cglLemma62EulerCorrection_right_factor_lower
    (B : CGLLemma62InducedCharacter) (z : CGLLemma62HighStripPoint)
    (p : ↑B.ambient.value.primeFactors) :
    1 - (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpone : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.one_le
  have hpow : ‖(p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
      (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    apply Real.rpow_le_rpow_of_exponent_le hpone
    simp only [neg_re, sub_re, one_re]
    linarith [z.upper]
  have hmul : ‖B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
      (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul]
    calc
      ‖B.primitive.character⁻¹ p.1‖ * ‖(p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
          1 * ‖(p.1 : ℂ) ^ (-(1 - z.value))‖ := by
            gcongr
            exact B.primitive.character⁻¹.norm_le_one p.1
      _ ≤ (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by simpa using hpow
  have htri : (1 : ℝ) ≤
      ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ +
        ‖B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(1 - B.primitive.character⁻¹ p.1 *
          (p.1 : ℂ) ^ (-(1 - z.value))) +
          B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := by
            congr 1
            ring
      _ ≤ ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ +
          ‖B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := norm_add_le _ _
  linarith

private theorem cglLemma62EulerCorrection_factor_bound
    (B : CGLLemma62InducedCharacter) (z : CGLLemma62HighStripPoint)
    (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ /
        ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
      (1 + (p.1 : ℝ)) / (1 - (p.1 : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hdenpos : 0 < 1 - (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hpowlt : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)
    linarith
  exact div_le_div₀ (by positivity) (cglLemma62EulerCorrection_left_factor_bound B z p)
    hdenpos (cglLemma62EulerCorrection_right_factor_lower B z p)

theorem cglLemma62EulerCorrectionAt_highStrip_norm_le
    (B : CGLLemma62InducedCharacter) (z : CGLLemma62HighStripPoint) :
    ‖cglLemma62EulerCorrectionAt B z.value‖ ≤ cglLemma62EulerCorrectionBudget B := by
  unfold cglLemma62EulerCorrectionAt cglLemma62EulerLeftFactorAt cglLemma62EulerRightFactorAt
    cglLemma62EulerCorrectionBudget
  rw [norm_div, norm_prod, norm_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro p hp
    exact cglLemma62EulerCorrection_factor_bound B z ⟨p, hp⟩

theorem cglLemma62_lengthPower_highStrip_norm_le
    (N : CGLPositiveLength) (z : CGLLemma62HighStripPoint) :
    ‖(N.value : ℂ) ^ z.value‖ ≤ (N.value : ℝ) ^ (2 : ℝ) := by
  rw [Complex.norm_natCast_cpow_of_pos N.positive]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt N.positive)
  · linarith [z.upper]

end

end RHTower
