import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailFunctionalGrowth
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteBounds

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- A point on CGL's far-left tail line for the Euler correction. -/
structure CGLLemma62TailEulerPoint (d : CGLLemma62TailContourDepth) where
  value : ℂ
  real_eq : value.re = -2 * (d.value : ℝ)

/-- A closed finite-product envelope for CGL's Euler correction on
`Re z = -2k`. -/
def cglLemma62TailEulerCorrectionBudget (B : CGLLemma62InducedCharacter)
    (d : CGLLemma62TailContourDepth) : ℝ :=
  ∏ p ∈ B.ambient.value.primeFactors,
    (1 + (p : ℝ) ^ (2 * (d.value : ℝ))) /
      (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))

private theorem cglLemma62_tailEuler_budget_factor_pos
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (p : ↑B.ambient.value.primeFactors) :
    0 < (1 + (p.1 : ℝ) ^ (2 * (d.value : ℝ))) /
      (1 - (p.1 : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpowlt : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)
  positivity

private theorem cglLemma62_tailEuler_left_factor_bound
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
      1 + (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hppos : 0 < (p.1 : ℝ) := by exact_mod_cast hp.pos
  have hpow : ‖(p.1 : ℂ) ^ (-z.value)‖ =
      (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    congr 1
    simp only [neg_re]
    rw [z.real_eq]
    ring
  have hmul : ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
      (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
    rw [norm_mul, hpow]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hppos.le _)
      (B.primitive.character.norm_le_one p.1)
  calc
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
        ‖(1 : ℂ)‖ + ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ :=
          norm_sub_le _ _
    _ = 1 + ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ := by norm_num
    _ ≤ 1 + (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by gcongr

private theorem cglLemma62_tailEuler_right_factor_lower
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) (p : ↑B.ambient.value.primeFactors) :
    1 - (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpone : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.one_le
  have hzupper : z.value.re ≤ (1 / 2 : ℝ) := by
    rw [z.real_eq]
    have hd : (0 : ℝ) ≤ d.value := Nat.cast_nonneg _
    linarith
  have hpow : ‖(p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
      (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    apply Real.rpow_le_rpow_of_exponent_le hpone
    simp only [neg_re, sub_re, one_re]
    linarith
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

private theorem cglLemma62_tailEuler_factor_bound
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ /
        ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
      (1 + (p.1 : ℝ) ^ (2 * (d.value : ℝ))) /
        (1 - (p.1 : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hdenpos : 0 < 1 - (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hpowlt : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)
    linarith
  exact div_le_div₀ (by positivity) (cglLemma62_tailEuler_left_factor_bound B d z p)
    hdenpos (cglLemma62_tailEuler_right_factor_lower B d z p)

/-- CGL's finite Euler correction has a closed data-only far-left envelope. -/
theorem cglLemma62EulerCorrectionAt_tail_norm_le
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) :
    ‖cglLemma62EulerCorrectionAt B z.value‖ ≤
      cglLemma62TailEulerCorrectionBudget B d := by
  unfold cglLemma62EulerCorrectionAt cglLemma62EulerLeftFactorAt cglLemma62EulerRightFactorAt
    cglLemma62TailEulerCorrectionBudget
  rw [norm_div, norm_prod, norm_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro p hp
    exact cglLemma62_tailEuler_factor_bound B d z ⟨p, hp⟩

end

end RHTower
