import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailFunctionalStrip

/-!
# Chen–Gupta–Li Lemma 6.2: the finite Euler correction on the tail strip

For a nonprincipal Dirichlet character modulo `q` induced by a primitive character `χ*`, the
reflected finite Euler correction is
`E(z) = ∏_{p | q} (1 - χ*(p) p^(-z)) / (1 - χ̄*(p) p^(-(1-z)))`. This module bounds `E` on the
tail strip `-2d ≤ Re z ≤ -1` (with contour depth `d ≥ 1`) by
`∏_{p | q} (1 + p^(2d)) / (1 - p^(-1/2))`, uniformly in `Im z`.

## Main results

- `CGLLemma62TailEulerStripPoint`: a point `z` with `-2d ≤ Re z ≤ -1`.
- `cglLemma62EulerCorrectionAt_tail_strip_norm_le`: `|E(z)| ≤ cglLemma62TailEulerCorrectionBudget B d`
  on the tail strip.

## Hypotheses

Unconditional; the strip condition is bundled in the point structure.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- A point `z` of the tail strip `-2d ≤ Re z ≤ -1`. -/
structure CGLLemma62TailEulerStripPoint (d : CGLLemma62TailContourDepth) where
  value : ℂ
  lower : -2 * (d.value : ℝ) ≤ value.re
  upper : value.re ≤ -1

private theorem cgl_tailEuler_strip_left
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerStripPoint d) (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
      1 + (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpow : ‖(p.1 : ℂ) ^ (-z.value)‖ ≤
      (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hp.one_le
    · simp only [neg_re]
      linarith [z.lower]
  have hmul : ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
      (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
    rw [norm_mul]
    calc
      ‖B.primitive.character p.1‖ * ‖(p.1 : ℂ) ^ (-z.value)‖ ≤
          1 * ‖(p.1 : ℂ) ^ (-z.value)‖ := by
            gcongr
            exact B.primitive.character.norm_le_one p.1
      _ ≤ _ := by simpa using hpow
  calc
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
        ‖(1 : ℂ)‖ + ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ := norm_sub_le _ _
    _ = 1 + ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ := by norm_num
    _ ≤ _ := by gcongr

private theorem cgl_tailEuler_strip_right
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerStripPoint d) (p : ↑B.ambient.value.primeFactors) :
    1 - (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpone : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.one_le
  have hzupper : z.value.re ≤ (1 / 2 : ℝ) := by linarith [z.upper]
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
      _ ≤ _ := by simpa using hpow
  have htri : (1 : ℝ) ≤
      ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ +
        ‖B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1-z.value))) +
          B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1-z.value))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  linarith

private theorem cgl_tailEuler_strip_factor
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerStripPoint d) (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ /
        ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1-z.value))‖ ≤
      (1 + (p.1 : ℝ) ^ (2*(d.value : ℝ))) /
        (1 - (p.1 : ℝ) ^ (-(1/2:ℝ))) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hden : 0 < 1 - (p.1 : ℝ) ^ (-(1/2:ℝ)) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt : (1 : ℝ) < p.1) (by norm_num : (-(1/2:ℝ)) < 0)
    linarith
  exact div_le_div₀ (by positivity) (cgl_tailEuler_strip_left B d z p) hden
    (cgl_tailEuler_strip_right B d z p)

/-- On the tail strip `-2d ≤ Re z ≤ -1`, the reflected finite Euler correction is bounded by
`∏_{p | q} (1 + p^(2d)) / (1 - p^(-1/2))`, independently of `Im z`. -/
theorem cglLemma62EulerCorrectionAt_tail_strip_norm_le
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerStripPoint d) :
    ‖cglLemma62EulerCorrectionAt B z.value‖ ≤ cglLemma62TailEulerCorrectionBudget B d := by
  unfold cglLemma62EulerCorrectionAt cglLemma62EulerLeftFactorAt cglLemma62EulerRightFactorAt
    cglLemma62TailEulerCorrectionBudget
  rw [norm_div, norm_prod, norm_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro p hp
    exact cgl_tailEuler_strip_factor B d z ⟨p,hp⟩

end

end RHTower
