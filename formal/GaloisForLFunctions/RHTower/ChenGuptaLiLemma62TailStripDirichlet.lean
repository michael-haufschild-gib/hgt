import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailBounds

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- A complementary Dirichlet-series point in the whole CGL tail rectangle. -/
structure CGLLemma62TailRightStripPoint where
  value : ℂ
  real_two : 2 ≤ value.re

/-- The CGL complementary series has a uniform elementary bound throughout
the tail rectangle's dual half-plane. -/
theorem cglLemma62_tail_dirichletTail_norm_le
    (B : CGLLemma62InducedCharacter) (J : CGLLemma62TailCutoff)
    (z : CGLLemma62TailRightStripPoint) :
    ‖cglLemma62DirichletTail B.character⁻¹ J.value
      ⟨z.value, by linarith [z.real_two]⟩‖ ≤ (J.value : ℝ) ^ (-(1 : ℝ)) := by
  let s : CGLAbsoluteConvergencePoint := ⟨z.value, by linarith [z.real_two]⟩
  let q : ℝ := -1
  have hq : q < 0 := by norm_num [q]
  have hweight : Summable (fun k : ℕ =>
      ((J.value : ℝ) + 1 + (k : ℝ)) ^ (q - 1)) :=
    GaloisForLFunctions.HTGeometry.summable_shift_rpow hq J.value
  have hterm : Summable (fun n : ℕ =>
      LSeries.term (↗B.character⁻¹) s.1 n) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re B.character⁻¹ s.2
  have htailnorm : Summable (fun k : ℕ =>
      ‖LSeries.term (↗B.character⁻¹) s.1 (k + (J.value + 1))‖) := by
    have hshift := (summable_nat_add_iff (f := fun n : ℕ =>
        ‖LSeries.term (↗B.character⁻¹) s.1 n‖) (J.value + 1)).mpr hterm.norm
    exact hshift
  rw [show (⟨z.value, by linarith [z.real_two]⟩ : CGLAbsoluteConvergencePoint) = s by rfl,
    cglLemma62_dirichletTail_eq_tsum_shift B.character⁻¹ J.value s]
  refine (norm_tsum_le_tsum_norm htailnorm).trans ?_
  refine (htailnorm.tsum_mono hweight ?_).trans ?_
  · intro k
    let n : ℕ := k + (J.value + 1)
    have hn : n ≠ 0 := by
      dsimp [n]
      omega
    have hχ : ‖B.character⁻¹ n‖ ≤ ‖(1 : ℂ)‖ := by
      simpa using (B.character⁻¹).norm_le_one n
    have hle : ‖LSeries.term (↗B.character⁻¹) s.1 n‖ ≤
        ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ :=
      LSeries.norm_term_le (f := (↗B.character⁻¹)) (g := fun _ : ℕ => (1 : ℂ)) s.1 hχ
    have hnorm : ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ =
        1 / (n : ℝ) ^ s.1.re := by
      rw [LSeries.norm_term_eq, if_neg hn]
      norm_num
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.1.re := by
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [z.real_two])
    have hpowpos : 0 < (n : ℝ) ^ (2 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
    have hdiv : 1 / (n : ℝ) ^ s.1.re ≤ 1 / (n : ℝ) ^ (2 : ℝ) :=
      one_div_le_one_div_of_le hpowpos hpow
    change ‖LSeries.term (↗B.character⁻¹) s.1 n‖ ≤ _
    calc
      ‖LSeries.term (↗B.character⁻¹) s.1 n‖ ≤
          ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ := hle
      _ = 1 / (n : ℝ) ^ s.1.re := hnorm
      _ ≤ 1 / (n : ℝ) ^ (2 : ℝ) := hdiv
      _ = ((J.value : ℝ) + 1 + (k : ℝ)) ^ (q - 1) := by
        have hncast : (n : ℝ) = (J.value : ℝ) + 1 + (k : ℝ) := by
          dsimp [n]
          push_cast
          ring
        rw [hncast, one_div]
        rw [← Real.rpow_neg (by positivity : 0 ≤ (J.value : ℝ) + 1 + (k : ℝ))]
        dsimp [q]
        congr 1
        ring
  · simpa [q] using
      GaloisForLFunctions.HTGeometry.tsum_shift_rpow_le hq J.one_le

end

end RHTower
