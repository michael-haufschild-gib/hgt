import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateHorizonBeforeNineHalves
import GaloisForLFunctions.WindowTowerOfSpecZ.TheReflectionCentralizerOfTheWindowAlgebra

/-!
# The second graph of the third Tate stage

Above ratio `9/2`, the canonical component has twelve vertices. Reflection
reduces positivity to six variables, and four completed squares leave a
two-variable Schur complement.
-/

noncomputable section

open Finset MeasureTheory

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory

/-- The twelve vertices present after ratio `9/2` and before ratio five. -/
def thirdStageLateNodes : Finset ℚ :=
  {1, 2, 4, 3, 4 / 3, 8 / 3, 9 / 2, 9 / 4, 9 / 8, 3 / 2, 27 / 8, 27 / 16}

theorem thirdStageLateNodes_closed {q s : ℚ} {n : ℕ}
    (hq : q ∈ thirdStageLateNodes) (hn : n ∈ Finset.Icc 2 4)
    (hlo : 1 ≤ s) (hhi : s < 81 / 16)
    (hrel : s = n * q ∨ q = n * s) : s ∈ thirdStageLateNodes := by
  have hn0 : (n : ℚ) ≠ 0 := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  rcases hrel with rfl | hrel
  · norm_num only [thirdStageLateNodes, Finset.mem_insert, Finset.mem_singleton] at hq
    obtain ⟨hn2, hn4⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num at hlo
    all_goals norm_num at hhi
    all_goals norm_num [thirdStageLateNodes]
  · have hs : s = q / n := (eq_div_iff hn0).mpr (by linarith only [hrel])
    rw [hs] at hlo hhi ⊢
    norm_num only [thirdStageLateNodes, Finset.mem_insert, Finset.mem_singleton] at hq
    obtain ⟨hn2, hn4⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num at hlo
    all_goals norm_num at hhi
    all_goals norm_num [thirdStageLateNodes]

/-- The twelve-vertex form, ordered in six reflection pairs. -/
def thirdStageTwelveForm (α β χ : ℝ) (x : Fin 12 → ℝ) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 +
    x 6 ^ 2 + x 7 ^ 2 + x 8 ^ 2 + x 9 ^ 2 + x 10 ^ 2 + x 11 ^ 2 +
    2 * α * (x 0 * x 1 + x 1 * x 2 + x 6 * x 7 + x 7 * x 8 +
      x 3 * x 9 + x 4 * x 5 + x 10 * x 11) +
    2 * β * (x 0 * x 3 + x 2 * x 4 + x 6 * x 9 + x 8 * x 10) +
    2 * χ * (x 0 * x 2 + x 6 * x 8)

theorem thirdStageTwelveForm_vec (α β χ a b c d e f g h i j k l : ℝ) :
    thirdStageTwelveForm α β χ ![a, b, c, d, e, f, g, h, i, j, k, l] =
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 +
        g ^ 2 + h ^ 2 + i ^ 2 + j ^ 2 + k ^ 2 + l ^ 2 +
        2 * α * (a * b + b * c + g * h + h * i + d * j + e * f + k * l) +
        2 * β * (a * d + c * e + g * j + i * k) + 2 * χ * (a * c + g * i) := rfl

private def thirdStageOddSix (α β χ : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + (1 - α) * x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 +
    2 * α * (x 0 * x 1 + x 1 * x 2 + x 4 * x 5) +
    2 * β * (x 0 * x 3 + x 2 * x 4) + 2 * χ * x 0 * x 2

private theorem thirdStageOddSix_vec (α β χ a b c d e f : ℝ) :
    thirdStageOddSix α β χ ![a, b, c, d, e, f] =
      a ^ 2 + b ^ 2 + c ^ 2 + (1 - α) * d ^ 2 + e ^ 2 + f ^ 2 +
        2 * α * (a * b + b * c + e * f) + 2 * β * (a * d + c * e) +
        2 * χ * a * c := rfl

private theorem thirdStageTwelveForm_reflection (α β χ : ℝ) (x : Fin 12 → ℝ) :
    thirdStageTwelveForm α β χ x =
      2 * thirdStageOddSix α β χ
        ![(x 0 - x 6) / 2, (x 1 - x 7) / 2, (x 2 - x 8) / 2,
          (x 3 - x 9) / 2, (x 4 - x 10) / 2, (x 5 - x 11) / 2] +
      2 * thirdStageOddSix α β χ
        ![(x 0 + x 6) / 2, (x 1 + x 7) / 2, (x 2 + x 8) / 2,
          (x 3 + x 9) / 2, (x 4 + x 10) / 2, (x 5 + x 11) / 2] +
      4 * α * ((x 3 + x 9) / 2) ^ 2 := by
  rw [thirdStageOddSix_vec, thirdStageOddSix_vec]
  unfold thirdStageTwelveForm
  ring

private theorem thirdStageTwelveForm_nonneg_iff_odd {α β χ : ℝ} (hα : 0 ≤ α) :
    (∀ x, 0 ≤ thirdStageTwelveForm α β χ x) ↔
      ∀ x, 0 ≤ thirdStageOddSix α β χ x := by
  constructor
  · intro h x
    have hx := h ![x 0, x 1, x 2, x 3, x 4, x 5,
      -x 0, -x 1, -x 2, -x 3, -x 4, -x 5]
    have he : thirdStageTwelveForm α β χ
        ![x 0, x 1, x 2, x 3, x 4, x 5, -x 0, -x 1, -x 2, -x 3, -x 4, -x 5] =
        2 * thirdStageOddSix α β χ x := by
      rw [thirdStageTwelveForm_vec]
      unfold thirdStageOddSix
      ring
    rw [he] at hx
    linarith only [hx]
  · intro h x
    rw [thirdStageTwelveForm_reflection]
    exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (h _))
      (mul_nonneg (by norm_num) (h _)))
      (mul_nonneg (mul_nonneg (by norm_num) hα) (sq_nonneg _))

/-- Left diagonal of the final two-variable Schur complement. -/
def thirdStageLateLeft (α β : ℝ) : ℝ := 1 - α ^ 2 - β ^ 2 / (1 - α)

/-- Right diagonal of the final two-variable Schur complement. -/
def thirdStageLateRight (α β : ℝ) : ℝ := 1 - α ^ 2 - β ^ 2 / (1 - α ^ 2)

private theorem thirdStageOddSix_complete_squares {α : ℝ}
    (hp : 1 - α ≠ 0) (hd : 1 - α ^ 2 ≠ 0) (β χ : ℝ) (x : Fin 6 → ℝ) :
    thirdStageOddSix α β χ x =
      (x 1 + α * (x 0 + x 2)) ^ 2 + (x 5 + α * x 4) ^ 2 +
      (1 - α) * (x 3 + β * x 0 / (1 - α)) ^ 2 +
      (1 - α ^ 2) * (x 4 + β * x 2 / (1 - α ^ 2)) ^ 2 +
      thirdStageLateLeft α β * x 0 ^ 2 +
      2 * (χ - α ^ 2) * x 0 * x 2 + thirdStageLateRight α β * x 2 ^ 2 := by
  have h1 : (1 - α) * (x 3 + β * x 0 / (1 - α)) ^ 2 =
      (1 - α) * x 3 ^ 2 + 2 * β * x 0 * x 3 + β ^ 2 / (1 - α) * x 0 ^ 2 := by
    field_simp [hp]
    ring
  have h2 : (1 - α ^ 2) * (x 4 + β * x 2 / (1 - α ^ 2)) ^ 2 =
      (1 - α ^ 2) * x 4 ^ 2 + 2 * β * x 2 * x 4 +
        β ^ 2 / (1 - α ^ 2) * x 2 ^ 2 := by
    field_simp [hd]
    ring
  rw [h1, h2]
  unfold thirdStageOddSix thirdStageLateLeft thirdStageLateRight
  ring

/-- Nonnegativity of a real binary form is equivalent to its two diagonal
conditions and the determinant condition, including singular diagonals. -/
theorem twoVariableForm_nonneg_iff {u z v : ℝ} :
    (∀ a c : ℝ, 0 ≤ u * a ^ 2 + 2 * z * a * c + v * c ^ 2) ↔
      0 ≤ u ∧ 0 ≤ v ∧ z ^ 2 ≤ u * v := by
  constructor
  · intro h
    have hu : 0 ≤ u := by simpa using h 1 0
    have hv : 0 ≤ v := by simpa using h 0 1
    refine ⟨hu, hv, ?_⟩
    rcases eq_or_lt_of_le hu with hu0 | hu0
    · have hx := h (-(v + 1)) z
      have hz : z = 0 := by
        rw [← hu0] at hx
        nlinarith only [hx, sq_nonneg z, mul_nonneg hv (sq_nonneg z)]
      simp only [hz, zero_pow two_ne_zero, ← hu0, zero_mul, le_refl]
    · have hx := h (-z) u
      have he : u * (-z) ^ 2 + 2 * z * (-z) * u + v * u ^ 2 =
          u * (u * v - z ^ 2) := by ring
      rw [he] at hx
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hu0).mp hx)
  · rintro ⟨hu, hv, hz⟩ a c
    exact ArithmeticCastelnuovoSeveri.quad_nonneg_of_psd hu hv hz a c

private theorem thirdStageOddSix_nonneg_iff {α β χ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∀ x, 0 ≤ thirdStageOddSix α β χ x) ↔
      0 ≤ thirdStageLateLeft α β ∧
        (χ - α ^ 2) ^ 2 ≤ thirdStageLateLeft α β * thirdStageLateRight α β := by
  have hp : 0 < 1 - α := sub_pos.mpr hα1
  have hd : 0 < 1 - α ^ 2 := by
    have hh : 0 < (1 - α) * (1 + α) := mul_pos hp (by linarith only [hα0])
    nlinarith only [hh]
  have hpd : 1 - α ≤ 1 - α ^ 2 := by
    have hh := mul_nonneg hα0 (sub_nonneg.mpr hα1.le)
    nlinarith only [hh]
  have huv : thirdStageLateLeft α β ≤ thirdStageLateRight α β := by
    have hh := div_le_div_of_nonneg_left (sq_nonneg β) hp hpd
    dsimp only [thirdStageLateLeft, thirdStageLateRight]
    linarith only [hh]
  constructor
  · intro h
    have hb : ∀ a c : ℝ, 0 ≤ thirdStageLateLeft α β * a ^ 2 +
        2 * (χ - α ^ 2) * a * c + thirdStageLateRight α β * c ^ 2 := by
      intro a c
      have hx := h ![a, -α * (a + c), c, -β * a / (1 - α),
        -β * c / (1 - α ^ 2), α * β * c / (1 - α ^ 2)]
      rw [thirdStageOddSix_complete_squares hp.ne' hd.ne'] at hx
      change 0 ≤ (-α * (a + c) + α * (a + c)) ^ 2 +
        (α * β * c / (1 - α ^ 2) + α * (-β * c / (1 - α ^ 2))) ^ 2 +
        (1 - α) * (-β * a / (1 - α) + β * a / (1 - α)) ^ 2 +
        (1 - α ^ 2) * (-β * c / (1 - α ^ 2) + β * c / (1 - α ^ 2)) ^ 2 +
        thirdStageLateLeft α β * a ^ 2 + 2 * (χ - α ^ 2) * a * c +
        thirdStageLateRight α β * c ^ 2 at hx
      ring_nf at hx ⊢
      exact hx
    have hh := twoVariableForm_nonneg_iff.mp hb
    exact ⟨hh.1, hh.2.2⟩
  · rintro ⟨hu, hz⟩ x
    have hq := ArithmeticCastelnuovoSeveri.quad_nonneg_of_psd hu (hu.trans huv) hz (x 0) (x 2)
    rw [thirdStageOddSix_complete_squares hp.ne' hd.ne']
    have h1 := sq_nonneg (x 1 + α * (x 0 + x 2))
    have h2 := sq_nonneg (x 5 + α * x 4)
    have h3 := mul_nonneg hp.le (sq_nonneg (x 3 + β * x 0 / (1 - α)))
    have h4 := mul_nonneg hd.le (sq_nonneg (x 4 + β * x 2 / (1 - α ^ 2)))
    linarith only [h1, h2, h3, h4, hq]

/-- For nonnegative ratio-two weight below one, the odd Schur complement
decides positivity of the twelve-vertex form. -/
theorem thirdStageTwelveForm_nonneg_iff {α β χ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∀ x, 0 ≤ thirdStageTwelveForm α β χ x) ↔
      0 ≤ thirdStageLateLeft α β ∧
        (χ - α ^ 2) ^ 2 ≤ thirdStageLateLeft α β * thirdStageLateRight α β :=
  (thirdStageTwelveForm_nonneg_iff_odd hα0).trans
    (thirdStageOddSix_nonneg_iff hα0 hα1)

/-- Every vertex lies between one and the new extremal ratio `9/2`. -/
theorem thirdStageLateNodes_bounds {r : ℚ} (hr : r ∈ thirdStageLateNodes) :
    1 ≤ r ∧ r ≤ 9 / 2 := by
  norm_num only [thirdStageLateNodes, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

private theorem thirdStage_late_edges_two (y : ℚ → ℝ) :
    (∑ r ∈ thirdStageLateNodes, if (2 : ℚ) * r ∈ thirdStageLateNodes then
      y r * y (2 * r) else 0) =
      y 1 * y 2 + y 2 * y 4 + y (9 / 2) * y (9 / 4) + y (9 / 4) * y (9 / 8) +
        y 3 * y (3 / 2) + y (4 / 3) * y (8 / 3) + y (27 / 8) * y (27 / 16) := by
  norm_num [thirdStageLateNodes]
  ring

private theorem thirdStage_late_edges_three (y : ℚ → ℝ) :
    (∑ r ∈ thirdStageLateNodes, if (3 : ℚ) * r ∈ thirdStageLateNodes then
      y r * y (3 * r) else 0) =
      y 1 * y 3 + y 4 * y (4 / 3) + y (9 / 2) * y (3 / 2) + y (9 / 8) * y (27 / 8) := by
  norm_num [thirdStageLateNodes]
  ring

private theorem thirdStage_late_edges_four (y : ℚ → ℝ) :
    (∑ r ∈ thirdStageLateNodes, if (4 : ℚ) * r ∈ thirdStageLateNodes then
      y r * y (4 * r) else 0) = y 1 * y 4 + y (9 / 2) * y (9 / 8) := by
  norm_num [thirdStageLateNodes]
  ring

/-- The rational template has exactly the edges in the twelve-variable form. -/
theorem thirdStage_late_graph_form (α β χ : ℝ) (y : ℚ → ℝ) :
    rationalHeckeForm 4 (thirdStageCoefficients α β χ) thirdStageLateNodes y =
      thirdStageTwelveForm α β χ
        ![y 1, y 2, y 4, y 3, y (4 / 3), y (8 / 3),
          y (9 / 2), y (9 / 4), y (9 / 8), y (3 / 2), y (27 / 8), y (27 / 16)] := by
  classical
  have hIcc : Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [rationalHeckeForm_eq_neighbor_sum, hIcc]
  norm_num [thirdStageCoefficients]
  rw [thirdStage_late_edges_two, thirdStage_late_edges_three, thirdStage_late_edges_four]
  rw [thirdStageTwelveForm_vec]
  norm_num [thirdStageLateNodes]
  ring

/-- Prescribed amplitudes on the twelve ordered vertices, extended by zero. -/
def thirdStageLateAmplitude (x : Fin 12 → ℝ) (r : ℚ) : ℝ :=
  if r = 1 then x 0 else if r = 2 then x 1 else if r = 4 then x 2 else
    if r = 3 then x 3 else if r = 4 / 3 then x 4 else if r = 8 / 3 then x 5 else
      if r = 9 / 2 then x 6 else if r = 9 / 4 then x 7 else if r = 9 / 8 then x 8 else
        if r = 3 / 2 then x 9 else if r = 27 / 8 then x 10 else
          if r = 27 / 16 then x 11 else 0

theorem thirdStageLateAmplitude_vec (x : Fin 12 → ℝ) :
    ![thirdStageLateAmplitude x 1, thirdStageLateAmplitude x 2,
      thirdStageLateAmplitude x 4, thirdStageLateAmplitude x 3,
      thirdStageLateAmplitude x (4 / 3), thirdStageLateAmplitude x (8 / 3),
      thirdStageLateAmplitude x (9 / 2), thirdStageLateAmplitude x (9 / 4),
      thirdStageLateAmplitude x (9 / 8), thirdStageLateAmplitude x (3 / 2),
      thirdStageLateAmplitude x (27 / 8), thirdStageLateAmplitude x (27 / 16)] = x := by
  funext i
  fin_cases i <;> norm_num [thirdStageLateAmplitude, Matrix.cons_val] <;> rfl

private theorem thirdStage_late_graph_nonneg_iff (α β χ : ℝ) :
    (∀ y : ℚ → ℝ,
      0 ≤ rationalHeckeForm 4 (thirdStageCoefficients α β χ) thirdStageLateNodes y) ↔
      ∀ x, 0 ≤ thirdStageTwelveForm α β χ x := by
  constructor
  · intro h x
    have hx := h (thirdStageLateAmplitude x)
    rw [thirdStage_late_graph_form] at hx
    rwa [thirdStageLateAmplitude_vec] at hx
  · intro h y
    rw [thirdStage_late_graph_form]
    exact h _

private theorem rationalHeckePositive_late_thirdStage_iff {A α β χ : ℝ}
    (hA9 : Real.log (9 / 2) < A) (hA5 : A ≤ Real.log 5) :
    RationalHeckePositive A 4 (thirdStageCoefficients α β χ) ↔
      ∀ x, 0 ≤ thirdStageTwelveForm α β χ x := by
  constructor
  · intro h
    apply (thirdStage_late_graph_nonneg_iff α β χ).mp
    apply h thirdStageLateNodes
    · intro r hr
      exact lt_of_lt_of_le (by norm_num) (thirdStageLateNodes_bounds hr).1
    · intro r hr s hs
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (thirdStageLateNodes_bounds hr).1
      have hs0 : (0 : ℝ) < s := by
        exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1)
          (thirdStageLateNodes_bounds hs).1
      have hs9Q : (2 : ℚ) * s ≤ 9 := by
        linarith only [(thirdStageLateNodes_bounds hs).2]
      have hs9R : (2 : ℝ) * s ≤ 9 := by exact_mod_cast hs9Q
      have hs9 : (s : ℝ) ≤ 9 / 2 := by linarith only [hs9R]
      have hlogr := Real.log_nonneg hr1
      have hlogs := Real.log_le_log hs0 hs9
      linarith only [hA9, hlogr, hlogs]
  · intro h S hpos hspread y
    apply rationalHeckeForm_nonneg_of_closed_template 4 (thirdStageCoefficients α β χ)
      thirdStageLateNodes 5 (by norm_num [thirdStageLateNodes])
      (fun n hn q hq s hlo hhi hrel =>
        thirdStageLateNodes_closed hq hn hlo (by linarith only [hhi]) hrel)
      ((thirdStage_late_graph_nonneg_iff α β χ).mpr h) S hpos ?_ y
    intro r hr s hs
    by_contra hsr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hpos r hr
    have hle : (5 : ℝ) * r ≤ s := by exact_mod_cast le_of_not_gt hsr
    have hl := Real.log_le_log (mul_pos (by norm_num) hr0) hle
    rw [Real.log_mul (by norm_num) hr0.ne'] at hl
    linarith only [hspread r hr s hs, hA5, hl]

private theorem tateFunction_thirdStage_through_five {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (hA4 : Real.log 4 < A) (hA5 : A ≤ Real.log 5) (k : ℝ) :
    tateFunction A H k = (∫ u, H u ^ 2) + ∑ n ∈ Finset.Icc 2 4,
      thirdStageCoefficients (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k) n *
        ∫ u, H u * H (u + Real.log n) := by
  rcases lt_or_eq_of_le hA5 with hlt | rfl
  · have hlev : windowLevel A = 4 := by
      rw [windowLevel, Nat.floor_eq_iff (Real.exp_pos A).le]
      constructor
      · have h := Real.exp_le_exp.mpr hA4.le
        rw [Real.exp_log (by norm_num)] at h
        norm_num
        exact h
      · have h := Real.exp_lt_exp.mpr hlt
        rw [Real.exp_log (by norm_num)] at h
        norm_num
        exact h
    exact tateFunction_thirdStage hH hlev k
  · have hlev : windowLevel (Real.log 5) = 5 := by
      norm_num [windowLevel, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
    have hz : (∫ u, H u * H (u + Real.log 5)) = 0 := by
      rw [← integral_windowShift_mul hH.vanish,
        windowShift_eq_zero_of_length_le hH.continuous hH.vanish le_rfl]
      simp only [Pi.zero_apply, zero_mul, integral_zero]
    have hIcc : Finset.Icc 1 5 = insert 5 (Finset.Icc 1 4) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [tateFunction_eq hH, hlev, hIcc, Finset.sum_insert (by norm_num),
      Nat.cast_ofNat, hz, mul_zero, zero_add, thirdStage_sum_eq_form]

private theorem thirdStageAlpha_lt_one_of_chi_le_one {k : ℝ} (hk : 0 ≤ k)
    (hχ : thirdStageChi k ≤ 1) : thirdStageAlpha k < 1 := by
  have h2 := two_mul_thirdStageAlpha_sq_le_chi hk
  by_contra h
  have ha := le_of_not_gt h
  nlinarith only [h2, hχ, ha, sq_nonneg (thirdStageAlpha k - 1)]

/-- The exact Tate horizon on the second part of stage three, including the
ratio-five endpoint where the new correlation still vanishes. -/
theorem tateFunction_nonneg_iff_thirdStage_afterNineHalves {A k : ℝ}
    (hA9 : Real.log (9 / 2) < A) (hA5 : A ≤ Real.log 5) (hk : 0 ≤ k) :
    (∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k) ↔
      thirdStageChi k ≤ 1 ∧
        0 ≤ thirdStageLateLeft (thirdStageAlpha k) (thirdStageBeta k) ∧
        (thirdStageChi k - thirdStageAlpha k ^ 2) ^ 2 ≤
          thirdStageLateLeft (thirdStageAlpha k) (thirdStageBeta k) *
            thirdStageLateRight (thirdStageAlpha k) (thirdStageBeta k) := by
  have hA4 : Real.log 4 < A :=
    (Real.log_lt_log (by norm_num) (by norm_num : (4 : ℝ) < 9 / 2)).trans hA9
  have hα0 := thirdStageAlpha_nonneg hk
  have hbridge : (∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k) ↔
      ∀ x, 0 ≤ thirdStageTwelveForm (thirdStageAlpha k) (thirdStageBeta k)
        (thirdStageChi k) x := by
    have hw := windowForm_nonneg_iff_rationalHeckePositive A 4
      (thirdStageCoefficients (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k))
    have hg := rationalHeckePositive_late_thirdStage_iff
      (α := thirdStageAlpha k) (β := thirdStageBeta k) (χ := thirdStageChi k) hA9 hA5
    constructor
    · intro h
      apply hg.mp
      apply hw.mp
      intro H hH
      rw [← tateFunction_thirdStage_through_five hH hA4 hA5 k]
      exact h H hH
    · intro h H hH
      have hh := hw.mpr (hg.mpr h) H hH
      rwa [← tateFunction_thirdStage_through_five hH hA4 hA5 k] at hh
  rw [hbridge]
  constructor
  · intro h
    have hχ : thirdStageChi k ≤ 1 := by
      have hx := h ![1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      rw [thirdStageTwelveForm_vec] at hx
      norm_num at hx
      linarith only [hx]
    exact ⟨hχ, (thirdStageTwelveForm_nonneg_iff hα0
      (thirdStageAlpha_lt_one_of_chi_le_one hk hχ)).mp h⟩
  · rintro ⟨hχ, h⟩
    exact (thirdStageTwelveForm_nonneg_iff hα0
      (thirdStageAlpha_lt_one_of_chi_le_one hk hχ)).mpr h

#print axioms thirdStageLateNodes_closed
#print axioms thirdStageTwelveForm_nonneg_iff
#print axioms tateFunction_nonneg_iff_thirdStage_afterNineHalves

end GaloisForLFunctions.WindowTowerOfSpecZ
