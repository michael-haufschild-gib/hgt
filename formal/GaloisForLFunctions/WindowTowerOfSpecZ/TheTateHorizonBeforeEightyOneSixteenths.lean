import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateHorizonAfterNineHalves

/-!
# The Tate horizon just above ratio five

Two reflected twelve-vertex graphs are joined by one ratio-five edge.
The odd block controls positivity. Eliminating its triangle centres and
outer arms leaves a four-vertex path with five strict Schur pivots.
-/

noncomputable section

open Finset MeasureTheory

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory

/-- Two reflected copies of the twelve-vertex template, joined at ratio five. -/
def fourthStageNodes : Finset ℚ :=
  {1, 2, 4, 3, 4 / 3, 8 / 3, 9 / 2, 9 / 4, 9 / 8, 3 / 2, 27 / 8, 27 / 16,
    5, 5 / 2, 5 / 4, 5 / 3, 15 / 4, 15 / 8, 10 / 9, 20 / 9, 40 / 9,
    10 / 3, 40 / 27, 80 / 27}

private theorem fourthStageNodes_mul_2 {q : ℚ}
    (hq : q ∈ fourthStageNodes) (hhi : 2 * q < 81 / 16) :
    2 * q ∈ fourthStageNodes := by
  norm_num only [fourthStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hhi
  all_goals norm_num [fourthStageNodes]

private theorem fourthStageNodes_div_2 {q : ℚ}
    (hq : q ∈ fourthStageNodes) (hlo : 1 ≤ q / 2) :
    q / 2 ∈ fourthStageNodes := by
  norm_num only [fourthStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hlo
  all_goals norm_num [fourthStageNodes]

private theorem fourthStageNodes_mul_3 {q : ℚ}
    (hq : q ∈ fourthStageNodes) (hhi : 3 * q < 81 / 16) :
    3 * q ∈ fourthStageNodes := by
  norm_num only [fourthStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hhi
  all_goals norm_num [fourthStageNodes]

private theorem fourthStageNodes_div_3 {q : ℚ}
    (hq : q ∈ fourthStageNodes) (hlo : 1 ≤ q / 3) :
    q / 3 ∈ fourthStageNodes := by
  norm_num only [fourthStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hlo
  all_goals norm_num [fourthStageNodes]

private theorem fourthStageNodes_mul_4 {q : ℚ}
    (hq : q ∈ fourthStageNodes) (hhi : 4 * q < 81 / 16) :
    4 * q ∈ fourthStageNodes := by
  norm_num only [fourthStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hhi
  all_goals norm_num [fourthStageNodes]

private theorem fourthStageNodes_div_4 {q : ℚ}
    (hq : q ∈ fourthStageNodes) (hlo : 1 ≤ q / 4) :
    q / 4 ∈ fourthStageNodes := by
  norm_num only [fourthStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hlo
  all_goals norm_num [fourthStageNodes]

private theorem fourthStageNodes_mul_5 {q : ℚ}
    (hq : q ∈ fourthStageNodes) (hhi : 5 * q < 81 / 16) :
    5 * q ∈ fourthStageNodes := by
  norm_num only [fourthStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hhi
  all_goals norm_num [fourthStageNodes]

private theorem fourthStageNodes_div_5 {q : ℚ}
    (hq : q ∈ fourthStageNodes) (hlo : 1 ≤ q / 5) :
    q / 5 ∈ fourthStageNodes := by
  norm_num only [fourthStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hlo
  all_goals norm_num [fourthStageNodes]

/-- Every ratio-two through ratio-five neighbor below `81/16` stays in the template. -/
theorem fourthStageNodes_closed {q s : ℚ} {n : ℕ}
    (hq : q ∈ fourthStageNodes) (hn : n ∈ Finset.Icc 2 5)
    (hlo : 1 ≤ s) (hhi : s < 81 / 16)
    (hrel : s = n * q ∨ q = n * s) : s ∈ fourthStageNodes := by
  obtain ⟨hn2, hn5⟩ := Finset.mem_Icc.mp hn
  rcases hrel with rfl | hrel
  · interval_cases n
    · exact fourthStageNodes_mul_2 hq hhi
    · exact fourthStageNodes_mul_3 hq hhi
    · exact fourthStageNodes_mul_4 hq hhi
    · exact fourthStageNodes_mul_5 hq hhi
  · have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hs : s = q / n := (eq_div_iff hn0).mpr (by linarith only [hrel])
    rw [hs] at hlo ⊢
    interval_cases n
    · exact fourthStageNodes_div_2 hq hlo
    · exact fourthStageNodes_div_3 hq hlo
    · exact fourthStageNodes_div_4 hq hlo
    · exact fourthStageNodes_div_5 hq hlo

/-- The ratio-five edge joins the distinguished vertices of two identical blocks. -/
def fourthStageDoubleForm (α β χ δ : ℝ) (x y : Fin 12 → ℝ) : ℝ :=
  thirdStageTwelveForm α β χ x + thirdStageTwelveForm α β χ y + 2 * δ * x 0 * y 0

/-- The odd block loses the ratio-five weight at its distinguished vertex. -/
def fourthStageRootForm (α β χ δ : ℝ) (x : Fin 12 → ℝ) : ℝ :=
  thirdStageTwelveForm α β χ x - δ * x 0 ^ 2

private theorem fourthStageDoubleForm_reflection (α β χ δ : ℝ) (x y : Fin 12 → ℝ) :
    fourthStageDoubleForm α β χ δ x y =
      2 * fourthStageRootForm α β χ δ (fun i => (x i - y i) / 2) +
      2 * fourthStageRootForm α β χ δ (fun i => (x i + y i) / 2) +
      4 * δ * ((x 0 + y 0) / 2) ^ 2 := by
  unfold fourthStageDoubleForm fourthStageRootForm thirdStageTwelveForm
  ring

/-- Reflection makes the odd twelve-dimensional block decisive. -/
theorem fourthStageDoubleForm_nonneg_iff {α β χ δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x y, 0 ≤ fourthStageDoubleForm α β χ δ x y) ↔
      ∀ x, 0 ≤ fourthStageRootForm α β χ δ x := by
  constructor
  · intro h x
    have hx := h x (fun i => -x i)
    have he : fourthStageDoubleForm α β χ δ x (fun i => -x i) =
        2 * fourthStageRootForm α β χ δ x := by
      unfold fourthStageDoubleForm fourthStageRootForm thirdStageTwelveForm
      ring
    rw [he] at hx
    linarith only [hx]
  · intro h x y
    rw [fourthStageDoubleForm_reflection]
    exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (h _))
      (mul_nonneg (by norm_num) (h _)))
      (mul_nonneg (mul_nonneg (by norm_num) hδ) (sq_nonneg _))

/-- The common diagonal after eliminating the two triangle centres. -/
def fourthStageD (α : ℝ) : ℝ := 1 - α ^ 2

/-- The outer endpoint diagonal after eliminating its attached arm. -/
def fourthStageV (α β : ℝ) : ℝ := fourthStageD α - β ^ 2 / fourthStageD α

/-- Each end diagonal of the remaining four-vertex path. -/
def fourthStageW (α β χ : ℝ) : ℝ :=
  fourthStageD α - (χ - α ^ 2) ^ 2 / fourthStageV α β

/-- The first interior pivot, eliminating the right endpoint. -/
def fourthStageP (α β χ : ℝ) : ℝ := 1 - β ^ 2 / fourthStageW α β χ

/-- The second interior pivot. -/
def fourthStageQ (α β χ : ℝ) : ℝ := 1 - α ^ 2 / fourthStageP α β χ

private theorem pos_left_of_binary_nonneg {u z v : ℝ} (hz : z ≠ 0)
    (h : ∀ a c : ℝ, 0 ≤ u * a ^ 2 + 2 * z * a * c + v * c ^ 2) : 0 < u := by
  obtain ⟨hu, _, hd⟩ := twoVariableForm_nonneg_iff.mp h
  by_contra hnot
  have hu0 : u = 0 := le_antisymm (le_of_not_gt hnot) hu
  rw [hu0, zero_mul] at hd
  have hz0 : z = 0 := by nlinarith only [hd, sq_nonneg z]
  exact hz hz0

private theorem weighted_square {d : ℝ} (hd : d ≠ 0) (x z : ℝ) :
    d * (x + z / d) ^ 2 = d * x ^ 2 + 2 * z * x + z ^ 2 / d := by
  field_simp [hd]
  ring

private theorem weighted_cancel {d : ℝ} (hd : d ≠ 0) (z x : ℝ) :
    d * (-z * x / d) ^ 2 + 2 * z * x * (-z * x / d) + z ^ 2 / d * x ^ 2 = 0 := by
  field_simp [hd]
  ring

/-- After removing the triangle centres and outer arms, four vertices form a path. -/
def fourthStagePathForm (α β w δ a b c d : ℝ) : ℝ :=
  (w - δ) * a ^ 2 + b ^ 2 + c ^ 2 + w * d ^ 2 +
    2 * β * (a * b + c * d) + 2 * α * b * c

private theorem fourthStageRootForm_complete_squares {α β χ δ : ℝ}
    (hD : fourthStageD α ≠ 0) (hV : fourthStageV α β ≠ 0) (x : Fin 12 → ℝ) :
    fourthStageRootForm α β χ δ x =
      (x 1 + α * (x 0 + x 2)) ^ 2 + (x 7 + α * (x 6 + x 8)) ^ 2 +
      (x 5 + α * x 4) ^ 2 + (x 11 + α * x 10) ^ 2 +
      fourthStageD α * (x 4 + β * x 2 / fourthStageD α) ^ 2 +
      fourthStageD α * (x 10 + β * x 8 / fourthStageD α) ^ 2 +
      fourthStageV α β * (x 2 + (χ - α ^ 2) * x 0 / fourthStageV α β) ^ 2 +
      fourthStageV α β * (x 8 + (χ - α ^ 2) * x 6 / fourthStageV α β) ^ 2 +
      fourthStagePathForm α β (fourthStageW α β χ) δ (x 0) (x 3) (x 9) (x 6) := by
  rw [weighted_square hD, weighted_square hD,
    weighted_square hV, weighted_square hV]
  unfold fourthStageRootForm thirdStageTwelveForm fourthStagePathForm
    fourthStageW fourthStageV fourthStageD
  ring

private theorem fourthStagePathForm_complete_squares {α β w δ : ℝ}
    (hw : w ≠ 0) (hp : 1 - β ^ 2 / w ≠ 0)
    (hq : 1 - α ^ 2 / (1 - β ^ 2 / w) ≠ 0) (a b c d : ℝ) :
    fourthStagePathForm α β w δ a b c d =
      w * (d + β * c / w) ^ 2 +
      (1 - β ^ 2 / w) * (c + α * b / (1 - β ^ 2 / w)) ^ 2 +
      (1 - α ^ 2 / (1 - β ^ 2 / w)) *
        (b + β * a / (1 - α ^ 2 / (1 - β ^ 2 / w))) ^ 2 +
      (w - δ - β ^ 2 / (1 - α ^ 2 / (1 - β ^ 2 / w))) * a ^ 2 := by
  rw [weighted_square hw, weighted_square hp, weighted_square hq]
  unfold fourthStagePathForm
  ring

private theorem fourthStagePathForm_nonneg_iff {α β w δ : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∀ a b c d, 0 ≤ fourthStagePathForm α β w δ a b c d) ↔
      0 < w ∧ 0 < 1 - β ^ 2 / w ∧
        0 < 1 - α ^ 2 / (1 - β ^ 2 / w) ∧
        0 ≤ w - δ - β ^ 2 / (1 - α ^ 2 / (1 - β ^ 2 / w)) := by
  constructor
  · intro h
    have hw : 0 < w := by
      apply pos_left_of_binary_nonneg (v := 1) hβ
      intro d c
      have hh := h 0 0 c d
      dsimp only [fourthStagePathForm] at hh
      nlinarith only [hh]
    have h3 (a b c : ℝ) :
        0 ≤ (w - δ) * a ^ 2 + b ^ 2 + (1 - β ^ 2 / w) * c ^ 2 +
          2 * β * a * b + 2 * α * b * c := by
      have hh := h a b c (-β * c / w)
      have hc := weighted_cancel hw.ne' β c
      dsimp only [fourthStagePathForm] at hh
      nlinarith only [hh, hc]
    have hp : 0 < 1 - β ^ 2 / w := by
      apply pos_left_of_binary_nonneg (v := 1) hα
      intro c b
      have hh := h3 0 b c
      nlinarith only [hh]
    have h2 (a b : ℝ) : 0 ≤ (w - δ) * a ^ 2 +
        (1 - α ^ 2 / (1 - β ^ 2 / w)) * b ^ 2 + 2 * β * a * b := by
      have hh := h3 a b (-α * b / (1 - β ^ 2 / w))
      have hc := weighted_cancel hp.ne' α b
      nlinarith only [hh, hc]
    have hq : 0 < 1 - α ^ 2 / (1 - β ^ 2 / w) := by
      apply pos_left_of_binary_nonneg (v := w - δ) hβ
      intro b a
      have hh := h2 a b
      nlinarith only [hh]
    refine ⟨hw, hp, hq, ?_⟩
    have hh := h2 1 (-β / (1 - α ^ 2 / (1 - β ^ 2 / w)))
    have hc := weighted_cancel hq.ne' β 1
    norm_num only [mul_one, one_pow] at hh hc
    nlinarith only [hh, hc]
  · rintro ⟨hw, hp, hq, hr⟩ a b c d
    rw [fourthStagePathForm_complete_squares hw.ne' hp.ne' hq.ne']
    exact add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg hw.le (sq_nonneg _)) (mul_nonneg hp.le (sq_nonneg _)))
      (mul_nonneg hq.le (sq_nonneg _))) (mul_nonneg hr (sq_nonneg _))

private theorem fourthStageD_pos_of_root_nonneg {α β χ δ : ℝ} (hβ : β ≠ 0)
    (h : ∀ x, 0 ≤ fourthStageRootForm α β χ δ x) : 0 < fourthStageD α := by
  apply pos_left_of_binary_nonneg (v := 1) hβ
  intro a c
  have hh := h ![0, 0, c, 0, a, -α * a, 0, 0, 0, 0, 0, 0]
  unfold fourthStageRootForm at hh
  rw [thirdStageTwelveForm_vec] at hh
  simp only [Matrix.cons_val_zero] at hh
  change 0 ≤ fourthStageD α * a ^ 2 + 2 * β * a * c + 1 * c ^ 2
  unfold fourthStageD
  nlinarith only [hh]

private theorem fourthStageV_pos_of_root_nonneg {α β χ δ : ℝ}
    (hz : χ - α ^ 2 ≠ 0) (hD : fourthStageD α ≠ 0)
    (h : ∀ x, 0 ≤ fourthStageRootForm α β χ δ x) : 0 < fourthStageV α β := by
  apply pos_left_of_binary_nonneg (v := fourthStageD α - δ) hz
  intro a c
  have hh := h ![c, -α * (c + a), a, 0, -β * a / fourthStageD α,
    -α * (-β * a / fourthStageD α), 0, 0, 0, 0, 0, 0]
  have he : fourthStageRootForm α β χ δ
      ![c, -α * (c + a), a, 0, -β * a / fourthStageD α,
        -α * (-β * a / fourthStageD α), 0, 0, 0, 0, 0, 0] =
      fourthStageV α β * a ^ 2 + 2 * (χ - α ^ 2) * a * c +
        (fourthStageD α - δ) * c ^ 2 := by
    unfold fourthStageRootForm
    rw [thirdStageTwelveForm_vec]
    change _ - δ * c ^ 2 = _
    unfold fourthStageV
    have hDn : 1 - α ^ 2 ≠ 0 := hD
    unfold fourthStageD
    field_simp [hDn]
    ring
  rwa [he] at hh

private theorem fourthStageRootForm_nonneg_iff_path {α β χ δ : ℝ}
    (hD : 0 < fourthStageD α) (hV : 0 < fourthStageV α β) :
    (∀ x, 0 ≤ fourthStageRootForm α β χ δ x) ↔
      ∀ a b c d, 0 ≤ fourthStagePathForm α β (fourthStageW α β χ) δ a b c d := by
  constructor
  · intro h a b c d
    have hh := h ![a, -α * (a - (χ - α ^ 2) * a / fourthStageV α β),
      -(χ - α ^ 2) * a / fourthStageV α β, b,
      -β * (-(χ - α ^ 2) * a / fourthStageV α β) / fourthStageD α,
      -α * (-β * (-(χ - α ^ 2) * a / fourthStageV α β) / fourthStageD α),
      d, -α * (d - (χ - α ^ 2) * d / fourthStageV α β),
      -(χ - α ^ 2) * d / fourthStageV α β, c,
      -β * (-(χ - α ^ 2) * d / fourthStageV α β) / fourthStageD α,
      -α * (-β * (-(χ - α ^ 2) * d / fourthStageV α β) / fourthStageD α)]
    rw [fourthStageRootForm_complete_squares hD.ne' hV.ne'] at hh
    change 0 ≤
      (-α * (a - (χ - α ^ 2) * a / fourthStageV α β) +
        α * (a + -(χ - α ^ 2) * a / fourthStageV α β)) ^ 2 +
      (-α * (d - (χ - α ^ 2) * d / fourthStageV α β) +
        α * (d + -(χ - α ^ 2) * d / fourthStageV α β)) ^ 2 +
      (-α * (-β * (-(χ - α ^ 2) * a / fourthStageV α β) / fourthStageD α) +
        α * (-β * (-(χ - α ^ 2) * a / fourthStageV α β) / fourthStageD α)) ^ 2 +
      (-α * (-β * (-(χ - α ^ 2) * d / fourthStageV α β) / fourthStageD α) +
        α * (-β * (-(χ - α ^ 2) * d / fourthStageV α β) / fourthStageD α)) ^ 2 +
      fourthStageD α *
        (-β * (-(χ - α ^ 2) * a / fourthStageV α β) / fourthStageD α +
          β * (-(χ - α ^ 2) * a / fourthStageV α β) / fourthStageD α) ^ 2 +
      fourthStageD α *
        (-β * (-(χ - α ^ 2) * d / fourthStageV α β) / fourthStageD α +
          β * (-(χ - α ^ 2) * d / fourthStageV α β) / fourthStageD α) ^ 2 +
      fourthStageV α β *
        (-(χ - α ^ 2) * a / fourthStageV α β +
          (χ - α ^ 2) * a / fourthStageV α β) ^ 2 +
      fourthStageV α β *
        (-(χ - α ^ 2) * d / fourthStageV α β +
          (χ - α ^ 2) * d / fourthStageV α β) ^ 2 +
      fourthStagePathForm α β (fourthStageW α β χ) δ a b c d at hh
    ring_nf at hh
    exact hh
  · intro h x
    rw [fourthStageRootForm_complete_squares hD.ne' hV.ne']
    have h1 := sq_nonneg (x 1 + α * (x 0 + x 2))
    have h2 := sq_nonneg (x 7 + α * (x 6 + x 8))
    have h3 := sq_nonneg (x 5 + α * x 4)
    have h4 := sq_nonneg (x 11 + α * x 10)
    have h5 := mul_nonneg hD.le (sq_nonneg (x 4 + β * x 2 / fourthStageD α))
    have h6 := mul_nonneg hD.le (sq_nonneg (x 10 + β * x 8 / fourthStageD α))
    have h7 := mul_nonneg hV.le
      (sq_nonneg (x 2 + (χ - α ^ 2) * x 0 / fourthStageV α β))
    have h8 := mul_nonneg hV.le
      (sq_nonneg (x 8 + (χ - α ^ 2) * x 6 / fourthStageV α β))
    linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h (x 0) (x 3) (x 9) (x 6)]

/-- The four-vertex path gives the exact successive Schur pivots. Nonzero
couplings force every eliminated pivot to be strictly positive. -/
theorem fourthStageRootForm_nonneg_iff {α β χ δ : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hz : χ - α ^ 2 ≠ 0) :
    (∀ x, 0 ≤ fourthStageRootForm α β χ δ x) ↔
      0 < fourthStageD α ∧ 0 < fourthStageV α β ∧
        0 < fourthStageW α β χ ∧ 0 < fourthStageP α β χ ∧
        0 < fourthStageQ α β χ ∧
        0 ≤ fourthStageW α β χ - δ - β ^ 2 / fourthStageQ α β χ := by
  constructor
  · intro h
    have hD := fourthStageD_pos_of_root_nonneg hβ h
    have hV := fourthStageV_pos_of_root_nonneg hz hD.ne' h
    have hp := (fourthStageRootForm_nonneg_iff_path hD hV).mp h
    exact ⟨hD, hV, (fourthStagePathForm_nonneg_iff hα hβ).mp hp⟩
  · rintro ⟨hD, hV, hp⟩
    apply (fourthStageRootForm_nonneg_iff_path hD hV).mpr
    exact (fourthStagePathForm_nonneg_iff hα hβ).mpr hp

/-- Multiplicative reflection reverses every Hecke edge and preserves its form. -/
theorem rationalHeckeForm_reciprocal (N : ℕ) (c : ℕ → ℝ)
    (T : Finset ℚ) (hT : ∀ q ∈ T, q ≠ 0) {r : ℚ} (hr : r ≠ 0) (y : ℚ → ℝ) :
    rationalHeckeForm N c (T.image fun q => r / q) y =
      rationalHeckeForm N c T (fun q => y (r / q)) := by
  classical
  have hinj : Set.InjOn (fun q : ℚ => r / q) T := by
    intro q hq s hs he
    have hh := (div_eq_div_iff (hT q hq) (hT s hs)).mp he
    exact (mul_left_cancel₀ hr hh).symm
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  unfold rationalHeckeForm
  congr 1
  · rw [Finset.sum_image hinj]
  · apply Finset.sum_congr rfl
    intro n _
    congr 1
    simp_rw [Finset.sum_image hinj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro s hs
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hT q hq
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hT s hs
    have he : ((r / q : ℚ) : ℝ) = n * ((r / s : ℚ) : ℝ) ↔
        (s : ℝ) = n * q := by
      push_cast
      rw [← mul_div_assoc, div_eq_div_iff hqR hsR]
      constructor
      · intro h
        apply mul_left_cancel₀ hrR
        calc (r : ℝ) * s = (n * r) * q := h
          _ = r * (n * q) := by ring
      · intro h
        rw [h]
        ring
    simp only [he, mul_comm]

private theorem fourthStageNodes_bounds {r : ℚ} (hr : r ∈ fourthStageNodes) :
    1 ≤ r ∧ r ≤ 5 := by
  norm_num only [fourthStageNodes, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

private theorem fourthStageNodes_eq_union : fourthStageNodes =
    thirdStageLateNodes ∪ thirdStageLateNodes.image (fun q : ℚ => 5 / q) := by
  norm_num [fourthStageNodes, thirdStageLateNodes]
  ext q
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem fourthStageNodes_disjoint : Disjoint thirdStageLateNodes
    (thirdStageLateNodes.image (fun q : ℚ => 5 / q)) := by
  norm_num [thirdStageLateNodes, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]

private theorem fourthStage_form_four_split (c : ℕ → ℝ) (y : ℚ → ℝ) :
    rationalHeckeForm 4 c fourthStageNodes y =
      rationalHeckeForm 4 c thirdStageLateNodes y +
      rationalHeckeForm 4 c thirdStageLateNodes (fun q => y (5 / q)) := by
  classical
  have hclosed : ∀ n : ℕ, n ∈ Finset.Icc 2 4 → ∀ r ∈ fourthStageNodes,
      r ∈ thirdStageLateNodes → ∀ s ∈ fourthStageNodes,
      s = (n : ℚ) * r ∨ r = (n : ℚ) * s → s ∈ thirdStageLateNodes := by
    intro n hn r _ hr s hs hrel
    exact thirdStageLateNodes_closed hr hn (fourthStageNodes_bounds hs).1
      (by linarith only [(fourthStageNodes_bounds hs).2]) hrel
  have hleft : fourthStageNodes.filter (fun q => q ∈ thirdStageLateNodes) =
      thirdStageLateNodes := by
    rw [fourthStageNodes_eq_union]
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hright : fourthStageNodes.filter (fun q => q ∉ thirdStageLateNodes) =
      thirdStageLateNodes.image (fun q : ℚ => 5 / q) := by
    rw [fourthStageNodes_eq_union]
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hq | hq, hn⟩
      · exact False.elim (hn hq)
      · exact hq
    · intro hq
      exact ⟨Or.inr hq, fun ht => Finset.disjoint_left.mp fourthStageNodes_disjoint ht hq⟩
  have ht : ∀ q ∈ thirdStageLateNodes, q ≠ 0 := fun q hq =>
    ne_of_gt (lt_of_lt_of_le (by norm_num) (thirdStageLateNodes_bounds hq).1)
  rw [rationalHeckeForm_split_closed 4 c fourthStageNodes thirdStageLateNodes y hclosed,
    hleft, hright, rationalHeckeForm_reciprocal 4 c thirdStageLateNodes ht (by norm_num) y]

private theorem fourthStage_edges_five (y : ℚ → ℝ) :
    (∑ r ∈ fourthStageNodes, if (5 : ℚ) * r ∈ fourthStageNodes then
      y r * y (5 * r) else 0) = y 1 * y 5 := by
  classical
  rw [Finset.sum_eq_single_of_mem 1 (by norm_num [fourthStageNodes])]
  · norm_num [fourthStageNodes]
  · intro q hq hq1
    have hn : (5 : ℚ) * q ∉ fourthStageNodes := by
      intro hm
      have hlo := (fourthStageNodes_bounds hq).1
      have hhi := (fourthStageNodes_bounds hm).2
      exact hq1 (by linarith only [hlo, hhi])
    rw [if_neg hn]

/-- The four active edge coefficients in the first part of stage four. -/
def fourthStageCoefficients (α β χ δ : ℝ) (n : ℕ) : ℝ :=
  if n = 5 then 2 * δ else thirdStageCoefficients α β χ n

private theorem fourthStage_form_split (α β χ δ : ℝ) (y : ℚ → ℝ) :
    rationalHeckeForm 5 (fourthStageCoefficients α β χ δ) fourthStageNodes y =
      rationalHeckeForm 4 (thirdStageCoefficients α β χ) thirdStageLateNodes y +
      rationalHeckeForm 4 (thirdStageCoefficients α β χ) thirdStageLateNodes
        (fun q => y (5 / q)) + 2 * δ * y 1 * y 5 := by
  have hfour : Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hfive : Finset.Icc 2 5 = ({2, 3, 4, 5} : Finset ℕ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have he : rationalHeckeForm 5 (fourthStageCoefficients α β χ δ) fourthStageNodes y =
      rationalHeckeForm 4 (thirdStageCoefficients α β χ) fourthStageNodes y +
        2 * δ * y 1 * y 5 := by
    rw [rationalHeckeForm_eq_neighbor_sum, rationalHeckeForm_eq_neighbor_sum, hfour, hfive]
    norm_num [fourthStageCoefficients, thirdStageCoefficients]
    rw [fourthStage_edges_five]
    ring
  rw [he, fourthStage_form_four_split]

private def lateCoordinates (y : ℚ → ℝ) : Fin 12 → ℝ :=
  ![y 1, y 2, y 4, y 3, y (4 / 3), y (8 / 3),
    y (9 / 2), y (9 / 4), y (9 / 8), y (3 / 2), y (27 / 8), y (27 / 16)]

private theorem lateCoordinates_congr {f g : ℚ → ℝ}
    (h : ∀ q ∈ thirdStageLateNodes, f q = g q) : lateCoordinates f = lateCoordinates g := by
  funext i
  fin_cases i <;> apply h <;> norm_num [thirdStageLateNodes]

private theorem lateCoordinates_amplitude (x : Fin 12 → ℝ) :
    lateCoordinates (thirdStageLateAmplitude x) = x := thirdStageLateAmplitude_vec x

private theorem fourthStage_graph_form (α β χ δ : ℝ) (y : ℚ → ℝ) :
    rationalHeckeForm 5 (fourthStageCoefficients α β χ δ) fourthStageNodes y =
      fourthStageDoubleForm α β χ δ (lateCoordinates y)
        (lateCoordinates fun q => y (5 / q)) := by
  rw [fourthStage_form_split, thirdStage_late_graph_form, thirdStage_late_graph_form]
  simp only [fourthStageDoubleForm, lateCoordinates, Matrix.cons_val_zero, div_one]

private def fourthStageAmplitude (x y : Fin 12 → ℝ) (q : ℚ) : ℝ :=
  if q ∈ thirdStageLateNodes then thirdStageLateAmplitude x q
  else thirdStageLateAmplitude y (5 / q)

private theorem fourthStage_graph_nonneg_iff (α β χ δ : ℝ) :
    (∀ y : ℚ → ℝ,
      0 ≤ rationalHeckeForm 5 (fourthStageCoefficients α β χ δ) fourthStageNodes y) ↔
      ∀ x y, 0 ≤ fourthStageDoubleForm α β χ δ x y := by
  classical
  constructor
  · intro h x y
    have hx : lateCoordinates (fourthStageAmplitude x y) = x := by
      calc
        lateCoordinates (fourthStageAmplitude x y) =
            lateCoordinates (thirdStageLateAmplitude x) := by
          apply lateCoordinates_congr
          intro q hq
          exact if_pos hq
        _ = x := lateCoordinates_amplitude x
    have hy : lateCoordinates (fun q => fourthStageAmplitude x y (5 / q)) = y := by
      calc
        lateCoordinates (fun q => fourthStageAmplitude x y (5 / q)) =
            lateCoordinates (thirdStageLateAmplitude y) := by
          apply lateCoordinates_congr
          intro q hq
          have hmem : (5 : ℚ) / q ∈ thirdStageLateNodes.image (fun q : ℚ => 5 / q) :=
            Finset.mem_image.mpr ⟨q, hq, rfl⟩
          have hn : (5 : ℚ) / q ∉ thirdStageLateNodes := fun ht =>
            Finset.disjoint_left.mp fourthStageNodes_disjoint ht hmem
          have hq0 : q ≠ 0 :=
            ne_of_gt (lt_of_lt_of_le (by norm_num) (thirdStageLateNodes_bounds hq).1)
          have he : (5 : ℚ) / (5 / q) = q := by field_simp [hq0]
          rw [fourthStageAmplitude, if_neg hn, he]
        _ = y := lateCoordinates_amplitude y
    have hh := h (fourthStageAmplitude x y)
    rwa [fourthStage_graph_form, hx, hy] at hh
  · intro h y
    rw [fourthStage_graph_form]
    exact h _ _

private theorem rationalHeckePositive_fourthStage_iff {A α β χ δ : ℝ}
    (hA5 : Real.log 5 < A) (hA81 : A ≤ Real.log (81 / 16)) :
    RationalHeckePositive A 5 (fourthStageCoefficients α β χ δ) ↔
      ∀ x y, 0 ≤ fourthStageDoubleForm α β χ δ x y := by
  constructor
  · intro h
    apply (fourthStage_graph_nonneg_iff α β χ δ).mp
    apply h fourthStageNodes
    · intro r hr
      exact lt_of_lt_of_le (by norm_num) (fourthStageNodes_bounds hr).1
    · intro r hr s hs
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (fourthStageNodes_bounds hr).1
      have hs0 : (0 : ℝ) < s := by
        exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1)
          (fourthStageNodes_bounds hs).1
      have hs5 : (s : ℝ) ≤ 5 := by exact_mod_cast (fourthStageNodes_bounds hs).2
      have hlr := Real.log_nonneg hr1
      have hls := Real.log_le_log hs0 hs5
      linarith only [hA5, hlr, hls]
  · intro h S hpos hspread y
    apply rationalHeckeForm_nonneg_of_closed_template 5 (fourthStageCoefficients α β χ δ)
      fourthStageNodes (81 / 16) (by norm_num [fourthStageNodes])
      (fun n hn q hq s hlo hhi hrel => fourthStageNodes_closed hq hn hlo hhi hrel)
      ((fourthStage_graph_nonneg_iff α β χ δ).mpr h) S hpos ?_ y
    intro r hr s hs
    by_contra hsr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hpos r hr
    have hleQ : (81 : ℚ) * r ≤ 16 * s := by nlinarith only [le_of_not_gt hsr]
    have hleR : (81 : ℝ) * r ≤ 16 * s := by exact_mod_cast hleQ
    have hle : (81 / 16 : ℝ) * r ≤ s := by linarith only [hleR]
    have hl := Real.log_le_log (mul_pos (by norm_num) hr0) hle
    rw [Real.log_mul (by norm_num) hr0.ne'] at hl
    linarith only [hspread r hr s hs, hA81, hl]

/-- Half the ratio-five Tate weight. -/
def fourthStageDelta (k : ℝ) : ℝ := ((5 : ℝ) ^ k - 1) / (2 * Real.sqrt 5)

private theorem fourthStageDelta_nonneg {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ fourthStageDelta k :=
  div_nonneg (sub_nonneg.mpr (Real.one_le_rpow (by norm_num) hk)) (by positivity)

private theorem thirdStageAlpha_pos {k : ℝ} (hk : 0 < k) : 0 < thirdStageAlpha k :=
  div_pos (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hk)) (by positivity)

private theorem thirdStageBeta_pos {k : ℝ} (hk : 0 < k) : 0 < thirdStageBeta k :=
  div_pos (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hk)) (by positivity)

private theorem windowLevel_eq_five_beforeEightyOneSixteenths {A : ℝ}
    (hA5 : Real.log 5 < A) (hA81 : A ≤ Real.log (81 / 16)) : windowLevel A = 5 := by
  rw [windowLevel, Nat.floor_eq_iff (Real.exp_pos A).le]
  constructor
  · have h := Real.exp_le_exp.mpr hA5.le
    rw [Real.exp_log (by norm_num)] at h
    norm_num
    exact h
  · have h := Real.exp_le_exp.mpr hA81
    rw [Real.exp_log (by norm_num)] at h
    norm_num
    linarith only [h]

private theorem tateFunction_fourthStage {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (hlev : windowLevel A = 5) (k : ℝ) :
    tateFunction A H k = (∫ u, H u ^ 2) + ∑ n ∈ Finset.Icc 2 5,
      fourthStageCoefficients (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k)
        (fourthStageDelta k) n * ∫ u, H u * H (u + Real.log n) := by
  have h5 : jordanTotient k 5 = (5 : ℝ) ^ k - 1 := by
    simpa using jordanTotient_prime_pow (by norm_num : Nat.Prime 5) k (a := 1) le_rfl
  have hIcc15 : Finset.Icc 1 5 = insert 5 (Finset.Icc 1 4) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hIcc24 : Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hIcc25 : Finset.Icc 2 5 = ({2, 3, 4, 5} : Finset ℕ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [tateFunction_eq hH, hlev, hIcc15, Finset.sum_insert (by norm_num),
    h5, thirdStage_sum_eq_form, hIcc24, hIcc25]
  norm_num [fourthStageCoefficients, thirdStageCoefficients, fourthStageDelta]
  ring

/-- The exact Tate positivity criterion just above ratio five. The five strict
pivots and final weak pivot include the zero-dimensional endpoint. -/
theorem tateFunction_nonneg_iff_fourthStage_beforeEightyOneSixteenths {A k : ℝ}
    (hA5 : Real.log 5 < A) (hA81 : A ≤ Real.log (81 / 16)) (hk : 0 ≤ k) :
    (∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k) ↔
      0 < fourthStageD (thirdStageAlpha k) ∧
        0 < fourthStageV (thirdStageAlpha k) (thirdStageBeta k) ∧
        0 < fourthStageW (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k) ∧
        0 < fourthStageP (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k) ∧
        0 < fourthStageQ (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k) ∧
        0 ≤ fourthStageW (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k) -
          fourthStageDelta k - thirdStageBeta k ^ 2 /
            fourthStageQ (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k) := by
  rcases eq_or_lt_of_le hk with rfl | hkpos
  · constructor
    · intro _
      norm_num [thirdStageAlpha, thirdStageBeta, thirdStageChi, fourthStageDelta,
        fourthStageD, fourthStageV, fourthStageW, fourthStageP, fourthStageQ]
    · intro _ H hH
      rw [tateFunction_zero hH]
      exact integral_nonneg (fun u => sq_nonneg (H u))
  · have hα := thirdStageAlpha_pos hkpos
    have hβ := thirdStageBeta_pos hkpos
    have hz : thirdStageChi k - thirdStageAlpha k ^ 2 ≠ 0 := by
      have hh := two_mul_thirdStageAlpha_sq_le_chi hkpos.le
      exact ne_of_gt (by nlinarith only [hh, sq_pos_of_pos hα])
    have hlev := windowLevel_eq_five_beforeEightyOneSixteenths hA5 hA81
    have hbridge : (∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k) ↔
        ∀ x, 0 ≤ fourthStageRootForm (thirdStageAlpha k) (thirdStageBeta k)
          (thirdStageChi k) (fourthStageDelta k) x := by
      have hw := windowForm_nonneg_iff_rationalHeckePositive A 5
        (fourthStageCoefficients (thirdStageAlpha k) (thirdStageBeta k)
          (thirdStageChi k) (fourthStageDelta k))
      have hg := rationalHeckePositive_fourthStage_iff
        (α := thirdStageAlpha k) (β := thirdStageBeta k) (χ := thirdStageChi k)
        (δ := fourthStageDelta k) hA5 hA81
      have hr := fourthStageDoubleForm_nonneg_iff (fourthStageDelta_nonneg hkpos.le)
        (α := thirdStageAlpha k) (β := thirdStageBeta k) (χ := thirdStageChi k)
      constructor
      · intro h
        apply hr.mp
        apply hg.mp
        apply hw.mp
        intro H hH
        rw [← tateFunction_fourthStage hH hlev k]
        exact h H hH
      · intro h H hH
        have hh := hw.mpr (hg.mpr (hr.mpr h)) H hH
        rwa [← tateFunction_fourthStage hH hlev k] at hh
    exact hbridge.trans (fourthStageRootForm_nonneg_iff hα.ne' hβ.ne' hz)

#print axioms fourthStageNodes_closed
#print axioms fourthStageDoubleForm_nonneg_iff
#print axioms fourthStageRootForm_nonneg_iff
#print axioms tateFunction_nonneg_iff_fourthStage_beforeEightyOneSixteenths

end GaloisForLFunctions.WindowTowerOfSpecZ
