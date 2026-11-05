import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AdjunctionThresholdLaw
import GaloisForLFunctions.WindowTowerOfSpecZ.FiniteTemplatesControlRationalHeckeGraphs

/-!
# The Tate horizon before ratio nine halves

Between apertures `log 4` and `log(9/2)`, every rational Hecke component
embeds in a seven-vertex graph. Reflection splits its quadratic form into
two three-variable forms; the odd one gives the exact positivity criterion.
-/

noncomputable section

open Finset MeasureTheory

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory

/-- The seven rational vertices of the third-stage graph before ratio `9/2`. -/
def thirdStageNodes : Finset ℚ := {1, 2, 4, 3, 3 / 2, 4 / 3, 8 / 3}

theorem thirdStageNodes_closed {q s : ℚ} {n : ℕ}
    (hq : q ∈ thirdStageNodes) (hn : n ∈ Finset.Icc 2 4)
    (hlo : 1 ≤ s) (hhi : s < 9 / 2)
    (hrel : s = n * q ∨ q = n * s) : s ∈ thirdStageNodes := by
  have hn0 : (n : ℚ) ≠ 0 := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  rcases hrel with rfl | hrel
  · norm_num only [thirdStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
    obtain ⟨hn2, hn4⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num at hlo
    all_goals norm_num at hhi
    all_goals norm_num [thirdStageNodes]
  · have hs : s = q / n := (eq_div_iff hn0).mpr (by linarith only [hrel])
    rw [hs] at hlo hhi ⊢
    norm_num only [thirdStageNodes, Finset.mem_insert, Finset.mem_singleton] at hq
    obtain ⟨hn2, hn4⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num at hlo
    all_goals norm_num at hhi
    all_goals norm_num [thirdStageNodes]

/-- The quadratic form on the triangle with two two-edge arms. -/
def thirdStageSevenForm (α β χ : ℝ) (x : Fin 7 → ℝ) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 +
    2 * α * (x 0 * x 1 + x 1 * x 2 + x 3 * x 4 + x 5 * x 6) +
    2 * β * (x 0 * x 3 + x 2 * x 5) + 2 * χ * x 0 * x 2

theorem thirdStageSevenForm_vec (α β χ a b c d e f g : ℝ) :
    thirdStageSevenForm α β χ ![a, b, c, d, e, f, g] =
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2 +
        2 * α * (a * b + b * c + d * e + f * g) +
        2 * β * (a * d + c * f) + 2 * χ * a * c := rfl

private def thirdStageTripleForm (α β d a b c : ℝ) : ℝ :=
  d * a ^ 2 + b ^ 2 + c ^ 2 + 2 * β * a * b + 2 * α * b * c

private theorem thirdStageTripleForm_nonneg {α β d : ℝ}
    (hd : 0 ≤ d) (hα : α ^ 2 ≤ 1) (hβ : β ^ 2 ≤ d * (1 - α ^ 2))
    (a b c : ℝ) : 0 ≤ thirdStageTripleForm α β d a b c := by
  have h := ArithmeticCastelnuovoSeveri.quad_nonneg_of_psd hd
    (sub_nonneg.mpr hα) hβ a b
  have hs := sq_nonneg (c + α * b)
  dsimp only [thirdStageTripleForm]
  nlinarith only [h, hs]

/-- Reflection in `r ↦ 4/r` splits the form into two three-variable forms and
the square at the central vertex. The extra even-sector term is nonnegative
whenever `α²≤χ`. -/
private theorem thirdStageSevenForm_reflection (α β χ : ℝ) (x : Fin 7 → ℝ) :
    thirdStageSevenForm α β χ x =
      2 * thirdStageTripleForm α β (1 - χ)
        ((x 0 - x 2) / 2) ((x 3 - x 5) / 2) ((x 4 - x 6) / 2) +
      2 * thirdStageTripleForm α β (1 - χ)
        ((x 0 + x 2) / 2) ((x 3 + x 5) / 2) ((x 4 + x 6) / 2) +
      4 * (χ - α ^ 2) * ((x 0 + x 2) / 2) ^ 2 +
      (x 1 + α * (x 0 + x 2)) ^ 2 := by
  unfold thirdStageSevenForm thirdStageTripleForm
  ring

/-- Exact positivity region of the seven-vertex form when the ratio-four
coupling dominates the square of the ratio-two coupling. -/
theorem thirdStageSevenForm_nonneg_iff {α β χ : ℝ} (hαχ : α ^ 2 ≤ χ) :
    (∀ x : Fin 7 → ℝ, 0 ≤ thirdStageSevenForm α β χ x) ↔
      χ ≤ 1 ∧ β ^ 2 ≤ (1 - χ) * (1 - α ^ 2) := by
  constructor
  · intro h
    have hχ : χ ≤ 1 := by
      have hx := h ![1, 0, -1, 0, 0, 0, 0]
      rw [thirdStageSevenForm_vec] at hx
      norm_num at hx
      linarith only [hx]
    refine ⟨hχ, ?_⟩
    have hα : α ^ 2 ≤ 1 := hαχ.trans hχ
    rcases eq_or_lt_of_le hα with heq | hlt
    · have hχeq : χ = 1 := by linarith only [hαχ, hχ, heq]
      have hx := h ![1, 0, -1, -β, α * β, β, -(α * β)]
      have hx' : thirdStageSevenForm α β χ
          ![1, 0, -1, -β, α * β, β, -(α * β)] =
          2 * (1 - χ) - 4 * β ^ 2 + 2 * (1 - α ^ 2) * β ^ 2 := by
        rw [thirdStageSevenForm_vec]
        ring
      rw [hx', hχeq, heq] at hx
      have hβ : β = 0 := by nlinarith only [hx, sq_nonneg β]
      simp only [hβ, zero_pow two_ne_zero, hχeq, sub_self, zero_mul, le_refl]
    · have hx := h ![1 - α ^ 2, 0, -(1 - α ^ 2), -β, α * β, β, -(α * β)]
      have hx' : thirdStageSevenForm α β χ
          ![1 - α ^ 2, 0, -(1 - α ^ 2), -β, α * β, β, -(α * β)] =
          2 * (1 - α ^ 2) * ((1 - χ) * (1 - α ^ 2) - β ^ 2) := by
        rw [thirdStageSevenForm_vec]
        ring
      rw [hx'] at hx
      have hd : 0 < 2 * (1 - α ^ 2) := by linarith only [hlt]
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hd).mp hx)
  · rintro ⟨hχ, hdet⟩ x
    have hα : α ^ 2 ≤ 1 := hαχ.trans hχ
    have h1 := thirdStageTripleForm_nonneg (sub_nonneg.mpr hχ) hα hdet
      ((x 0 - x 2) / 2) ((x 3 - x 5) / 2) ((x 4 - x 6) / 2)
    have h2 := thirdStageTripleForm_nonneg (sub_nonneg.mpr hχ) hα hdet
      ((x 0 + x 2) / 2) ((x 3 + x 5) / 2) ((x 4 + x 6) / 2)
    have h3 := mul_nonneg (sub_nonneg.mpr hαχ) (sq_nonneg ((x 0 + x 2) / 2))
    rw [thirdStageSevenForm_reflection]
    nlinarith only [h1, h2, h3, sq_nonneg (x 1 + α * (x 0 + x 2))]

#print axioms thirdStageNodes_closed
#print axioms thirdStageSevenForm_nonneg_iff

/-- Ratio-two, ratio-three and ratio-four edge coefficients. -/
def thirdStageCoefficients (α β χ : ℝ) (n : ℕ) : ℝ :=
  if n = 2 then 2 * α else if n = 3 then 2 * β else if n = 4 then 2 * χ else 0

private theorem thirdStageNodes_bounds {r : ℚ} (hr : r ∈ thirdStageNodes) :
    1 ≤ r ∧ r ≤ 4 := by
  norm_num only [thirdStageNodes, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- At each vertex, a fixed ratio has at most one outgoing neighbour. -/
theorem rationalHeckeForm_eq_neighbor_sum (N : ℕ) (c : ℕ → ℝ)
    (S : Finset ℚ) (y : ℚ → ℝ) :
    rationalHeckeForm N c S y = (∑ r ∈ S, y r ^ 2) +
      ∑ n ∈ Finset.Icc 2 N, c n * ∑ r ∈ S,
        if (n : ℚ) * r ∈ S then y r * y (n * r) else 0 := by
  classical
  unfold rationalHeckeForm
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  have he (s : ℚ) : (s : ℝ) = n * r ↔ s = (n : ℚ) * r := by
    constructor <;> intro h <;> exact_mod_cast h
  simp_rw [he]
  by_cases hm : (n : ℚ) * r ∈ S
  · rw [if_pos hm, Finset.sum_eq_single_of_mem ((n : ℚ) * r) hm
      (fun s _ hs => if_neg hs), if_pos rfl]
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro s hs
    have hne : s ≠ (n : ℚ) * r := fun h => hm (h ▸ hs)
    rw [if_neg hne]

private theorem thirdStage_edges_two (y : ℚ → ℝ) :
    (∑ r ∈ thirdStageNodes, if (2 : ℚ) * r ∈ thirdStageNodes then
      y r * y (2 * r) else 0) =
      y 1 * y 2 + y 2 * y 4 + y 3 * y (3 / 2) + y (4 / 3) * y (8 / 3) := by
  norm_num [thirdStageNodes]
  ring

private theorem thirdStage_edges_three (y : ℚ → ℝ) :
    (∑ r ∈ thirdStageNodes, if (3 : ℚ) * r ∈ thirdStageNodes then
      y r * y (3 * r) else 0) = y 1 * y 3 + y 4 * y (4 / 3) := by
  norm_num [thirdStageNodes]
  ring

private theorem thirdStage_edges_four (y : ℚ → ℝ) :
    (∑ r ∈ thirdStageNodes, if (4 : ℚ) * r ∈ thirdStageNodes then
      y r * y (4 * r) else 0) = y 1 * y 4 := by
  norm_num [thirdStageNodes]

private theorem thirdStage_graph_form (α β χ : ℝ) (y : ℚ → ℝ) :
    rationalHeckeForm 4 (thirdStageCoefficients α β χ) thirdStageNodes y =
      thirdStageSevenForm α β χ ![y 1, y 2, y 4, y 3, y (3 / 2), y (4 / 3), y (8 / 3)] := by
  classical
  have hIcc : Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [rationalHeckeForm_eq_neighbor_sum, hIcc]
  norm_num [thirdStageCoefficients]
  rw [thirdStage_edges_two, thirdStage_edges_three, thirdStage_edges_four]
  rw [thirdStageSevenForm_vec]
  norm_num [thirdStageNodes]
  ring

private def thirdStageAmplitude (x : Fin 7 → ℝ) (r : ℚ) : ℝ :=
  if r = 1 then x 0 else if r = 2 then x 1 else if r = 4 then x 2 else
    if r = 3 then x 3 else if r = 3 / 2 then x 4 else if r = 4 / 3 then x 5 else
      if r = 8 / 3 then x 6 else 0

private theorem thirdStage_graph_nonneg_iff {α β χ : ℝ} (hαχ : α ^ 2 ≤ χ) :
    (∀ y : ℚ → ℝ,
      0 ≤ rationalHeckeForm 4 (thirdStageCoefficients α β χ) thirdStageNodes y) ↔
      χ ≤ 1 ∧ β ^ 2 ≤ (1 - χ) * (1 - α ^ 2) := by
  constructor
  · intro h
    apply (thirdStageSevenForm_nonneg_iff hαχ).mp
    intro x
    have hx := h (thirdStageAmplitude x)
    rw [thirdStage_graph_form] at hx
    have he : ![thirdStageAmplitude x 1, thirdStageAmplitude x 2, thirdStageAmplitude x 4,
        thirdStageAmplitude x 3, thirdStageAmplitude x (3 / 2),
        thirdStageAmplitude x (4 / 3), thirdStageAmplitude x (8 / 3)] = x := by
      funext i
      fin_cases i <;> norm_num [thirdStageAmplitude, Matrix.cons_val] <;> rfl
    rwa [he] at hx
  · intro h y
    rw [thirdStage_graph_form]
    exact (thirdStageSevenForm_nonneg_iff hαχ).mpr h _

/-- Below ratio `9/2`, the seven-vertex graph decides the full window form. -/
private theorem rationalHeckePositive_thirdStage_iff {A α β χ : ℝ}
    (hA4 : Real.log 4 < A) (hA9 : A ≤ Real.log (9 / 2)) (hαχ : α ^ 2 ≤ χ) :
    RationalHeckePositive A 4 (thirdStageCoefficients α β χ) ↔
      χ ≤ 1 ∧ β ^ 2 ≤ (1 - χ) * (1 - α ^ 2) := by
  constructor
  · intro h
    apply (thirdStage_graph_nonneg_iff hαχ).mp
    apply h thirdStageNodes
    · intro r hr
      exact lt_of_lt_of_le (by norm_num) (thirdStageNodes_bounds hr).1
    · intro r hr s hs
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (thirdStageNodes_bounds hr).1
      have hs0 : (0 : ℝ) < s := by
        exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1)
          (thirdStageNodes_bounds hs).1
      have hs4 : (s : ℝ) ≤ 4 := by exact_mod_cast (thirdStageNodes_bounds hs).2
      have hlogr := Real.log_nonneg hr1
      have hlogs := Real.log_le_log hs0 hs4
      linarith only [hA4, hlogr, hlogs]
  · intro h S hpos hspread y
    apply rationalHeckeForm_nonneg_of_closed_template 4 (thirdStageCoefficients α β χ)
      thirdStageNodes (9 / 2) (by norm_num [thirdStageNodes])
      (fun n hn q hq s hlo hhi hrel => thirdStageNodes_closed hq hn hlo hhi hrel)
      ((thirdStage_graph_nonneg_iff hαχ).mpr h) S hpos ?_ y
    intro r hr s hs
    by_contra hsr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hpos r hr
    have hleQ : (9 : ℚ) * r ≤ 2 * s := by nlinarith only [le_of_not_gt hsr]
    have hleR : (9 : ℝ) * r ≤ 2 * s := by exact_mod_cast hleQ
    have hle : (9 / 2 : ℝ) * r ≤ s := by linarith only [hleR]
    have hl := Real.log_le_log (mul_pos (by norm_num) hr0) hle
    rw [Real.log_mul (by norm_num) hr0.ne'] at hl
    linarith only [hspread r hr s hs, hA9, hl]

/-- Half the ratio-two Tate weight. -/
def thirdStageAlpha (k : ℝ) : ℝ := ((2 : ℝ) ^ k - 1) / (2 * Real.sqrt 2)

/-- Half the ratio-three Tate weight. -/
def thirdStageBeta (k : ℝ) : ℝ := ((3 : ℝ) ^ k - 1) / (2 * Real.sqrt 3)

/-- Half the ratio-four Tate weight. -/
def thirdStageChi (k : ℝ) : ℝ := ((4 : ℝ) ^ k - (2 : ℝ) ^ k) / 4

private theorem four_rpow_eq_two_rpow_sq (k : ℝ) :
    (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
  calc (4 : ℝ) ^ k = ((2 : ℝ) * 2) ^ k := by norm_num
    _ = (2 : ℝ) ^ k * (2 : ℝ) ^ k := Real.mul_rpow (by norm_num) (by norm_num)
    _ = ((2 : ℝ) ^ k) ^ 2 := by ring

/-- Nonnegative Tate dimensions have nonnegative ratio-two weight. -/
theorem thirdStageAlpha_nonneg {k : ℝ} (hk : 0 ≤ k) : 0 ≤ thirdStageAlpha k :=
  div_nonneg (sub_nonneg.mpr (Real.one_le_rpow (by norm_num) hk)) (by positivity)

/-- The squared ratio-two coefficient contains no square root. -/
theorem thirdStageAlpha_sq (k : ℝ) :
    thirdStageAlpha k ^ 2 = ((2 : ℝ) ^ k - 1) ^ 2 / 8 := by
  unfold thirdStageAlpha
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The ratio-four coupling dominates twice the square of the ratio-two coupling. -/
theorem two_mul_thirdStageAlpha_sq_le_chi {k : ℝ} (hk : 0 ≤ k) :
    2 * thirdStageAlpha k ^ 2 ≤ thirdStageChi k := by
  have hx : 1 ≤ (2 : ℝ) ^ k := Real.one_le_rpow (by norm_num) hk
  rw [thirdStageAlpha_sq, thirdStageChi, four_rpow_eq_two_rpow_sq]
  nlinarith only [hx]

private theorem thirdStageAlpha_sq_le_chi {k : ℝ} (hk : 0 ≤ k) :
    thirdStageAlpha k ^ 2 ≤ thirdStageChi k := by
  have h := two_mul_thirdStageAlpha_sq_le_chi hk
  linarith only [h, sq_nonneg (thirdStageAlpha k)]

private theorem windowLevel_eq_four_beforeNineHalves {A : ℝ}
    (hA4 : Real.log 4 < A) (hA9 : A ≤ Real.log (9 / 2)) : windowLevel A = 4 := by
  rw [windowLevel, Nat.floor_eq_iff (Real.exp_pos A).le]
  constructor
  · have h := Real.exp_le_exp.mpr hA4.le
    rw [Real.exp_log (by norm_num)] at h
    norm_num
    exact h
  · have h := Real.exp_le_exp.mpr hA9
    rw [Real.exp_log (by norm_num)] at h
    norm_num
    linarith only [h]

/-- The first four Jordan terms give the three-lag correlation form. -/
theorem thirdStage_sum_eq_form (H : ℝ → ℝ) (k : ℝ) :
    (∑ n ∈ Finset.Icc 1 4, jordanTotient k n / Real.sqrt n *
      ∫ u, H u * H (u + Real.log n)) = (∫ u, H u ^ 2) + ∑ n ∈ Finset.Icc 2 4,
      thirdStageCoefficients (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k) n *
        ∫ u, H u * H (u + Real.log n) := by
  have h2 : jordanTotient k 2 = (2 : ℝ) ^ k - 1 := by
    simpa using jordanTotient_prime_pow Nat.prime_two k (a := 1) le_rfl
  have h3 : jordanTotient k 3 = (3 : ℝ) ^ k - 1 := by
    simpa using jordanTotient_prime_pow Nat.prime_three k (a := 1) le_rfl
  have h4 : jordanTotient k 4 = (4 : ℝ) ^ k - (2 : ℝ) ^ k := by
    have h := jordanTotient_prime_pow Nat.prime_two k (a := 2) (by norm_num)
    norm_num at h
    rw [h, four_rpow_eq_two_rpow_sq]
    ring
  have hIcc14 : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hIcc24 : Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hsq : (∫ u, H u * H u) = ∫ u, H u ^ 2 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => (sq (H u)).symm
  rw [hIcc14, hIcc24]
  norm_num [thirdStageCoefficients, thirdStageAlpha, thirdStageBeta, thirdStageChi,
    h2, h3, h4, jordanTotient_one, hsq]
  ring

/-- At level four, the Tate functional is the three-lag correlation form. -/
theorem tateFunction_thirdStage {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (hlev : windowLevel A = 4) (k : ℝ) :
    tateFunction A H k = (∫ u, H u ^ 2) + ∑ n ∈ Finset.Icc 2 4,
      thirdStageCoefficients (thirdStageAlpha k) (thirdStageBeta k) (thirdStageChi k) n *
        ∫ u, H u * H (u + Real.log n) := by
  rw [tateFunction_eq hH, hlev, thirdStage_sum_eq_form]

/-- The exact Tate horizon on the first part of stage three. Every finite
Hecke component embeds into the seven-vertex graph, whose odd sector is decisive. -/
theorem tateFunction_nonneg_iff_thirdStage_beforeNineHalves {A k : ℝ}
    (hA4 : Real.log 4 < A) (hA9 : A ≤ Real.log (9 / 2)) (hk : 0 ≤ k) :
    (∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k) ↔
      thirdStageChi k ≤ 1 ∧ thirdStageBeta k ^ 2 ≤
        (1 - thirdStageChi k) * (1 - thirdStageAlpha k ^ 2) := by
  have hlev := windowLevel_eq_four_beforeNineHalves hA4 hA9
  have hαχ := thirdStageAlpha_sq_le_chi hk
  constructor
  · intro h
    apply (rationalHeckePositive_thirdStage_iff hA4 hA9 hαχ).mp
    apply (windowForm_nonneg_iff_rationalHeckePositive A 4 _).mp
    intro H hH
    rw [← tateFunction_thirdStage hH hlev k]
    exact h H hH
  · intro h H hH
    have hp := (rationalHeckePositive_thirdStage_iff hA4 hA9 hαχ).mpr h
    have hw := (windowForm_nonneg_iff_rationalHeckePositive A 4 _).mpr hp H hH
    rwa [← tateFunction_thirdStage hH hlev k] at hw

#print axioms tateFunction_nonneg_iff_thirdStage_beforeNineHalves

end GaloisForLFunctions.WindowTowerOfSpecZ
