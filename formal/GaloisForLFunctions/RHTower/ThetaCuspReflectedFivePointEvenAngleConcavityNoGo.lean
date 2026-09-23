import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointParityWall

/-!
# Five-point even-parity obstruction to angle-only theta D1

The five-point reflection-even Toeplitz compression is the finite section whose confluent leading
coefficient is native rank-three D1.  The theta corpus proves that its normalized reflected-source
correlation angle is increasing, concave, normalized at zero, and contained in `[0, π/2]`.

Those scalar angle facts do not force five-point even positivity.  On the saturated first angular
face `c₂ = 2c₁² - 1`, the even determinant is exactly the negative square
`-4 (c₁ + c₃ - 2c₁c₂)²`.  Hence a positive extension must satisfy the exact null-coupling identity
`c₁ + c₃ = 2c₁c₂`.  An explicit strictly increasing concave angle violates that identity.

This kills the proposed proof arrow

`theta correlation-angle concavity → five-point even PSD → confluent D1 nonnegativity`.

The positive survivor is precise: any finite-section proof of D1 must establish the new
three-channel null-coupling law (or a strict interior replacement) from theta dynamics, not from
scalar correlation-angle concavity alone.
-/

open Matrix Set

namespace RHTower

noncomputable section

/-- Real palindromic Toeplitz matrix on the five nodes `-2,-1,0,1,2`. -/
def toeplitzFive (a b c d e : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![a, b, c, d, e;
     b, a, b, c, d;
     c, b, a, b, c;
     d, c, b, a, b;
     e, d, c, b, a]

/-- Unnormalized reflection-even compression in the basis center, first pair, second pair. -/
def toeplitzFiveEvenBlock (a b c d e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, 2 * b, 2 * c;
     2 * b, 2 * (a + c), 2 * (b + d);
     2 * c, 2 * (b + d), 2 * (a + e)]

/-- Embed the three even coordinates into the five-node packet. -/
def toeplitzFiveEvenCoordinates (s : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![s 2, s 1, s 0, s 1, s 2]

theorem toeplitzFiveEvenBlock_isHermitian (a b c d e : ℝ) :
    (toeplitzFiveEvenBlock a b c d e).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toeplitzFiveEvenBlock]

/-- The displayed three-by-three matrix is exactly the five-point even quadratic compression. -/
theorem toeplitzFive_even_quadratic (a b c d e : ℝ) (s : Fin 3 → ℝ) :
    star (toeplitzFiveEvenCoordinates s) ⬝ᵥ
        (toeplitzFive a b c d e).mulVec (toeplitzFiveEvenCoordinates s) =
      star s ⬝ᵥ (toeplitzFiveEvenBlock a b c d e).mulVec s := by
  simp [toeplitzFiveEvenCoordinates, toeplitzFive, toeplitzFiveEvenBlock,
    dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

/-- Full five-point positivity necessarily passes to the even compression. -/
theorem toeplitzFiveEvenBlock_posSemidef_of_toeplitzFive
    {a b c d e : ℝ} (hfive : Matrix.PosSemidef (toeplitzFive a b c d e)) :
    Matrix.PosSemidef (toeplitzFiveEvenBlock a b c d e) := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (toeplitzFiveEvenBlock_isHermitian a b c d e) fun s => ?_
  rw [← toeplitzFive_even_quadratic]
  exact hfive.dotProduct_mulVec_nonneg (toeplitzFiveEvenCoordinates s)

/-- Saturating the first angle face collapses the five-even determinant to one negative square. -/
theorem det_toeplitzFiveEvenBlock_of_head_saturated
    {c₁ c₂ c₃ c₄ : ℝ} (hsat : c₂ = 2 * c₁ ^ (2 : ℕ) - 1) :
    (toeplitzFiveEvenBlock 1 c₁ c₂ c₃ c₄).det =
      -4 * (c₁ + c₃ - 2 * c₁ * c₂) ^ (2 : ℕ) := by
  rw [Matrix.det_fin_three]
  simp [toeplitzFiveEvenBlock]
  rw [hsat]
  ring

/-- Positive-survivor classifier: a PSD five-even extension of a saturated head has zero coupling
to the new even channel. -/
theorem toeplitzFiveEvenBlock_boundary_coupling_eq_zero_of_posSemidef
    {c₁ c₂ c₃ c₄ : ℝ} (hsat : c₂ = 2 * c₁ ^ (2 : ℕ) - 1)
    (hpsd : Matrix.PosSemidef (toeplitzFiveEvenBlock 1 c₁ c₂ c₃ c₄)) :
    c₁ + c₃ = 2 * c₁ * c₂ := by
  have hdet := hpsd.det_nonneg
  rw [det_toeplitzFiveEvenBlock_of_head_saturated hsat] at hdet
  nlinarith [sq_nonneg (c₁ + c₃ - 2 * c₁ * c₂)]

/-- A globally concave, strictly increasing angle with a saturated first two-step face. -/
def fivePointStrictConcaveAngle (x : ℝ) : ℝ :=
  (Real.pi / 24) * x + (Real.pi / 24) * min x 3 +
    (Real.pi / 12) * min x 2

private theorem concaveOn_min_const (c : ℝ) :
    ConcaveOn ℝ Set.univ (fun x : ℝ => min x c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_min
  · exact add_le_add
      (mul_le_mul_of_nonneg_left (min_le_left x c) ha)
      (mul_le_mul_of_nonneg_left (min_le_left y c) hb)
  · calc
      a * min x c + b * min y c ≤ a * c + b * c :=
        add_le_add
          (mul_le_mul_of_nonneg_left (min_le_right x c) ha)
          (mul_le_mul_of_nonneg_left (min_le_right y c) hb)
      _ = (a + b) * c := by ring
      _ = c := by rw [hab]; ring

theorem concaveOn_fivePointStrictConcaveAngle :
    ConcaveOn ℝ Set.univ fivePointStrictConcaveAngle := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have h3 := (concaveOn_min_const 3).2 (Set.mem_univ x) (Set.mem_univ y)
    ha hb hab
  have h2 := (concaveOn_min_const 2).2 (Set.mem_univ x) (Set.mem_univ y)
    ha hb hab
  simp only [smul_eq_mul] at h3 h2
  calc
    a * fivePointStrictConcaveAngle x + b * fivePointStrictConcaveAngle y =
        (Real.pi / 24) * (a * x + b * y) +
          (Real.pi / 24) * (a * min x 3 + b * min y 3) +
          (Real.pi / 12) * (a * min x 2 + b * min y 2) := by
      simp only [fivePointStrictConcaveAngle]
      ring
    _ ≤ (Real.pi / 24) * (a * x + b * y) +
          (Real.pi / 24) * min (a * x + b * y) 3 +
          (Real.pi / 12) * min (a * x + b * y) 2 := by
      gcongr
    _ = fivePointStrictConcaveAngle (a * x + b * y) := rfl

theorem strictMono_fivePointStrictConcaveAngle :
    StrictMono fivePointStrictConcaveAngle := by
  intro x y hxy
  have hpi : 0 < Real.pi := Real.pi_pos
  have h3 : min x 3 ≤ min y 3 := min_le_min hxy.le le_rfl
  have h2 : min x 2 ≤ min y 2 := min_le_min hxy.le le_rfl
  dsimp only [fivePointStrictConcaveAngle]
  nlinarith

@[simp] theorem fivePointStrictConcaveAngle_zero :
    fivePointStrictConcaveAngle 0 = 0 := by
  simp [fivePointStrictConcaveAngle]

@[simp] theorem fivePointStrictConcaveAngle_one :
    fivePointStrictConcaveAngle 1 = Real.pi / 6 := by
  norm_num [fivePointStrictConcaveAngle]
  ring

@[simp] theorem fivePointStrictConcaveAngle_two :
    fivePointStrictConcaveAngle 2 = Real.pi / 3 := by
  norm_num [fivePointStrictConcaveAngle]
  ring

@[simp] theorem fivePointStrictConcaveAngle_three :
    fivePointStrictConcaveAngle 3 = 5 * Real.pi / 12 := by
  norm_num [fivePointStrictConcaveAngle]
  ring

@[simp] theorem fivePointStrictConcaveAngle_four :
    fivePointStrictConcaveAngle 4 = 11 * Real.pi / 24 := by
  norm_num [fivePointStrictConcaveAngle]
  ring

theorem fivePointStrictConcaveAngle_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 4) :
    fivePointStrictConcaveAngle x ∈ Icc 0 (Real.pi / 2) := by
  have hmono := strictMono_fivePointStrictConcaveAngle.monotone
  constructor
  · simpa only [fivePointStrictConcaveAngle_zero] using hmono hx.1
  · have hupper := hmono hx.2
    rw [fivePointStrictConcaveAngle_four] at hupper
    nlinarith [Real.pi_pos]

/-- Closed counterexample: the cosine kernel of the explicit increasing concave angle has an
indefinite five-point reflection-even block. -/
theorem not_posSemidef_toeplitzFiveEvenBlock_cos_fivePointStrictConcaveAngle :
    ¬ Matrix.PosSemidef
      (toeplitzFiveEvenBlock
        (Real.cos (fivePointStrictConcaveAngle 0))
        (Real.cos (fivePointStrictConcaveAngle 1))
        (Real.cos (fivePointStrictConcaveAngle 2))
        (Real.cos (fivePointStrictConcaveAngle 3))
        (Real.cos (fivePointStrictConcaveAngle 4))) := by
  intro hpsd
  have hsqrt : (Real.sqrt 3) ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  have hsat : Real.cos (fivePointStrictConcaveAngle 2) =
      2 * Real.cos (fivePointStrictConcaveAngle 1) ^ (2 : ℕ) - 1 := by
    rw [fivePointStrictConcaveAngle_one, fivePointStrictConcaveAngle_two,
      Real.cos_pi_div_six, Real.cos_pi_div_three]
    nlinarith
  simp only [fivePointStrictConcaveAngle_zero, Real.cos_zero] at hpsd
  have hcoupling :=
    toeplitzFiveEvenBlock_boundary_coupling_eq_zero_of_posSemidef hsat hpsd
  rw [fivePointStrictConcaveAngle_one, fivePointStrictConcaveAngle_two,
    Real.cos_pi_div_six, Real.cos_pi_div_three] at hcoupling
  have hcos : 0 < Real.cos (5 * Real.pi / 12) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  rw [fivePointStrictConcaveAngle_three] at hcoupling
  nlinarith

/-- Route-kill capstone: normalization, global concavity, strict increase, and the physical angular
range do not imply five-point even positivity. -/
theorem exists_strictMono_concave_angle_with_nonPSD_toeplitzFiveEvenBlock :
    ∃ alpha : ℝ → ℝ,
      alpha 0 = 0 ∧
      ConcaveOn ℝ Set.univ alpha ∧
      StrictMono alpha ∧
      Set.MapsTo alpha (Icc (0 : ℝ) 4) (Icc 0 (Real.pi / 2)) ∧
      ¬ Matrix.PosSemidef
        (toeplitzFiveEvenBlock
          (Real.cos (alpha 0))
          (Real.cos (alpha 1))
          (Real.cos (alpha 2))
          (Real.cos (alpha 3))
          (Real.cos (alpha 4))) := by
  refine ⟨fivePointStrictConcaveAngle, fivePointStrictConcaveAngle_zero,
    concaveOn_fivePointStrictConcaveAngle, strictMono_fivePointStrictConcaveAngle,
    ?_, not_posSemidef_toeplitzFiveEvenBlock_cos_fivePointStrictConcaveAngle⟩
  intro x hx
  exact fivePointStrictConcaveAngle_mem_Icc hx

end

end RHTower
