import Mathlib

/-!
# Connes--van Suijlekom, Appendix B.1: the `N = 1` source family

The finite `N = 1` matrices in Proposition B.1 have the exact
divided-difference form supplied by Proposition 4.2: an even diagonal and a
constant off-diagonal determined by the odd source parameter.  This module
builds that source family and the affine reduction used in Appendix B.1.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `N = 1` even-diagonal, odd-divided-difference matrix family from
Proposition 4.2, indexed in source order `(-1, 0, 1)`. -/
def connesVanSuijlekomB1Matrix (a₀ a₁ b₁ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a₁, b₁, b₁;
     b₁, a₀, b₁;
     b₁, b₁, a₁]

/-- The normalized matrix `M(c)` displayed in Appendix B.1, equation (30). -/
def connesVanSuijlekomB1NormalizedMatrix (c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -1, -1;
     -1, c, -1;
     -1, -1, 0]

/-- The reversal symmetry on the source coordinates `(-1, 0, 1)`. -/
def connesVanSuijlekomB1Reflection : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

/-- The odd eigenvector of `M(c)`. -/
def connesVanSuijlekomB1OddVector : Fin 3 → ℝ := ![-1, 0, 1]

/-- The even vectors used for the two remaining eigendirections of `M(c)`. -/
def connesVanSuijlekomB1EvenVector (x : ℝ) : Fin 3 → ℝ := ![1, x, 1]

/-- The discriminant of the even `2 × 2` block of `M(c)`. -/
def connesVanSuijlekomB1Discriminant (c : ℝ) : ℝ := (c + 1) ^ 2 + 8

/-- The two even-eigenvector parameters of `M(c)`. -/
def connesVanSuijlekomB1RootPlus (c : ℝ) : ℝ :=
  (-(c + 1) + Real.sqrt (connesVanSuijlekomB1Discriminant c)) / 2

def connesVanSuijlekomB1RootMinus (c : ℝ) : ℝ :=
  (-(c + 1) - Real.sqrt (connesVanSuijlekomB1Discriminant c)) / 2

private theorem connesVanSuijlekomB1_discriminant_pos (c : ℝ) :
    0 < connesVanSuijlekomB1Discriminant c := by
  dsimp [connesVanSuijlekomB1Discriminant]
  nlinarith [sq_nonneg (c + 1)]

theorem connesVanSuijlekomB1_rootPlus_equation (c : ℝ) :
    (connesVanSuijlekomB1RootPlus c) ^ 2 + (c + 1) * connesVanSuijlekomB1RootPlus c - 2 = 0 := by
  have hsq := Real.sq_sqrt (connesVanSuijlekomB1_discriminant_pos c).le
  simp only [connesVanSuijlekomB1RootPlus, connesVanSuijlekomB1Discriminant] at hsq ⊢
  nlinarith

theorem connesVanSuijlekomB1_rootMinus_equation (c : ℝ) :
    (connesVanSuijlekomB1RootMinus c) ^ 2 + (c + 1) * connesVanSuijlekomB1RootMinus c - 2 = 0 := by
  have hsq := Real.sq_sqrt (connesVanSuijlekomB1_discriminant_pos c).le
  simp only [connesVanSuijlekomB1RootMinus, connesVanSuijlekomB1Discriminant] at hsq ⊢
  nlinarith

private theorem connesVanSuijlekomB1_root_sum (c : ℝ) :
    connesVanSuijlekomB1RootPlus c + connesVanSuijlekomB1RootMinus c = -(c + 1) := by
  simp only [connesVanSuijlekomB1RootPlus, connesVanSuijlekomB1RootMinus]
  ring

private theorem connesVanSuijlekomB1_root_product (c : ℝ) :
    connesVanSuijlekomB1RootPlus c * connesVanSuijlekomB1RootMinus c = -2 := by
  have hsq := Real.sq_sqrt (connesVanSuijlekomB1_discriminant_pos c).le
  simp only [connesVanSuijlekomB1RootPlus, connesVanSuijlekomB1RootMinus,
    connesVanSuijlekomB1Discriminant] at hsq ⊢
  nlinarith

private theorem connesVanSuijlekomB1_even_quadratic_factor (c x : ℝ) :
    x ^ 2 + (c + 1) * x - 2 =
      (x - connesVanSuijlekomB1RootPlus c) * (x - connesVanSuijlekomB1RootMinus c) := by
  have hsum := connesVanSuijlekomB1_root_sum c
  have hprod := connesVanSuijlekomB1_root_product c
  linear_combination x * hsum - hprod

private theorem connesVanSuijlekomB1_even_root_eq_plus_or_minus {c x : ℝ}
    (hx : x ^ 2 + (c + 1) * x - 2 = 0) :
    x = connesVanSuijlekomB1RootPlus c ∨ x = connesVanSuijlekomB1RootMinus c := by
  rw [connesVanSuijlekomB1_even_quadratic_factor] at hx
  rcases mul_eq_zero.mp hx with hplus | hminus
  · exact Or.inl (sub_eq_zero.mp hplus)
  · exact Or.inr (sub_eq_zero.mp hminus)

private theorem connesVanSuijlekomB1_sqrt_discriminant_sq (c : ℝ) :
    (Real.sqrt (connesVanSuijlekomB1Discriminant c)) ^ 2 =
      connesVanSuijlekomB1Discriminant c := by
  exact Real.sq_sqrt (connesVanSuijlekomB1_discriminant_pos c).le

theorem connesVanSuijlekomB1_rootPlus_pos (c : ℝ) :
    0 < connesVanSuijlekomB1RootPlus c := by
  have hsqrt : 0 ≤ Real.sqrt (connesVanSuijlekomB1Discriminant c) := Real.sqrt_nonneg _
  have hsq := connesVanSuijlekomB1_sqrt_discriminant_sq c
  have hlt : (c + 1) ^ 2 < (Real.sqrt (connesVanSuijlekomB1Discriminant c)) ^ 2 := by
    rw [hsq]
    dsimp [connesVanSuijlekomB1Discriminant]
    nlinarith
  have habs : |c + 1| < Real.sqrt (connesVanSuijlekomB1Discriminant c) :=
    by simpa [abs_of_nonneg hsqrt] using sq_lt_sq.mp hlt
  have hlt' : c + 1 < Real.sqrt (connesVanSuijlekomB1Discriminant c) :=
    (abs_lt.mp habs).2
  dsimp [connesVanSuijlekomB1RootPlus]
  linarith

theorem connesVanSuijlekomB1_rootMinus_neg (c : ℝ) :
    connesVanSuijlekomB1RootMinus c < 0 := by
  have hsqrt : 0 ≤ Real.sqrt (connesVanSuijlekomB1Discriminant c) := Real.sqrt_nonneg _
  have hsq := connesVanSuijlekomB1_sqrt_discriminant_sq c
  have hlt : (c + 1) ^ 2 < (Real.sqrt (connesVanSuijlekomB1Discriminant c)) ^ 2 := by
    rw [hsq]
    dsimp [connesVanSuijlekomB1Discriminant]
    nlinarith
  have habs : |c + 1| < Real.sqrt (connesVanSuijlekomB1Discriminant c) :=
    by simpa [abs_of_nonneg hsqrt] using sq_lt_sq.mp hlt
  have hlt' : -(c + 1) < Real.sqrt (connesVanSuijlekomB1Discriminant c) :=
    by linarith [(abs_lt.mp habs).1]
  dsimp [connesVanSuijlekomB1RootMinus]
  linarith

theorem connesVanSuijlekomB1_rootMinus_le_neg_two_of_nonneg {c : ℝ} (hc : 0 ≤ c) :
    connesVanSuijlekomB1RootMinus c ≤ -2 := by
  have hsqrt : 0 ≤ Real.sqrt (connesVanSuijlekomB1Discriminant c) := Real.sqrt_nonneg _
  have hsq := connesVanSuijlekomB1_sqrt_discriminant_sq c
  have hthreeSq : 3 ^ 2 ≤ (Real.sqrt (connesVanSuijlekomB1Discriminant c)) ^ 2 := by
    rw [hsq]
    dsimp [connesVanSuijlekomB1Discriminant]
    nlinarith [sq_nonneg c]
  have hthree : 3 ≤ Real.sqrt (connesVanSuijlekomB1Discriminant c) :=
    (sq_le_sq₀ (by norm_num) hsqrt).mp hthreeSq
  dsimp [connesVanSuijlekomB1RootMinus]
  linarith

theorem connesVanSuijlekomB1_neg_two_lt_rootMinus_of_neg {c : ℝ} (hc : c < 0) :
    -2 < connesVanSuijlekomB1RootMinus c := by
  have hsqrt : 0 ≤ Real.sqrt (connesVanSuijlekomB1Discriminant c) := Real.sqrt_nonneg _
  have hsq := connesVanSuijlekomB1_sqrt_discriminant_sq c
  have hbound : 0 ≤ 4 - (c + 1) := by linarith
  have hsquare : (Real.sqrt (connesVanSuijlekomB1Discriminant c)) ^ 2 <
      (4 - (c + 1)) ^ 2 := by
    rw [hsq]
    dsimp [connesVanSuijlekomB1Discriminant]
    nlinarith
  have hlt : Real.sqrt (connesVanSuijlekomB1Discriminant c) < 4 - (c + 1) :=
    (sq_lt_sq₀ hsqrt hbound).mp hsquare
  dsimp [connesVanSuijlekomB1RootMinus]
  linarith

theorem connesVanSuijlekomB1_normalized_odd_eigenvector (c : ℝ) :
    connesVanSuijlekomB1NormalizedMatrix c *ᵥ connesVanSuijlekomB1OddVector =
      (1 : ℝ) • connesVanSuijlekomB1OddVector := by
  ext i
  fin_cases i <;> simp [connesVanSuijlekomB1NormalizedMatrix,
    connesVanSuijlekomB1OddVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem connesVanSuijlekomB1_normalized_even_eigenvector
    {c x : ℝ} (hx : x ^ 2 + (c + 1) * x - 2 = 0) :
    connesVanSuijlekomB1NormalizedMatrix c *ᵥ connesVanSuijlekomB1EvenVector x =
      (-x - 1) • connesVanSuijlekomB1EvenVector x := by
  ext i
  fin_cases i <;> simp [connesVanSuijlekomB1NormalizedMatrix,
    connesVanSuijlekomB1EvenVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  all_goals nlinarith

private theorem connesVanSuijlekomB1_normalized_eigenvector_even_of_ne_one
    {c l : ℝ} {v : Fin 3 → ℝ}
    (hEig : connesVanSuijlekomB1NormalizedMatrix c *ᵥ v = l • v) (hl : l ≠ 1) :
    v 0 = v 2 := by
  have h0 := congrFun hEig 0
  have h2 := congrFun hEig 2
  simp [connesVanSuijlekomB1NormalizedMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three] at h0 h2
  have hdiff : (1 - l) * (v 0 - v 2) = 0 := by
    linear_combination h0 - h2
  have hfactor : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hfactor)

private theorem connesVanSuijlekomB1_normalized_nonunit_eigenvector_parameter
    {c l : ℝ} {v : Fin 3 → ℝ} (hv : v ≠ 0)
    (hEig : connesVanSuijlekomB1NormalizedMatrix c *ᵥ v = l • v) (hl : l ≠ 1) :
    ∃ x : ℝ, v = v 0 • connesVanSuijlekomB1EvenVector x ∧
      x ^ 2 + (c + 1) * x - 2 = 0 ∧ l = -x - 1 := by
  have hEven := connesVanSuijlekomB1_normalized_eigenvector_even_of_ne_one hEig hl
  have h0 := congrFun hEig 0
  have h1 := congrFun hEig 1
  simp [connesVanSuijlekomB1NormalizedMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three] at h0 h1
  have hv0 : v 0 ≠ 0 := by
    intro hv0
    apply hv
    have hv2 : v 2 = 0 := by linarith [hEven]
    have hv1 : v 1 = 0 := by rw [hv0, hv2] at h0; linarith
    funext i
    fin_cases i <;> simp [hv0, hv1, hv2]
  let x : ℝ := v 1 / v 0
  have hscale : v = v 0 • connesVanSuijlekomB1EvenVector x := by
    ext i
    fin_cases i
    · simp [connesVanSuijlekomB1EvenVector]
    · simp only [connesVanSuijlekomB1EvenVector, Pi.smul_apply, smul_eq_mul]
      dsimp [x]
      field_simp
    · simp [connesVanSuijlekomB1EvenVector, hEven]
  have hlx : l = -x - 1 := by
    dsimp [x]
    field_simp
    nlinarith
  have hquad : x ^ 2 + (c + 1) * x - 2 = 0 := by
    rw [← hEven] at h1
    rw [hlx] at h1
    dsimp [x] at h1 ⊢
    field_simp [hv0] at h1 ⊢
    nlinarith
  exact ⟨x, hscale, hquad, hlx⟩

/-- Every complex zero of the finite numerator lies on the real axis. -/
def ConnesVanSuijlekomB1AllRootsReal (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, F z = 0 → z.im = 0

/-- The polynomial numerator in Equation (21), specialized to `N = 1` and
source coordinate order `(-1, 0, 1)`. -/
def connesVanSuijlekomB1FourierNumerator (v : Fin 3 → ℝ) (s : ℂ) : ℂ :=
  (v 0 : ℂ) * (0 - s) * (1 - s) +
    (v 1 : ℂ) * (-1 - s) * (1 - s) +
      (v 2 : ℂ) * (-1 - s) * (0 - s)

theorem connesVanSuijlekomB1FourierNumerator_expand (v : Fin 3 → ℝ) (s : ℂ) :
    connesVanSuijlekomB1FourierNumerator v s =
      ((v 0 + v 1 + v 2 : ℝ) : ℂ) * s ^ 2 + ((v 2 - v 0 : ℝ) : ℂ) * s - v 1 := by
  simp [connesVanSuijlekomB1FourierNumerator]
  ring

private theorem connesVanSuijlekomB1_normalized_unit_eigenvector_numerator_allRootsReal
    {c : ℝ} {v : Fin 3 → ℝ} (hv : v ≠ 0)
    (hEig : connesVanSuijlekomB1NormalizedMatrix c *ᵥ v = (1 : ℝ) • v) :
    ConnesVanSuijlekomB1AllRootsReal (connesVanSuijlekomB1FourierNumerator v) := by
  have h0 := congrFun hEig 0
  simp [connesVanSuijlekomB1NormalizedMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three] at h0
  have hsum : v 0 + v 1 + v 2 = 0 := by linarith
  intro z hz
  rw [connesVanSuijlekomB1FourierNumerator_expand] at hz
  rw [hsum] at hz
  norm_num at hz
  have hz' : ((v 2 - v 0 : ℝ) : ℂ) * z = v 1 := by
    simpa using sub_eq_zero.mp hz
  have hcoef : v 2 - v 0 ≠ 0 := by
    intro hzero
    have hv1 : v 1 = 0 := by
      have := congrArg Complex.re hz'
      simp [hzero] at this
      have hreal : (0 : ℝ) = v 1 := by exact_mod_cast this
      exact hreal.symm
    apply hv
    have hv02 : v 0 = 0 := by linarith
    have hv2 : v 2 = 0 := by linarith [hsum]
    funext i
    fin_cases i <;> simp [hv02, hv1, hv2]
  have him := congrArg Complex.im hz'
  simp [Complex.mul_im] at him
  rcases him with hzero | him
  · exact (hcoef hzero).elim
  · exact him

theorem connesVanSuijlekomB1_rootPlus_eigenvector (c : ℝ) :
    connesVanSuijlekomB1NormalizedMatrix c *ᵥ
      connesVanSuijlekomB1EvenVector (connesVanSuijlekomB1RootPlus c) =
        (-connesVanSuijlekomB1RootPlus c - 1) •
          connesVanSuijlekomB1EvenVector (connesVanSuijlekomB1RootPlus c) :=
  connesVanSuijlekomB1_normalized_even_eigenvector
    (connesVanSuijlekomB1_rootPlus_equation c)

theorem connesVanSuijlekomB1_rootMinus_eigenvector (c : ℝ) :
    connesVanSuijlekomB1NormalizedMatrix c *ᵥ
      connesVanSuijlekomB1EvenVector (connesVanSuijlekomB1RootMinus c) =
        (-connesVanSuijlekomB1RootMinus c - 1) •
          connesVanSuijlekomB1EvenVector (connesVanSuijlekomB1RootMinus c) :=
  connesVanSuijlekomB1_normalized_even_eigenvector
    (connesVanSuijlekomB1_rootMinus_equation c)

/-- Appendix B.1's reduction of a nonzero off-diagonal source matrix to `M(c)`,
up to a nonzero scalar and a scalar identity shift. -/
theorem connesVanSuijlekomB1_affine_reduction (a₀ a₁ b₁ : ℝ) (hb : b₁ ≠ 0) :
    connesVanSuijlekomB1Matrix a₀ a₁ b₁ =
      (-b₁) • connesVanSuijlekomB1NormalizedMatrix ((a₀ - a₁) / (-b₁)) +
        a₁ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB1Matrix, connesVanSuijlekomB1NormalizedMatrix]
  all_goals (field_simp; ring)

/-- The normalized source family commutes with reflection, as required by the
even/odd eigenspace split in Appendix B.1. -/
theorem connesVanSuijlekomB1_normalized_commutes_reflection (c : ℝ) :
    connesVanSuijlekomB1NormalizedMatrix c * connesVanSuijlekomB1Reflection =
      connesVanSuijlekomB1Reflection * connesVanSuijlekomB1NormalizedMatrix c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB1NormalizedMatrix, connesVanSuijlekomB1Reflection,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- A nonzero eigenvector for an eigenvalue that is least or greatest among all
real eigenvalues.  This is the finite meaning of ``extremal eigenvalue'' in
Appendix B.1. -/
def ConnesVanSuijlekomB1IsExtremalEigenvector
    (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) (l : ℝ) : Prop :=
  v ≠ 0 ∧ M *ᵥ v = l • v ∧
    ((∀ l' w, w ≠ 0 → M *ᵥ w = l' • w → l ≤ l') ∨
      ∀ l' w, w ≠ 0 → M *ᵥ w = l' • w → l' ≤ l)

private theorem connesVanSuijlekomB1_rootMinus_lt_rootPlus (c : ℝ) :
    connesVanSuijlekomB1RootMinus c < connesVanSuijlekomB1RootPlus c := by
  have hdisc : 0 < connesVanSuijlekomB1Discriminant c :=
    connesVanSuijlekomB1_discriminant_pos c
  have hsqrt : 0 < Real.sqrt (connesVanSuijlekomB1Discriminant c) := Real.sqrt_pos.2 hdisc
  dsimp [connesVanSuijlekomB1RootMinus, connesVanSuijlekomB1RootPlus]
  linarith

private theorem connesVanSuijlekomB1_rootMinus_not_extremal_of_neg {c : ℝ} (hc : c < 0) :
    ¬ ConnesVanSuijlekomB1IsExtremalEigenvector
      (connesVanSuijlekomB1NormalizedMatrix c)
      (connesVanSuijlekomB1EvenVector (connesVanSuijlekomB1RootMinus c))
      (-connesVanSuijlekomB1RootMinus c - 1) := by
  intro hExtreme
  have hplusNe : connesVanSuijlekomB1EvenVector (connesVanSuijlekomB1RootPlus c) ≠ 0 := by
    intro hzero
    have h := congrFun hzero 0
    simp [connesVanSuijlekomB1EvenVector] at h
  have hoddNe : connesVanSuijlekomB1OddVector ≠ 0 := by
    intro hzero
    have h := congrFun hzero 0
    simp [connesVanSuijlekomB1OddVector] at h
  have horder := connesVanSuijlekomB1_rootMinus_lt_rootPlus c
  have hbelow : -connesVanSuijlekomB1RootPlus c - 1 <
      -connesVanSuijlekomB1RootMinus c - 1 := by linarith
  have habove : -connesVanSuijlekomB1RootMinus c - 1 < 1 := by
    have h := connesVanSuijlekomB1_neg_two_lt_rootMinus_of_neg hc
    linarith
  rcases hExtreme.2.2 with hmin | hmax
  · have := hmin (-connesVanSuijlekomB1RootPlus c - 1)
      (connesVanSuijlekomB1EvenVector (connesVanSuijlekomB1RootPlus c)) hplusNe
      (connesVanSuijlekomB1_rootPlus_eigenvector c)
    linarith
  · have := hmax 1 connesVanSuijlekomB1OddVector hoddNe
      (connesVanSuijlekomB1_normalized_odd_eigenvector c)
    linarith

theorem connesVanSuijlekomB1_even_numerator (x : ℝ) (s : ℂ) :
    connesVanSuijlekomB1FourierNumerator (connesVanSuijlekomB1EvenVector x) s =
      ((x + 2 : ℝ) : ℂ) * s ^ 2 - x := by
  rw [connesVanSuijlekomB1FourierNumerator_expand]
  change (((1 + x + 1 : ℝ) : ℂ) * s ^ 2 + ((1 - 1 : ℝ) : ℂ) * s - (x : ℂ)) = _
  push_cast
  ring

private theorem connesVanSuijlekomB1_complex_sq_eq_nonneg_im_zero
    {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : z ^ 2 = (r : ℂ)) : z.im = 0 := by
  have him := congrArg Complex.im hz
  have hre := congrArg Complex.re hz
  simp [pow_two, Complex.mul_im, Complex.mul_re] at him hre
  have hprod : z.re * z.im = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hre0 | him0
  · rw [hre0] at hre
    nlinarith [sq_nonneg z.im]
  · exact him0

/-- The `N = 1` even-vector numerator has only real complex roots whenever the
source's exact criterion `x(x+2) ≥ 0` holds. -/
theorem connesVanSuijlekomB1_even_numerator_allRootsReal
    {x : ℝ} (hx : 0 ≤ x * (x + 2)) :
    ConnesVanSuijlekomB1AllRootsReal
      (connesVanSuijlekomB1FourierNumerator (connesVanSuijlekomB1EvenVector x)) := by
  intro z hz
  rw [connesVanSuijlekomB1_even_numerator] at hz
  by_cases hden : x + 2 = 0
  · have hx' : x = -2 := by linarith
    norm_num [hx'] at hz
  · have hdenC : ((x + 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hden
    have hdenC' : (x : ℂ) + 2 ≠ 0 := by simpa using hdenC
    have hmul : ((x + 2 : ℝ) : ℂ) * z ^ 2 = x := by
      linear_combination hz
    have hmul' : ((x : ℂ) + 2) * z ^ 2 = x := by simpa using hmul
    have hsq : z ^ 2 = ((x / (x + 2) : ℝ) : ℂ) := by
      push_cast
      apply (eq_div_iff hdenC').2
      calc
        z ^ 2 * ((x : ℂ) + 2) = ((x : ℂ) + 2) * z ^ 2 := mul_comm _ _
        _ = (x : ℂ) := hmul'
    have hratio : 0 ≤ x / (x + 2) := by
      by_cases hpos : 0 < x + 2
      · exact div_nonneg (nonneg_of_mul_nonneg_left hx hpos) hpos.le
      · have hneg : x + 2 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hden
        exact div_nonneg_iff.mpr (Or.inr ⟨nonpos_of_mul_nonneg_left hx hneg, hneg.le⟩)
    exact connesVanSuijlekomB1_complex_sq_eq_nonneg_im_zero hratio hsq

theorem connesVanSuijlekomB1_rootPlus_numerator_allRootsReal (c : ℝ) :
    ConnesVanSuijlekomB1AllRootsReal
      (connesVanSuijlekomB1FourierNumerator (connesVanSuijlekomB1EvenVector
        (connesVanSuijlekomB1RootPlus c))) := by
  apply connesVanSuijlekomB1_even_numerator_allRootsReal
  have hpos := connesVanSuijlekomB1_rootPlus_pos c
  nlinarith

theorem connesVanSuijlekomB1_rootMinus_numerator_allRootsReal_of_nonneg
    {c : ℝ} (hc : 0 ≤ c) :
    ConnesVanSuijlekomB1AllRootsReal
      (connesVanSuijlekomB1FourierNumerator (connesVanSuijlekomB1EvenVector
        (connesVanSuijlekomB1RootMinus c))) := by
  apply connesVanSuijlekomB1_even_numerator_allRootsReal
  have hle := connesVanSuijlekomB1_rootMinus_le_neg_two_of_nonneg hc
  exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

theorem connesVanSuijlekomB1_odd_numerator_allRootsReal :
    ConnesVanSuijlekomB1AllRootsReal
      (connesVanSuijlekomB1FourierNumerator connesVanSuijlekomB1OddVector) := by
  intro z hz
  rw [connesVanSuijlekomB1FourierNumerator_expand] at hz
  change ((-1 + 0 + 1 : ℝ) : ℂ) * z ^ 2 + ((1 - -1 : ℝ) : ℂ) * z - (0 : ℂ) = 0 at hz
  norm_num at hz
  simp [hz]

private theorem connesVanSuijlekomB1_numerator_smul_allRootsReal
    {r : ℝ} (hr : r ≠ 0) {v : Fin 3 → ℝ}
    (hv : ConnesVanSuijlekomB1AllRootsReal (connesVanSuijlekomB1FourierNumerator v)) :
    ConnesVanSuijlekomB1AllRootsReal
      (connesVanSuijlekomB1FourierNumerator (r • v)) := by
  intro z hz
  have hscale : connesVanSuijlekomB1FourierNumerator (r • v) z =
      (r : ℂ) * connesVanSuijlekomB1FourierNumerator v z := by
    simp [connesVanSuijlekomB1FourierNumerator]
    ring
  rw [hscale] at hz
  exact hv z ((mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hr))

/-- The normalized `N = 1` source matrix has real Fourier-numerator zeros for
every eigenvector belonging to an extremal eigenvalue. -/
theorem connesVanSuijlekomB1_normalized_extremal_numerator_allRootsReal
    {c l : ℝ} {v : Fin 3 → ℝ}
    (hExtreme : ConnesVanSuijlekomB1IsExtremalEigenvector
      (connesVanSuijlekomB1NormalizedMatrix c) v l) :
    ConnesVanSuijlekomB1AllRootsReal (connesVanSuijlekomB1FourierNumerator v) := by
  rcases hExtreme with ⟨hv, hEig, hExt⟩
  by_cases hl : l = 1
  · subst l
    exact connesVanSuijlekomB1_normalized_unit_eigenvector_numerator_allRootsReal hv hEig
  · obtain ⟨x, hscale, hquad, hlx⟩ :=
      connesVanSuijlekomB1_normalized_nonunit_eigenvector_parameter hv hEig hl
    have hr : v 0 ≠ 0 := by
      intro hzero
      apply hv
      rw [hscale, hzero]
      simp
    rw [hscale]
    obtain hplus | hminus := connesVanSuijlekomB1_even_root_eq_plus_or_minus hquad
    · rw [hplus]
      exact connesVanSuijlekomB1_numerator_smul_allRootsReal hr
        (connesVanSuijlekomB1_rootPlus_numerator_allRootsReal c)
    · rw [hminus]
      by_cases hc : 0 ≤ c
      · exact connesVanSuijlekomB1_numerator_smul_allRootsReal hr
          (connesVanSuijlekomB1_rootMinus_numerator_allRootsReal_of_nonneg hc)
      · exfalso
        have hc' : c < 0 := lt_of_not_ge hc
        have horder := connesVanSuijlekomB1_rootMinus_lt_rootPlus c
        have hbelow : -connesVanSuijlekomB1RootPlus c - 1 <
            -connesVanSuijlekomB1RootMinus c - 1 := by linarith
        have habove : -connesVanSuijlekomB1RootMinus c - 1 < 1 := by
          have h := connesVanSuijlekomB1_neg_two_lt_rootMinus_of_neg hc'
          linarith
        rw [hlx, hminus] at hExt
        rcases hExt with hmin | hmax
        · have hplusNe : connesVanSuijlekomB1EvenVector (connesVanSuijlekomB1RootPlus c) ≠ 0 := by
            intro hzero
            have h := congrFun hzero 0
            simp [connesVanSuijlekomB1EvenVector] at h
          have := hmin (-connesVanSuijlekomB1RootPlus c - 1)
            (connesVanSuijlekomB1EvenVector (connesVanSuijlekomB1RootPlus c)) hplusNe
            (connesVanSuijlekomB1_rootPlus_eigenvector c)
          linarith
        · have hoddNe : connesVanSuijlekomB1OddVector ≠ 0 := by
            intro hzero
            have h := congrFun hzero 0
            simp [connesVanSuijlekomB1OddVector] at h
          have := hmax 1 connesVanSuijlekomB1OddVector hoddNe
            (connesVanSuijlekomB1_normalized_odd_eigenvector c)
          linarith

private theorem connesVanSuijlekomB1_affine_eigenvector
    (M : Matrix (Fin 3) (Fin 3) ℝ) {l α β : ℝ} {v : Fin 3 → ℝ}
    (hEig : M *ᵥ v = l • v) :
    (α • M + β • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ v = (α * l + β) • v := by
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hEig]
  ext i
  simp
  ring

/-- Proposition B.1 is false as printed when the extremal eigenvalue is not
simple: the zero `N = 1` source matrix makes every nonzero vector extremal,
while the numerator of `(1,-1,1)` has the non-real zero `I`. -/
theorem connesVanSuijlekomB1_counterexample :
    ConnesVanSuijlekomB1IsExtremalEigenvector
      (connesVanSuijlekomB1Matrix 0 0 0) (![1, -1, 1] : Fin 3 → ℝ) 0 ∧
      ¬ ConnesVanSuijlekomB1AllRootsReal
        (connesVanSuijlekomB1FourierNumerator (![1, -1, 1] : Fin 3 → ℝ)) := by
  constructor
  · refine ⟨?_, ?_, Or.inl ?_⟩
    · intro hzero
      have h := congrFun hzero 0
      norm_num at h
    · ext i
      fin_cases i <;> simp [connesVanSuijlekomB1Matrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three]
    · intro l w hw hEig
      have hzeroM : connesVanSuijlekomB1Matrix 0 0 0 = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [connesVanSuijlekomB1Matrix]
      rw [hzeroM] at hEig
      simp at hEig
      have hne : ∃ i, w i ≠ 0 := by
        by_contra h
        push Not at h
        exact hw (funext h)
      obtain ⟨i, hi⟩ := hne
      have h := congrFun hEig i
      rcases mul_eq_zero.mp h.symm with hl | hi'
      · linarith
      · exact (hi hi').elim
  · intro hreal
    have hz : connesVanSuijlekomB1FourierNumerator (![1, -1, 1] : Fin 3 → ℝ) Complex.I = 0 := by
      rw [connesVanSuijlekomB1FourierNumerator_expand]
      have h0 : (![1, -1, 1] : Fin 3 → ℝ) 0 = 1 := rfl
      have h1 : (![1, -1, 1] : Fin 3 → ℝ) 1 = -1 := rfl
      have h2 : (![1, -1, 1] : Fin 3 → ℝ) 2 = 1 := rfl
      rw [h0, h1, h2]
      norm_num
    have := hreal Complex.I hz
    norm_num at this

end

end GaloisForLFunctions.HTGeometry
