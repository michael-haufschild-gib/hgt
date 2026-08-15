import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit
import GaloisForLFunctions.HTGeometry.SeparatedOffDiagonalBound

/-!
# Finite-degree shifted Hankel tail stability

For a finite shifted Hankel block, a certified positive bulk margin absorbs a
tail whose quadratic form is smaller than that margin.  The module derives the
quadratic tail bound from the exact Frobenius sum of the entrywise moment
budgets, then applies it to every principal block.
-/

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- The shifted Hankel block of degree `d` associated to a real moment sequence. -/
def finiteDegreeShiftedHankel (m : ℕ → ℝ) (d : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => m (i.1 + j.1 + 1)

/-- The Frobenius tail budget formed from the shifted moment budgets. -/
noncomputable def finiteDegreeShiftedHankelFrobeniusBudget (eta : ℕ → ℝ) (d : ℕ) : ℝ :=
  √(∑ i : Fin (d + 1), ∑ j : Fin (d + 1), eta (i.1 + j.1 + 1) ^ 2)

/-- The exact absolute row-sum tail budget of a shifted Hankel block. -/
noncomputable def finiteDegreeShiftedHankelRowSumBudget (eta : ℕ → ℝ) (d : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin (d + 1) => ∑ j : Fin (d + 1), eta (i.1 + j.1 + 1))

/-- Every row sum is bounded by the exact finite maximum defining the row-sum budget. -/
theorem shiftedHankel_rowSum_le_rowSumBudget (eta : ℕ → ℝ) (d : ℕ) (i : Fin (d + 1)) :
    (∑ j : Fin (d + 1), eta (i.1 + j.1 + 1)) ≤
      finiteDegreeShiftedHankelRowSumBudget eta d := by
  unfold finiteDegreeShiftedHankelRowSumBudget
  exact Finset.le_sup' (s := (Finset.univ : Finset (Fin (d + 1))))
    (f := fun i : Fin (d + 1) => ∑ j : Fin (d + 1), eta (i.1 + j.1 + 1))
    (Finset.mem_univ i)

/-- The shifted Hankel block is Hermitian over the reals. -/
theorem finiteDegreeShiftedHankel_isHermitian (m : ℕ → ℝ) (d : ℕ) :
    (finiteDegreeShiftedHankel m d).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp [finiteDegreeShiftedHankel, Nat.add_comm]

/-- Splitting a moment sequence splits its shifted Hankel block entrywise. -/
theorem finiteDegreeShiftedHankel_add (L E : ℕ → ℝ) (d : ℕ) :
    finiteDegreeShiftedHankel (L + E) d =
      finiteDegreeShiftedHankel L d + finiteDegreeShiftedHankel E d := by
  ext i j
  simp [finiteDegreeShiftedHankel]

/-- The quadratic form of a finite real matrix is bounded by its Frobenius sum. -/
theorem abs_dotProduct_mulVec_le_frobenius {n : ℕ}
    (R : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    |x ⬝ᵥ R *ᵥ x| ≤
      √(∑ i : Fin n, ∑ j : Fin n, |R i j| ^ 2) * (x ⬝ᵥ x) := by
  have hquad : x ⬝ᵥ R *ᵥ x = ∑ i, ∑ j, x i * R i j * x j := by
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hquad]
  have habs :
      |∑ i, ∑ j, x i * R i j * x j| ≤
        ∑ i, ∑ j, |R i j| * |x i * x j| := by
    calc
      |∑ i, ∑ j, x i * R i j * x j| ≤
          ∑ i, ∑ j, |x i * R i j * x j| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun j _ => le_rfl
      _ = ∑ i, ∑ j, |R i j| * |x i * x j| := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_mul, abs_mul]
        ring
  have hcs :
      (∑ i : Fin n, ∑ j : Fin n, |R i j| * |x i * x j|) ≤
        √(∑ i : Fin n, ∑ j : Fin n, |R i j| ^ 2) *
          √(∑ i : Fin n, ∑ j : Fin n, |x i * x j| ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt
      (Finset.univ : Finset (Fin n × Fin n))
      (fun ij : Fin n × Fin n => |R ij.1 ij.2|)
      (fun ij : Fin n × Fin n => |x ij.1 * x ij.2|)
    rw [← Finset.univ_product_univ] at h
    rw [Finset.sum_product, Finset.sum_product, Finset.sum_product] at h
    simpa using h
  have hsquare :
      √(∑ i : Fin n, ∑ j : Fin n, |x i * x j| ^ 2) = x ⬝ᵥ x := by
    have hsum :
        (∑ i : Fin n, ∑ j : Fin n, |x i * x j| ^ 2) = (x ⬝ᵥ x) ^ 2 := by
      calc
        (∑ i : Fin n, ∑ j : Fin n, |x i * x j| ^ 2) =
            ∑ i, ∑ j, x i ^ 2 * x j ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [sq_abs, mul_pow]
        _ = (∑ i, x i ^ 2) * ∑ j, x j ^ 2 := by
              rw [Finset.sum_mul_sum]
        _ = (x ⬝ᵥ x) ^ 2 := by
              simp only [dotProduct, pow_two]
    rw [hsum, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  calc
    |∑ i, ∑ j, x i * R i j * x j| ≤
        ∑ i, ∑ j, |R i j| * |x i * x j| := habs
    _ ≤ √(∑ i : Fin n, ∑ j : Fin n, |R i j| ^ 2) *
          √(∑ i : Fin n, ∑ j : Fin n, |x i * x j| ^ 2) := hcs
    _ = √(∑ i : Fin n, ∑ j : Fin n, |R i j| ^ 2) * (x ⬝ᵥ x) := by rw [hsquare]

/-- Entrywise shifted-moment bounds control the exact Frobenius tail budget. -/
theorem shiftedHankelFrobeniusBudget_le
    {E eta : ℕ → ℝ} {d : ℕ}
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1)) :
    √(∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        |E (i.1 + j.1 + 1)| ^ 2) ≤
      finiteDegreeShiftedHankelFrobeniusBudget eta d := by
  unfold finiteDegreeShiftedHankelFrobeniusBudget
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  refine Finset.sum_le_sum fun j _ => ?_
  have hnonneg : 0 ≤ eta (i.1 + j.1 + 1) :=
    (abs_nonneg _).trans (hE i j)
  nlinarith [abs_nonneg (E (i.1 + j.1 + 1)), hE i j]

/-- The shifted tail quadratic form is bounded by the exact Frobenius budget. -/
theorem abs_shiftedHankelTailQuadratic_le_frobeniusBudget
    {E eta : ℕ → ℝ} {d : ℕ}
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (x : Fin (d + 1) → ℝ) :
    |x ⬝ᵥ finiteDegreeShiftedHankel E d *ᵥ x| ≤
      finiteDegreeShiftedHankelFrobeniusBudget eta d * (x ⬝ᵥ x) := by
  have hquad := abs_dotProduct_mulVec_le_frobenius
    (finiteDegreeShiftedHankel E d) x
  have hbudget := shiftedHankelFrobeniusBudget_le hE
  have hnorm : 0 ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  calc
    |x ⬝ᵥ finiteDegreeShiftedHankel E d *ᵥ x| ≤
        √(∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          |E (i.1 + j.1 + 1)| ^ 2) * (x ⬝ᵥ x) := by
            simpa only [finiteDegreeShiftedHankel] using hquad
    _ ≤ finiteDegreeShiftedHankelFrobeniusBudget eta d * (x ⬝ᵥ x) :=
      mul_le_mul_of_nonneg_right hbudget hnorm

/-- A positive bulk margin larger than a certified quadratic tail budget makes the full shifted
Hankel block positive definite. -/
theorem finiteDegreeShiftedHankel_posDef_of_quadratic_tail_margin
    {L E : ℕ → ℝ} {d : ℕ} {mu beta : ℝ}
    (hbulk : ∀ x : Fin (d + 1) → ℝ,
      mu * (x ⬝ᵥ x) ≤ x ⬝ᵥ finiteDegreeShiftedHankel L d *ᵥ x)
    (htail : ∀ x : Fin (d + 1) → ℝ,
      |x ⬝ᵥ finiteDegreeShiftedHankel E d *ᵥ x| ≤ beta * (x ⬝ᵥ x))
    (hmargin : beta < mu) :
    (finiteDegreeShiftedHankel (L + E) d).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (finiteDegreeShiftedHankel_isHermitian (L + E) d) ?_
  intro x hx
  have hstar : star x = x := by
    ext i
    simp
  rw [hstar]
  have hxpos : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne
      (by
        rw [dotProduct]
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
      (Ne.symm fun h => hx ((dotProduct_self_eq_zero).mp h))
  have htailLower :
      -(beta * (x ⬝ᵥ x)) ≤
        x ⬝ᵥ finiteDegreeShiftedHankel E d *ᵥ x := by
    linarith [neg_abs_le (x ⬝ᵥ finiteDegreeShiftedHankel E d *ᵥ x), htail x]
  have hsplit :
      x ⬝ᵥ finiteDegreeShiftedHankel (L + E) d *ᵥ x =
        x ⬝ᵥ finiteDegreeShiftedHankel L d *ᵥ x +
          x ⬝ᵥ finiteDegreeShiftedHankel E d *ᵥ x := by
    rw [finiteDegreeShiftedHankel_add, Matrix.add_mulVec, dotProduct_add]
  have hgap : 0 <
      (mu - beta) * (x ⬝ᵥ x) :=
    mul_pos (sub_pos.mpr hmargin) hxpos
  nlinarith [hbulk x]

/-- A positive bulk margin larger than the Frobenius tail budget makes the full shifted
Hankel block positive definite. -/
theorem finiteDegreeShiftedHankel_posDef_of_frobenius_margin
    {L E eta : ℕ → ℝ} {d : ℕ} {mu : ℝ}
    (hbulk : ∀ x : Fin (d + 1) → ℝ,
      mu * (x ⬝ᵥ x) ≤ x ⬝ᵥ finiteDegreeShiftedHankel L d *ᵥ x)
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelFrobeniusBudget eta d < mu) :
    (finiteDegreeShiftedHankel (L + E) d).PosDef :=
  finiteDegreeShiftedHankel_posDef_of_quadratic_tail_margin hbulk
    (fun x => abs_shiftedHankelTailQuadratic_le_frobeniusBudget hE x) hmargin

/-- Every principal determinant is positive once the certified Frobenius margin holds. -/
theorem finiteDegreeShiftedHankel_principal_det_pos_of_frobenius_margin
    {L E eta : ℕ → ℝ} {d r : ℕ} {mu : ℝ}
    (hbulk : ∀ x : Fin (d + 1) → ℝ,
      mu * (x ⬝ᵥ x) ≤ x ⬝ᵥ finiteDegreeShiftedHankel L d *ᵥ x)
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelFrobeniusBudget eta d < mu)
    (e : Fin r → Fin (d + 1)) (he : Function.Injective e) :
    0 < ((finiteDegreeShiftedHankel (L + E) d).submatrix e e).det := by
  exact (finiteDegreeShiftedHankel_posDef_of_frobenius_margin hbulk hE hmargin |>.submatrix he).det_pos

/-- The shifted block controls its own quadratic form by the Frobenius norm of its entries. -/
theorem abs_shiftedHankelQuadratic_le_own_frobeniusBudget
    (m : ℕ → ℝ) (d : ℕ) (x : Fin (d + 1) → ℝ) :
    |x ⬝ᵥ finiteDegreeShiftedHankel m d *ᵥ x| ≤
      finiteDegreeShiftedHankelFrobeniusBudget m d * (x ⬝ᵥ x) := by
  simpa only [finiteDegreeShiftedHankel, finiteDegreeShiftedHankelFrobeniusBudget, sq_abs]
    using (abs_dotProduct_mulVec_le_frobenius (finiteDegreeShiftedHankel m d) x)

/-- The Euclidean square of a nonzero finite real vector is strictly positive. -/
theorem finiteDegreeShiftedHankel_dotProduct_self_pos {d : ℕ}
    (x : Fin (d + 1) → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  exact lt_of_le_of_ne
    (by
      rw [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
    (Ne.symm fun h => hx ((dotProduct_self_eq_zero).mp h))

/-- The Rayleigh quotient of a finite shifted Hankel block at a nonzero real vector. -/
noncomputable def finiteDegreeShiftedHankelRayleigh (m : ℕ → ℝ) (d : ℕ)
    (x : {x : Fin (d + 1) → ℝ // x ≠ 0}) : ℝ :=
  (x.1 ⬝ᵥ finiteDegreeShiftedHankel m d *ᵥ x.1) / (x.1 ⬝ᵥ x.1)

/-- The literal smallest spectral (Rayleigh) value of a finite shifted Hankel block. -/
noncomputable def finiteDegreeShiftedHankelLambdaMin (m : ℕ → ℝ) (d : ℕ) : ℝ :=
  sInf (Set.range (finiteDegreeShiftedHankelRayleigh m d))

/-- The Rayleigh spectrum of a finite shifted Hankel block is bounded below. -/
theorem finiteDegreeShiftedHankel_rayleigh_bddBelow (m : ℕ → ℝ) (d : ℕ) :
    BddBelow (Set.range (finiteDegreeShiftedHankelRayleigh m d)) := by
  refine ⟨-finiteDegreeShiftedHankelFrobeniusBudget m d, ?_⟩
  rintro q ⟨x, rfl⟩
  unfold finiteDegreeShiftedHankelRayleigh
  have hxpos := finiteDegreeShiftedHankel_dotProduct_self_pos x.1 x.2
  have hquad := abs_shiftedHankelQuadratic_le_own_frobeniusBudget m d x.1
  exact (le_div_iff₀ hxpos).mpr (by
    nlinarith [neg_abs_le (x.1 ⬝ᵥ finiteDegreeShiftedHankel m d *ᵥ x.1)])

/-- The literal Rayleigh minimum is a lower bound for every nonzero vector quotient. -/
theorem finiteDegreeShiftedHankel_lambdaMin_le_rayleigh
    (m : ℕ → ℝ) (d : ℕ) (x : Fin (d + 1) → ℝ) (hx : x ≠ 0) :
    finiteDegreeShiftedHankelLambdaMin m d ≤
      (x ⬝ᵥ finiteDegreeShiftedHankel m d *ᵥ x) / (x ⬝ᵥ x) := by
  unfold finiteDegreeShiftedHankelLambdaMin
  apply csInf_le (finiteDegreeShiftedHankel_rayleigh_bddBelow m d)
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The literal Rayleigh minimum gives the bulk quadratic lower bound. -/
theorem finiteDegreeShiftedHankel_lambdaMin_mul_dotProduct_le
    (m : ℕ → ℝ) (d : ℕ) (x : Fin (d + 1) → ℝ) :
    finiteDegreeShiftedHankelLambdaMin m d * (x ⬝ᵥ x) ≤
      x ⬝ᵥ finiteDegreeShiftedHankel m d *ᵥ x := by
  by_cases hx : x = 0
  · subst hx
    simp
  · exact (le_div_iff₀ (finiteDegreeShiftedHankel_dotProduct_self_pos x hx)).mp
      (finiteDegreeShiftedHankel_lambdaMin_le_rayleigh m d x hx)

/-- The shifted tail quadratic form is bounded by the exact maximum absolute row sum. -/
theorem abs_shiftedHankelTailQuadratic_le_rowSumBudget
    {E eta : ℕ → ℝ} {d : ℕ}
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (x : Fin (d + 1) → ℝ) :
    |x ⬝ᵥ finiteDegreeShiftedHankel E d *ᵥ x| ≤
      finiteDegreeShiftedHankelRowSumBudget eta d * (x ⬝ᵥ x) := by
  have hquad : x ⬝ᵥ finiteDegreeShiftedHankel E d *ᵥ x =
      ∑ i, ∑ j, x i * E (i.1 + j.1 + 1) * x j := by
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [finiteDegreeShiftedHankel]
    ring
  rw [hquad]
  have habs :
      |∑ i, ∑ j, x i * E (i.1 + j.1 + 1) * x j| ≤
        ∑ i, ∑ j, |E (i.1 + j.1 + 1)| * |x i * x j| := by
    calc
      |∑ i, ∑ j, x i * E (i.1 + j.1 + 1) * x j| ≤
          ∑ i, ∑ j, |x i * E (i.1 + j.1 + 1) * x j| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun j _ => le_rfl
      _ = ∑ i, ∑ j, |E (i.1 + j.1 + 1)| * |x i * x j| := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_mul, abs_mul]
        ring
  have hrow : ∀ i : Fin (d + 1),
      ∑ j : Fin (d + 1), |E (i.1 + j.1 + 1)| ≤
        finiteDegreeShiftedHankelRowSumBudget eta d := by
    intro i
    calc
      ∑ j : Fin (d + 1), |E (i.1 + j.1 + 1)| ≤
          ∑ j : Fin (d + 1), eta (i.1 + j.1 + 1) :=
        Finset.sum_le_sum fun j _ => hE i j
      _ ≤ finiteDegreeShiftedHankelRowSumBudget eta d :=
        shiftedHankel_rowSum_le_rowSumBudget eta d i
  have hbound := GaloisForLFunctions.weighted_double_sum_le_rowBound
    (b := x) (H := finiteDegreeShiftedHankelRowSumBudget eta d)
    (K := fun i j : Fin (d + 1) => |E (i.1 + j.1 + 1)|)
    (by
      intro i j
      simp [Nat.add_comm])
    (by
      intro i j
      exact abs_nonneg _)
    hrow
  calc
    |∑ i, ∑ j, x i * E (i.1 + j.1 + 1) * x j| ≤
        ∑ i, ∑ j, |E (i.1 + j.1 + 1)| * |x i * x j| := habs
    _ = ∑ i, ∑ j, |x i| * |x j| * |E (i.1 + j.1 + 1)| := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul]
      ring
    _ ≤ finiteDegreeShiftedHankelRowSumBudget eta d * ∑ i, (x i) ^ 2 := hbound
    _ = finiteDegreeShiftedHankelRowSumBudget eta d * (x ⬝ᵥ x) := by
      simp only [dotProduct, pow_two]

/-- A positive bulk margin larger than the exact row-sum tail budget is positive definite. -/
theorem finiteDegreeShiftedHankel_posDef_of_rowSum_margin
    {L E eta : ℕ → ℝ} {d : ℕ} {mu : ℝ}
    (hbulk : ∀ x : Fin (d + 1) → ℝ,
      mu * (x ⬝ᵥ x) ≤ x ⬝ᵥ finiteDegreeShiftedHankel L d *ᵥ x)
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelRowSumBudget eta d < mu) :
    (finiteDegreeShiftedHankel (L + E) d).PosDef :=
  finiteDegreeShiftedHankel_posDef_of_quadratic_tail_margin hbulk
    (fun x => abs_shiftedHankelTailQuadratic_le_rowSumBudget hE x) hmargin

/-- Every principal determinant is positive once the certified row-sum margin holds. -/
theorem finiteDegreeShiftedHankel_principal_det_pos_of_rowSum_margin
    {L E eta : ℕ → ℝ} {d r : ℕ} {mu : ℝ}
    (hbulk : ∀ x : Fin (d + 1) → ℝ,
      mu * (x ⬝ᵥ x) ≤ x ⬝ᵥ finiteDegreeShiftedHankel L d *ᵥ x)
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelRowSumBudget eta d < mu)
    (e : Fin r → Fin (d + 1)) (he : Function.Injective e) :
    0 < ((finiteDegreeShiftedHankel (L + E) d).submatrix e e).det := by
  exact (finiteDegreeShiftedHankel_posDef_of_rowSum_margin hbulk hE hmargin |>.submatrix he).det_pos

/-- The literal `lambda_min > F_d` gate makes the full shifted Hankel block positive definite. -/
theorem finiteDegreeShiftedHankel_posDef_of_lambdaMin_frobenius_margin
    {L E eta : ℕ → ℝ} {d : ℕ}
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelFrobeniusBudget eta d <
      finiteDegreeShiftedHankelLambdaMin L d) :
    (finiteDegreeShiftedHankel (L + E) d).PosDef :=
  finiteDegreeShiftedHankel_posDef_of_frobenius_margin
    (finiteDegreeShiftedHankel_lambdaMin_mul_dotProduct_le L d) hE hmargin

/-- The literal `lambda_min > G_d` gate makes the full shifted Hankel block positive definite. -/
theorem finiteDegreeShiftedHankel_posDef_of_lambdaMin_rowSum_margin
    {L E eta : ℕ → ℝ} {d : ℕ}
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelRowSumBudget eta d <
      finiteDegreeShiftedHankelLambdaMin L d) :
    (finiteDegreeShiftedHankel (L + E) d).PosDef :=
  finiteDegreeShiftedHankel_posDef_of_rowSum_margin
    (finiteDegreeShiftedHankel_lambdaMin_mul_dotProduct_le L d) hE hmargin

/-- Every principal determinant is positive under the literal `lambda_min > F_d` gate. -/
theorem finiteDegreeShiftedHankel_principal_det_pos_of_lambdaMin_frobenius_margin
    {L E eta : ℕ → ℝ} {d r : ℕ}
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelFrobeniusBudget eta d <
      finiteDegreeShiftedHankelLambdaMin L d)
    (e : Fin r → Fin (d + 1)) (he : Function.Injective e) :
    0 < ((finiteDegreeShiftedHankel (L + E) d).submatrix e e).det := by
  exact (finiteDegreeShiftedHankel_posDef_of_lambdaMin_frobenius_margin hE hmargin |>.submatrix he).det_pos

/-- Every principal determinant is positive under the literal `lambda_min > G_d` gate. -/
theorem finiteDegreeShiftedHankel_principal_det_pos_of_lambdaMin_rowSum_margin
    {L E eta : ℕ → ℝ} {d r : ℕ}
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelRowSumBudget eta d <
      finiteDegreeShiftedHankelLambdaMin L d)
    (e : Fin r → Fin (d + 1)) (he : Function.Injective e) :
    0 < ((finiteDegreeShiftedHankel (L + E) d).submatrix e e).det := by
  exact (finiteDegreeShiftedHankel_posDef_of_lambdaMin_rowSum_margin hE hmargin |>.submatrix he).det_pos

/-- Either exact tail gate (`lambda_min > F_d` or `lambda_min > G_d`) closes the full block. -/
theorem finiteDegreeShiftedHankel_posDef_of_lambdaMin_margin
    {L E eta : ℕ → ℝ} {d : ℕ}
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelFrobeniusBudget eta d <
        finiteDegreeShiftedHankelLambdaMin L d ∨
      finiteDegreeShiftedHankelRowSumBudget eta d <
        finiteDegreeShiftedHankelLambdaMin L d) :
    (finiteDegreeShiftedHankel (L + E) d).PosDef := by
  rcases hmargin with hmargin | hmargin
  · exact finiteDegreeShiftedHankel_posDef_of_lambdaMin_frobenius_margin hE hmargin
  · exact finiteDegreeShiftedHankel_posDef_of_lambdaMin_rowSum_margin hE hmargin

/-- Every principal determinant is positive under either literal finite-degree tail gate. -/
theorem finiteDegreeShiftedHankel_principal_det_pos_of_lambdaMin_margin
    {L E eta : ℕ → ℝ} {d r : ℕ}
    (hE : ∀ i j : Fin (d + 1),
      |E (i.1 + j.1 + 1)| ≤ eta (i.1 + j.1 + 1))
    (hmargin : finiteDegreeShiftedHankelFrobeniusBudget eta d <
        finiteDegreeShiftedHankelLambdaMin L d ∨
      finiteDegreeShiftedHankelRowSumBudget eta d <
        finiteDegreeShiftedHankelLambdaMin L d)
    (e : Fin r → Fin (d + 1)) (he : Function.Injective e) :
    0 < ((finiteDegreeShiftedHankel (L + E) d).submatrix e e).det := by
  exact (finiteDegreeShiftedHankel_posDef_of_lambdaMin_margin hE hmargin |>.submatrix he).det_pos

end GaloisForLFunctions.HTGeometry
