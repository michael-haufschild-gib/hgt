import GaloisForLFunctions.HTGeometry.GammaShiftLadderPolynomial

/-!
# The shifted ladder coefficients are polynomials in the shift

`shiftLadderPoly mu M` is built from `C mu` and `X` by ring operations alone, so each of its
`X`-coefficients is a polynomial in `mu`.  Making that precise means running the same recursion once
more in `(ℂ[Y])[X]` and mapping down by `Y ↦ mu`.

The degree bookkeeping is the point: the two-variable ladder polynomial is *sub-graded*, meaning its
`X^{j+1}` coefficient has `Y`-degree at most `j`.  Hence `shiftLadderCoeff mu M`, which reads the
`X^{M+2}` coefficient, is a polynomial in `mu` of degree at most `M+1` — exactly the triangularity
the power-sum reading of `finite-archimedean-gamma-product-boundary-law` §5 needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- `Y`-degree bounded by `X`-degree. -/
def Graded (P : Polynomial (Polynomial ℂ)) : Prop := ∀ j : ℕ, ((P.coeff j).natDegree) ≤ j

/-- `Y`-degree bounded by `X`-degree minus one, with vanishing constant term. -/
def SubGraded (P : Polynomial (Polynomial ℂ)) : Prop :=
  P.coeff 0 = 0 ∧ ∀ j : ℕ, ((P.coeff (j + 1)).natDegree) ≤ j

theorem graded_one : Graded 1 := by
  intro j
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · have hj : j ≠ 0 := by omega
    rw [Polynomial.coeff_one]
    simp [hj]

theorem graded_X : Graded X := by
  intro j
  rw [Polynomial.coeff_X]
  by_cases h : 1 = j
  · simp [h]
  · simp [h]

theorem Graded.add {P Q : Polynomial (Polynomial ℂ)} (hP : Graded P) (hQ : Graded Q) :
    Graded (P + Q) := by
  intro j
  rw [Polynomial.coeff_add]
  exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (hP j) (hQ j))

theorem Graded.mul {P Q : Polynomial (Polynomial ℂ)} (hP : Graded P) (hQ : Graded Q) :
    Graded (P * Q) := by
  intro j
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x hx => ?_
  have hx' : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  refine le_trans Polynomial.natDegree_mul_le ?_
  have := hP x.1
  have := hQ x.2
  omega

theorem Graded.pow {P : Polynomial (Polynomial ℂ)} (hP : Graded P) : ∀ n : ℕ, Graded (P ^ n)
  | 0 => by simpa using graded_one
  | (n + 1) => by
      rw [pow_succ]
      exact (hP.pow n).mul hP

theorem graded_C_C (c : ℂ) : Graded (C (Polynomial.C c)) := by
  intro j
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · rw [Polynomial.coeff_C]
    simp [Nat.ne_of_gt h]

/-- `C d * X^n` is graded as soon as `deg d ≤ n`. -/
theorem graded_C_mul_X_pow {d : Polynomial ℂ} {n : ℕ} (hd : d.natDegree ≤ n) :
    Graded (C d * X ^ n) := by
  intro j
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : j = n
  · subst h; simpa using hd
  · simp [h]

theorem graded_C_muY_mul_X : Graded (C (Polynomial.X : Polynomial ℂ) * X) := by
  have h : (Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by simp
  simpa using graded_C_mul_X_pow (n := 1) h

theorem SubGraded.add {P Q : Polynomial (Polynomial ℂ)} (hP : SubGraded P) (hQ : SubGraded Q) :
    SubGraded (P + Q) := by
  refine ⟨by rw [Polynomial.coeff_add, hP.1, hQ.1, add_zero], fun j => ?_⟩
  rw [Polynomial.coeff_add]
  exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (hP.2 j) (hQ.2 j))

theorem SubGraded.neg {P : Polynomial (Polynomial ℂ)} (hP : SubGraded P) : SubGraded (-P) := by
  refine ⟨by rw [Polynomial.coeff_neg, hP.1, neg_zero], fun j => ?_⟩
  rw [Polynomial.coeff_neg, Polynomial.natDegree_neg]
  exact hP.2 j

theorem SubGraded.sub {P Q : Polynomial (Polynomial ℂ)} (hP : SubGraded P) (hQ : SubGraded Q) :
    SubGraded (P - Q) := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg

theorem SubGraded.mul_graded {P Q : Polynomial (Polynomial ℂ)} (hP : SubGraded P) (hQ : Graded Q) :
    SubGraded (P * Q) := by
  constructor
  · rw [Polynomial.mul_coeff_zero, hP.1, zero_mul]
  · intro j
    rw [Polynomial.coeff_mul]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x hx => ?_
    have hx' : x.1 + x.2 = j + 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rcases Nat.eq_zero_or_pos x.1 with h | h
    · rw [h, hP.1, zero_mul]
      simp
    · obtain ⟨i, hi⟩ : ∃ i, x.1 = i + 1 := ⟨x.1 - 1, by omega⟩
      refine le_trans Polynomial.natDegree_mul_le ?_
      have h1 := hP.2 i
      have h2 := hQ x.2
      rw [hi] at hx' ⊢
      omega

theorem Graded.mul_subGraded {P Q : Polynomial (Polynomial ℂ)} (hP : Graded P) (hQ : SubGraded Q) :
    SubGraded (P * Q) := by
  rw [mul_comm]
  exact hQ.mul_graded hP

theorem subGraded_X_pow_succ (n : ℕ) : SubGraded ((X : Polynomial (Polynomial ℂ)) ^ (n + 1)) := by
  constructor
  · rw [Polynomial.coeff_X_pow]
    simp
  · intro j
    rw [Polynomial.coeff_X_pow]
    by_cases h : j + 1 = n + 1
    · simp [h]
    · have hj : j ≠ n := by omega
      simp [hj]

theorem subGraded_one_sub_one_add_X_pow (n : ℕ) :
    SubGraded (1 - (1 + X : Polynomial (Polynomial ℂ)) ^ n) := by
  constructor
  · rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_one_add_X_pow]
    simp
  · intro j
    rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_one_add_X_pow]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    refine max_le ?_ ?_
    · simp
    · simp


/-- The two-variable forced ladder coefficient. -/
def ladderCoeffOfTwo (P : Polynomial (Polynomial ℂ)) (M : ℕ) : Polynomial ℂ :=
  Polynomial.C (((M : ℂ) + 1)⁻¹) * (P.coeff (M + 2) + Polynomial.C ((-1) ^ M / ((M : ℂ) + 2)))

/-- The shifted ladder polynomial with the shift kept as a second indeterminate. -/
def shiftLadderPolyTwo : ℕ → Polynomial (Polynomial ℂ)
  | 0 => -(C (Polynomial.X : Polynomial ℂ)) * X ^ 2
  | (M + 1) =>
      (1 + X) * shiftLadderPolyTwo M
        - C (Polynomial.C ((-1 : ℂ) ^ (M + 1) / ((M : ℂ) + 2)))
            * (X ^ (M + 2) * ((1 + X) ^ (M + 1) * (1 + C (Polynomial.X : Polynomial ℂ) * X)))
        + C (ladderCoeffOfTwo (shiftLadderPolyTwo M) M)
            * (X ^ (M + 1) * ((1 + C (Polynomial.X : Polynomial ℂ) * X)
                * (1 - (1 + X) ^ (M + 1))))

theorem shiftLadderPolyTwo_succ (M : ℕ) :
    shiftLadderPolyTwo (M + 1) =
      (1 + X) * shiftLadderPolyTwo M
        - C (Polynomial.C ((-1 : ℂ) ^ (M + 1) / ((M : ℂ) + 2)))
            * (X ^ (M + 2) * ((1 + X) ^ (M + 1) * (1 + C (Polynomial.X : Polynomial ℂ) * X)))
        + C (ladderCoeffOfTwo (shiftLadderPolyTwo M) M)
            * (X ^ (M + 1) * ((1 + C (Polynomial.X : Polynomial ℂ) * X)
                * (1 - (1 + X) ^ (M + 1)))) := rfl

theorem eval_ladderCoeffOfTwo (mu : ℂ) (P : Polynomial (Polynomial ℂ)) (M : ℕ) :
    (ladderCoeffOfTwo P M).eval mu = ladderCoeffOf (P.map (Polynomial.evalRingHom mu)) M := by
  rw [ladderCoeffOfTwo, ladderCoeffOf, Polynomial.coeff_map]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.coe_evalRingHom, div_eq_mul_inv]
  ring

/-- **The two-variable ladder specialises to the one-variable ladder.** -/
theorem map_shiftLadderPolyTwo (mu : ℂ) : ∀ M : ℕ,
    (shiftLadderPolyTwo M).map (Polynomial.evalRingHom mu) = shiftLadderPoly mu M := by
  intro M
  induction M with
  | zero =>
      rw [shiftLadderPolyTwo, shiftLadderPoly]
      simp
  | succ M ih =>
      rw [shiftLadderPolyTwo_succ, shiftLadderPoly_succ, shiftLadderCoeff]
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_one, Polynomial.map_X, Polynomial.map_C, Polynomial.coe_evalRingHom,
        Polynomial.eval_X]
      rw [ih, eval_ladderCoeffOfTwo, ih]
      simp

/-- **The two-variable ladder polynomial is sub-graded.** -/
theorem subGraded_shiftLadderPolyTwo : ∀ M : ℕ, SubGraded (shiftLadderPolyTwo M) := by
  intro M
  induction M with
  | zero =>
      have h : -(C (Polynomial.X : Polynomial ℂ)) * (X : Polynomial (Polynomial ℂ)) ^ 2
          = -((C (Polynomial.X : Polynomial ℂ) * X) * X) := by ring
      rw [shiftLadderPolyTwo, h]
      exact (graded_C_muY_mul_X.mul_subGraded (by simpa using subGraded_X_pow_succ 0)).neg
  | succ M ih =>
      have hd : (ladderCoeffOfTwo (shiftLadderPolyTwo M) M).natDegree ≤ M + 1 := by
        rw [ladderCoeffOfTwo]
        refine le_trans Polynomial.natDegree_mul_le ?_
        have h1 : (Polynomial.C (((M : ℂ) + 1)⁻¹)).natDegree = 0 := Polynomial.natDegree_C _
        have h2 : ((shiftLadderPolyTwo M).coeff (M + 2)
            + Polynomial.C ((-1 : ℂ) ^ M / ((M : ℂ) + 2))).natDegree ≤ M + 1 := by
          refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
          · exact ih.2 (M + 1)
          · simp
        omega
      rw [shiftLadderPolyTwo_succ]
      refine SubGraded.add (SubGraded.sub ?_ ?_) ?_
      · exact (graded_one.add graded_X).mul_subGraded ih
      · exact (graded_C_C _).mul_subGraded
          ((subGraded_X_pow_succ (M + 1)).mul_graded
            (((graded_one.add graded_X).pow (M + 1)).mul (graded_one.add graded_C_muY_mul_X)))
      · have hassoc : C (ladderCoeffOfTwo (shiftLadderPolyTwo M) M)
            * ((X : Polynomial (Polynomial ℂ)) ^ (M + 1)
              * ((1 + C (Polynomial.X : Polynomial ℂ) * X) * (1 - (1 + X) ^ (M + 1))))
            = (C (ladderCoeffOfTwo (shiftLadderPolyTwo M) M) * X ^ (M + 1))
              * ((1 + C (Polynomial.X : Polynomial ℂ) * X) * (1 - (1 + X) ^ (M + 1))) := by ring
        rw [hassoc]
        exact (graded_C_mul_X_pow hd).mul_subGraded
          ((graded_one.add graded_C_muY_mul_X).mul_subGraded
            (subGraded_one_sub_one_add_X_pow (M + 1)))

/-- The `M`-th shifted ladder coefficient, as a polynomial in the shift. -/
def shiftLadderCoeffPoly (M : ℕ) : Polynomial ℂ := ladderCoeffOfTwo (shiftLadderPolyTwo M) M

/-- **Degree bound**: the `M`-th ladder coefficient has degree at most `M+1` in the shift. -/
theorem natDegree_shiftLadderCoeffPoly_le (M : ℕ) : (shiftLadderCoeffPoly M).natDegree ≤ M + 1 := by
  rw [shiftLadderCoeffPoly, ladderCoeffOfTwo]
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : (Polynomial.C (((M : ℂ) + 1)⁻¹)).natDegree = 0 := Polynomial.natDegree_C _
  have h2 : ((shiftLadderPolyTwo M).coeff (M + 2)
      + Polynomial.C ((-1 : ℂ) ^ M / ((M : ℂ) + 2))).natDegree ≤ M + 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact (subGraded_shiftLadderPolyTwo M).2 (M + 1)
    · simp
  omega

/-- **The ladder coefficient is a polynomial in the shift.** -/
theorem shiftLadderCoeff_eq_eval (mu : ℂ) (M : ℕ) :
    shiftLadderCoeff mu M = (shiftLadderCoeffPoly M).eval mu := by
  rw [shiftLadderCoeff, shiftLadderCoeffPoly, eval_ladderCoeffOfTwo, map_shiftLadderPolyTwo]

end

end GaloisForLFunctions.HTGeometry
