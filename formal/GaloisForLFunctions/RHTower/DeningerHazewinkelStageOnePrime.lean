import GaloisForLFunctions.RHTower.DeningerHazewinkelPrimeReduction

/-!
# Primeness of the first Hazewinkel stage

The first Hazewinkel determinantal ideal is identified exactly with the kernel of the monomial
moment map `X_j ↦ T^(j+1)`.  Every generator of the kernel is obtained from a literal `2 × 2`
Hankel minor; no finite-variable truncation or field base change is used.  Since the target is
` ℤ[T]`, this proves primeness over `ℤ`.
-/

namespace RHTower

noncomputable section

/-- Evaluation of the universal coefficient sequence on the rank-one moment curve. -/
def deningerHazewinkelRankOneEval : MvPolynomial ℕ ℤ →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C fun j => Polynomial.X ^ (j + 1)

/-- Inclusion of the rank-one parameter into the first universal coefficient. -/
def deningerHazewinkelRankOneInclude : Polynomial ℤ →+* MvPolynomial ℕ ℤ :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

/-- Retraction onto polynomials in the first universal coefficient. -/
def deningerHazewinkelRankOneRetract : MvPolynomial ℕ ℤ →+* MvPolynomial ℕ ℤ :=
  deningerHazewinkelRankOneInclude.comp deningerHazewinkelRankOneEval

@[simp] theorem deningerHazewinkelRankOneEval_X (j : ℕ) :
    deningerHazewinkelRankOneEval (MvPolynomial.X j) = Polynomial.X ^ (j + 1) := by
  simp [deningerHazewinkelRankOneEval]

@[simp] theorem deningerHazewinkelRankOneRetract_X (j : ℕ) :
    deningerHazewinkelRankOneRetract (MvPolynomial.X j) =
      MvPolynomial.X 0 ^ (j + 1) := by
  simp [deningerHazewinkelRankOneRetract, deningerHazewinkelRankOneInclude]

@[simp] theorem deningerHazewinkelRankOneEval_universalCoeff (s : ℕ) :
    deningerHazewinkelRankOneEval (deningerHazewinkelUniversalCoeff s) =
      Polynomial.X ^ s := by
  cases s <;> simp [deningerHazewinkelUniversalCoeff]

theorem deningerHazewinkelIdeal_one_le_ker_rankOneEval :
    deningerHazewinkelIdeal 1 ≤ RingHom.ker deningerHazewinkelRankOneEval := by
  rw [deningerHazewinkelIdeal, deningerMatrixMinorIdeal, Ideal.span_le]
  rintro z ⟨rows, cols, rfl⟩
  change deningerHazewinkelRankOneEval
    ((deningerHazewinkelUniversalHankel.submatrix rows cols).det) = 0
  rw [deningerHazewinkelRankOneEval.map_det]
  change Matrix.det (fun i j => deningerHazewinkelRankOneEval
    (deningerHazewinkelUniversalHankel (rows i) (cols j))) = 0
  rw [Matrix.det_fin_two]
  simp only [deningerHazewinkelUniversalHankel,
    deningerHazewinkelRankOneEval_universalCoeff]
  rw [← pow_add, ← pow_add]
  rw [show rows 0 + cols 0 + (rows 1 + cols 1) =
    rows 0 + cols 1 + (rows 1 + cols 0) by omega]
  simp

/-- The adjacent rank-one recurrence is a literal Hankel-minor relation. -/
theorem deningerHazewinkelRankOne_recurrence_mem (j : ℕ) :
    MvPolynomial.X (j + 1) - MvPolynomial.X j * MvPolynomial.X 0 ∈
      deningerHazewinkelIdeal 1 := by
  let rows : Fin 2 → ℕ := ![0, 1]
  let cols : Fin 2 → ℕ := ![0, j + 1]
  have h := deningerMatrixMinorDet_mem 2 deningerHazewinkelUniversalHankel rows cols
  change (deningerHazewinkelUniversalHankel.submatrix rows cols).det ∈
    deningerHazewinkelIdeal 1 at h
  simpa [rows, cols, Matrix.det_fin_two, Matrix.submatrix_apply,
    deningerHazewinkelUniversalHankel, deningerHazewinkelUniversalCoeff,
    mul_comm, Nat.add_comm] using h

/-- Every universal coefficient equals the corresponding power of `X_0` modulo `J₁`. -/
theorem deningerHazewinkelRankOne_X_sub_pow_mem (j : ℕ) :
    MvPolynomial.X j - MvPolynomial.X 0 ^ (j + 1) ∈
      deningerHazewinkelIdeal 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hr := deningerHazewinkelRankOne_recurrence_mem j
      have hmul := (deningerHazewinkelIdeal 1).mul_mem_right (MvPolynomial.X 0) ih
      convert (deningerHazewinkelIdeal 1).add_mem hr hmul using 1
      all_goals ring

theorem deningerHazewinkelRankOne_sub_retract_mem (p : MvPolynomial ℕ ℤ) :
    p - deningerHazewinkelRankOneRetract p ∈ deningerHazewinkelIdeal 1 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [deningerHazewinkelRankOneRetract, deningerHazewinkelRankOneInclude]
  | add p q hp hq =>
      rw [map_add]
      convert (deningerHazewinkelIdeal 1).add_mem hp hq using 1
      all_goals ring
  | mul_X p j hp =>
      rw [map_mul, deningerHazewinkelRankOneRetract_X]
      have hx := deningerHazewinkelRankOne_X_sub_pow_mem j
      have h₁ := (deningerHazewinkelIdeal 1).mul_mem_right (MvPolynomial.X j) hp
      have h₂ := (deningerHazewinkelIdeal 1).mul_mem_left
        (deningerHazewinkelRankOneRetract p) hx
      convert (deningerHazewinkelIdeal 1).add_mem h₁ h₂ using 1
      all_goals ring

theorem deningerHazewinkelRankOne_ker_le_ideal :
    RingHom.ker deningerHazewinkelRankOneEval ≤ deningerHazewinkelIdeal 1 := by
  intro p hp
  have hzero : deningerHazewinkelRankOneRetract p = 0 := by
    rw [deningerHazewinkelRankOneRetract, RingHom.comp_apply,
      RingHom.mem_ker.mp hp, map_zero]
  simpa [hzero] using deningerHazewinkelRankOne_sub_retract_mem p

/-- Exact kernel presentation of the first Hazewinkel stage. -/
theorem deningerHazewinkelIdeal_one_eq_ker_rankOneEval :
    deningerHazewinkelIdeal 1 = RingHom.ker deningerHazewinkelRankOneEval :=
  le_antisymm deningerHazewinkelIdeal_one_le_ker_rankOneEval
    deningerHazewinkelRankOne_ker_le_ideal

/-- The first positive Hazewinkel determinantal ideal is prime over `ℤ`. -/
theorem deningerHazewinkelIdeal_one_isPrime : (deningerHazewinkelIdeal 1).IsPrime := by
  rw [deningerHazewinkelIdeal_one_eq_ker_rankOneEval]
  exact RingHom.ker_isPrime deningerHazewinkelRankOneEval

/-- Corrected Hazewinkel multiplication at the first positive stage, over every commutative ring.
This is the first unconditional nonreduced-target instance of the universal stage theorem. -/
theorem deninger_hankelRankLT_three_mul_of_rankLT_two
    {A : Type*} [CommRing A] {u v : DeningerBigWittAdditive A}
    (hu : DeningerBigWittHankelRankLT 2 u)
    (hv : DeningerBigWittHankelRankLT 2 v) :
    DeningerBigWittHankelRankLT 3 (deningerBigWittMul u v) := by
  simpa [deningerCorrectedWittMulStageBound] using
    (deninger_hankelRankLT_mul_corrected_of_hazewinkel_isPrime
      (n := 1) (m := 1) (by omega) (by omega)
      deningerHazewinkelIdeal_one_isPrime deningerHazewinkelIdeal_one_isPrime hu hv)

end

end RHTower
