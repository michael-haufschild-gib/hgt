import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeAtFourTraceHasTwentyCosets

/-!
# The Hecke-at-four trace is a phased sum over Hecke points

The Hecke points of `Θ` at the inert prime `2` are `Θ^{(∞)}(w) = Θ(Aw)` (`heckeHigh`) and
`Θ^{(t)}(w) = Θ(A⁻¹T_{3t}w)` (`heckeLow`). For each of the twenty representatives the two factors of
`F_Θ(δw) = Θ(Aδw) Θ(A⁻¹δw)` are Hecke points, after moving a level-three matrix to the left
(`A T_{3t} = T_{6t} A`, `A⁻¹ L_c = L_{2c} A⁻¹`, `A W = W₊ (−A⁻¹T_{−3})`, `A⁻¹ W = W₋ (−A)`,
`A L_u = L₊(u) (−A⁻¹T_{−3u²})`). The only nontrivial multiplier is `κ(L₊(u)) = (−3u/−2)₃ = u`
(`complexCharacter_lowerUp`: Euler's criterion at `2`, whose residue field has four elements). Hence
(`heckeFourTrace_eq_hecke`), for `Θ` of multiplier `κ`,

`Tr F_Θ = Σ_t Θ^{(∞)} Θ^{(t)} + Σ_t Θ^{(t−1)} Θ^{(∞)} + Σ_{u, t} u Θ^{(t−u²)} Θ^{(t)}`,

`t ∈ {0, 1, ω, ω²}`, `u ∈ {1, ω, ω²}`. The last sum carries the cubic character `u` of `𝔽₄^×`: it is the 2-adic
cubic twist of the products of Hecke points.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein

/-! ### `−1` acts trivially -/

theorem neg_one_smul_hyperbolic (w : HyperbolicSpace) : (-1 : SL(2, ℂ)) • w = w := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  have h1 : (-1 : SL(2, ℂ))⁻¹ = -1 := inv_eq_of_mul_eq_one_right (by rw [neg_one_mul, neg_neg])
  have h : ((-1 : SL(2, ℂ)) * g)⁻¹ * g = -1 := by
    rw [mul_inv_rev, h1, mul_neg_one, neg_mul, inv_mul_cancel]
  rw [h]
  show ((-1 : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  exact Matrix.mem_unitaryGroup_iff.mpr (by simp)

theorem neg_smul_hyperbolic (g : SL(2, ℂ)) (w : HyperbolicSpace) : (-g) • w = g • w := by
  rw [← neg_one_mul g, mul_smul, neg_one_smul_hyperbolic]

/-! ### Euler's criterion at `2` -/

/-- `(ω^j/−2)₃ = ω^j`: the residue field at `2` has four elements, so Euler's exponent is `1`. -/
theorem symbol_root_neg_two (j : ℕ) (hj : j < 3) : symbol (omega ^ j) (-2) = omega ^ j := by
  haveI hmax : (Ideal.span {(-2 : O)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible CanonicalRowCompletion.negative_two_prime.irreducible
  have hgood : lambda ∉ Ideal.span {(-2 : O)} :=
    primary_maximal_divisor_good (-2) primary_neg_two _ (Ideal.subset_span rfl)
  rw [symbol_prime (-2) CanonicalRowCompletion.negative_two_prime primary_neg_two, primeValue_eq _ hgood]
  have hcard : Nat.card (O ⧸ Ideal.span {(-2 : O)}) = 4 := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, absNorm_span_neg_two]
  apply reduce_injective_on_roots _ hgood (cubicChar_values _ _ _) (Or.inr ⟨j, hj, rfl⟩)
  rw [cubicChar_reduce, hcard]
  norm_num

theorem uO_eq_pow (k : Fin 3) : uO k = omega ^ (k : ℕ) := by
  fin_cases k <;> simp [uO]

theorem uO_cube (k : Fin 3) : uO k ^ 3 = 1 := by
  rw [uO_eq_pow, ← pow_mul, mul_comm, pow_mul, omega_primitive.pow_eq_one, one_pow]

theorem symbol_uO_neg_two (k : Fin 3) : symbol (uO k) (-2) = uO k := by
  rw [uO_eq_pow]
  exact symbol_root_neg_two _ k.isLt

/-! ### The level-three matrices moved through `A` -/

/-- `W₊ = [[4, 3], [−3, −2]]`. -/
def wUp : levelThree :=
  ⟨⟨!![4, 3; -3, -2], by rw [Matrix.det_fin_two_of]; norm_num⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨1, by norm_num⟩
      · exact ⟨1, by norm_num⟩
      · exact ⟨-1, by norm_num⟩
      · exact ⟨-1, by norm_num⟩)⟩

/-- `W₋ = [[1, −3], [−3, 10]]`. -/
def wDown : levelThree :=
  ⟨⟨!![1, -3; -3, 10], by rw [Matrix.det_fin_two_of]; norm_num⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨0, by norm_num⟩
      · exact ⟨-1, by norm_num⟩
      · exact ⟨-1, by norm_num⟩
      · exact ⟨3, by norm_num⟩)⟩

/-- `L₊(u) = [[−2, −3u²], [−3u, −5]]` for `u³ = 1`. -/
def lowerUp (k : Fin 3) : levelThree :=
  ⟨⟨!![-2, -3 * uO k ^ 2; -3 * uO k, -5], by
      rw [Matrix.det_fin_two_of]
      linear_combination (-9 : O) * uO_cube k⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨-1, by norm_num⟩
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          zero_ne_one, if_false, sub_zero]
        exact ⟨-uO k ^ 2, by ring⟩
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          one_ne_zero, if_false, sub_zero]
        exact ⟨-uO k, by ring⟩
      · exact ⟨-2, by norm_num⟩)⟩

theorem transThree_mul (a b : O) : transThree a * transThree b = transThree (a + b) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [transThree, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem coe_complexMatrix_transThree (t : O) :
    ((complexMatrix (transThree t) : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 3 * ringComplex t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complexMatrix_apply, transThree, map_ofNat]

theorem fourDilation_trans (t : O) :
    fourDilation * complexMatrix (transThree t) = complexMatrix (transThree (2 * t)) * fourDilation := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourDilation, complexDiagonal, complexMatrix_apply, transThree, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  all_goals (try simp only [sqrtTwo_inv]); ring

theorem fourContraction_lower (c : O) :
    fourContraction * complexMatrix (lowerThree c) = complexMatrix (lowerThree (2 * c)) * fourContraction := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourContraction, complexDiagonal, complexMatrix_apply, lowerThree, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  all_goals (try simp only [sqrtTwo_inv]); ring

theorem coe_complexMatrix_lowerUp (k : Fin 3) :
    ((complexMatrix (lowerUp k) : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![-2, -3 * ringComplex (uO k) ^ 2; -3 * ringComplex (uO k), -5] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complexMatrix_apply, lowerUp, map_ofNat]

theorem fourDilation_wMat :
    fourDilation * complexMatrix wMat =
      complexMatrix wUp * -(fourContraction * complexMatrix (transThree (-1))) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourDilation, fourContraction, complexDiagonal, complexMatrix_apply, wMat, wUp,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.mul_apply, Fin.sum_univ_two,
      map_ofNat, coe_complexMatrix_transThree]
  all_goals (try simp only [sqrtTwo_inv]); ring

theorem fourContraction_wMat : fourContraction * complexMatrix wMat = complexMatrix wDown * -fourDilation := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourDilation, fourContraction, complexDiagonal, complexMatrix_apply, wMat, wDown,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.mul_apply, Fin.sum_univ_two,
      map_ofNat]
  all_goals (try simp only [sqrtTwo_inv]); ring

theorem fourDilation_lower (k : Fin 3) :
    fourDilation * complexMatrix (lowerThree (uO k)) =
      complexMatrix (lowerUp k) * -(fourContraction * complexMatrix (transThree (-(uO k ^ 2)))) := by
  have hu : ringComplex (uO k) ^ 3 = 1 := by rw [← map_pow, uO_cube, map_one]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourDilation, fourContraction, complexDiagonal, complexMatrix_apply, lowerThree,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.mul_apply, Fin.sum_univ_two,
      map_ofNat, coe_complexMatrix_transThree, coe_complexMatrix_lowerUp]
  all_goals (try simp only [sqrtTwo_inv])
  all_goals first | ring1 | linear_combination (9 / 2 * sqrtTwo) * hu

/-! ### Multipliers -/

theorem complexCharacter_wUp : complexCharacter wUp = 1 := by
  change ringComplex (symbol (-3) 4) = 1
  have h := CubicEisenstein.RationalSource.integer_symbol_eq_one (-3) 4 (by
    push_cast
    rw [show (4 : O) - 1 = -(-3) by ring]
    exact (dvd_neg).mpr lambda_sq_dvd_neg_three) (by decide)
  push_cast at h
  rw [h, map_one]

theorem complexCharacter_wDown : complexCharacter wDown = 1 := by
  change ringComplex (symbol (-3) 1) = 1
  rw [symbol_one, map_one]

/-- **`κ(L₊(u)) = u`.** -/
theorem complexCharacter_lowerUp (k : Fin 3) : complexCharacter (lowerUp k) = ringComplex (uO k) := by
  change ringComplex (symbol (-3 * uO k) (-2)) = ringComplex (uO k)
  have h := CubicEisenstein.RationalSource.integer_symbol_eq_one (-3) (-2) (by
    push_cast
    rw [show (-2 : O) - 1 = -3 by ring]
    exact lambda_sq_dvd_neg_three) (by decide)
  push_cast at h
  rw [symbol_mul_numerator, h, one_mul, symbol_uO_neg_two]

/-! ### The trace over Hecke points -/

/-- `Θ^{(∞)}(w) = Θ(Aw)`. -/
def heckeHigh (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ := Θ (fourDilation • w)

/-- `Θ^{(t)}(w) = Θ(A⁻¹T_{3t}w)`. -/
def heckeLow (Θ : HyperbolicSpace → ℂ) (t : O) (w : HyperbolicSpace) : ℂ :=
  Θ (fourContraction • complexMatrix (transThree t) • w)

section Hecke

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
include hΘ

theorem heckeHigh_trans (t : O) (w : HyperbolicSpace) :
    Θ (fourDilation • complexMatrix (transThree t) • w) = heckeHigh Θ w := by
  rw [← mul_smul, fourDilation_trans, mul_smul, hΘ, complexCharacter_transThree, one_mul, heckeHigh]

theorem correlation_trans (t : O) (w : HyperbolicSpace) :
    heckeFourCorrelation Θ (complexMatrix (transThree t) • w) = heckeHigh Θ w * heckeLow Θ t w := by
  rw [heckeFourCorrelation, heckeHigh_trans Θ hΘ, heckeLow]

theorem correlation_w (t : O) (w : HyperbolicSpace) :
    heckeFourCorrelation Θ (complexMatrix (wMat * transThree t) • w) =
      heckeLow Θ (-1 + t) w * heckeHigh Θ w := by
  have h1 : Θ (fourDilation • complexMatrix (wMat * transThree t) • w) = heckeLow Θ (-1 + t) w := by
    rw [map_mul, mul_smul, ← mul_smul fourDilation, fourDilation_wMat, mul_smul, hΘ, complexCharacter_wUp,
      one_mul, neg_smul_hyperbolic, mul_smul, ← mul_smul (complexMatrix (transThree (-1))), ← map_mul,
      transThree_mul, heckeLow]
  have h2 : Θ (fourContraction • complexMatrix (wMat * transThree t) • w) = heckeHigh Θ w := by
    rw [map_mul, mul_smul, ← mul_smul fourContraction, fourContraction_wMat, mul_smul, hΘ, complexCharacter_wDown,
      one_mul, neg_smul_hyperbolic, heckeHigh_trans Θ hΘ]
  rw [heckeFourCorrelation, h1, h2]

theorem correlation_lower (k : Fin 3) (t : O) (w : HyperbolicSpace) :
    heckeFourCorrelation Θ (complexMatrix (lowerThree (uO k) * transThree t) • w) =
      ringComplex (uO k) * (heckeLow Θ (-(uO k ^ 2) + t) w * heckeLow Θ t w) := by
  have h1 : Θ (fourDilation • complexMatrix (lowerThree (uO k) * transThree t) • w) =
      ringComplex (uO k) * heckeLow Θ (-(uO k ^ 2) + t) w := by
    rw [map_mul, mul_smul, ← mul_smul fourDilation, fourDilation_lower, mul_smul, hΘ, complexCharacter_lowerUp,
      neg_smul_hyperbolic, mul_smul, ← mul_smul (complexMatrix (transThree _)), ← map_mul, transThree_mul,
      heckeLow]
  have h2 : Θ (fourContraction • complexMatrix (lowerThree (uO k) * transThree t) • w) = heckeLow Θ t w := by
    rw [map_mul, mul_smul, ← mul_smul fourContraction, fourContraction_lower, mul_smul, hΘ,
      complexCharacter_lowerThree, one_mul, heckeLow]
  rw [heckeFourCorrelation, h1, h2]
  ring

/-- **The Hecke-at-four trace over Hecke points.** -/
theorem heckeFourTrace_eq_hecke (w : HyperbolicSpace) :
    heckeFourTrace Θ w =
      ∑ x : Fin 4, heckeHigh Θ w * heckeLow Θ (tO x) w +
        ∑ x : Fin 4, heckeLow Θ (-1 + tO x) w * heckeHigh Θ w +
          ∑ k : Fin 3, ∑ x : Fin 4,
            ringComplex (uO k) * (heckeLow Θ (-(uO k ^ 2) + tO x) w * heckeLow Θ (tO x) w) := by
  rw [heckeFourTrace_eq_sum Θ hΘ, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, ← add_assoc]
  simp only [cosetRep, correlation_trans Θ hΘ, correlation_w Θ hΘ, correlation_lower Θ hΘ]

end Hecke

end GaloisForLFunctions.OrderSixMetaplecticTheory
