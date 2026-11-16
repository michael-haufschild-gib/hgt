import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsASumOverTheProjectiveLine

/-!
# The Hecke trace at a primary prime is a phased sum over Hecke points

With `T_t = [[1, 3t], [0, 1]]`, the Hecke points of `w` are `A_pw` (`z ↦ pz`) and `A_p⁻¹T_tw` (`z ↦ (z + 3t)/p`).
Each representative of `Γ(3)/Γ_p` is moved to them by a matrix of `Γ(3)`:

* `A_pT_t = T_{pt}A_p` and `A_p⁻¹L(y) = L(py)A_p⁻¹`;
* `A_p⁻¹W = L(k)T_1A_p` and `A_pW = M_W A_p⁻¹T_{f}`, `M_W = [[p², 3m], [3k, n]]` (`p²n − 9km = 1`,
  `f = pn − mδ`);
* `A_pL(y) = M_y A_p⁻¹T_{−β}`, `M_y = [[p, 3β], [3y, δ_y]]` (`pδ_y − 9yβ = 1`).

The multipliers are `κ(M_y) = (3y/p)₃` and `κ(M_W) = (3k/p²)₃ = κ(W)²`, so (`heckeTrace_eq_hecke`)

`Tr_pF_Θ(w) = Σ_x Θ^{high}Θ^{(x)} + Σ_x Θ^{(x+f)}Θ^{high} + Σ_{x, y≢0} (3y/p)₃ Θ^{(x−β_y)}Θ^{(x)}`,

`Θ^{high}(w) = Θ(A_pw)`, `Θ^{(t)}(w) = Θ(A_p⁻¹T_tw)`, `x` over `O/p`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Bezout matrices -/

theorem isCoprime_nine_mul (y : O) (hy : ¬ P.p ∣ y) : IsCoprime P.p (9 * y) := by
  have h9 : IsCoprime P.p 9 := by
    have := P.isCoprime_three.pow_left (m := 2)
    norm_num at this
    exact this.symm
  exact h9.mul_right ((Irreducible.coprime_iff_not_dvd P.prime.irreducible).mpr hy)

theorem exists_lowBezout (y : O) (hy : ¬ P.p ∣ y) : ∃ δ β : O, P.p * δ - 9 * y * β = 1 := by
  obtain ⟨u, v, h⟩ := P.isCoprime_nine_mul y hy
  exact ⟨u, -v, by linear_combination h⟩

/-- `δ_y` in `pδ_y − 9yβ_y = 1` (`0` if `p ∣ y`). -/
def lowDelta (y : O) : O := if hy : P.p ∣ y then 0 else (P.exists_lowBezout y hy).choose

/-- `β_y` in `pδ_y − 9yβ_y = 1`. -/
def lowBeta (y : O) : O := if hy : P.p ∣ y then 0 else (P.exists_lowBezout y hy).choose_spec.choose

theorem low_det (y : O) (hy : ¬ P.p ∣ y) : P.p * P.lowDelta y - 9 * y * P.lowBeta y = 1 := by
  simp only [lowDelta, lowBeta, dif_neg hy]
  exact (P.exists_lowBezout y hy).choose_spec.choose_spec

theorem three_dvd_of_primary_mul (δ c : O) (h : P.p * δ - 9 * c = 1) : (3 : O) ∣ δ - 1 := by
  obtain ⟨t, ht⟩ := P.three_dvd_sub_one
  exact ⟨3 * c - δ * t, by linear_combination h - δ * ht⟩

/-- `M_y = [[p, 3β_y], [3y, δ_y]]`. -/
def lowMat (y : O) (hy : ¬ P.p ∣ y) : levelThree :=
  ⟨⟨!![P.p, 3 * P.lowBeta y; 3 * y, P.lowDelta y], by
      rw [Matrix.det_fin_two_of]; linear_combination P.low_det y hy⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using P.three_dvd_sub_one
      · simp
      · simp
      · simpa using P.three_dvd_of_primary_mul _ (y * P.lowBeta y) (by linear_combination P.low_det y hy))⟩

theorem exists_highBezout : ∃ n m : O, P.p ^ 2 * n - 9 * P.wK * m = 1 := by
  have hk : ¬ P.p ∣ P.wK := fun h => P.res_wK_ne_zero ((P.res_eq_zero_iff _).mpr h)
  have h1 : IsCoprime (P.p ^ 2) (9 * P.wK) := (P.isCoprime_nine_mul P.wK hk).pow_left
  obtain ⟨u, v, h⟩ := h1
  exact ⟨u, -v, by linear_combination h⟩

/-- `n` in `p²n − 9km = 1`. -/
def highN : O := P.exists_highBezout.choose

/-- `m` in `p²n − 9km = 1`. -/
def highM : O := P.exists_highBezout.choose_spec.choose

theorem high_det : P.p ^ 2 * P.highN - 9 * P.wK * P.highM = 1 := P.exists_highBezout.choose_spec.choose_spec

/-- `M_W = [[p², 3m], [3k, n]]`. -/
def highMat : levelThree :=
  ⟨⟨!![P.p ^ 2, 3 * P.highM; 3 * P.wK, P.highN], by
      rw [Matrix.det_fin_two_of]; linear_combination P.high_det⟩,
    levelThree_of_entries _ (by
      obtain ⟨t, ht⟩ := P.three_dvd_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨t * (P.p + 1), by simp; linear_combination (P.p + 1) * ht⟩
      · simp
      · simp
      · exact ⟨3 * P.wK * P.highM - P.highN * t * (P.p + 1), by
          simp; linear_combination P.high_det - P.highN * (P.p + 1) * ht⟩)⟩

/-- The shift `f = pn − mδ` of the `W`-type Hecke points. -/
def wShift : O := P.p * P.highN - P.highM * P.wDelta

/-! ### Matrix identities -/

theorem dilation_transThree (t : O) :
    P.dilation * complexMatrix (transThree t) = complexMatrix (transThree (P.p * t)) * P.dilation := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, transThree,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← hr]
  field_simp

theorem contraction_lowerThree (y : O) :
    P.contraction * complexMatrix (lowerThree y) = complexMatrix (lowerThree (P.p * y)) * P.contraction := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, complexDiagonal, complexMatrix_apply, lowerThree,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← hr]
  field_simp

theorem ringComplex_three : ringComplex (3 : O) = 3 := map_ofNat ringComplex 3

theorem contraction_wMat :
    P.contraction * complexMatrix P.wMat =
      complexMatrix (lowerThree P.wK) * complexMatrix (transThree 1) * P.dilation := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  have hc3 := ringComplex_three
  have hd := congrArg ringComplex P.w_det
  simp only [map_sub, map_mul, map_one, map_ofNat] at hd
  rw [← hr] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, lowerThree,
      transThree, wMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hr])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd)

theorem dilation_wMat :
    P.dilation * complexMatrix P.wMat =
      complexMatrix P.highMat * P.contraction * complexMatrix (transThree P.wShift) := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  have hc3 := ringComplex_three
  have hd := congrArg ringComplex P.w_det
  have hh := congrArg ringComplex P.high_det
  simp only [map_sub, map_mul, map_one, map_ofNat, map_pow] at hd hh
  rw [← hr] at hd hh
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, highMat,
      transThree, wMat, wShift, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hr])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd | linear_combination -hd | linear_combination (-1) * hh + ringComplex P.highM * hd | linear_combination (-ringComplex P.wDelta) * hh + (P.root ^ 2 * ringComplex P.highN) * hd)

theorem dilation_lowerThree (y : O) (hy : ¬ P.p ∣ y) :
    P.dilation * complexMatrix (lowerThree y) =
      complexMatrix (P.lowMat y hy) * P.contraction * complexMatrix (transThree (-P.lowBeta y)) := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  have hc3 := ringComplex_three
  have hd := congrArg ringComplex (P.low_det y hy)
  simp only [map_sub, map_mul, map_one, map_ofNat] at hd
  rw [← hr] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, lowMat,
      transThree, lowerThree, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hr])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd | linear_combination -hd)


/-! ### The Hecke points -/

/-- `Θ^{high}(w) = Θ(A_pw)`. -/
def heckeHigh (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ := Θ (P.dilation • w)

/-- `Θ^{(t)}(w) = Θ(A_p⁻¹T_tw)`. -/
def heckeLow (Θ : HyperbolicSpace → ℂ) (t : O) (w : HyperbolicSpace) : ℂ :=
  Θ (P.contraction • (complexMatrix (transThree t) • w))

theorem transThree_mul (s t : O) : transThree s * transThree t = transThree (s + t) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [transThree, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem complexCharacter_highMat : complexCharacter P.highMat = complexCharacter P.wMat ^ 2 := by
  have h1 : ((P.highMat : levelThree) : SL(2, O)) 1 0 = 3 * P.wK := rfl
  have h2 : ((P.highMat : levelThree) : SL(2, O)) 0 0 = P.p ^ 2 := rfl
  have h3 : ((P.wMat : levelThree) : SL(2, O)) 1 0 = 3 * P.wK := rfl
  have h4 : ((P.wMat : levelThree) : SL(2, O)) 0 0 = P.p := rfl
  rw [complexCharacter_eq_symbol, complexCharacter_eq_symbol, h1, h2, h3, h4, pow_two, symbol_mul_denominator,
    map_mul, pow_two]

theorem complexCharacter_lowMat (y : O) (hy : ¬ P.p ∣ y) :
    complexCharacter (P.lowMat y hy) = ringComplex (symbol (3 * y) P.p) := rfl

theorem not_dvd_lift (y : {y : P.Res // y ≠ 0}) : ¬ P.p ∣ P.lift y.1 := by
  rw [← P.res_eq_zero_iff, res_lift]
  exact y.2

variable {P}

theorem correlation_transThree (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (t : O) (w : HyperbolicSpace) :
    P.heckeCorrelation Θ (complexMatrix (transThree t) • w) = P.heckeHigh Θ w * P.heckeLow Θ t w := by
  unfold heckeCorrelation heckeHigh heckeLow
  rw [← mul_smul, P.dilation_transThree, mul_smul, hΘ, complexCharacter_transThree, one_mul]

theorem correlation_wMat (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (t : O) (w : HyperbolicSpace) :
    P.heckeCorrelation Θ (complexMatrix (P.wMat * transThree t) • w) =
      complexCharacter P.wMat ^ 2 * (P.heckeLow Θ (P.wShift + t) w * P.heckeHigh Θ w) := by
  have h1 : Θ (P.dilation • (complexMatrix (P.wMat * transThree t) • w)) =
      complexCharacter P.wMat ^ 2 * Θ (P.contraction • (complexMatrix (transThree (P.wShift + t)) • w)) := by
    rw [map_mul, mul_smul, ← mul_smul P.dilation, P.dilation_wMat, mul_smul, mul_smul, hΘ,
      complexCharacter_highMat, ← mul_smul (complexMatrix (transThree P.wShift)), ← map_mul, transThree_mul]
  have h2 : Θ (P.contraction • (complexMatrix (P.wMat * transThree t) • w)) = Θ (P.dilation • w) := by
    rw [map_mul, mul_smul, ← mul_smul P.contraction, P.contraction_wMat, mul_smul, mul_smul, hΘ,
      complexCharacter_lowerThree, one_mul, hΘ, complexCharacter_transThree, one_mul, ← mul_smul,
      P.dilation_transThree, mul_smul, hΘ, complexCharacter_transThree, one_mul]
  unfold heckeCorrelation heckeHigh heckeLow
  rw [h1, h2]
  ring

theorem correlation_lowerThree (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (y : O) (hy : ¬ P.p ∣ y) (t : O) (w : HyperbolicSpace) :
    P.heckeCorrelation Θ (complexMatrix (lowerThree y * transThree t) • w) =
      ringComplex (symbol (3 * y) P.p) * P.heckeLow Θ (t - P.lowBeta y) w * P.heckeLow Θ t w := by
  have h1 : Θ (P.dilation • (complexMatrix (lowerThree y * transThree t) • w)) =
      ringComplex (symbol (3 * y) P.p) * Θ (P.contraction • (complexMatrix (transThree (t - P.lowBeta y)) • w)) := by
    rw [map_mul, mul_smul, ← mul_smul P.dilation, P.dilation_lowerThree y hy, mul_smul, mul_smul, hΘ,
      P.complexCharacter_lowMat y hy, ← mul_smul (complexMatrix (transThree (-P.lowBeta y))), ← map_mul,
      transThree_mul, show -P.lowBeta y + t = t - P.lowBeta y by ring]
  have h2 : Θ (P.contraction • (complexMatrix (lowerThree y * transThree t) • w)) =
      Θ (P.contraction • (complexMatrix (transThree t) • w)) := by
    rw [map_mul, mul_smul, ← mul_smul P.contraction, P.contraction_lowerThree, mul_smul, hΘ,
      complexCharacter_lowerThree, one_mul]
  unfold heckeCorrelation heckeLow
  rw [h1, h2]

variable (P)

/-- **The Hecke trace at `p` as a phased sum over Hecke points.** -/
theorem heckeTrace_eq_hecke (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (w : HyperbolicSpace) :
    P.heckeTrace Θ w =
      (∑ x : P.Res, P.heckeHigh Θ w * P.heckeLow Θ (P.lift x) w) +
        ((∑ x : P.Res, P.heckeLow Θ (P.wShift + P.lift x) w * P.heckeHigh Θ w) +
          ∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
            P.heckeLow Θ (P.lift x - P.lowBeta (P.lift y.1)) w * P.heckeLow Θ (P.lift x) w) := by
  rw [P.heckeTrace_eq_sum Θ hΘ, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hW : complexCharacter P.wMat ≠ 0 := by
    intro h
    have := norm_complexCharacter P.wMat
    rw [h, norm_zero] at this
    exact zero_ne_one this
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    change (complexCharacter (transThree (P.lift x)) ^ 2)⁻¹ *
      P.heckeCorrelation Θ (complexMatrix (transThree (P.lift x)) • w) = _
    rw [complexCharacter_transThree, one_pow, inv_one, one_mul, correlation_transThree Θ hΘ]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    change (complexCharacter (P.wMat * transThree (P.lift x)) ^ 2)⁻¹ *
      P.heckeCorrelation Θ (complexMatrix (P.wMat * transThree (P.lift x)) • w) = _
    rw [map_mul, complexCharacter_transThree, mul_one, correlation_wMat Θ hΘ, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hW), one_mul]
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    change (complexCharacter (lowerThree (P.lift y.1) * transThree (P.lift x)) ^ 2)⁻¹ *
      P.heckeCorrelation Θ (complexMatrix (lowerThree (P.lift y.1) * transThree (P.lift x)) • w) = _
    rw [map_mul, complexCharacter_transThree, complexCharacter_lowerThree, mul_one, one_pow, inv_one, one_mul,
      correlation_lowerThree Θ hΘ _ (P.not_dvd_lift y)]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
