import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCuspZeroOfTheFractionalTraceReadsLowPointsOfLowPoints

/-!
# The middle cusps of the fractional trace carry Jacobi phases

The `N(q) − 1` cosets `L_{qx} = [[1, 0], [3qx, 1]]` (`x ≢ 0`) of the fractional trace sit over the cusps `3qx`.
With `T_{3t/q} = A_q⁻¹T(t)A_q`, a fractional translation of `L_{qx}` is again a fractional translation, or a
high point:

* if `a = 1 + 9tx ≢ 0 mod q`: `T_tL_{qx} = M T_{t/a}` with `M = [[a, 3tr], [3qx, 1 − 9txe]] ∈ Γ(3)`,
  `ea + qr = 1` (`fracShift_mul_lowerThree`), and by cubic reciprocity `κ(M) = (3qx/a)₃ = (a/q)₃ = χ(a)`
  (`complexCharacter_midMat`);
* if `a = qa₁`: `T_tL_{qx} = [[a₁, 3t], [3x, q]] A_q²` (`fracShift_mul_lowerThree_high`), with phase
  `(3x/a₁)₃ = χ(3x)⁻¹`.

Hence (`fracCorrelation_lowerThree`) the pair `(t, −t)` contributes `χ(1 − s²) Θ(T_{t/(1+s)}w)Θ(T_{−t/(1−s)}w)`,
`s = 9tx`, unless `s = ∓1`, where one point is the high point `A_q²w` (height `N(q)v`) with phase
`χ(2)χ(3x)⁻¹`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `T_{3(u + qr)/q} = T(r)T_{3u/q}`. -/
theorem fracShift_add_mul (u r : O) :
    P.fracShift (u + P.p * r) = complexMatrix (transThree r) * P.fracShift u := by
  have hP := P.ringComplex_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fracShift, complexTranslation, complexMatrix_apply, transThree, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  field_simp

/-- `Θ(T_{3u/q}w)` depends on `u` modulo `q`. -/
theorem theta_fracShift_lift (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (u : O) (w : HyperbolicSpace) : Θ (P.fracShift (P.lift (P.res u)) • w) = Θ (P.fracShift u • w) := by
  have h : P.res (P.lift (P.res u) - u) = 0 := by rw [map_sub, res_lift, sub_self]
  obtain ⟨r, hr⟩ := (P.res_eq_zero_iff _).mp h
  rw [show P.lift (P.res u) = u + P.p * r by linear_combination hr, P.fracShift_add_mul, mul_smul, hΘ,
    complexCharacter_transThree, one_mul]

/-! ### The generic points -/

/-- `M = [[a, 3tr], [3qx, 1 − 9txe]]`, `a = 1 + 9tx`, `ea + qr = 1`. -/
def midMat (T X e r : O) (hr : e * (1 + 9 * T * X) + P.p * r = 1) : levelThree :=
  ⟨⟨!![1 + 9 * T * X, 3 * T * r; 3 * (P.p * X), 1 - 9 * T * X * e], by
      rw [Matrix.det_fin_two_of]; linear_combination (-(9 * T * X)) * hr⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨3 * T * X, by simp; ring⟩
      · exact ⟨T * r, by simp; ring⟩
      · exact ⟨P.p * X, by simp⟩
      · exact ⟨-(3 * T * X * e), by simp; ring⟩)⟩

theorem fracShift_mul_lowerThree (T X e r : O) (hr : e * (1 + 9 * T * X) + P.p * r = 1) :
    P.fracShift T * complexMatrix (lowerThree (P.p * X)) = complexMatrix (P.midMat T X e r hr) * P.fracShift (T * e) := by
  have hP := P.ringComplex_ne_zero
  have h := congrArg ringComplex hr
  simp only [map_add, map_mul, map_one, map_ofNat] at h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fracShift, complexTranslation, complexMatrix_apply, midMat, lowerThree, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination (3 * ringComplex T) * h | linear_combination (-(3 * ringComplex T)) * h |
    linear_combination (9 * ringComplex T * ringComplex X) * h | linear_combination (-(9 * ringComplex T * ringComplex X)) * h |
    linear_combination (9 * ringComplex T * ringComplex X - ringComplex T) * h |
    linear_combination (ringComplex T - 9 * ringComplex T * ringComplex X) * h |
    linear_combination (-ringComplex T) * h)

/-- **The generic phase is `χ(a)`** (cubic reciprocity). -/
theorem complexCharacter_midMat (T X e r : O) (hr : e * (1 + 9 * T * X) + P.p * r = 1) :
    complexCharacter (P.midMat T X e r hr) = P.chi (P.res (1 + 9 * T * X)) := by
  rw [complexCharacter_eq_symbol]
  have ha : lambda ^ 2 ∣ (1 + 9 * T * X) - 1 :=
    (lambda_sq_dvd_three.trans (dvd_mul_right 3 3)).trans ⟨T * X, by ring⟩
  have h1 : symbol (3 * X) (1 + 9 * T * X) = 1 := by
    rw [symbol_denominator_congr (3 * X) _ 1 ha (by simp) ⟨T * X, by ring⟩ ⟨3 * T, by ring⟩, symbol_one]
  show ringComplex (symbol (3 * (P.p * X)) (1 + 9 * T * X)) = _
  rw [show 3 * (P.p * X) = 3 * X * P.p by ring, symbol_mul_numerator, h1, one_mul,
    symbol_reciprocity _ _ P.primary ha, P.chi_res]

/-! ### The high points -/

/-- `[[a₁, 3t], [3x, q]]` with `qa₁ = 1 + 9tx`. -/
def topMat (T X a : O) (ha : 1 + 9 * T * X = P.p * a) : levelThree :=
  ⟨⟨!![a, 3 * T; 3 * X, P.p], by rw [Matrix.det_fin_two_of]; linear_combination -ha⟩,
    levelThree_of_entries _ (by
      obtain ⟨u, hu⟩ := P.three_dvd_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨-(a * u) + 3 * T * X, by simp; linear_combination -ha - a * hu⟩
      · exact ⟨T, by simp⟩
      · exact ⟨X, by simp⟩
      · simpa using P.three_dvd_sub_one)⟩

theorem fracShift_mul_lowerThree_high (T X a : O) (ha : 1 + 9 * T * X = P.p * a) :
    P.fracShift T * complexMatrix (lowerThree (P.p * X)) =
      complexMatrix (P.topMat T X a ha) * (P.dilation * P.dilation) := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  have h := congrArg ringComplex ha
  simp only [map_add, map_mul, map_one, map_ofNat] at h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fracShift, complexTranslation, complexMatrix_apply, topMat, lowerThree, PrimaryPrime.dilation,
      complexDiagonal, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  all_goals (try rw [← hr])
  all_goals (try rw [← hr] at h)
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination h)

/-- **The high phase is `χ(3x)⁻¹`.** -/
theorem complexCharacter_topMat (T X a : O) (ha : 1 + 9 * T * X = P.p * a) :
    complexCharacter (P.topMat T X a ha) * P.chi (P.res (3 * X)) = 1 := by
  rw [complexCharacter_eq_symbol, P.chi_res]
  show ringComplex (symbol (3 * X) a) * ringComplex (symbol (3 * X) P.p) = 1
  have hla : lambda ^ 2 ∣ a - 1 := by
    obtain ⟨u, hu⟩ := P.three_dvd_sub_one
    exact lambda_sq_dvd_three.trans ⟨-(a * u) + 3 * T * X, by linear_combination -ha - a * hu⟩
  have hpa : lambda ^ 2 ∣ a * P.p - 1 := by
    rw [mul_comm, ← ha]
    exact (lambda_sq_dvd_three.trans (dvd_mul_right 3 3)).trans ⟨T * X, by ring⟩
  rw [← map_mul, ← symbol_mul_denominator, symbol_denominator_congr (3 * X) _ 1 hpa (by simp)
    ⟨T * X, by linear_combination -ha⟩ ⟨3 * T, by linear_combination -ha⟩, symbol_one, map_one]


section Points

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
include hΘ

/-- The generic point: `Θ(T_tL_{qx}w) = χ(1 + 9tx) Θ(T_{t/(1+9tx)}w)`. -/
theorem theta_mid_generic (x : {x : P.Res // x ≠ 0}) (T : O) (hT : 1 + 9 * P.res T * x.1 ≠ 0) (w : HyperbolicSpace) :
    Θ (P.fracShift T • complexMatrix (lowerThree (P.p * P.lift x.1)) • w) =
      P.chi (1 + 9 * P.res T * x.1) * Θ (P.fracShift (P.lift (P.res T / (1 + 9 * P.res T * x.1))) • w) := by
  set X := P.lift x.1
  have hres : P.res (1 + 9 * T * X) = 1 + 9 * P.res T * x.1 := by simp [X, map_ofNat]
  set e := P.lift (1 + 9 * P.res T * x.1)⁻¹
  have h0 : P.res (1 - e * (1 + 9 * T * X)) = 0 := by
    rw [map_sub, map_mul, hres, res_lift, map_one, inv_mul_cancel₀ hT, sub_self]
  obtain ⟨r, hr⟩ := (P.res_eq_zero_iff _).mp h0
  have hr' : e * (1 + 9 * T * X) + P.p * r = 1 := by linear_combination -hr
  rw [← mul_smul, P.fracShift_mul_lowerThree T X e r hr', mul_smul, hΘ, P.complexCharacter_midMat, hres,
    ← P.theta_fracShift_lift Θ hΘ (T * e)]
  congr 3
  rw [map_mul, res_lift, div_eq_mul_inv]

/-- The high point: `Θ(T_tL_{qx}w) = χ(3x)⁻¹ Θ(A_q²w)` when `1 + 9tx ≡ 0`. -/
theorem theta_mid_high (x : {x : P.Res // x ≠ 0}) (T : O) (hT : 1 + 9 * P.res T * x.1 = 0) (w : HyperbolicSpace) :
    Θ (P.fracShift T • complexMatrix (lowerThree (P.p * P.lift x.1)) • w) =
      (P.chi (3 * x.1))⁻¹ * Θ (P.dilation • P.dilation • w) := by
  set X := P.lift x.1
  have hres : P.res (1 + 9 * T * X) = 0 := by simpa [X, map_ofNat] using hT
  obtain ⟨a, ha⟩ := (P.res_eq_zero_iff _).mp hres
  have hκ := P.complexCharacter_topMat T X a ha
  have h3 : P.res (3 * X) = 3 * x.1 := by simp [X, map_ofNat]
  rw [h3] at hκ
  rw [← mul_smul, P.fracShift_mul_lowerThree_high T X a ha, mul_smul, hΘ, mul_smul, eq_inv_of_mul_eq_one_left hκ]

/-- **The pairs over the middle cusps.** For `s = 9tx`: a Jacobi phase `χ(1 − s²)` on two fractional translations,
or (at `s = ∓1`) the high point `A_q²w` with phase `χ(2)χ(3x)⁻¹`. -/
theorem fracCorrelation_lowerThree (h2 : (2 : P.Res) ≠ 0) (x : {x : P.Res // x ≠ 0}) (t : P.Res) (w : HyperbolicSpace) :
    P.fracCorrelation Θ (P.lift t) (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) =
      if 1 + 9 * t * x.1 = 0 then
        P.chi 2 * (P.chi (3 * x.1))⁻¹ * (Θ (P.dilation • P.dilation • w) * Θ (P.fracShift (P.lift (-t / 2)) • w))
      else if 1 - 9 * t * x.1 = 0 then
        P.chi 2 * (P.chi (3 * x.1))⁻¹ * (Θ (P.dilation • P.dilation • w) * Θ (P.fracShift (P.lift (t / 2)) • w))
      else
        P.chi (1 - (9 * t * x.1) ^ 2) *
          (Θ (P.fracShift (P.lift (t / (1 + 9 * t * x.1))) • w) * Θ (P.fracShift (P.lift (-t / (1 - 9 * t * x.1))) • w)) := by
  have hn : P.res (-P.lift t) = -t := by rw [map_neg, res_lift]
  have hp : P.res (P.lift t) = t := res_lift _ _
  unfold fracCorrelation
  split_ifs with h1 h1'
  · have hm : 1 + 9 * P.res (-P.lift t) * x.1 ≠ 0 := by
      rw [hn, show 1 + 9 * -t * x.1 = 2 - (1 + 9 * t * x.1) by ring, h1, sub_zero]
      exact h2
    rw [P.theta_mid_high Θ hΘ x _ (by rw [hp]; exact h1), P.theta_mid_generic Θ hΘ x _ hm, hn,
      show 1 + 9 * -t * x.1 = 2 by linear_combination -h1]
    ring
  · have hm : 1 + 9 * P.res (P.lift t) * x.1 ≠ 0 := by
      rw [hp, show 1 + 9 * t * x.1 = 2 - (1 - 9 * t * x.1) by ring, h1', sub_zero]
      exact h2
    rw [P.theta_mid_generic Θ hΘ x _ hm, P.theta_mid_high Θ hΘ x _ (by rw [hn]; linear_combination h1'), hp,
      show 1 + 9 * t * x.1 = 2 by linear_combination -h1']
    ring
  · have hm1 : 1 + 9 * P.res (P.lift t) * x.1 ≠ 0 := by rw [hp]; exact h1
    have hm2 : 1 + 9 * P.res (-P.lift t) * x.1 ≠ 0 := by
      rw [hn, show 1 + 9 * -t * x.1 = 1 - 9 * t * x.1 by ring]; exact h1'
    rw [P.theta_mid_generic Θ hΘ x _ hm1, P.theta_mid_generic Θ hΘ x _ hm2, hp, hn,
      show 1 + 9 * -t * x.1 = 1 - 9 * t * x.1 by ring, show -t / (1 - 9 * t * x.1) = -t / (1 - 9 * t * x.1) from rfl,
      show (1 : P.Res) - (9 * t * x.1) ^ 2 = (1 + 9 * t * x.1) * (1 - 9 * t * x.1) by ring, map_mul]
    ring

end Points

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
