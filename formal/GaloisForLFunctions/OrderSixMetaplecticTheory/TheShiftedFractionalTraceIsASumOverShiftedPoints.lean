import GaloisForLFunctions.OrderSixMetaplecticTheory.TheShiftedFractionalTraceHasTheSquareMultiplier
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheMiddleCuspsOfTheFractionalTraceCarryJacobiPhases
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCuspZeroOfTheFractionalTraceReadsLowPointsOfLowPoints

/-!
# The shifted fractional trace is a sum over shifted points

Write `Θ_b(w) = Θ(T_bw)`. Every coset of the shifted trace `Tr G^b_Θ` reads the points of the fractional trace,
with `Θ_b` on the first factor and `Θ_{−b}` on the second, and the same phases:

* the middle cusps (`shiftCorrelation_lowerThree`): the pair `(t, −t)` over `L_{qx}` gives
  `χ(1 − s²) Θ_b(T_{t/(1+s)}w) Θ_{−b}(T_{−t/(1−s)}w)` (`s = 9tx`), or a high point with phase `χ(2)χ(3x)⁻¹`;
* the classes over the cusp `0` (`shiftSum_gamma0`), without the symmetry `S` (which the shift breaks):
  `T_tγ₀ = g_t A_q⁻¹T(−β_{−t})A_q⁻¹` with `g_t = δ_t⁻¹M_{−t} ∈ Γ(3)` of lower-left entry `3kq` for every `t`
  (`fracShift_mul_gamma0`, `gZero_lowerLeft`), so
  `G^b_Θ(γ₀y) = Θ_b(y)Θ_{−b}(y) + Σ_{x ≢ 0} χ(−9x²) Θ_b^{(−β_{−x})}(A_q⁻¹y) Θ_{−b}^{(−β_x)}(A_q⁻¹y)`.

The phases agree with the unshifted ones because conjugation by `T_{±b}` changes `κ` by opposite ramified factors:
for equal lower-left entries (`complexCharacter_translation_pair`) and for lower-left entries `c`, `qc`
(`complexCharacter_translation_pair_prime`: `(q/(a − bqc))₃ = (q/a)₃` by cubic reciprocity).
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- Opposite shifts over the numerators `c` and `qc` (`q` primary prime) cancel their ramified phases. -/
theorem symbol_pair_shifts_prime (q : O) (hq3 : (3 : O) ∣ q - 1) (a₁ a₂ b c : O) (h₁ : (3 : O) ∣ a₁ - 1)
    (h₂ : (3 : O) ∣ a₂ - 1) (hc : (3 : O) ∣ c) :
    symbol c (a₁ + b * c) * symbol (q * c) (a₂ - b * (q * c)) = symbol c a₁ * symbol (q * c) a₂ := by
  have hq : lambda ^ 2 ∣ q - 1 := lambda_sq_dvd_three.trans hq3
  have hl₁ : lambda ^ 2 ∣ a₁ - 1 := lambda_sq_dvd_three.trans h₁
  have hl₂ : lambda ^ 2 ∣ a₂ - 1 := lambda_sq_dvd_three.trans h₂
  have hbc : lambda ^ 2 ∣ b * c := dvd_mul_of_dvd_right (lambda_sq_dvd_three.trans hc) b
  have hbqc : lambda ^ 2 ∣ b * (q * c) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (lambda_sq_dvd_three.trans hc) q) b
  have hA : lambda ^ 2 ∣ a₁ + b * c - 1 := by convert dvd_add hl₁ hbc using 1; ring
  have hB : lambda ^ 2 ∣ a₂ - b * (q * c) - 1 := by convert dvd_sub hl₂ hbqc using 1; ring
  have hAB : lambda ^ 2 ∣ (a₁ + b * c) * (a₂ - b * (q * c)) - 1 := by
    convert dvd_add (dvd_mul_of_dvd_left hA (a₂ - b * (q * c))) hB using 1; ring
  have h12 : lambda ^ 2 ∣ a₁ * a₂ - 1 := by
    convert dvd_add (dvd_mul_of_dvd_left hl₁ a₂) hl₂ using 1; ring
  have h9 : (9 : O) ∣ (a₁ + b * c) * (a₂ - b * (q * c)) - a₁ * a₂ := by
    obtain ⟨k, hk⟩ := hc
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    obtain ⟨f, hf⟩ := hq3
    refine ⟨b * k * (e₂ - f - e₁ - 3 * f * e₁) - b ^ 2 * q * k ^ 2, ?_⟩
    rw [hk]
    linear_combination (3 * b * k) * he₂ - (3 * b * k * q) * he₁ - (3 * b * k) * hf - (9 * b * k * e₁) * hf
  have hcc : c ∣ (a₁ + b * c) * (a₂ - b * (q * c)) - a₁ * a₂ :=
    ⟨b * (a₂ - q * a₁) - b ^ 2 * q * c, by ring⟩
  have hc' : symbol c (a₁ + b * c) * symbol c (a₂ - b * (q * c)) = symbol c a₁ * symbol c a₂ := by
    rw [← symbol_mul_denominator, ← symbol_mul_denominator]
    exact symbol_denominator_congr c _ _ hAB h12 h9 hcc
  have hq' : symbol q (a₂ - b * (q * c)) = symbol q a₂ := by
    rw [symbol_reciprocity q _ hq hB, symbol_reciprocity q _ hq hl₂]
    exact symbol_congr ⟨-(b * c), by ring⟩
  rw [symbol_mul_numerator, symbol_mul_numerator, hq']
  linear_combination (symbol q a₂) * hc'

/-- **Pair cancellation over `c` and `qc`.** If `n₂` has lower-left entry `q` times that of `n₁`,
`κ(T_bn₁T_{−b}) κ(T_{−b}n₂T_b) = κ(n₁) κ(n₂)`. -/
theorem complexCharacter_translation_pair_prime (q : O) (hq : (3 : O) ∣ q - 1) (b : O) (n₁ n₂ : levelThree)
    (h : (n₂ : SL(2, O)) 1 0 = q * (n₁ : SL(2, O)) 1 0) :
    complexCharacter (levelThreeConjugate (integralTranslation b) n₁) *
      complexCharacter (levelThreeConjugate (integralTranslation (-b)) n₂) =
        complexCharacter n₁ * complexCharacter n₂ := by
  have h₁ : (3 : O) ∣ (n₁ : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry n₁ 0 0
  have h₂ : (3 : O) ∣ (n₂ : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry n₂ 0 0
  have hc : (3 : O) ∣ (n₁ : SL(2, O)) 1 0 := by simpa using levelThree_entry n₁ 1 0
  rw [complexCharacter_translationConjugate, complexCharacter_translationConjugate, complexCharacter_eq_symbol,
    complexCharacter_eq_symbol, h, ← map_mul, ← map_mul,
    show (n₂ : SL(2, O)) 0 0 + -b * (q * (n₁ : SL(2, O)) 1 0) =
      (n₂ : SL(2, O)) 0 0 - b * (q * (n₁ : SL(2, O)) 1 0) by ring,
    symbol_pair_shifts_prime q hq _ _ b _ h₁ h₂ hc]

/-- Translations are fixed by conjugation with `T_b`: `κ(T_bT(r)T_{−b}) = 1`. -/
theorem complexCharacter_translationConjugate_transThree (b r : O) :
    complexCharacter (levelThreeConjugate (integralTranslation b) (transThree r)) = 1 := by
  rw [complexCharacter_translationConjugate, ← complexCharacter_transThree r, complexCharacter_eq_symbol]
  simp [transThree]

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The classes over the cusp `0` -/

/-- `g_t = δ_t⁻¹M_{−t} ∈ Γ(3)`. -/
def gZero (t : O) (ht : ¬ P.p ∣ t) : levelThree :=
  (P.deltaS P.sKM t)⁻¹ * P.lowMat (-t) (fun h => ht (dvd_neg.mp h))

/-- `T_tγ₀ = g_t A_q⁻¹T(−β_{−t})A_q⁻¹` (no `S`). -/
theorem fracShift_mul_gamma0 (t : O) (ht : ¬ P.p ∣ t) :
    P.fracShift t * complexMatrix P.gamma0 =
      complexMatrix (P.gZero t ht) *
        (P.contraction * complexMatrix (transThree (-P.lowBeta (-t))) * P.contraction) := by
  have ht' : ¬ P.p ∣ -t := fun h => ht (dvd_neg.mp h)
  have h1 := P.fracShift_mul_S P.sKM t
  have h2 := P.fracShift_mul_sO t
  have h3 : complexMatrix (P.deltaS P.sKM t) * (P.fracShift t * complexMatrix P.gamma0) =
      P.dilation * complexMatrix (lowerThree (-t)) * P.contraction := mul_left_cancel (h1.symm.trans h2)
  rw [P.dilation_lowerThree (-t) ht'] at h3
  rw [gZero, map_mul, map_inv, mul_assoc, eq_inv_mul_iff_mul_eq, h3]
  simp only [mul_assoc]

theorem gZero_lowerLeft (t : O) (ht : ¬ P.p ∣ t) :
    ((P.gZero t ht : levelThree) : SL(2, O)) 1 0 = 3 * P.sK * P.p := by
  have e10 := (P.deltaS_entries P.sKM t).1
  have e00 := (P.deltaS_entries P.sKM t).2
  simp only [gZero, Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  rw [e10, e00]
  simp [lowMat]
  ring

/-- The phase of a pair over the cusp `0`: `κ(g_t)κ(g_{−t}) = χ(−9t²)`. -/
theorem complexCharacter_gZero_mul (t : O) (ht : ¬ P.p ∣ t) (ht' : ¬ P.p ∣ -t) :
    complexCharacter (P.gZero t ht) * complexCharacter (P.gZero (-t) ht') = P.chi (-9 * P.res t ^ 2) := by
  have hd := P.deltaS_character_mul P.sKM t
  have e : complexCharacter (P.gZero t ht) * complexCharacter (P.gZero (-t) ht') =
      (complexCharacter (P.deltaS P.sKM t) * complexCharacter (P.deltaS P.sKM (-t)))⁻¹ *
        (ringComplex (symbol (3 * -t) P.p) * ringComplex (symbol (3 * - -t) P.p)) := by
    simp only [gZero, map_mul, map_inv, P.complexCharacter_lowMat]
    rw [mul_inv]
    ring
  have hr : P.res (3 * -t) * P.res (3 * - -t) = -9 * P.res t ^ 2 := by
    simp only [map_mul, map_neg, neg_neg, map_ofNat]
    ring
  rw [e, hd, inv_one, one_mul, ← P.chi_res, ← P.chi_res, ← map_mul, hr]

section Points

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
include hΘ

/-- `Θ_b(T_{3u/q}w)` depends on `u` modulo `q`. -/
theorem shift_theta_fracShift_lift (b u : O) (w : HyperbolicSpace) :
    Θ (integralComplexMatrix (integralTranslation b) • P.fracShift (P.lift (P.res u)) • w) =
      Θ (integralComplexMatrix (integralTranslation b) • P.fracShift u • w) := by
  have h : P.res (P.lift (P.res u) - u) = 0 := by rw [map_sub, res_lift, sub_self]
  obtain ⟨r, hr⟩ := (P.res_eq_zero_iff _).mp h
  rw [show P.lift (P.res u) = u + P.p * r by linear_combination hr, P.fracShift_add_mul, mul_smul, conj_smul, hΘ,
    complexCharacter_translationConjugate_transThree, one_mul]

/-- The shifted generic point over `L_{qx}`. -/
theorem shift_mid_point (b T X e r : O) (hr : e * (1 + 9 * T * X) + P.p * r = 1) (w : HyperbolicSpace) :
    Θ (integralComplexMatrix (integralTranslation b) • P.fracShift T • complexMatrix (lowerThree (P.p * X)) • w) =
      complexCharacter (levelThreeConjugate (integralTranslation b) (P.midMat T X e r hr)) *
        Θ (integralComplexMatrix (integralTranslation b) • P.fracShift (T * e) • w) := by
  rw [← mul_smul (P.fracShift T), P.fracShift_mul_lowerThree T X e r hr, mul_smul, conj_smul, hΘ]

/-- The shifted high point over `L_{qx}`. -/
theorem shift_high_point (b T X a : O) (ha : 1 + 9 * T * X = P.p * a) (w : HyperbolicSpace) :
    Θ (integralComplexMatrix (integralTranslation b) • P.fracShift T • complexMatrix (lowerThree (P.p * X)) • w) =
      complexCharacter (levelThreeConjugate (integralTranslation b) (P.topMat T X a ha)) *
        Θ (integralComplexMatrix (integralTranslation b) • P.dilation • P.dilation • w) := by
  rw [← mul_smul (P.fracShift T), P.fracShift_mul_lowerThree_high T X a ha, mul_smul, conj_smul, hΘ, mul_smul]

/-- The generic representative `T e` reduces to `t/(1 + 9tx)` modulo `q`. -/
theorem shift_mid_lift (b : O) (x : {x : P.Res // x ≠ 0}) (T e : O) (he : P.res e = (1 + 9 * P.res T * x.1)⁻¹)
    (w : HyperbolicSpace) :
    Θ (integralComplexMatrix (integralTranslation b) • P.fracShift (T * e) • w) =
      Θ (integralComplexMatrix (integralTranslation b) •
        P.fracShift (P.lift (P.res T / (1 + 9 * P.res T * x.1))) • w) := by
  rw [← P.shift_theta_fracShift_lift Θ hΘ b (T * e)]
  congr 4
  rw [map_mul, he, div_eq_mul_inv]

/-- **The shifted pairs over the middle cusps** carry the phases of the unshifted ones. -/
theorem shiftCorrelation_lowerThree (h2 : (2 : P.Res) ≠ 0) (b : O) (x : {x : P.Res // x ≠ 0}) (t : P.Res)
    (w : HyperbolicSpace) :
    P.shiftCorrelation Θ b (P.lift t) (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) =
      if 1 + 9 * t * x.1 = 0 then
        P.chi 2 * (P.chi (3 * x.1))⁻¹ *
          (Θ (integralComplexMatrix (integralTranslation b) • P.dilation • P.dilation • w) *
            Θ (integralComplexMatrix (integralTranslation (-b)) • P.fracShift (P.lift (-t / 2)) • w))
      else if 1 - 9 * t * x.1 = 0 then
        P.chi 2 * (P.chi (3 * x.1))⁻¹ *
          (Θ (integralComplexMatrix (integralTranslation b) • P.fracShift (P.lift (t / 2)) • w) *
            Θ (integralComplexMatrix (integralTranslation (-b)) • P.dilation • P.dilation • w))
      else
        P.chi (1 - (9 * t * x.1) ^ 2) *
          (Θ (integralComplexMatrix (integralTranslation b) • P.fracShift (P.lift (t / (1 + 9 * t * x.1))) • w) *
            Θ (integralComplexMatrix (integralTranslation (-b)) •
              P.fracShift (P.lift (-t / (1 - 9 * t * x.1))) • w)) := by
  set X := P.lift x.1
  set T := P.lift t
  have hX : P.res X = x.1 := res_lift _ _
  have hT : P.res T = t := res_lift _ _
  have hres : ∀ U : O, P.res (1 + 9 * U * X) = 1 + 9 * P.res U * x.1 := fun U => by
    simp [map_ofNat, hX]
  -- a generic factorization at `U` with `1 + 9ux ≢ 0`
  have gen : ∀ U : O, 1 + 9 * P.res U * x.1 ≠ 0 → ∃ e r : O, ∃ hr : e * (1 + 9 * U * X) + P.p * r = 1,
      P.res e = (1 + 9 * P.res U * x.1)⁻¹ := by
    intro U hU
    set e := P.lift (1 + 9 * P.res U * x.1)⁻¹
    have h0 : P.res (1 - e * (1 + 9 * U * X)) = 0 := by
      rw [map_sub, map_mul, hres, res_lift, map_one, inv_mul_cancel₀ hU, sub_self]
    obtain ⟨r, hr⟩ := (P.res_eq_zero_iff _).mp h0
    exact ⟨e, r, by linear_combination -hr, res_lift _ _⟩
  have hn : P.res (-T) = -t := by rw [map_neg, hT]
  unfold shiftCorrelation
  split_ifs with h1 h1'
  · -- the first point is high
    have hm : 1 + 9 * P.res (-T) * x.1 ≠ 0 := by
      rw [hn, show 1 + 9 * -t * x.1 = 2 - (1 + 9 * t * x.1) by ring, h1, sub_zero]
      exact h2
    obtain ⟨a, ha⟩ := (P.res_eq_zero_iff _).mp (show P.res (1 + 9 * T * X) = 0 by rw [hres, hT]; exact h1)
    obtain ⟨e, r, hr, he⟩ := gen (-T) hm
    rw [P.shift_high_point Θ hΘ b T X a ha, P.shift_mid_point Θ hΘ (-b) (-T) X e r hr,
      P.shift_mid_lift Θ hΘ (-b) x (-T) e he, hn,
      show 1 + 9 * -t * x.1 = 2 by linear_combination -h1]
    have hpair := complexCharacter_translation_pair_prime P.p P.three_dvd_sub_one b (P.topMat T X a ha) (P.midMat (-T) X e r hr)
      (by show 3 * (P.p * X) = P.p * (3 * X); ring)
    have hκ := P.complexCharacter_topMat T X a ha
    have h3 : P.res (3 * X) = 3 * x.1 := by simp [map_ofNat, hX]
    rw [h3] at hκ
    rw [P.complexCharacter_midMat, hres, hn, show 1 + 9 * -t * x.1 = 2 by linear_combination -h1] at hpair
    rw [show ∀ A B C D : ℂ, A * C * (B * D) = (A * B) * (C * D) from fun A B C D => by ring, hpair,
      eq_inv_of_mul_eq_one_left hκ]
    ring
  · -- the second point is high
    have hm : 1 + 9 * P.res T * x.1 ≠ 0 := by
      rw [hT, show 1 + 9 * t * x.1 = 2 - (1 - 9 * t * x.1) by ring, h1', sub_zero]
      exact h2
    obtain ⟨a, ha⟩ := (P.res_eq_zero_iff _).mp
      (show P.res (1 + 9 * (-T) * X) = 0 by rw [hres, hn]; linear_combination h1')
    obtain ⟨e, r, hr, he⟩ := gen T hm
    rw [P.shift_mid_point Θ hΘ b T X e r hr, P.shift_mid_lift Θ hΘ b x T e he, hT,
      P.shift_high_point Θ hΘ (-b) (-T) X a ha, show 1 + 9 * t * x.1 = 2 by linear_combination -h1']
    have hpair := complexCharacter_translation_pair_prime P.p P.three_dvd_sub_one (-b) (P.topMat (-T) X a ha)
      (P.midMat T X e r hr) (by show 3 * (P.p * X) = P.p * (3 * X); ring)
    rw [neg_neg] at hpair
    have hκ := P.complexCharacter_topMat (-T) X a ha
    have h3 : P.res (3 * X) = 3 * x.1 := by simp [map_ofNat, hX]
    rw [h3] at hκ
    rw [P.complexCharacter_midMat, hres, hT, show 1 + 9 * t * x.1 = 2 by linear_combination -h1'] at hpair
    rw [show ∀ A B C D : ℂ, A * C * (B * D) = (B * A) * (C * D) from fun A B C D => by ring, hpair,
      eq_inv_of_mul_eq_one_left hκ]
    ring
  · have hm1 : 1 + 9 * P.res T * x.1 ≠ 0 := by rw [hT]; exact h1
    have hm2 : 1 + 9 * P.res (-T) * x.1 ≠ 0 := by
      rw [hn, show 1 + 9 * -t * x.1 = 1 - 9 * t * x.1 by ring]; exact h1'
    obtain ⟨e, r, hr, he⟩ := gen T hm1
    obtain ⟨e', r', hr', he'⟩ := gen (-T) hm2
    rw [P.shift_mid_point Θ hΘ b T X e r hr, P.shift_mid_lift Θ hΘ b x T e he,
      P.shift_mid_point Θ hΘ (-b) (-T) X e' r' hr', P.shift_mid_lift Θ hΘ (-b) x (-T) e' he', hT, hn,
      show 1 + 9 * -t * x.1 = 1 - 9 * t * x.1 by ring]
    have hpair := complexCharacter_translation_pair b (P.midMat T X e r hr) (P.midMat (-T) X e' r' hr') rfl
    rw [P.complexCharacter_midMat, P.complexCharacter_midMat, hres, hres, hT, hn,
      show 1 + 9 * -t * x.1 = 1 - 9 * t * x.1 by ring] at hpair
    rw [show ∀ A B C D : ℂ, A * C * (B * D) = (A * B) * (C * D) from fun A B C D => by ring, hpair,
      show (1 : P.Res) - (9 * t * x.1) ^ 2 = (1 + 9 * t * x.1) * (1 - 9 * t * x.1) by ring, map_mul]

/-- The shifted point of a class over the cusp `0`. -/
theorem shift_theta_gamma0 (b t : O) (ht : ¬ P.p ∣ t) (y : HyperbolicSpace) :
    Θ (integralComplexMatrix (integralTranslation b) • P.fracShift t • complexMatrix P.gamma0 • y) =
      complexCharacter (levelThreeConjugate (integralTranslation b) (P.gZero t ht)) *
        P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation b) • w)) (-P.lowBeta (-t))
          (P.contraction • y) := by
  rw [← mul_smul (P.fracShift t), P.fracShift_mul_gamma0 t ht, mul_smul, conj_smul, hΘ, heckeLow, mul_smul,
    mul_smul]

/-- **The shifted classes over the cusp `0`.** -/
theorem shiftSum_gamma0 (b : O) (y : HyperbolicSpace) :
    P.shiftSum Θ b (complexMatrix P.gamma0 • y) =
      Θ (integralComplexMatrix (integralTranslation b) • y) * Θ (integralComplexMatrix (integralTranslation (-b)) • y) +
        ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
          (P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation b) • w)) (-P.lowBeta (-P.lift x.1))
              (P.contraction • y) *
            P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation (-b)) • w)) (-P.lowBeta (P.lift x.1))
              (P.contraction • y)) := by
  unfold shiftSum
  rw [Fintype.sum_eq_add_sum_compl (0 : P.Res),
    Finset.sum_subtype _ (fun x => by simp : ∀ x, x ∈ ({0}ᶜ : Finset P.Res) ↔ x ≠ 0)]
  congr 1
  · rw [show P.lift 0 = P.lift (P.res 0) by rw [map_zero], P.shiftCorrelation_lift Θ hΘ, shiftCorrelation, neg_zero,
      P.fracShift_zero, one_smul, conj_smul, conj_smul, hΘ, hΘ]
    have hpair := complexCharacter_translation_pair b P.gamma0 P.gamma0 rfl
    have hγ : complexCharacter P.gamma0 = 1 := P.gammaS_character P.sKM P.sK_dvd
    rw [hγ, mul_one] at hpair
    linear_combination (Θ (integralComplexMatrix (integralTranslation b) • y) *
      Θ (integralComplexMatrix (integralTranslation (-b)) • y)) * hpair
  · refine Finset.sum_congr rfl fun x _ => ?_
    have hx : ¬ P.p ∣ P.lift x.1 := fun h => x.2 (P.res_lift_eq_zero h)
    have hx' : ¬ P.p ∣ -P.lift x.1 := fun h => hx (dvd_neg.mp h)
    rw [shiftCorrelation, P.shift_theta_gamma0 Θ hΘ b _ hx, P.shift_theta_gamma0 Θ hΘ (-b) _ hx', neg_neg]
    have hpair := complexCharacter_translation_pair b (P.gZero _ hx) (P.gZero _ hx')
      (by rw [P.gZero_lowerLeft, P.gZero_lowerLeft])
    rw [P.complexCharacter_gZero_mul _ hx hx', res_lift] at hpair
    rw [show ∀ A B C D : ℂ, A * C * (B * D) = (A * B) * (C * D) from fun A B C D => by ring, hpair]

/-- **The shifted trace over the three kinds of classes.** -/
theorem shiftTrace_eq (b : O) (w : HyperbolicSpace) :
    P.shiftTrace Θ b w = P.shiftSum Θ b w +
      (∑ x : {x : P.Res // x ≠ 0}, P.shiftSum Θ b (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) +
        ∑ s : P.Res × P.Res, P.shiftSum Θ b (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • w)) := by
  rw [P.shiftTrace_eq_sum Θ hΘ, Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · simp [fracRep]
  · congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [fracRep, map_mul, mul_smul]

end Points

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
