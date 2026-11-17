import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFractionalTraceIsASumOverTheProjectiveLineModuloTheSquare
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheOppositeTranslationsPreserveTheCubicMultiplier

/-!
# The shifted fractional trace has the square multiplier

For an odd primary prime `q` (`PrimaryPrime`) and `b ∈ O`, shift the two opposite fractional translations of the
fractional trace by `±b`:

`G^b_Θ(w) = Σ_{t ∈ O/q} Θ(T_bT_tw) Θ(T_{−b}T_{−t}w)`   (`PrimaryPrime.shiftSum`).

Conjugation by the integral translation `T_b` maps `Γ(3)` to itself and changes `κ(γ) = (c/a)₃` into
`(c/(a + bc))₃` (`complexCharacter_translationConjugate`). For two matrices with the same lower-left entry `c`
the opposite changes cancel (`symbol_pair_shifts`): `(a₁ + bc)(a₂ − bc) ≡ a₁a₂` modulo `9` and `c`, because
`3 ∣ a₂ − a₁`. The conjugated matrices `M_{±t}` of the fractional trace share their lower-left entry, so `G^b_Θ`
keeps the multiplier `κ²` on `Γ(3) ∩ Γ₀(q²)` (`shiftSum_automorphy`), its trace is automorphic on `Γ(3)`
(`shiftTrace_automorphy`), and the trace is the sum over the representatives of the fractional trace
(`shiftTrace_eq_sum`). At `b = 0` it is the fractional trace (`shiftSum_zero`).
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- Opposite shifts of two denominators over a common numerator `c` cancel their ramified phases. -/
theorem symbol_pair_shifts (a₁ a₂ b c : O) (h₁ : (3 : O) ∣ a₁ - 1) (h₂ : (3 : O) ∣ a₂ - 1)
    (hc : (3 : O) ∣ c) :
    symbol c (a₁ + b * c) * symbol c (a₂ - b * c) = symbol c a₁ * symbol c a₂ := by
  have hl₁ : lambda ^ 2 ∣ a₁ - 1 := lambda_sq_dvd_three.trans h₁
  have hl₂ : lambda ^ 2 ∣ a₂ - 1 := lambda_sq_dvd_three.trans h₂
  have hbc : lambda ^ 2 ∣ b * c := dvd_mul_of_dvd_right (lambda_sq_dvd_three.trans hc) b
  have hA : lambda ^ 2 ∣ a₁ + b * c - 1 := by convert dvd_add hl₁ hbc using 1; ring
  have hB : lambda ^ 2 ∣ a₂ - b * c - 1 := by convert dvd_sub hl₂ hbc using 1; ring
  have hAB : lambda ^ 2 ∣ (a₁ + b * c) * (a₂ - b * c) - 1 := by
    convert dvd_add (dvd_mul_of_dvd_left hA (a₂ - b * c)) hB using 1; ring
  have h12 : lambda ^ 2 ∣ a₁ * a₂ - 1 := by
    convert dvd_add (dvd_mul_of_dvd_left hl₁ a₂) hl₂ using 1; ring
  have h9 : (9 : O) ∣ (a₁ + b * c) * (a₂ - b * c) - a₁ * a₂ := by
    obtain ⟨k, hk⟩ := hc
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨b * k * (e₂ - e₁) - (b * k) ^ 2, ?_⟩
    rw [hk]
    linear_combination (3 * b * k) * he₂ - (3 * b * k) * he₁
  have hcc : c ∣ (a₁ + b * c) * (a₂ - b * c) - a₁ * a₂ := ⟨b * (a₂ - a₁) - b ^ 2 * c, by ring⟩
  calc
    _ = symbol c ((a₁ + b * c) * (a₂ - b * c)) := (symbol_mul_denominator _ _ _).symm
    _ = symbol c (a₁ * a₂) := symbol_denominator_congr c _ _ hAB h12 h9 hcc
    _ = _ := symbol_mul_denominator _ _ _

/-- Conjugation by `T_b` turns `κ(γ) = (c/a)₃` into `(c/(a + bc))₃`. -/
theorem complexCharacter_translationConjugate (b : O) (n : levelThree) :
    complexCharacter (levelThreeConjugate (integralTranslation b) n) =
      ringComplex (symbol ((n : SL(2, O)) 1 0) ((n : SL(2, O)) 0 0 + b * (n : SL(2, O)) 1 0)) := by
  change ringComplex (value _) = _
  congr 1
  simp only [value, levelThreeConjugate, integralTranslation,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp

/-- **Pair cancellation.** For `n₁, n₂ ∈ Γ(3)` with the same lower-left entry,
`κ(T_bn₁T_{−b}) κ(T_{−b}n₂T_b) = κ(n₁) κ(n₂)`. -/
theorem complexCharacter_translation_pair (b : O) (n₁ n₂ : levelThree)
    (h : (n₁ : SL(2, O)) 1 0 = (n₂ : SL(2, O)) 1 0) :
    complexCharacter (levelThreeConjugate (integralTranslation b) n₁) *
      complexCharacter (levelThreeConjugate (integralTranslation (-b)) n₂) =
        complexCharacter n₁ * complexCharacter n₂ := by
  have h₁ : (3 : O) ∣ (n₁ : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry n₁ 0 0
  have h₂ : (3 : O) ∣ (n₂ : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry n₂ 0 0
  have hc : (3 : O) ∣ (n₂ : SL(2, O)) 1 0 := by simpa using levelThree_entry n₂ 1 0
  rw [complexCharacter_translationConjugate, complexCharacter_translationConjugate, complexCharacter_eq_symbol,
    complexCharacter_eq_symbol, h, ← map_mul, ← map_mul,
    show (n₂ : SL(2, O)) 0 0 + -b * (n₂ : SL(2, O)) 1 0 = (n₂ : SL(2, O)) 0 0 - b * (n₂ : SL(2, O)) 1 0 by ring,
    symbol_pair_shifts _ _ b _ h₁ h₂ hc]

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `F^b_t(w) = Θ(T_bT_tw) Θ(T_{−b}T_{−t}w)`. -/
def shiftCorrelation (Θ : HyperbolicSpace → ℂ) (b t : O) (w : HyperbolicSpace) : ℂ :=
  Θ (integralComplexMatrix (integralTranslation b) • (P.fracShift t • w)) *
    Θ (integralComplexMatrix (integralTranslation (-b)) • (P.fracShift (-t) • w))

/-- `G^b_Θ = Σ_{t ∈ O/q} F^b_t`. -/
def shiftSum (Θ : HyperbolicSpace → ℂ) (b : O) (w : HyperbolicSpace) : ℂ :=
  ∑ x : P.Res, P.shiftCorrelation Θ b (P.lift x) w

theorem shiftSum_zero (Θ : HyperbolicSpace → ℂ) : P.shiftSum Θ 0 = P.fracSum Θ := by
  have h1 : integralTranslation (0 : O) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [integralTranslation]
  funext w
  simp only [shiftSum, fracSum, shiftCorrelation, fracCorrelation, neg_zero, h1, map_one, one_smul]

/-- `F^b_t` depends on `t` modulo `q`. -/
theorem shiftCorrelation_lift (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b t : O) (w : HyperbolicSpace) :
    P.shiftCorrelation Θ b (P.lift (P.res t)) w = P.shiftCorrelation Θ b t w := by
  have hP := P.ringComplex_ne_zero
  have hsh : ∀ u r : O, P.fracShift (u + P.p * r) = complexMatrix (transThree r) * P.fracShift u := by
    intro u r
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [fracShift, complexTranslation, complexMatrix_apply, transThree, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
    field_simp
  have h : P.res (P.lift (P.res t) - t) = 0 := by rw [map_sub, res_lift, sub_self]
  obtain ⟨s, hs⟩ := (P.res_eq_zero_iff _).mp h
  rw [show P.lift (P.res t) = t + P.p * s by linear_combination hs]
  unfold shiftCorrelation
  have hT : ∀ (g r : O), complexCharacter (levelThreeConjugate (integralTranslation g) (transThree r)) = 1 := by
    intro g r
    rw [complexCharacter_translationConjugate, ← complexCharacter_transThree r, complexCharacter_eq_symbol]
    simp [transThree]
  rw [hsh, show -(t + P.p * s) = -t + P.p * (-s) by ring, hsh, mul_smul, mul_smul, conj_smul, conj_smul, hΘ, hΘ,
    hT, hT, one_mul, one_mul]

/-- Moving `δ ∈ Γ(3) ∩ Γ₀(q²)` through the shifted translate: `Θ(T_bT_tδw) = κ(T_bM_tT_{−b})Θ(T_bT_{td²}w)`. -/
theorem shift_fracShift_mul (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b : O) (δ : levelThree) (c₂ : O) (hc : (δ : SL(2, O)) 1 0 = P.p ^ 2 * c₂) (t : O)
    (hdet : (δ : SL(2, O)) 0 0 * (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 1 * (P.p ^ 2 * c₂) = 1)
    (ha : (3 : O) ∣ (δ : SL(2, O)) 0 0 - 1) (hb : (3 : O) ∣ (δ : SL(2, O)) 0 1)
    (hc3 : (3 : O) ∣ P.p ^ 2 * c₂) (hd : (3 : O) ∣ (δ : SL(2, O)) 1 1 - 1) (w : HyperbolicSpace) :
    Θ (integralComplexMatrix (integralTranslation b) • (P.fracShift t • (complexMatrix δ • w))) =
      complexCharacter (levelThreeConjugate (integralTranslation b)
          (P.fracConj ((δ : SL(2, O)) 0 0) ((δ : SL(2, O)) 0 1) c₂ ((δ : SL(2, O)) 1 1) t hdet ha hb hc3 hd)) *
        Θ (integralComplexMatrix (integralTranslation b) • (P.fracShift (t * (δ : SL(2, O)) 1 1 ^ 2) • w)) := by
  rw [← mul_smul (P.fracShift t) (complexMatrix δ) w, P.fracShift_mul δ c₂ hc t hdet ha hb hc3 hd, mul_smul,
    conj_smul, hΘ]

/-- **The shifted sum has the multiplier `κ²` on `Γ(3) ∩ Γ₀(q²)`.** -/
theorem shiftSum_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b : O) (δ : levelThree) (hδ : δ ∈ P.levelSqGroup) (w : HyperbolicSpace) :
    P.shiftSum Θ b (complexMatrix δ • w) = complexCharacter δ ^ 2 * P.shiftSum Θ b w := by
  obtain ⟨c₂, hc⟩ := hδ
  have hdet : (δ : SL(2, O)) 0 0 * (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 1 * (P.p ^ 2 * c₂) = 1 := by
    rw [← hc, ← Matrix.det_fin_two]
    exact (δ : SL(2, O)).det_coe
  have ha : (3 : O) ∣ (δ : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry δ 0 0
  have hb : (3 : O) ∣ (δ : SL(2, O)) 0 1 := by simpa using levelThree_entry δ 0 1
  have hc3 : (3 : O) ∣ P.p ^ 2 * c₂ := by rw [← hc]; simpa using levelThree_entry δ 1 0
  have hd : (3 : O) ∣ (δ : SL(2, O)) 1 1 - 1 := by simpa using levelThree_entry δ 1 1
  have hκ : complexCharacter δ = ringComplex (symbol (P.p ^ 2 * c₂) ((δ : SL(2, O)) 0 0)) := by
    rw [complexCharacter_eq_symbol, hc]
  have hterm : ∀ t : O, P.shiftCorrelation Θ b t (complexMatrix δ • w) =
      complexCharacter δ ^ 2 * P.shiftCorrelation Θ b (t * (δ : SL(2, O)) 1 1 ^ 2) w := by
    intro t
    unfold shiftCorrelation
    rw [P.shift_fracShift_mul Θ hΘ b δ c₂ hc t hdet ha hb hc3 hd,
      P.shift_fracShift_mul Θ hΘ (-b) δ c₂ hc (-t) hdet ha hb hc3 hd, hκ,
      ← P.fracConj_character_mul _ _ c₂ _ t hdet ha hb hc3 hd,
      ← complexCharacter_translation_pair b (P.fracConj _ _ c₂ _ t hdet ha hb hc3 hd)
        (P.fracConj _ _ c₂ _ (-t) hdet ha hb hc3 hd) rfl,
      show -t * (δ : SL(2, O)) 1 1 ^ 2 = -(t * (δ : SL(2, O)) 1 1 ^ 2) by ring]
    ring
  have hd0 : P.res ((δ : SL(2, O)) 1 1) ≠ 0 := by
    intro h0
    have h := congrArg P.res hdet
    rw [map_sub, map_mul, map_mul, h0, mul_zero, map_mul, map_pow, P.res_p] at h
    simp at h
  unfold shiftSum
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  have hbij : Function.Bijective (fun x : P.Res => x * P.res ((δ : SL(2, O)) 1 1) ^ 2) :=
    mulRight_bijective₀ _ (pow_ne_zero 2 hd0)
  rw [← hbij.sum_comp (fun y => P.shiftCorrelation Θ b (P.lift y) w)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show x * P.res ((δ : SL(2, O)) 1 1) ^ 2 = P.res (P.lift x * (δ : SL(2, O)) 1 1 ^ 2) by
      rw [map_mul, map_pow, res_lift],
    P.shiftCorrelation_lift Θ hΘ]

/-- The trace `Tr G^b_Θ(w) = Σ_{γ(Γ(3) ∩ Γ₀(q²))} κ(γ)² G^b_Θ(γ⁻¹w)`. -/
def shiftTrace (Θ : HyperbolicSpace → ℂ) (b : O) (w : HyperbolicSpace) : ℂ :=
  cosetTrace complexMatrix P.levelSqGroup kubotaSquare (P.shiftSum Θ b) w

/-- **The shifted trace has the multiplier `κ²` on `Γ(3)`.** -/
theorem shiftTrace_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b : O) (M : levelThree) (w : HyperbolicSpace) :
    P.shiftTrace Θ b (complexMatrix M • w) = complexCharacter M ^ 2 * P.shiftTrace Θ b w :=
  cosetTrace_smul (ρ := complexMatrix) (H := P.levelSqGroup) (χ := kubotaSquare)
    (F := P.shiftSum Θ b) (fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.shiftSum_automorphy Θ hΘ b δ hδ x) M w

/-- **The shifted trace over the representatives** `1`, `L_{qx}`, `γ₀T(3s)` (all weights `1`). -/
theorem shiftTrace_eq_sum (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b : O) (w : HyperbolicSpace) :
    P.shiftTrace Θ b w = ∑ i : P.FracIndex, P.shiftSum Θ b (complexMatrix (P.fracRep i) • w) := by
  have hF : ∀ δ ∈ P.levelSqGroup, ∀ x, P.shiftSum Θ b (complexMatrix δ • x) = kubotaSquare δ * P.shiftSum Θ b x :=
    fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.shiftSum_automorphy Θ hΘ b δ hδ x
  unfold shiftTrace cosetTrace
  rw [← P.fracCoset_bijective.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cosetTerm_congr hF w (γ := (P.fracCoset i).out) (γ' := (P.fracRep i)⁻¹) (QuotientGroup.out_eq' _)]
  unfold cosetTerm
  rw [inv_inv, kubotaSquare_apply, map_inv, P.complexCharacter_fracRep, inv_one, one_pow, one_mul]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
