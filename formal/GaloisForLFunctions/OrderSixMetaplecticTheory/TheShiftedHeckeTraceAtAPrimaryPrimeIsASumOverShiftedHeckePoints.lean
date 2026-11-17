import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsAPhasedSumOverHeckePoints
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheShiftedFractionalTraceIsASumOverShiftedPoints

/-!
# The shifted Hecke trace at a primary prime is a sum over shifted Hecke points

For a primary prime `p`, `b ∈ O` and `Θ` of multiplier `κ` on `Γ(3)`, shift the two Hecke points in opposite
directions:

`F^b_Θ(w) = Θ(T_bA_pw) Θ(T_{−b}A_p⁻¹w)`   (`PrimaryPrime.heckeShiftCorrelation`).

For `γ = [[a, pb'], [pc, d]] ∈ Γ_p` the two conjugates `A_pγA_p⁻¹`, `A_p⁻¹γA_p` have lower-left entries `c` and `p²c`.
Conjugation by `T_{±b}` changes `κ = (c/a)₃` into `(c/(a ± bc))₃`, and over `c`, `p²c` the two changes cancel
(`3 ∣ p² − 1`, cubic reciprocity; `HeckeEntries.character_shift_up_mul_down`). So `F^b_Θ` keeps the multiplier `κ²`
on `Γ_p` and its trace to `Γ(3)` has the multiplier `κ²` (`heckeShiftTrace_automorphy`).

Every coset reads the same Hecke points as the unshifted trace, with `Θ_b = Θ(T_b·)` on the first factor and
`Θ_{−b}` on the second, and with the same phases (`heckeShiftTrace_eq_hecke`): the pairs `(M_W, L(k))` have equal
lower-left entries `3k`, the pairs `(M_y, L(py))` have lower-left entries `3y`, `3py`, and translations commute with
`T_b`:

`Tr_pF^b_Θ = Σ_x Θ_b^{high}Θ_{−b}^{(x)} + Σ_x Θ_b^{(x+f)}Θ_{−b}^{high} + Σ_{x, y≢0} (3y/p)₃ Θ_b^{(x−β_y)}Θ_{−b}^{(x)}`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace HeckeEntries

variable {P : PrimaryPrime} (e : HeckeEntries P)

/-- **The shifted dilates keep the square multiplier.**
`κ(T_b(A_pγA_p⁻¹)T_{−b}) κ(T_{−b}(A_p⁻¹γA_p)T_b) = κ(γ)²`. -/
theorem character_shift_up_mul_down (b : O) :
    complexCharacter (levelThreeConjugate (integralTranslation b) e.up) *
      complexCharacter (levelThreeConjugate (integralTranslation (-b)) e.down) = complexCharacter e.mat ^ 2 := by
  have h3 : (3 : O) ∣ P.p ^ 2 - 1 := by
    obtain ⟨t, ht⟩ := P.three_dvd_sub_one
    exact ⟨t * (P.p + 1), by linear_combination (P.p + 1) * ht⟩
  have hc : ((e.down : levelThree) : SL(2, O)) 1 0 = P.p ^ 2 * ((e.up : levelThree) : SL(2, O)) 1 0 := rfl
  rw [complexCharacter_translation_pair_prime (P.p ^ 2) h3 b e.up e.down hc, e.character_up_mul_down]

end HeckeEntries

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- The shifted Hecke correlation `F^b_Θ(w) = Θ(T_bA_pw) Θ(T_{−b}A_p⁻¹w)`. -/
def heckeShiftCorrelation (Θ : HyperbolicSpace → ℂ) (b : O) (w : HyperbolicSpace) : ℂ :=
  Θ (integralComplexMatrix (integralTranslation b) • (P.dilation • w)) *
    Θ (integralComplexMatrix (integralTranslation (-b)) • (P.contraction • w))

/-- **The shifted Hecke correlation has the multiplier `κ²` on `Γ_p`.** -/
theorem heckeShiftCorrelation_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b : O) (γ : levelThree) (hγ : γ ∈ P.heckeGroup) (w : HyperbolicSpace) :
    P.heckeShiftCorrelation Θ b (complexMatrix γ • w) = complexCharacter γ ^ 2 * P.heckeShiftCorrelation Θ b w := by
  obtain ⟨e, rfl⟩ := P.exists_entries_of_mem γ hγ
  unfold heckeShiftCorrelation
  rw [← mul_smul P.dilation, e.dilation_mul, mul_smul, conj_smul, hΘ, ← mul_smul P.contraction, e.contraction_mul,
    mul_smul, conj_smul, hΘ, ← e.character_shift_up_mul_down b]
  ring

/-- **The shifted Hecke trace** `Tr_pF^b_Θ(w) = Σ_{γΓ_p} κ(γ)² F^b_Θ(γ⁻¹w)`. -/
def heckeShiftTrace (Θ : HyperbolicSpace → ℂ) (b : O) (w : HyperbolicSpace) : ℂ :=
  cosetTrace complexMatrix P.heckeGroup kubotaSquare (P.heckeShiftCorrelation Θ b) w

/-- **The shifted Hecke trace has the multiplier `κ²` on `Γ(3)`.** -/
theorem heckeShiftTrace_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b : O) (M : levelThree) (w : HyperbolicSpace) :
    P.heckeShiftTrace Θ b (complexMatrix M • w) = complexCharacter M ^ 2 * P.heckeShiftTrace Θ b w :=
  cosetTrace_smul (ρ := complexMatrix) (H := P.heckeGroup) (χ := kubotaSquare)
    (F := P.heckeShiftCorrelation Θ b) (fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.heckeShiftCorrelation_automorphy Θ hΘ b δ hδ x) M w

/-- The shifted Hecke trace over the representatives `U(x)`, `WU(x)`, `L(y)U(x)`. -/
theorem heckeShiftTrace_eq_sum (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b : O) (w : HyperbolicSpace) :
    P.heckeShiftTrace Θ b w = ∑ i : P.Index,
      (complexCharacter (P.rep i) ^ 2)⁻¹ * P.heckeShiftCorrelation Θ b (complexMatrix (P.rep i) • w) := by
  have hF : ∀ δ ∈ P.heckeGroup, ∀ x, P.heckeShiftCorrelation Θ b (complexMatrix δ • x) =
      kubotaSquare δ * P.heckeShiftCorrelation Θ b x := fun δ hδ x => by
    rw [kubotaSquare_apply]
    exact P.heckeShiftCorrelation_automorphy Θ hΘ b δ hδ x
  unfold heckeShiftTrace cosetTrace
  rw [← P.cosetOf_bijective.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cosetTerm_congr hF w (γ := (P.cosetOf i).out) (γ' := (P.rep i)⁻¹) (QuotientGroup.out_eq' _)]
  unfold cosetTerm
  rw [inv_inv, kubotaSquare_apply, map_inv, inv_pow]

/-! ### The shifted Hecke points -/

variable {P}

/-- Translations commute with `T_b`: `Θ(T_bT_tX) = Θ(T_bX)`. -/
theorem shift_transThree (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b t : O) (X : HyperbolicSpace) :
    Θ (integralComplexMatrix (integralTranslation b) • (complexMatrix (transThree t) • X)) =
      Θ (integralComplexMatrix (integralTranslation b) • X) := by
  rw [conj_smul, hΘ, complexCharacter_translationConjugate_transThree, one_mul]

theorem heckeShiftCorrelation_transThree (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b t : O) (w : HyperbolicSpace) :
    P.heckeShiftCorrelation Θ b (complexMatrix (transThree t) • w) =
      P.heckeHigh (fun w => Θ (integralComplexMatrix (integralTranslation b) • w)) w *
        P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation (-b)) • w)) t w := by
  simp only [heckeShiftCorrelation, heckeHigh, heckeLow]
  rw [← mul_smul P.dilation, P.dilation_transThree, mul_smul, shift_transThree Θ hΘ]

theorem heckeShiftCorrelation_wMat (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b t : O) (w : HyperbolicSpace) :
    P.heckeShiftCorrelation Θ b (complexMatrix (P.wMat * transThree t) • w) =
      complexCharacter P.wMat ^ 2 *
        (P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation b) • w)) (P.wShift + t) w *
          P.heckeHigh (fun w => Θ (integralComplexMatrix (integralTranslation (-b)) • w)) w) := by
  have h1 : Θ (integralComplexMatrix (integralTranslation b) • (P.dilation • (complexMatrix (P.wMat * transThree t) • w))) =
      complexCharacter (levelThreeConjugate (integralTranslation b) P.highMat) *
        Θ (integralComplexMatrix (integralTranslation b) •
          (P.contraction • (complexMatrix (transThree (P.wShift + t)) • w))) := by
    rw [map_mul, mul_smul, ← mul_smul P.dilation, P.dilation_wMat, mul_smul, mul_smul, conj_smul, hΘ,
      ← mul_smul (complexMatrix (transThree P.wShift)), ← map_mul, transThree_mul]
  have h2 : Θ (integralComplexMatrix (integralTranslation (-b)) •
        (P.contraction • (complexMatrix (P.wMat * transThree t) • w))) =
      complexCharacter (levelThreeConjugate (integralTranslation (-b)) (lowerThree P.wK)) *
        Θ (integralComplexMatrix (integralTranslation (-b)) • (P.dilation • w)) := by
    rw [map_mul, mul_smul, ← mul_smul P.contraction, P.contraction_wMat, mul_smul, mul_smul, conj_smul, hΘ,
      shift_transThree Θ hΘ, ← mul_smul P.dilation, P.dilation_transThree, mul_smul, shift_transThree Θ hΘ]
  have hp : complexCharacter (levelThreeConjugate (integralTranslation b) P.highMat) *
      complexCharacter (levelThreeConjugate (integralTranslation (-b)) (lowerThree P.wK)) =
        complexCharacter P.wMat ^ 2 := by
    rw [complexCharacter_translation_pair b P.highMat (lowerThree P.wK) rfl, P.complexCharacter_highMat,
      complexCharacter_lowerThree, mul_one]
  simp only [heckeShiftCorrelation, heckeHigh, heckeLow]
  rw [h1, h2]
  linear_combination (Θ (integralComplexMatrix (integralTranslation b) •
      (P.contraction • (complexMatrix (transThree (P.wShift + t)) • w))) *
    Θ (integralComplexMatrix (integralTranslation (-b)) • (P.dilation • w))) * hp

theorem heckeShiftCorrelation_lowerThree (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b y : O) (hy : ¬ P.p ∣ y) (t : O) (w : HyperbolicSpace) :
    P.heckeShiftCorrelation Θ b (complexMatrix (lowerThree y * transThree t) • w) =
      ringComplex (symbol (3 * y) P.p) *
        P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation b) • w)) (t - P.lowBeta y) w *
          P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation (-b)) • w)) t w := by
  have h1 : Θ (integralComplexMatrix (integralTranslation b) •
        (P.dilation • (complexMatrix (lowerThree y * transThree t) • w))) =
      complexCharacter (levelThreeConjugate (integralTranslation b) (P.lowMat y hy)) *
        Θ (integralComplexMatrix (integralTranslation b) •
          (P.contraction • (complexMatrix (transThree (t - P.lowBeta y)) • w))) := by
    rw [map_mul, mul_smul, ← mul_smul P.dilation, P.dilation_lowerThree y hy, mul_smul, mul_smul, conj_smul, hΘ,
      ← mul_smul (complexMatrix (transThree (-P.lowBeta y))), ← map_mul, transThree_mul,
      show -P.lowBeta y + t = t - P.lowBeta y by ring]
  have h2 : Θ (integralComplexMatrix (integralTranslation (-b)) •
        (P.contraction • (complexMatrix (lowerThree y * transThree t) • w))) =
      complexCharacter (levelThreeConjugate (integralTranslation (-b)) (lowerThree (P.p * y))) *
        Θ (integralComplexMatrix (integralTranslation (-b)) • (P.contraction • (complexMatrix (transThree t) • w))) := by
    rw [map_mul, mul_smul, ← mul_smul P.contraction, P.contraction_lowerThree, mul_smul, conj_smul, hΘ]
  have hc : ((lowerThree (P.p * y) : levelThree) : SL(2, O)) 1 0 =
      P.p * ((P.lowMat y hy : levelThree) : SL(2, O)) 1 0 := by
    show 3 * (P.p * y) = P.p * (3 * y)
    ring
  have hp : complexCharacter (levelThreeConjugate (integralTranslation b) (P.lowMat y hy)) *
      complexCharacter (levelThreeConjugate (integralTranslation (-b)) (lowerThree (P.p * y))) =
        ringComplex (symbol (3 * y) P.p) := by
    rw [complexCharacter_translation_pair_prime P.p P.three_dvd_sub_one b _ _ hc, P.complexCharacter_lowMat y hy,
      complexCharacter_lowerThree, mul_one]
  simp only [heckeShiftCorrelation, heckeLow]
  rw [h1, h2]
  linear_combination (Θ (integralComplexMatrix (integralTranslation b) •
      (P.contraction • (complexMatrix (transThree (t - P.lowBeta y)) • w))) *
    Θ (integralComplexMatrix (integralTranslation (-b)) • (P.contraction • (complexMatrix (transThree t) • w)))) * hp

variable (P)

/-- **The shifted Hecke trace at `p` as a phased sum over shifted Hecke points.** -/
theorem heckeShiftTrace_eq_hecke (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (b : O) (w : HyperbolicSpace) :
    P.heckeShiftTrace Θ b w =
      (∑ x : P.Res, P.heckeHigh (fun w => Θ (integralComplexMatrix (integralTranslation b) • w)) w *
          P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation (-b)) • w)) (P.lift x) w) +
        ((∑ x : P.Res, P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation b) • w))
              (P.wShift + P.lift x) w *
            P.heckeHigh (fun w => Θ (integralComplexMatrix (integralTranslation (-b)) • w)) w) +
          ∑ x : P.Res, ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
            P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation b) • w))
              (P.lift x - P.lowBeta (P.lift y.1)) w *
            P.heckeLow (fun w => Θ (integralComplexMatrix (integralTranslation (-b)) • w)) (P.lift x) w) := by
  rw [P.heckeShiftTrace_eq_sum Θ hΘ, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hW : complexCharacter P.wMat ≠ 0 := by
    intro h
    have := norm_complexCharacter P.wMat
    rw [h, norm_zero] at this
    exact zero_ne_one this
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    change (complexCharacter (transThree (P.lift x)) ^ 2)⁻¹ *
      P.heckeShiftCorrelation Θ b (complexMatrix (transThree (P.lift x)) • w) = _
    rw [complexCharacter_transThree, one_pow, inv_one, one_mul, heckeShiftCorrelation_transThree Θ hΘ]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    change (complexCharacter (P.wMat * transThree (P.lift x)) ^ 2)⁻¹ *
      P.heckeShiftCorrelation Θ b (complexMatrix (P.wMat * transThree (P.lift x)) • w) = _
    rw [map_mul, complexCharacter_transThree, mul_one, heckeShiftCorrelation_wMat Θ hΘ, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hW), one_mul]
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    change (complexCharacter (lowerThree (P.lift y.1) * transThree (P.lift x)) ^ 2)⁻¹ *
      P.heckeShiftCorrelation Θ b (complexMatrix (lowerThree (P.lift y.1) * transThree (P.lift x)) • w) = _
    rw [map_mul, complexCharacter_transThree, complexCharacter_lowerThree, mul_one, one_pow, inv_one, one_mul,
      heckeShiftCorrelation_lowerThree Θ hΘ _ _ (P.not_dvd_lift y)]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
