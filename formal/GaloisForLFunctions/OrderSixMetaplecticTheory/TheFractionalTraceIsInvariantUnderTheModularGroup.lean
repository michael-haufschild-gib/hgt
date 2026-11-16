import GaloisForLFunctions.OrderSixMetaplecticTheory.TheOppositeFractionalTranslationsHaveTheSquareMultiplier

/-!
# The fractional trace is invariant under the modular group

For `Θ` of multiplier `κ` on `Γ(3)` and invariant under `SL₂(ℤ)` (as `θ_s` is), the trace `Tr G_Θ` of the
opposite fractional translations is invariant under `SL₂(ℤ)` (`fracTrace_rational`):

* `T = [[1, 1], [0, 1]]` commutes with every `T_t` and fixes `Θ`, and conjugation by `T` fixes `c`;
* for `S`, choose `k, m ∈ O` with `q⁴m + 9k² = 1` and `q² ∣ 3k − 1`, and put `γ₀ = [[q², −3k], [3k, q²m]] ∈ Γ(3)`
  (`γ₀ ≡ S mod q²`). Then `S⁻¹T_tS = δ_tT_tγ₀` with `δ_t ∈ Γ(3)` for **every** `t`
  (`fracShift_mul_S`), and `κ(δ_t)κ(δ_{−t}) = (9k² − 9t²q²m²/q²m)₃ = 1`, so `G_Θ ∘ S = G_Θ ∘ γ₀`
  (`fracSum_S`). The element `g = Sγ₀⁻¹ ≡ 1 mod q²` normalizes `Γ(3) ∩ Γ₀(q²)` and fixes `G_Θ`, so it fixes the
  trace, and `κ(γ₀) = (3k/q²)₃ = 1`.

Hence the trace sees all four rational cusps of `Γ(3)` alike: only its constant term at `∞` is needed.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Conjugation permutes the cosets -/

theorem mem_levelSqGroup (γ : levelThree) : γ ∈ P.levelSqGroup ↔ P.p ^ 2 ∣ (γ : SL(2, O)) 1 0 := Iff.rfl

theorem fracConjCoset_rel (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.levelSqGroup ↔ γ ∈ P.levelSqGroup)
    (a b : levelThree) : (QuotientGroup.leftRel P.levelSqGroup) a b ↔
      (QuotientGroup.leftRel P.levelSqGroup) ((conjLevel g).toEquiv a) ((conjLevel g).toEquiv b) := by
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
  show a⁻¹ * b ∈ P.levelSqGroup ↔ (conjLevel g a)⁻¹ * conjLevel g b ∈ P.levelSqGroup
  rw [← map_inv, ← map_mul, hA]

/-- Conjugation permutes the cosets of `Γ(3) ∩ Γ₀(q²)`. -/
def fracConjCoset (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.levelSqGroup ↔ γ ∈ P.levelSqGroup) :
    (levelThree ⧸ P.levelSqGroup) ≃ (levelThree ⧸ P.levelSqGroup) :=
  Quotient.congr (conjLevel g).toEquiv (P.fracConjCoset_rel g hA)

theorem fracConjCoset_mk (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.levelSqGroup ↔ γ ∈ P.levelSqGroup)
    (γ : levelThree) : P.fracConjCoset g hA (γ : levelThree ⧸ P.levelSqGroup) = ((conjLevel g γ : levelThree) : _) := by
  unfold fracConjCoset
  exact Quotient.congr_mk _ _ γ

/-- **Conjugation equivariance of the trace.** If `g` normalizes `Γ(3) ∩ Γ₀(q²)`, fixes `κ` and multiplies `G_Θ` by
`c`, it multiplies the trace by `c`. -/
theorem fracTrace_conj (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.levelSqGroup ↔ γ ∈ P.levelSqGroup)
    (hκ : ∀ γ : levelThree, complexCharacter (conjLevel g γ) = complexCharacter γ) (c : ℂ)
    (hF : ∀ w, P.fracSum Θ (integralComplexMatrix g • w) = c * P.fracSum Θ w)
    (w : HyperbolicSpace) :
    P.fracTrace Θ (integralComplexMatrix g • w) = c * P.fracTrace Θ w := by
  have hFΘ : ∀ δ ∈ P.levelSqGroup, ∀ x, P.fracSum Θ (complexMatrix δ • x) = kubotaSquare δ * P.fracSum Θ x :=
    fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.fracSum_automorphy Θ hΘ δ hδ x
  unfold fracTrace cosetTrace
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (P.fracConjCoset g hA) _ _ fun q => ?_
  have hq : (((P.fracConjCoset g hA q).out : levelThree) : levelThree ⧸ P.levelSqGroup) =
      ((conjLevel g q.out : levelThree) : _) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact P.fracConjCoset_mk g hA q.out
  rw [cosetTerm_congr hFΘ w hq]
  unfold cosetTerm
  rw [kubotaSquare_apply, kubotaSquare_apply, hκ]
  have hmat : complexMatrix (conjLevel g q.out)⁻¹ =
      (integralComplexMatrix g)⁻¹ * complexMatrix q.out⁻¹ * integralComplexMatrix g := by
    rw [map_inv, map_inv, complexMatrix_eq, complexMatrix_eq, conjLevel_coe, map_mul, map_mul, map_inv]
    group
  have hw : complexMatrix q.out⁻¹ • integralComplexMatrix g • w =
      integralComplexMatrix g • (complexMatrix (conjLevel g q.out)⁻¹ • w) := by
    rw [hmat, ← mul_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hw, hF]
  ring

/-! ### The generator `T` -/

theorem fracShift_mul_T (t : O) :
    P.fracShift t * integralComplexMatrix (tPowO 1) = integralComplexMatrix (tPowO 1) * P.fracShift t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fracShift, complexTranslation, integralComplexMatrix, coe_tPowO, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]
  ring

theorem conjLevel_mem_iff_T (γ : levelThree) :
    conjLevel (tPowO 1) γ ∈ P.levelSqGroup ↔ γ ∈ P.levelSqGroup := by
  have hinv : (((tPowO 1)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) = !![1, -1; 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, coe_tPowO]
    simp [Matrix.adjugate_fin_two]
  have h10 : ((tPowO 1)⁻¹ * (γ : SL(2, O)) * tPowO 1) 1 0 = (γ : SL(2, O)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_tPowO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [mem_levelSqGroup, mem_levelSqGroup, conjLevel_coe, h10]

section Rational

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
  (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
include hΘ hΘr

omit hΘ in
theorem fracSum_T (w : HyperbolicSpace) :
    P.fracSum Θ (integralComplexMatrix (tPowO 1) • w) = P.fracSum Θ w := by
  unfold fracSum fracCorrelation
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_smul, ← mul_smul, P.fracShift_mul_T, P.fracShift_mul_T, mul_smul, mul_smul, tPowO, hΘr, hΘr]

theorem fracTrace_T (w : HyperbolicSpace) :
    P.fracTrace Θ (integralComplexMatrix (tPowO 1) • w) = P.fracTrace Θ w := by
  have h := P.fracTrace_conj Θ hΘ (tPowO 1) P.conjLevel_mem_iff_T (complexCharacter_conjLevel_rational _) 1
    (fun y => by rw [one_mul]; exact P.fracSum_T Θ hΘr y) w
  rw [h, one_mul]

end Rational


/-! ### The generator `S` -/

theorem exists_sData : ∃ k m : O, P.p ^ 4 * m + 9 * k ^ 2 = 1 ∧ P.p ^ 2 ∣ 3 * k - 1 := by
  obtain ⟨a, b, hab⟩ := P.isCoprime_three.pow_right (n := 4)
  exact ⟨a, b * (1 + 3 * a), by linear_combination (1 + 3 * a) * hab, ⟨-(b * P.p ^ 2), by linear_combination hab⟩⟩

theorem three_dvd_sq_sub_one : (3 : O) ∣ P.p ^ 2 - 1 := by
  obtain ⟨a, ha⟩ := P.three_dvd_sub_one
  exact ⟨a * (P.p + 1), by linear_combination (P.p + 1) * ha⟩

section SData

variable {k m : O} (hkm : P.p ^ 4 * m + 9 * k ^ 2 = 1)
include hkm

theorem three_dvd_sMid : (3 : O) ∣ P.p ^ 2 * m - 1 := by
  obtain ⟨a, ha⟩ := P.three_dvd_sub_one
  exact ⟨-(a * (P.p + 1) * P.p ^ 2 * m) - 3 * k ^ 2, by
    linear_combination (-((P.p + 1) * P.p ^ 2 * m)) * ha + hkm⟩

/-- `γ₀ = [[q², −3k], [3k, q²m]] ∈ Γ(3)`; `γ₀ ≡ S mod q²`. -/
def gammaS : levelThree :=
  ⟨⟨!![P.p ^ 2, -3 * k; 3 * k, P.p ^ 2 * m], by rw [Matrix.det_fin_two_of]; linear_combination hkm⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using P.three_dvd_sq_sub_one
      · exact ⟨-k, by simp⟩
      · exact ⟨k, by simp⟩
      · simpa using P.three_dvd_sMid hkm)⟩

/-- `δ_t = [[q²m, 3k − 3tqm], [−3k − 3tqm, q² + 9t²m]] ∈ Γ(3)`. -/
def deltaS (t : O) : levelThree :=
  ⟨⟨!![P.p ^ 2 * m, 3 * k - 3 * t * P.p * m; -3 * k - 3 * t * P.p * m, P.p ^ 2 + 9 * t ^ 2 * m], by
      rw [Matrix.det_fin_two_of]; linear_combination hkm⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using P.three_dvd_sMid hkm
      · exact ⟨k - t * P.p * m, by simp; ring⟩
      · exact ⟨-k - t * P.p * m, by simp; ring⟩
      · obtain ⟨a, ha⟩ := P.three_dvd_sq_sub_one
        exact ⟨a + 3 * t ^ 2 * m, by simp; linear_combination ha⟩)⟩

/-- `T_uS = S δ_t T_u γ₀` whenever `uq = 3t`. -/
theorem translation_mul_S (t : O) (u : ℂ) (hu : u * ringComplex P.p = 3 * ringComplex t) :
    complexTranslation u * integralComplexMatrix sO =
      integralComplexMatrix sO * (complexMatrix (P.deltaS hkm t) * (complexTranslation u * complexMatrix (P.gammaS hkm))) := by
  have hdet := congrArg ringComplex hkm
  simp only [map_add, map_mul, map_pow, map_one, map_ofNat] at hdet
  rw [complexMatrix_eq, complexMatrix_eq]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation, integralComplexMatrix, coe_sO, deltaS, gammaS, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map, Matrix.vecMul, dotProduct, map_ofNat]
  · linear_combination (-u) * hdet +
      (ringComplex P.p ^ 3 * ringComplex m - 9 * ringComplex t * ringComplex k * ringComplex m) * hu
  · linear_combination hdet + (-3 * ringComplex k * ringComplex P.p * ringComplex m -
      3 * ringComplex t * ringComplex P.p ^ 2 * ringComplex m ^ 2) * hu
  · linear_combination (-1 : ℂ) * hdet + (-3 * ringComplex k * ringComplex P.p * ringComplex m) * hu
  · linear_combination (-(ringComplex P.p ^ 3 * ringComplex m ^ 2)) * hu


theorem fracShift_mul_S (t : O) :
    P.fracShift t * integralComplexMatrix sO =
      integralComplexMatrix sO * (complexMatrix (P.deltaS hkm t) * (P.fracShift t * complexMatrix (P.gammaS hkm))) :=
  P.translation_mul_S hkm t _ (by field_simp [P.ringComplex_ne_zero])

theorem deltaS_entries (t : O) : ((P.deltaS hkm t : levelThree) : SL(2, O)) 1 0 = -3 * k - 3 * t * P.p * m ∧
    ((P.deltaS hkm t : levelThree) : SL(2, O)) 0 0 = P.p ^ 2 * m := by
  constructor <;> simp [deltaS]

theorem gammaS_entries : ((P.gammaS hkm : levelThree) : SL(2, O)) 1 0 = 3 * k ∧
    ((P.gammaS hkm : levelThree) : SL(2, O)) 0 0 = P.p ^ 2 := by
  constructor <;> simp [gammaS]

/-- The phases cancel: `κ(δ_t)κ(δ_{−t}) = (9k² − 9t²q²m²/q²m)₃ = 1`. -/
theorem deltaS_character_mul (t : O) :
    complexCharacter (P.deltaS hkm t) * complexCharacter (P.deltaS hkm (-t)) = 1 := by
  rw [complexCharacter_eq_symbol, complexCharacter_eq_symbol, ← map_mul, (P.deltaS_entries hkm t).1,
    (P.deltaS_entries hkm t).2, (P.deltaS_entries hkm (-t)).1, (P.deltaS_entries hkm (-t)).2,
    ← symbol_mul_numerator, symbol_congr (y := 1) ⟨-P.p ^ 2 - 9 * t ^ 2 * m, by linear_combination hkm⟩,
    symbol_one_numerator _ (lambda_sq_dvd_three.trans (P.three_dvd_sMid hkm)), map_one]

theorem gammaS_character (hk : P.p ^ 2 ∣ 3 * k - 1) : complexCharacter (P.gammaS hkm) = 1 := by
  rw [complexCharacter_eq_symbol, (P.gammaS_entries hkm).1, (P.gammaS_entries hkm).2, symbol_congr (y := 1) hk, symbol_one_numerator _ (lambda_sq_dvd_three.trans P.three_dvd_sq_sub_one), map_one]

/-- `g = Sγ₀⁻¹ = [[3k, −q²], [q²m, 3k]] ≡ 1 mod q²`. -/
def gS : SL(2, O) :=
  ⟨!![3 * k, -P.p ^ 2; P.p ^ 2 * m, 3 * k], by rw [Matrix.det_fin_two_of]; linear_combination hkm⟩

theorem gS_mul_gammaS : P.gS hkm * (P.gammaS hkm : SL(2, O)) = sO := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [gS, gammaS, coe_sO, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination hkm | linear_combination -hkm

theorem conjLevel_mem_iff_gS (γ : levelThree) :
    conjLevel (P.gS hkm) γ ∈ P.levelSqGroup ↔ γ ∈ P.levelSqGroup := by
  have hinv : (((P.gS hkm)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) = !![3 * k, P.p ^ 2; -(P.p ^ 2 * m), 3 * k] := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    simp [gS, Matrix.adjugate_fin_two]
  set a := (γ : SL(2, O)) 0 0
  set b := (γ : SL(2, O)) 0 1
  set c := (γ : SL(2, O)) 1 0
  set d := (γ : SL(2, O)) 1 1
  have h10 : ((P.gS hkm)⁻¹ * (γ : SL(2, O)) * P.gS hkm) 1 0 =
      P.p ^ 2 * (-(P.p ^ 2 * m * c) - 3 * k * m * a - P.p ^ 2 * m ^ 2 * b + 3 * k * m * d) + c := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv]
    simp [gS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, a, b, c, d]
    linear_combination c * hkm
  rw [mem_levelSqGroup, mem_levelSqGroup, conjLevel_coe, h10, dvd_add_right (dvd_mul_right _ _)]

theorem complexCharacter_conjLevel_gS (hk : P.p ^ 2 ∣ 3 * k - 1) (γ : levelThree) :
    complexCharacter (conjLevel (P.gS hkm) γ) = complexCharacter γ := by
  have hg : P.gS hkm = sO * ((P.gammaS hkm : levelThree) : SL(2, O))⁻¹ := by
    rw [← P.gS_mul_gammaS hkm]
    group
  have hc : conjLevel (P.gS hkm) γ = P.gammaS hkm * conjLevel sO γ * (P.gammaS hkm)⁻¹ := by
    apply Subtype.ext
    simp only [conjLevel_coe, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hg]
    group
  rw [hc, map_mul, map_mul, map_inv, P.gammaS_character hkm hk, inv_one, one_mul, mul_one]
  exact complexCharacter_conjLevel_rational ModularGroup.S γ

end SData

section RationalS

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
  (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
  {k m : O} (hkm : P.p ^ 4 * m + 9 * k ^ 2 = 1)
include hΘ hΘr hkm

/-- **`G_Θ ∘ S = G_Θ ∘ γ₀`.** -/
theorem fracSum_S (w : HyperbolicSpace) :
    P.fracSum Θ (integralComplexMatrix sO • w) = P.fracSum Θ (complexMatrix (P.gammaS hkm) • w) := by
  have hS : ∀ y, Θ (integralComplexMatrix sO • y) = Θ y := hΘr ModularGroup.S
  have key : ∀ t : O, Θ (P.fracShift t • integralComplexMatrix sO • w) =
      complexCharacter (P.deltaS hkm t) * Θ (P.fracShift t • complexMatrix (P.gammaS hkm) • w) := by
    intro t
    rw [← mul_smul, P.fracShift_mul_S hkm, mul_smul, hS, mul_smul, hΘ, mul_smul]
  unfold fracSum fracCorrelation
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [key, key]
  linear_combination (Θ (P.fracShift (P.lift x) • complexMatrix (P.gammaS hkm) • w) *
    Θ (P.fracShift (-P.lift x) • complexMatrix (P.gammaS hkm) • w)) * P.deltaS_character_mul hkm (P.lift x)

theorem fracSum_gS (w : HyperbolicSpace) :
    P.fracSum Θ (integralComplexMatrix (P.gS hkm) • w) = P.fracSum Θ w := by
  have hg : P.gS hkm = sO * ((P.gammaS hkm : levelThree) : SL(2, O))⁻¹ := by
    rw [← P.gS_mul_gammaS hkm]
    group
  rw [hg, map_mul, mul_smul, P.fracSum_S Θ hΘ hΘr hkm, complexMatrix_eq, ← mul_smul, ← map_mul, mul_inv_cancel,
    map_one, one_smul]

omit hkm in
theorem fracTrace_S (w : HyperbolicSpace) :
    P.fracTrace Θ (integralComplexMatrix sO • w) = P.fracTrace Θ w := by
  obtain ⟨k, m, hkm, hk⟩ := P.exists_sData
  have hw : integralComplexMatrix sO • w = integralComplexMatrix (P.gS hkm) • (complexMatrix (P.gammaS hkm) • w) := by
    rw [← P.gS_mul_gammaS hkm, map_mul, mul_smul]
    rfl
  rw [hw, P.fracTrace_conj Θ hΘ (P.gS hkm) (P.conjLevel_mem_iff_gS hkm) (P.complexCharacter_conjLevel_gS hkm hk) 1
    (fun y => by rw [one_mul]; exact P.fracSum_gS Θ hΘ hΘr hkm y), one_mul, P.fracTrace_automorphy Θ hΘ,
    P.gammaS_character hkm hk, one_pow, one_mul]

omit hkm in
/-- **The fractional trace is invariant under `SL₂(ℤ)`.** -/
theorem fracTrace_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    P.fracTrace Θ (integralComplexMatrix (rationalEmbedding r) • w) = P.fracTrace Θ w := by
  have hr : r ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top r
  induction hr using Subgroup.closure_induction generalizing w with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact P.fracTrace_S Θ hΘ hΘr w
    · rw [show rationalEmbedding ModularGroup.T = tPowO 1 by rw [tPowO, zpow_one]]
      exact P.fracTrace_T Θ hΘ hΘr w
  | one => rw [map_one, map_one, one_smul]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, mul_smul, hx, hy]
  | inv x _ hx =>
    rw [← hx (integralComplexMatrix (rationalEmbedding x⁻¹) • w), ← mul_smul, ← map_mul, ← map_mul, mul_inv_cancel,
      map_one, map_one, one_smul]

end RationalS

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
