import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFamilyLayerIsTheUnramifiedDilateCorrelationAtNine

/-!
# Opposite translations by thirds have the square multiplier

The 3-adic character `ξ_{ω²λ²} = (9/·)₃` of the family layer is a function of the frequency modulo `9`; additive
characters modulo `9` are translations of `θ` by `β/3`, `β ∈ O`. On

`Γ_Z = {[[a, b], [c, d]] ∈ Γ(3) : 27 ∣ c, 9 ∣ d − a}`   (`thirdsGroup`)

a translation by `β/3` conjugates into `Γ(3)` without moving the translate:
`τ_{β/3} δ = M_β τ_{β/3}`, `M_β = [[a + 9βc₂, b + 3βe − 3β²c₂], [27c₂, d − 9βc₂]]` (`c = 27c₂`, `d − a = 9e`;
`thirdShift_mul`). The Kubota symbol `(c/a)₃` sees `a` modulo `9c`, and
`(a + 9βc₂)(a − 9βc₂) ≡ a²` modulo `9` and `c`, so `κ(M_β)κ(M_{−β}) = κ(δ)²` (`thirdConj_character_mul`): the opposite
translations `θ(w + β/3)θ(w − β/3)` have the multiplier `κ²` on `Γ_Z` (`thirdCorrelation_automorphy`). This is the
3-adic analogue of the fractional translations at a prime `q` and the first step of the trace that reads the
family layer through `ξ_{ω²λ²}`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- `τ_{β/3}`, translation by `β/3`. -/
def thirdShift (β : O) : SL(2, ℂ) := complexTranslation (ringComplex β / 3)

/-- `θ(w + β/3) θ(w − β/3)`. -/
def thirdCorrelation (Θ : HyperbolicSpace → ℂ) (β : O) (w : HyperbolicSpace) : ℂ :=
  Θ (thirdShift β • w) * Θ (thirdShift (-β) • w)

/-- `Γ_Z = {γ ∈ Γ(3) : 27 ∣ c, 9 ∣ d − a}`. -/
def thirdsGroup : Subgroup levelThree where
  carrier := {γ | (27 : O) ∣ (γ : SL(2, O)) 1 0 ∧ (9 : O) ∣ (γ : SL(2, O)) 1 1 - (γ : SL(2, O)) 0 0}
  one_mem' := by simp
  mul_mem' := by
    rintro γ δ ⟨hc, hd⟩ ⟨hc', hd'⟩
    have hb : (3 : O) ∣ (γ : SL(2, O)) 0 1 := by simpa using levelThree_entry γ 0 1
    have hb' : (3 : O) ∣ (δ : SL(2, O)) 0 1 := by simpa using levelThree_entry δ 0 1
    refine ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (hc.mul_right _) (hc'.mul_left _)
    · simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      obtain ⟨x, hx⟩ := hc
      obtain ⟨y, hy⟩ := hc'
      obtain ⟨u, hu⟩ := hd
      obtain ⟨v, hv⟩ := hd'
      obtain ⟨k, hk⟩ := hb
      obtain ⟨l, hl⟩ := hb'
      refine ⟨9 * x * l + (γ : SL(2, O)) 1 1 * v + (δ : SL(2, O)) 0 0 * u - 9 * k * y, ?_⟩
      rw [hx, hk, hl, hy]
      linear_combination (γ : SL(2, O)) 1 1 * hv + (δ : SL(2, O)) 0 0 * hu
  inv_mem' := by
    rintro γ ⟨hc, hd⟩
    refine ⟨?_, ?_⟩
    · simp only [Subgroup.coe_inv, Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.SpecialLinearGroup.coe_mk,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hc.neg_right
    · simp only [Subgroup.coe_inv, Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.SpecialLinearGroup.coe_mk,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      obtain ⟨u, hu⟩ := hd
      exact ⟨-u, by linear_combination -hu⟩

/-- `M_β = τ_{β/3} δ τ_{−β/3}` for `δ = [[a, b], [27c₂, d]]`, `d − a = 9e`. -/
def thirdConj (a b c₂ d e β : O) (hdet : a * d - b * (27 * c₂) = 1) (hde : d - a = 9 * e)
    (ha : (3 : O) ∣ a - 1) (hb : (3 : O) ∣ b) : levelThree :=
  ⟨⟨!![a + 9 * β * c₂, b + 3 * β * e - 3 * β ^ 2 * c₂; 27 * c₂, d - 9 * β * c₂], by
      rw [Matrix.det_fin_two_of]; linear_combination hdet + 9 * β * c₂ * hde⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · obtain ⟨k, hk⟩ := ha
        exact ⟨k + 3 * β * c₂, by simp; linear_combination hk⟩
      · obtain ⟨k, hk⟩ := hb
        exact ⟨k + β * e - β ^ 2 * c₂, by simp; linear_combination hk⟩
      · exact ⟨9 * c₂, by simp; ring⟩
      · obtain ⟨k, hk⟩ := ha
        exact ⟨k + 3 * e - 3 * β * c₂, by simp; linear_combination hk + hde⟩)⟩

theorem thirdConj_character (a b c₂ d e β : O) (hdet : a * d - b * (27 * c₂) = 1) (hde : d - a = 9 * e)
    (ha : (3 : O) ∣ a - 1) (hb : (3 : O) ∣ b) :
    complexCharacter (thirdConj a b c₂ d e β hdet hde ha hb) = ringComplex (symbol (27 * c₂) (a + 9 * β * c₂)) :=
  rfl

/-- **The two translates cancel their phases:** `κ(M_β)κ(M_{−β}) = (c/a)₃²`. -/
theorem thirdConj_character_mul (a b c₂ d e β : O) (hdet : a * d - b * (27 * c₂) = 1) (hde : d - a = 9 * e)
    (ha : (3 : O) ∣ a - 1) (hb : (3 : O) ∣ b) :
    complexCharacter (thirdConj a b c₂ d e β hdet hde ha hb) *
        complexCharacter (thirdConj a b c₂ d e (-β) hdet hde ha hb) =
      ringComplex (symbol (27 * c₂) a) ^ 2 := by
  rw [thirdConj_character, thirdConj_character, ← map_mul, ← symbol_mul_denominator, ← map_pow,
    pow_two (symbol (27 * c₂) a), ← symbol_mul_denominator]
  have hla : lambda ^ 2 ∣ a - 1 := lambda_sq_dvd_three.trans ha
  have h9 : lambda ^ 2 ∣ 9 * β * c₂ :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (lambda_sq_dvd_three.trans ⟨3, by norm_num⟩) _) _
  have hA : lambda ^ 2 ∣ a + 9 * β * c₂ - 1 := by convert dvd_add hla h9 using 1; ring
  have hB : lambda ^ 2 ∣ a + 9 * -β * c₂ - 1 := by convert dvd_sub hla h9 using 1; ring
  have hAB : lambda ^ 2 ∣ (a + 9 * β * c₂) * (a + 9 * -β * c₂) - 1 := by
    convert dvd_add (dvd_mul_of_dvd_left hA (a + 9 * -β * c₂)) hB using 1; ring
  have haa : lambda ^ 2 ∣ a * a - 1 := by convert dvd_mul_of_dvd_left hla (a + 1) using 1; ring
  have hn : (9 : O) ∣ (a + 9 * β * c₂) * (a + 9 * -β * c₂) - a * a := ⟨-(9 * β ^ 2 * c₂ ^ 2), by ring⟩
  have hx : 27 * c₂ ∣ (a + 9 * β * c₂) * (a + 9 * -β * c₂) - a * a := ⟨-(3 * β ^ 2 * c₂), by ring⟩
  rw [symbol_denominator_congr _ _ _ hAB haa hn hx]

/-- `τ_{β/3} δ = M_β τ_{β/3}`. -/
theorem thirdShift_mul (δ : levelThree) (c₂ e : O) (hc : (δ : SL(2, O)) 1 0 = 27 * c₂)
    (hde : (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 0 = 9 * e) (β : O)
    (hdet : (δ : SL(2, O)) 0 0 * (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 1 * (27 * c₂) = 1)
    (ha : (3 : O) ∣ (δ : SL(2, O)) 0 0 - 1) (hb : (3 : O) ∣ (δ : SL(2, O)) 0 1) :
    thirdShift β * complexMatrix δ =
      complexMatrix (thirdConj ((δ : SL(2, O)) 0 0) ((δ : SL(2, O)) 0 1) c₂ ((δ : SL(2, O)) 1 1) e β hdet hde ha hb) *
        thirdShift β := by
  have hde' := congrArg ringComplex hde
  simp only [map_sub, map_mul, map_ofNat] at hde'
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [thirdShift, complexTranslation, complexMatrix_apply, thirdConj, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, hc, map_ofNat]
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination (3 * ringComplex β) * hde' |
    linear_combination (-(3 * ringComplex β)) * hde' | linear_combination (4 * ringComplex β) * hde' |
    linear_combination (-(4 * ringComplex β)) * hde' | linear_combination ringComplex β * hde')

/-- **Opposite translations by thirds have the multiplier `κ²` on `Γ_Z`.** -/
theorem thirdCorrelation_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (δ : levelThree) (hδ : δ ∈ thirdsGroup) (β : O) (w : HyperbolicSpace) :
    thirdCorrelation Θ β (complexMatrix δ • w) = complexCharacter δ ^ 2 * thirdCorrelation Θ β w := by
  obtain ⟨⟨c₂, hc⟩, ⟨e, hde⟩⟩ := hδ
  have hdet : (δ : SL(2, O)) 0 0 * (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 1 * (27 * c₂) = 1 := by
    rw [← hc, ← Matrix.det_fin_two]
    exact (δ : SL(2, O)).det_coe
  have ha : (3 : O) ∣ (δ : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry δ 0 0
  have hb : (3 : O) ∣ (δ : SL(2, O)) 0 1 := by simpa using levelThree_entry δ 0 1
  have hκ : complexCharacter δ = ringComplex (symbol (27 * c₂) ((δ : SL(2, O)) 0 0)) := by
    rw [complexCharacter_eq_symbol, hc]
  unfold thirdCorrelation
  rw [← mul_smul, thirdShift_mul δ c₂ e hc hde β hdet ha hb, mul_smul, hΘ, ← mul_smul,
    thirdShift_mul δ c₂ e hc hde (-β) hdet ha hb, mul_smul, hΘ, hκ,
    ← thirdConj_character_mul _ _ c₂ _ e β hdet hde ha hb]
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
