import GaloisForLFunctions.OrderSixMetaplecticTheory.TheDilateCorrelationAtEveryPrimaryPrimeHasADoublePole

/-!
# Opposite fractional translations have the square multiplier

For a primary prime `q` and `t ∈ O`, let `T_t = [[1, 3t/q], [0, 1]]` (a translation by `3t/q`, not in `SL₂(O)`). For
`Θ` of multiplier `κ` on `Γ(3)`, the sum of opposite fractional translations

`G_Θ(w) = Σ_{t ∈ O/q} Θ(T_tw) Θ(T_{−t}w)`   (`PrimaryPrime.fracSum`)

has the multiplier `κ²` on `Γ(3) ∩ Γ₀(q²)` (`fracSum_automorphy`): for `δ = [[a, b], [c, d]]` with `q² ∣ c`,
`T_tδ = M_tT_{td²}` with `M_t ∈ Γ(3)`, `κ(M_t)κ(M_{−t}) = (c/(a² − 9t²c²/q²))₃ = κ(δ)²` (the two denominators multiply
to `a²` modulo `9c`), and `t ↦ td²` permutes `O/q` (`ad ≡ 1 mod q`). Its trace to `Γ(3)` is automorphic
(`fracTrace_automorphy`). At the cusp `∞` the sum over `t` projects `θ²` onto the frequencies divisible by `q`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `T_t = [[1, 3t/q], [0, 1]]`. -/
def fracShift (t : O) : SL(2, ℂ) := complexTranslation (3 * ringComplex t / ringComplex P.p)

/-- `F_t(w) = Θ(T_tw) Θ(T_{−t}w)`. -/
def fracCorrelation (Θ : HyperbolicSpace → ℂ) (t : O) (w : HyperbolicSpace) : ℂ :=
  Θ (P.fracShift t • w) * Θ (P.fracShift (-t) • w)

/-- `G_Θ = Σ_{t ∈ O/q} F_t`. -/
def fracSum (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑ x : P.Res, P.fracCorrelation Θ (P.lift x) w

/-- `Γ(3) ∩ Γ₀(q²)`. -/
def levelSqGroup : Subgroup levelThree where
  carrier := {γ | P.p ^ 2 ∣ (γ : SL(2, O)) 1 0}
  one_mem' := by simp
  mul_mem' := by
    rintro γ δ hc hc'
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    exact dvd_add (hc.mul_right _) (hc'.mul_left _)
  inv_mem' := by
    rintro γ hc
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact hc.neg_right

/-! ### The conjugated matrices -/

/-- `M_t = T_t δ T_{−td²}` for `δ = [[a, b], [q²c₂, d]]`. -/
def fracConj (a b c₂ d t : O) (hdet : a * d - b * (P.p ^ 2 * c₂) = 1) (ha : (3 : O) ∣ a - 1)
    (hb : (3 : O) ∣ b) (hc : (3 : O) ∣ P.p ^ 2 * c₂) (hd : (3 : O) ∣ d - 1) : levelThree :=
  ⟨⟨!![a + 3 * t * P.p * c₂, b - 3 * t * d * b * P.p * c₂ - 9 * t ^ 2 * d ^ 2 * c₂;
      P.p ^ 2 * c₂, d - 3 * t * d ^ 2 * P.p * c₂], by
      rw [Matrix.det_fin_two_of]; linear_combination (1 - 3 * t * d * P.p * c₂) * hdet⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · obtain ⟨k, hk⟩ := ha
        exact ⟨k + t * P.p * c₂, by simp; linear_combination hk⟩
      · obtain ⟨k, hk⟩ := hb
        exact ⟨k - 3 * t * d * k * P.p * c₂ - 3 * t ^ 2 * d ^ 2 * c₂, by simp; linear_combination (1 - 3 * t * d * P.p * c₂) * hk⟩
      · simpa using hc
      · obtain ⟨k, hk⟩ := hd
        exact ⟨k - t * d ^ 2 * P.p * c₂, by simp; linear_combination hk⟩)⟩

end PrimaryPrime


namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem fracShift_apply (t : O) :
    ((P.fracShift t : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 3 * ringComplex t / ringComplex P.p; 0, 1] := rfl

/-- `T_tδ = M_tT_{td²}`. -/
theorem fracShift_mul (δ : levelThree) (c₂ : O) (hc : (δ : SL(2, O)) 1 0 = P.p ^ 2 * c₂) (t : O)
    (hdet : (δ : SL(2, O)) 0 0 * (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 1 * (P.p ^ 2 * c₂) = 1)
    (ha : (3 : O) ∣ (δ : SL(2, O)) 0 0 - 1) (hb : (3 : O) ∣ (δ : SL(2, O)) 0 1)
    (hc3 : (3 : O) ∣ P.p ^ 2 * c₂) (hd : (3 : O) ∣ (δ : SL(2, O)) 1 1 - 1) :
    P.fracShift t * complexMatrix δ =
      complexMatrix (P.fracConj ((δ : SL(2, O)) 0 0) ((δ : SL(2, O)) 0 1) c₂ ((δ : SL(2, O)) 1 1) t hdet ha hb hc3 hd) *
        P.fracShift (t * (δ : SL(2, O)) 1 1 ^ 2) := by
  have hP := P.ringComplex_ne_zero
  have hdet' := congrArg ringComplex hdet
  simp only [map_sub, map_mul, map_pow, map_one] at hdet'
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fracShift, complexTranslation, complexMatrix_apply, fracConj, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, hc, map_ofNat]
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination (3 * ringComplex t * ringComplex ((δ : SL(2, O)) 1 1)) * hdet' |
    linear_combination (-(3 * ringComplex t * ringComplex ((δ : SL(2, O)) 1 1))) * hdet')

theorem fracConj_character (a b c₂ d t : O) (hdet : a * d - b * (P.p ^ 2 * c₂) = 1) (ha : (3 : O) ∣ a - 1)
    (hb : (3 : O) ∣ b) (hc : (3 : O) ∣ P.p ^ 2 * c₂) (hd : (3 : O) ∣ d - 1) :
    complexCharacter (P.fracConj a b c₂ d t hdet ha hb hc hd) =
      ringComplex (symbol (P.p ^ 2 * c₂) (a + 3 * t * P.p * c₂)) := rfl

/-- The fractional shifts cancel their phases: `κ(M_t)κ(M_{−t}) = κ(δ)²`. -/
theorem fracConj_character_mul (a b c₂ d t : O) (hdet : a * d - b * (P.p ^ 2 * c₂) = 1) (ha : (3 : O) ∣ a - 1)
    (hb : (3 : O) ∣ b) (hc : (3 : O) ∣ P.p ^ 2 * c₂) (hd : (3 : O) ∣ d - 1) :
    complexCharacter (P.fracConj a b c₂ d t hdet ha hb hc hd) *
        complexCharacter (P.fracConj a b c₂ d (-t) hdet ha hb hc hd) =
      ringComplex (symbol (P.p ^ 2 * c₂) a) ^ 2 := by
  rw [fracConj_character, fracConj_character, ← map_mul, ← symbol_mul_denominator, ← map_pow,
    pow_two (symbol (P.p ^ 2 * c₂) a), ← symbol_mul_denominator]
  have hla : lambda ^ 2 ∣ a - 1 := (lambda_sq_dvd_three).trans ha
  have h3 : lambda ^ 2 ∣ 3 * t * P.p * c₂ := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left lambda_sq_dvd_three _) _) _
  have hA : lambda ^ 2 ∣ a + 3 * t * P.p * c₂ - 1 := by convert dvd_add hla h3 using 1; ring
  have hB : lambda ^ 2 ∣ a + 3 * -t * P.p * c₂ - 1 := by convert dvd_sub hla h3 using 1; ring
  have hAB : lambda ^ 2 ∣ (a + 3 * t * P.p * c₂) * (a + 3 * -t * P.p * c₂) - 1 := by
    convert dvd_add (dvd_mul_of_dvd_left hA (a + 3 * -t * P.p * c₂)) hB using 1; ring
  have haa : lambda ^ 2 ∣ a * a - 1 := by convert dvd_mul_of_dvd_left hla (a + 1) using 1; ring
  have h9 : (9 : O) ∣ (a + 3 * t * P.p * c₂) * (a + 3 * -t * P.p * c₂) - a * a :=
    ⟨-(t * P.p * c₂) ^ 2, by ring⟩
  have hx : P.p ^ 2 * c₂ ∣ (a + 3 * t * P.p * c₂) * (a + 3 * -t * P.p * c₂) - a * a :=
    ⟨-(9 * t ^ 2 * c₂), by ring⟩
  rw [symbol_denominator_congr _ _ _ hAB haa h9 hx]

/-- `F_t` depends on `t` modulo `q`. -/
theorem fracCorrelation_add (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (t s : O) (w : HyperbolicSpace) :
    P.fracCorrelation Θ (t + P.p * s) w = P.fracCorrelation Θ t w := by
  have hP := P.ringComplex_ne_zero
  have hsh : ∀ u r : O, P.fracShift (u + P.p * r) = complexMatrix (transThree r) * P.fracShift u := by
    intro u r
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [fracShift, complexTranslation, complexMatrix_apply, transThree, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
    field_simp
  unfold fracCorrelation
  rw [hsh, show -(t + P.p * s) = -t + P.p * (-s) by ring, hsh, mul_smul, mul_smul, hΘ, hΘ,
    complexCharacter_transThree, complexCharacter_transThree, one_mul, one_mul]

theorem fracCorrelation_lift (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (t : O) (w : HyperbolicSpace) :
    P.fracCorrelation Θ (P.lift (P.res t)) w = P.fracCorrelation Θ t w := by
  have h : P.res (P.lift (P.res t) - t) = 0 := by rw [map_sub, res_lift, sub_self]
  obtain ⟨s, hs⟩ := (P.res_eq_zero_iff _).mp h
  rw [show P.lift (P.res t) = t + P.p * s by linear_combination hs, P.fracCorrelation_add Θ hΘ]

/-- **The sum of opposite fractional translations has the multiplier `κ²` on `Γ(3) ∩ Γ₀(q²)`.** -/
theorem fracSum_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (δ : levelThree) (hδ : δ ∈ P.levelSqGroup) (w : HyperbolicSpace) :
    P.fracSum Θ (complexMatrix δ • w) = complexCharacter δ ^ 2 * P.fracSum Θ w := by
  obtain ⟨c₂, hc⟩ := hδ
  have hdet : (δ : SL(2, O)) 0 0 * (δ : SL(2, O)) 1 1 - (δ : SL(2, O)) 0 1 * (P.p ^ 2 * c₂) = 1 := by
    rw [← hc, ← Matrix.det_fin_two]
    exact (δ : SL(2, O)).det_coe
  have ha : (3 : O) ∣ (δ : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry δ 0 0
  have hb : (3 : O) ∣ (δ : SL(2, O)) 0 1 := by simpa using levelThree_entry δ 0 1
  have hc3 : (3 : O) ∣ P.p ^ 2 * c₂ := by rw [← hc]; simpa using levelThree_entry δ 1 0
  have hd : (3 : O) ∣ (δ : SL(2, O)) 1 1 - 1 := by simpa using levelThree_entry δ 1 1
  set d := (δ : SL(2, O)) 1 1
  have hκ : complexCharacter δ = ringComplex (symbol (P.p ^ 2 * c₂) ((δ : SL(2, O)) 0 0)) := by
    rw [complexCharacter_eq_symbol, hc]
  have hterm : ∀ t : O, P.fracCorrelation Θ t (complexMatrix δ • w) =
      complexCharacter δ ^ 2 * P.fracCorrelation Θ (t * d ^ 2) w := by
    intro t
    unfold fracCorrelation
    rw [← mul_smul, P.fracShift_mul δ c₂ hc t hdet ha hb hc3 hd, mul_smul, hΘ, ← mul_smul,
      P.fracShift_mul δ c₂ hc (-t) hdet ha hb hc3 hd, mul_smul, hΘ, hκ,
      ← P.fracConj_character_mul _ _ c₂ _ t hdet ha hb hc3 hd, show -t * d ^ 2 = -(t * d ^ 2) by ring]
    ring
  have hd0 : P.res d ≠ 0 := by
    intro h0
    have h := congrArg P.res hdet
    rw [map_sub, map_mul, map_mul, h0, mul_zero, map_mul, map_pow, P.res_p] at h
    simp at h
  unfold fracSum
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  have hbij : Function.Bijective (fun x : P.Res => x * P.res d ^ 2) :=
    mulRight_bijective₀ _ (pow_ne_zero 2 hd0)
  rw [← hbij.sum_comp (fun y => P.fracCorrelation Θ (P.lift y) w)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show x * P.res d ^ 2 = P.res (P.lift x * d ^ 2) by rw [map_mul, map_pow, res_lift],
    P.fracCorrelation_lift Θ hΘ]

/-! ### The trace -/

theorem levelSqGroup_finiteIndex : P.levelSqGroup.FiniteIndex := by
  have hq : P.p ^ 2 ≠ 0 := pow_ne_zero 2 P.ne_zero
  obtain ⟨hL, -⟩ := integralDiagonal_finite_covers (P.p ^ 2) hq
  haveI : ((integralDiagonalLeft (P.p ^ 2)).range.subgroupOf levelThree).FiniteIndex := inferInstance
  refine Subgroup.finiteIndex_of_le (H := (integralDiagonalLeft (P.p ^ 2)).range.subgroupOf levelThree) fun γ hγ => ?_
  rw [Subgroup.mem_subgroupOf] at hγ
  obtain ⟨x, hx⟩ := hγ
  have ex := integralDiagonal_entries (P.p ^ 2) x
  change x.1.1 = (γ : SL(2, O)) at hx
  show P.p ^ 2 ∣ (γ : SL(2, O)) 1 0
  rw [← hx, ex.2.2.1]
  exact dvd_mul_left _ _

instance (P : PrimaryPrime) : P.levelSqGroup.FiniteIndex := P.levelSqGroup_finiteIndex

noncomputable instance (P : PrimaryPrime) : Fintype (levelThree ⧸ P.levelSqGroup) :=
  Subgroup.fintypeQuotientOfFiniteIndex

/-- The trace `Tr G_Θ(w) = Σ_{γ(Γ(3) ∩ Γ₀(q²))} κ(γ)² G_Θ(γ⁻¹w)`. -/
def fracTrace (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  cosetTrace complexMatrix P.levelSqGroup kubotaSquare (P.fracSum Θ) w

/-- **The trace of the opposite fractional translations has the multiplier `κ²` on `Γ(3)`.** -/
theorem fracTrace_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (M : levelThree) (w : HyperbolicSpace) :
    P.fracTrace Θ (complexMatrix M • w) = complexCharacter M ^ 2 * P.fracTrace Θ w :=
  cosetTrace_smul (ρ := complexMatrix) (H := P.levelSqGroup) (χ := kubotaSquare)
    (F := P.fracSum Θ) (fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.fracSum_automorphy Θ hΘ δ hδ x) M w

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
