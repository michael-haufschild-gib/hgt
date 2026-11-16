import GaloisForLFunctions.OrderSixMetaplecticTheory.TheOrderSixFamilyIsOrthogonalToTheUntwistedSquare

/-!
# The Hecke-at-four correlation has the square multiplier

The 2-adic analogue of STCC's Hecke correlations. With `A = diag(√2, 1/√2)` (`z ↦ 2z`, `v ↦ 2v`) and any
function `Θ` of multiplier `κ` on `Γ(3)`, the correlation `F_Θ(w) = Θ(Aw) Θ(A⁻¹w)` transforms under

`Γ_A = Γ(3) ∩ {2 ∣ b, 2 ∣ c}`   (`fourCorrelationGroup`)

with the multiplier `κ²` of `Θ²` (`heckeFourCorrelation_automorphy`): for `γ = [[a, 2b], [2c, d]]` the conjugates
`AγA⁻¹ = [[a, 4b], [c, d]]` and `A⁻¹γA = [[a, b], [4c, d]]` lie in `Γ(3)`, and the cubic symbols of their lower-left
entries multiply to `(c/a)₃(4c/a)₃ = (2c/a)₃² = κ(γ)²`: the 2-adic nebentypus `(2/a)₃^{∓1}` of the two dilates cancels.
-/

noncomputable section

open scoped Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota

/-- `√2` as a complex number. -/
abbrev sqrtTwo : ℂ := (Real.sqrt 2 : ℂ)

theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem sqrtTwo_ne_zero : sqrtTwo ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'

theorem sqrtTwo_inv : sqrtTwo⁻¹ = sqrtTwo / 2 := by
  field_simp
  exact sqrtTwo_sq.symm

/-- `A = diag(√2, 1/√2)`. -/
def fourDilation : SL(2, ℂ) := complexDiagonal sqrtTwo sqrtTwo_ne_zero

/-- `A⁻¹ = diag(1/√2, √2)`. -/
def fourContraction : SL(2, ℂ) := complexDiagonal sqrtTwo⁻¹ (inv_ne_zero sqrtTwo_ne_zero)

theorem three_dvd_of_three_dvd_two_mul {x : O} (h : (3 : O) ∣ 2 * x) : (3 : O) ∣ x := by
  have hc : IsCoprime (3 : O) 2 := ⟨1, -1, by norm_num⟩
  exact hc.dvd_of_dvd_mul_left h

/-- The level-three matrix `[[a, 2b], [2c, d]]` of `Γ_A`. -/
structure FourCorrelationEntries where
  a : O
  b : O
  c : O
  d : O
  det : a * d - 4 * (b * c) = 1
  ha : (3 : O) ∣ a - 1
  hb : (3 : O) ∣ b
  hc : (3 : O) ∣ c
  hd : (3 : O) ∣ d - 1

namespace FourCorrelationEntries

variable (e : FourCorrelationEntries)

/-- `γ = [[a, 2b], [2c, d]]`. -/
def mat : levelThree :=
  ⟨⟨!![e.a, 2 * e.b; 2 * e.c, e.d], by rw [Matrix.det_fin_two_of]; linear_combination e.det⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using e.ha
      · simpa using e.hb.mul_left 2
      · simpa using e.hc.mul_left 2
      · simpa using e.hd)⟩

/-- `AγA⁻¹ = [[a, 4b], [c, d]]`. -/
def up : levelThree :=
  ⟨⟨!![e.a, 4 * e.b; e.c, e.d], by rw [Matrix.det_fin_two_of]; linear_combination e.det⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using e.ha
      · simpa using e.hb.mul_left 4
      · simpa using e.hc
      · simpa using e.hd)⟩

/-- `A⁻¹γA = [[a, b], [4c, d]]`. -/
def down : levelThree :=
  ⟨⟨!![e.a, e.b; 4 * e.c, e.d], by rw [Matrix.det_fin_two_of]; linear_combination e.det⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using e.ha
      · simpa using e.hb
      · simpa using e.hc.mul_left 4
      · simpa using e.hd)⟩

theorem fourDilation_mul : fourDilation * complexMatrix e.mat = complexMatrix e.up * fourDilation := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourDilation, complexDiagonal, complexMatrix_apply, mat, up, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  all_goals (try simp only [sqrtTwo_inv]); ring

theorem fourContraction_mul : fourContraction * complexMatrix e.mat = complexMatrix e.down * fourContraction := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourContraction, complexDiagonal, complexMatrix_apply, mat, down, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  all_goals (try simp only [sqrtTwo_inv]); ring

/-- The 2-adic nebentypus cancels: `κ(AγA⁻¹) κ(A⁻¹γA) = κ(γ)²`. -/
theorem character_up_mul_down :
    complexCharacter e.up * complexCharacter e.down = complexCharacter e.mat ^ 2 := by
  change ringComplex (symbol e.c e.a) * ringComplex (symbol (4 * e.c) e.a) =
    ringComplex (symbol (2 * e.c) e.a) ^ 2
  rw [← map_mul, ← map_pow, ← symbol_mul_numerator, pow_two, ← symbol_mul_numerator]
  congr 2
  ring

end FourCorrelationEntries

/-- `Γ_A = Γ(3) ∩ {2 ∣ b, 2 ∣ c}`. -/
def fourCorrelationGroup : Subgroup levelThree where
  carrier := {γ | (2 : O) ∣ (γ : SL(2, O)) 0 1 ∧ (2 : O) ∣ (γ : SL(2, O)) 1 0}
  one_mem' := by simp
  mul_mem' := by
    rintro γ δ ⟨hb, hc⟩ ⟨hb', hc'⟩
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    exact ⟨dvd_add (hb'.mul_left _) (hb.mul_right _), dvd_add (hc.mul_right _) (hc'.mul_left _)⟩
  inv_mem' := by
    rintro γ ⟨hb, hc⟩
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact ⟨hb.neg_right, hc.neg_right⟩

/-- Every element of `Γ_A` has the form `[[a, 2b], [2c, d]]`. -/
theorem exists_entries_of_mem (γ : levelThree) (hγ : γ ∈ fourCorrelationGroup) :
    ∃ e : FourCorrelationEntries, e.mat = γ := by
  obtain ⟨b, hb⟩ := hγ.1
  obtain ⟨c, hc⟩ := hγ.2
  have hdet : (γ : SL(2, O)) 0 0 * (γ : SL(2, O)) 1 1 - (γ : SL(2, O)) 0 1 * (γ : SL(2, O)) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact (γ : SL(2, O)).det_coe
  have h01 := levelThree_entry γ 0 1
  have h10 := levelThree_entry γ 1 0
  simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_false, sub_zero] at h01 h10
  rw [hb] at h01
  rw [hc] at h10
  refine ⟨⟨(γ : SL(2, O)) 0 0, b, c, (γ : SL(2, O)) 1 1, ?_, by simpa using levelThree_entry γ 0 0,
    three_dvd_of_three_dvd_two_mul h01, three_dvd_of_three_dvd_two_mul h10,
    by simpa using levelThree_entry γ 1 1⟩, ?_⟩
  · rw [hb, hc] at hdet
    linear_combination hdet
  · apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [FourCorrelationEntries.mat, hb, hc]

/-- The Hecke-at-four correlation `F_Θ(w) = Θ(Aw) Θ(A⁻¹w)`. -/
def heckeFourCorrelation (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  Θ (fourDilation • w) * Θ (fourContraction • w)

/-- **The Hecke-at-four correlation has the multiplier `κ²` on `Γ_A`.** -/
theorem heckeFourCorrelation_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (γ : levelThree) (hγ : γ ∈ fourCorrelationGroup) (w : HyperbolicSpace) :
    heckeFourCorrelation Θ (complexMatrix γ • w) = complexCharacter γ ^ 2 * heckeFourCorrelation Θ w := by
  obtain ⟨e, rfl⟩ := exists_entries_of_mem γ hγ
  unfold heckeFourCorrelation
  rw [← mul_smul, e.fourDilation_mul, mul_smul, hΘ, ← mul_smul, e.fourContraction_mul, mul_smul, hΘ,
    ← e.character_up_mul_down]
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
