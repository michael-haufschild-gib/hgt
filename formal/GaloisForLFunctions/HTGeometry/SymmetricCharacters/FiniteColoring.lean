import GaloisForLFunctions.Core
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.NNReal.Basic
import Mathlib.GroupTheory.Perm.Option

/-!
# Symmetric-group characters from independent colors

A permutation preserves an independently colored word precisely when every cycle is
monochromatic. Its weighted fixed-word sum is positive definite: each fixed-word kernel is
a pullback of the identity matrix. This construction separates character restriction from
deletion consistency of probability laws on permutations.
-/

noncomputable section
open scoped BigOperators ComplexOrder Classical

namespace GaloisForLFunctions.SymmetricCharacters

variable {X A J : Type*} [Fintype X] [Fintype A]

/-- Product mass of a word under independent color weights. -/
def wordWeight (w : A → NNReal) (x : X → A) : ℝ := ∏ i, (w (x i) : ℝ)

/-- Weighted probability that a permutation preserves every color. -/
def coloringCharacter (w : A → NNReal) (σ : Equiv.Perm X) : ℝ :=
  ∑ x : X → A, if x ∘ σ = x then wordWeight w x else 0

omit [Fintype A] in
theorem wordWeight_nonneg (w : A → NNReal) (x : X → A) : 0 ≤ wordWeight w x :=
  Finset.prod_nonneg fun _ _ => (w _).coe_nonneg

omit [Fintype A] in
theorem wordWeight_comp (w : A → NNReal) (x : X → A) (σ : Equiv.Perm X) :
    wordWeight w (x ∘ σ) = wordWeight w x :=
  Equiv.prod_comp σ (fun i => (w (x i) : ℝ))

/-- The identity value is the total color mass raised to the number of positions. -/
theorem coloringCharacter_one (w : A → NNReal) :
    coloringCharacter (X := X) w 1 = (∑ a, (w a : ℝ)) ^ Fintype.card X := by
  classical
  simp only [coloringCharacter, Equiv.Perm.coe_one, Function.comp_id, ite_true, wordWeight]
  simpa using (Fintype.prod_sum (fun (_ : X) (a : A) => (w a : ℝ))).symm

omit [Fintype X] [Fintype A] in
private theorem fixed_inv_mul_iff (x : X → A) (σ τ : Equiv.Perm X) :
    x ∘ (σ⁻¹ * τ) = x ↔ x ∘ σ.symm = x ∘ τ.symm := by
  constructor
  · intro h
    funext i
    have hi := congrFun h (τ⁻¹ i)
    simpa using hi
  · intro h
    funext i
    have hi := congrFun h (τ i)
    simpa using hi

/-- Positivity holds at every rank and for every test family, without a spectral assumption. -/
theorem coloringCharacter_posSemidef (w : A → NNReal) (g : J → Equiv.Perm X) :
    Matrix.PosSemidef (fun i j => (coloringCharacter w ((g i)⁻¹ * g j) : ℂ)) := by
  classical
  have h := Matrix.posSemidef_sum Finset.univ
    (fun (x : X → A) _ =>
      ((Matrix.PosSemidef.one : Matrix.PosSemidef (1 : Matrix (X → A) (X → A) ℂ)).submatrix
        (fun j => x ∘ (g j).symm)).smul (Complex.zero_le_real.mpr (wordWeight_nonneg w x)))
  convert h using 1
  ext i j
  simp only [coloringCharacter, Complex.ofReal_sum, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.submatrix_apply, Matrix.one_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  simp only [fixed_inv_mul_iff]
  split_ifs <;> simp

/-- Relabeling positions conjugates the permutation and preserves its character. -/
theorem coloringCharacter_conj (w : A → NNReal) (σ τ : Equiv.Perm X) :
    coloringCharacter w (τ * σ * τ⁻¹) = coloringCharacter w σ := by
  classical
  unfold coloringCharacter
  apply Fintype.sum_equiv (Equiv.arrowCongr τ.symm (Equiv.refl A))
  intro x
  have hweight : wordWeight w ((Equiv.arrowCongr τ.symm (Equiv.refl A)) x) =
      wordWeight w x := wordWeight_comp w x τ
  rw [hweight]
  have hfix : x ∘ (τ * σ * τ⁻¹) = x ↔ (x ∘ τ) ∘ σ = x ∘ τ := by
    constructor
    · intro h
      funext i
      simpa using congrFun h (τ i)
    · intro h
      funext i
      simpa using congrFun h (τ⁻¹ i)
  change (if x ∘ (τ * σ * τ⁻¹) = x then wordWeight w x else 0) =
    (if (x ∘ τ) ∘ σ = x ∘ τ then wordWeight w x else 0)
  simp only [hfix]

variable {Y : Type*} [Fintype Y]

/-- Independent blocks give exact multiplicativity on disjoint permutation supports. -/
theorem coloringCharacter_sumCongr (w : A → NNReal)
    (σ : Equiv.Perm X) (τ : Equiv.Perm Y) :
    coloringCharacter w (Equiv.sumCongr σ τ) =
      coloringCharacter w σ * coloringCharacter w τ := by
  classical
  letI : DecidableEq (X ⊕ Y) := Classical.decEq _
  have hterm (x : X ⊕ Y → A) :
      (if x ∘ Equiv.sumCongr σ τ = x then wordWeight w x else 0) =
      (if (x ∘ Sum.inl) ∘ σ = x ∘ Sum.inl then wordWeight w (x ∘ Sum.inl) else 0) *
      (if (x ∘ Sum.inr) ∘ τ = x ∘ Sum.inr then wordWeight w (x ∘ Sum.inr) else 0) := by
    have hfix : x ∘ Equiv.sumCongr σ τ = x ↔
        (x ∘ Sum.inl) ∘ σ = x ∘ Sum.inl ∧
        (x ∘ Sum.inr) ∘ τ = x ∘ Sum.inr := by
      constructor
      · intro h
        exact ⟨funext (fun i => congrFun h (Sum.inl i)),
          funext (fun i => congrFun h (Sum.inr i))⟩
      · rintro ⟨h₁, h₂⟩
        funext i
        cases i with
        | inl i => exact congrFun h₁ i
        | inr i => exact congrFun h₂ i
    have hw : wordWeight w x =
        wordWeight w (x ∘ Sum.inl) * wordWeight w (x ∘ Sum.inr) :=
      Fintype.prod_sum_type (fun i => (w (x i) : ℝ))
    simp only [hfix, hw]
    split_ifs <;> simp_all
  unfold coloringCharacter
  refine (Fintype.sum_equiv (Equiv.sumPiEquivProdPi (fun _ => A)) _
    (fun xy : (X → A) × (Y → A) =>
      (if xy.1 ∘ σ = xy.1 then wordWeight w xy.1 else 0) *
      (if xy.2 ∘ τ = xy.2 then wordWeight w xy.2 else 0)) hterm).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- Adjoining one fixed position multiplies by the total color mass. -/
theorem coloringCharacter_optionCongr (w : A → NNReal) (σ : Equiv.Perm X) :
    coloringCharacter w (Equiv.optionCongr σ) =
      (∑ a, (w a : ℝ)) * coloringCharacter w σ := by
  classical
  letI : DecidableEq (Option X) := Classical.decEq _
  have hterm (x : Option X → A) :
      (if x ∘ Equiv.optionCongr σ = x then wordWeight w x else 0) =
        (w (x none) : ℝ) *
          (if (x ∘ some) ∘ σ = x ∘ some then wordWeight w (x ∘ some) else 0) := by
    have hfix : x ∘ Equiv.optionCongr σ = x ↔ (x ∘ some) ∘ σ = x ∘ some := by
      constructor
      · intro h
        exact funext (fun i => congrFun h (some i))
      · intro h
        funext i
        cases i with
        | none => rfl
        | some i => exact congrFun h i
    have hw : wordWeight w x = (w (x none) : ℝ) * wordWeight w (x ∘ some) :=
      Fintype.prod_option (fun i => (w (x i) : ℝ))
    simp only [hfix, hw]
    split_ifs <;> simp
  unfold coloringCharacter
  refine (Fintype.sum_equiv Equiv.piOptionEquivProd _
    (fun ax : A × (X → A) => (w ax.1 : ℝ) *
      (if ax.2 ∘ σ = ax.2 then wordWeight w ax.2 else 0)) hterm).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- A canonical probability alphabet with an additional color of positive mass. -/
def probabilityWeights (w : A → NNReal) : Option A → NNReal
  | none => 1 / (1 + ∑ a, w a)
  | some a => w a / (1 + ∑ a, w a)

theorem sum_probabilityWeights (w : A → NNReal) :
    ∑ a, (probabilityWeights w a : ℝ) = 1 := by
  rw [Fintype.sum_option]
  simp only [probabilityWeights, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add,
    NNReal.coe_sum, ← Finset.sum_div, ← add_div]
  exact div_self (by positivity)

/-- Normalized finite characters produced without assuming any positivity theorem. -/
def probabilityCharacter (w : A → NNReal) (σ : Equiv.Perm X) : ℝ :=
  coloringCharacter (probabilityWeights w) σ

theorem probabilityCharacter_one (w : A → NNReal) :
    probabilityCharacter (X := X) w 1 = 1 := by
  rw [probabilityCharacter, coloringCharacter_one, sum_probabilityWeights, one_pow]

theorem probabilityCharacter_restrict (w : A → NNReal) (σ : Equiv.Perm X) :
    probabilityCharacter w (Equiv.optionCongr σ) = probabilityCharacter w σ := by
  rw [probabilityCharacter, coloringCharacter_optionCongr, sum_probabilityWeights, one_mul]
  rfl

theorem probabilityCharacter_posSemidef (w : A → NNReal) (g : J → Equiv.Perm X) :
    Matrix.PosSemidef (fun i j => (probabilityCharacter w ((g i)⁻¹ * g j) : ℂ)) :=
  coloringCharacter_posSemidef (probabilityWeights w) g

end GaloisForLFunctions.SymmetricCharacters
