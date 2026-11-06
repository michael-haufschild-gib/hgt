import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CyclicTrace
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.WordProducts

/-!
# Independent-color characters for summable alphabets

Summable nonnegative color weights give absolutely convergent fixed-word sums at every finite
rank. Positivity follows by taking finite sums of fixed-word Gram kernels and passing to their
entrywise limits. The same alphabet is used at every rank.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical ComplexOrder

namespace GaloisForLFunctions.SymmetricCharacters

variable {A X Y J : Type*} [Fintype X] [Fintype Y]

/-- Fixed-word sum for an arbitrary summable color alphabet. -/
def wordCharacter (w : A → NNReal) (σ : Equiv.Perm X) : ℝ :=
  ∑' x : X → A, if x ∘ σ = x then wordWeight w x else 0

private theorem wordWeight_summable_and_tsum (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) :
    Summable (wordWeight (X := X) w) ∧
      (∑' x : X → A, wordWeight w x) = (∑' a, (w a : ℝ)) ^ Fintype.card X := by
  let e : (Fin (Fintype.card X) → A) ≃ (X → A) :=
    Equiv.arrowCongr (Fintype.equivFin X).symm (Equiv.refl A)
  have he (x : Fin (Fintype.card X) → A) :
      wordWeight w (e x) = ∏ j, (w (x j) : ℝ) := by
    exact Equiv.prod_comp (Fintype.equivFin X) (fun j => (w (x j) : ℝ))
  obtain ⟨hs, ht⟩ := wordProducts_summable_and_tsum hw
    (fun a => (w a).coe_nonneg) (Fintype.card X)
  constructor
  · apply e.summable_iff.mp
    exact hs.congr fun x => (he x).symm
  · rw [← e.tsum_eq (wordWeight w)]
    simpa only [he] using ht

theorem summable_fixedWordWeight (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (σ : Equiv.Perm X) :
    Summable (fun x : X → A => if x ∘ σ = x then wordWeight w x else 0) := by
  apply Summable.of_nonneg_of_le
    (fun x => by split_ifs <;> exacts [wordWeight_nonneg w x, le_rfl])
    (fun x => by split_ifs <;> exacts [le_rfl, wordWeight_nonneg w x])
    (wordWeight_summable_and_tsum (X := X) w hw).1

theorem wordCharacter_one (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) :
    wordCharacter (X := X) w 1 = (∑' a, (w a : ℝ)) ^ Fintype.card X := by
  simp only [wordCharacter, Equiv.Perm.coe_one, Function.comp_id, ite_true]
  exact (wordWeight_summable_and_tsum w hw).2

/-- Entrywise absolutely convergent sums of finite positive kernels are positive. -/
private theorem positiveKernel_tsum {B : Type*} [Fintype J]
    (K : B → Matrix J J ℂ) (hK : ∀ b, (K b).PosSemidef)
    (hs : ∀ i j, Summable (fun b => K b i j)) :
    Matrix.PosSemidef (fun i j => ∑' b, K b i j) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    have hstar := (continuous_star.tendsto _).comp (hs j i).hasSum
    apply tendsto_nhds_unique hstar
    apply (hs i j).hasSum.congr'
    filter_upwards with s
    simp only [star_sum]
    exact Finset.sum_congr rfl (fun b _ => ((hK b).isHermitian.apply i j).symm)
  · intro v
    have hquad : Tendsto
        (fun s : Finset B =>
          dotProduct (star v) (Matrix.mulVec (fun i j => ∑ b ∈ s, K b i j) v))
        atTop (𝓝 (dotProduct (star v)
          (Matrix.mulVec (fun i j => ∑' b, K b i j) v))) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply tendsto_finsetSum
      intro i _
      apply tendsto_finsetSum
      intro j _
      exact tendsto_const_nhds.mul ((hs i j).hasSum.mul_const (v j))
    apply ge_of_tendsto hquad
    exact Filter.Eventually.of_forall fun s => by
      simpa only [Matrix.sum_apply] using
        (Matrix.posSemidef_sum s (fun b _ => hK b)).dotProduct_mulVec_nonneg v

/-- Every finite test matrix of a summable independent-color character is positive. -/
theorem wordCharacter_posSemidef [Fintype J] (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (g : J → Equiv.Perm X) :
    Matrix.PosSemidef (fun i j => (wordCharacter w ((g i)⁻¹ * g j) : ℂ)) := by
  let K (x : X → A) : Matrix J J ℂ :=
    (wordWeight w x : ℂ) •
      (1 : Matrix (X → A) (X → A) ℂ).submatrix (fun j => x ∘ (g j).symm)
        (fun j => x ∘ (g j).symm)
  have hfix (x : X → A) (i j : J) :
      x ∘ ((g i)⁻¹ * g j) = x ↔ x ∘ (g i).symm = x ∘ (g j).symm := by
    constructor
    · intro h
      funext a
      simpa using congrFun h ((g j)⁻¹ a)
    · intro h
      funext a
      simpa using congrFun h (g j a)
  have he (x : X → A) (i j : J) :
      K x i j = ((if x ∘ ((g i)⁻¹ * g j) = x then wordWeight w x else 0 : ℝ) : ℂ) := by
    simp only [K, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.one_apply,
      smul_eq_mul, hfix]
    split_ifs <;> simp
  have hK (x : X → A) : (K x).PosSemidef :=
    ((Matrix.PosSemidef.one : Matrix.PosSemidef (1 : Matrix (X → A) (X → A) ℂ)).submatrix
      (fun j => x ∘ (g j).symm)).smul
      (Complex.zero_le_real.mpr (wordWeight_nonneg w x))
  have hs (i j : J) : Summable (fun x => K x i j) := by
    simp only [he]
    exact Complex.summable_ofReal.mpr (summable_fixedWordWeight w hw _)
  convert positiveKernel_tsum K hK hs using 1
  ext i j
  simp only [he, wordCharacter, Complex.ofReal_tsum]

/-- Relabeling positions preserves the infinite-alphabet character. -/
theorem wordCharacter_conj (w : A → NNReal) (σ τ : Equiv.Perm X) :
    wordCharacter w (τ * σ * τ⁻¹) = wordCharacter w σ := by
  let e := Equiv.arrowCongr τ.symm (Equiv.refl A)
  have he (x : X → A) :
      (if x ∘ (τ * σ * τ⁻¹) = x then wordWeight w x else 0) =
      (if (e x) ∘ σ = e x then wordWeight w (e x) else 0) := by
    have hweight : wordWeight w (e x) = wordWeight w x := wordWeight_comp w x τ
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
    rw [hfix]
  exact (tsum_congr he).trans (e.tsum_eq _)

/-- Disjoint blocks use independent letters, including for infinite summable alphabets. -/
theorem wordCharacter_sumCongr (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (σ : Equiv.Perm X) (τ : Equiv.Perm Y) :
    wordCharacter w (Equiv.sumCongr σ τ) = wordCharacter w σ * wordCharacter w τ := by
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
    have hm : wordWeight w x =
        wordWeight w (x ∘ Sum.inl) * wordWeight w (x ∘ Sum.inr) :=
      Fintype.prod_sum_type (fun i => (w (x i) : ℝ))
    simp only [hfix, hm]
    split_ifs <;> simp_all
  unfold wordCharacter
  refine (tsum_congr hterm).trans ?_
  rw [(Equiv.sumPiEquivProdPi (fun _ => A)).tsum_eq
    (fun xy : (X → A) × (Y → A) =>
      (if xy.1 ∘ σ = xy.1 then wordWeight w xy.1 else 0) *
      (if xy.2 ∘ τ = xy.2 then wordWeight w xy.2 else 0))]
  exact (tsum_mul_tsum_of_summable_norm
    (summable_fixedWordWeight w hw σ).norm (summable_fixedWordWeight w hw τ).norm).symm

/-- Restriction multiplies by total mass, so a probability alphabet is coherent at every rank. -/
theorem wordCharacter_optionCongr (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (σ : Equiv.Perm X) :
    wordCharacter w (Equiv.optionCongr σ) = (∑' a, (w a : ℝ)) * wordCharacter w σ := by
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
    have hm : wordWeight w x = (w (x none) : ℝ) * wordWeight w (x ∘ some) :=
      Fintype.prod_option (fun i => (w (x i) : ℝ))
    simp only [hfix, hm]
    split_ifs <;> simp
  unfold wordCharacter
  refine (tsum_congr hterm).trans ?_
  rw [(Equiv.piOptionEquivProd : (Option X → A) ≃ A × (X → A)).tsum_eq
    (fun ax : A × (X → A) => (w ax.1 : ℝ) *
      (if ax.2 ∘ σ = ax.2 then wordWeight w ax.2 else 0))]
  exact (tsum_mul_tsum_of_summable_norm hw.norm
    (summable_fixedWordWeight w hw σ).norm).symm

end GaloisForLFunctions.SymmetricCharacters
