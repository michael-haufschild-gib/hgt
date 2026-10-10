import GaloisForLFunctions.RHTower.WeilLogShiftGramFiberCost

/-! Every actual Gram test has a distinct-node encoding preserving all its forms
and costing no more at any nonnegative tail normalization. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

def FiniteWeilGramDistinctNodes : FiniteWeilGramTest → Prop
  | ⟨_, x, _, _⟩ => Function.Injective x

def finiteWeilGramCoalesce : FiniteWeilGramTest → FiniteWeilGramTest
  | ⟨N, x, u, a⟩ =>
    let S := Finset.univ.image x
    let q : Fin N → S := fun i => ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩
    finiteWeilGramTestOfFinite (fun y : S => (y : ℝ))
      (finiteWeilGramFiberAmplitude q u) a

theorem finiteWeilGramCoalesce_distinct (w : FiniteWeilGramTest) :
    FiniteWeilGramDistinctNodes (finiteWeilGramCoalesce w) := by
  rcases w with ⟨N, x, u, a⟩
  let S := Finset.univ.image x
  change Function.Injective ((fun y : S => (y : ℝ)) ∘ (Fintype.equivFin S).symm)
  intro i j h
  apply (Fintype.equivFin S).symm.injective
  exact Subtype.ext h

theorem finiteWeilGramForm_coalesce (s : Finset ℕ) (w : FiniteWeilGramTest) :
    finiteWeilGramForm s (finiteWeilGramCoalesce w) = finiteWeilGramForm s w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramCoalesce]
  rw [finiteWeilGramForm_fiberAmplitude]
  apply LinearMap.ext
  intro c
  rw [finiteWeilGramCoefficientVector_pairing, finiteWeilGramCoefficientVector_pairing]
  apply Finset.sum_congr rfl
  intro k _
  simp only [finiteWeilGramCoefficientVector_ofFinite, finiteWeilGramCoefficientVector_apply,
    Function.comp_apply]

theorem finiteWeilGramTailCost_coalesce_le {B : ℝ} (hB : 0 ≤ B)
    (w : FiniteWeilGramTest) :
    finiteWeilGramTailCost B (finiteWeilGramCoalesce w) ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  let S := Finset.univ.image x
  let q : Fin N → S := fun i => ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩
  have h := finiteWeilGramTailCost_fiberAmplitude_le hB q (fun y : S => (y : ℝ)) u a
  calc
    _ ≤ finiteWeilGramTailCost B
        (finiteWeilGramTestOfFinite ((fun y : S => (y : ℝ)) ∘ q) u a) := h
    _ = _ := by
      rw [finiteWeilGramTailCost_ofFinite]
      rfl

/-- No producer premise: normalize an arbitrary actual test simultaneously for
all supports and all nonnegative tail constants. -/
theorem exists_finiteWeilGram_distinct_node_normalization (w : FiniteWeilGramTest) :
    ∃ z : FiniteWeilGramTest, FiniteWeilGramDistinctNodes z ∧
      (∀ s : Finset ℕ, finiteWeilGramForm s z = finiteWeilGramForm s w) ∧
      ∀ B : NNReal, finiteWeilGramTailCost (B : ℝ) z ≤ finiteWeilGramTailCost (B : ℝ) w :=
  ⟨finiteWeilGramCoalesce w, finiteWeilGramCoalesce_distinct w,
    fun s => finiteWeilGramForm_coalesce s w,
    fun B => finiteWeilGramTailCost_coalesce_le (NNReal.coe_nonneg B) w⟩

end RHTower
