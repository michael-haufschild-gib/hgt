import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.DivisibleSymbolOrthogonality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The linear Singleton bound

Prescribing zero on fewer coordinates than the code dimension leaves a
nonzero word: otherwise restriction would inject into a smaller vector
space. Applying this to one fewer coordinate than the dimension gives
the Singleton bound. A matching lower bound therefore determines the
minimum nonzero weight exactly.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
variable {K ι : Type*} [Field K] [Fintype ι]

/-- Fewer homogeneous coordinate conditions than the code dimension have a nonzero solution. -/
theorem exists_nonzero_word_vanishing (C : Submodule K (ι → K))
    (S : Finset ι) (hS : S.card < Module.finrank K C) :
    ∃ w ∈ C, w ≠ 0 ∧ ∀ i ∈ S, w i = 0 := by
  classical
  let E : C →ₗ[K] (S → K) :=
    { toFun := fun w i => w.val i.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hnot : ¬ Function.Injective E := by
    intro hE
    have hdim := LinearMap.finrank_le_finrank_of_injective hE
    rw [Module.finrank_pi, Fintype.card_coe] at hdim
    omega
  simp only [Function.Injective] at hnot
  push Not at hnot
  obtain ⟨x, y, hE, hxy⟩ := hnot
  refine ⟨(x - y).val, (x - y).property, ?_, ?_⟩
  · intro h
    exact hxy (sub_eq_zero.mp (show x - y = (0 : C) from Subtype.ext h))
  · intro i hi
    change x.val i - y.val i = 0
    exact sub_eq_zero.mpr (congrFun hE ⟨i, hi⟩)

/-- A positive-dimensional linear code has a nonzero word of weight at most `length+1-dimension`. -/
theorem exists_nonzero_word_weight_le_singleton (C : Submodule K (ι → K))
    (hC : 0 < Module.finrank K C) :
    ∃ w ∈ C, w ≠ 0 ∧ weight w ≤ Fintype.card ι + 1 - Module.finrank K C := by
  classical
  have hdim : Module.finrank K C ≤ Fintype.card ι := by
    have h := LinearMap.finrank_le_finrank_of_injective
      (f := C.subtype) Subtype.val_injective
    simpa only [Module.finrank_pi] using h
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset ι)) (n := Module.finrank K C - 1)
    (by rw [Finset.card_univ]; omega)
  obtain ⟨w, hw, hw0, hz⟩ := exists_nonzero_word_vanishing C S (by omega)
  have hzeros : S.card ≤ symbolCount w 0 := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hz i hi⟩
  have hpartition := symbolCount_add_weight_sub w 0
  simp only [sub_zero] at hpartition
  change symbolCount w 0 + weight w = Fintype.card ι at hpartition
  exact ⟨w, hw, hw0, by omega⟩

/-- When the designed bound meets Singleton, it is the attained minimum nonzero weight. -/
theorem minimum_weight_eq_singleton (C : Submodule K (ι → K)) (m : ℕ)
    (hdim : Module.finrank K C = m + 1)
    (hweight : ∀ w ∈ C, w ≠ 0 → Fintype.card ι - m ≤ weight w) :
    IsLeast {d : ℕ | ∃ w ∈ C, w ≠ 0 ∧ weight w = d} (Fintype.card ι - m) := by
  obtain ⟨w, hw, hw0, hbound⟩ := exists_nonzero_word_weight_le_singleton C (by omega)
  have hlower := hweight w hw hw0
  have heq : weight w = Fintype.card ι - m := by rw [hdim] at hbound; omega
  refine ⟨⟨w, hw, hw0, heq⟩, ?_⟩
  rintro d ⟨v, hv, hv0, rfl⟩
  exact hweight v hv hv0

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
