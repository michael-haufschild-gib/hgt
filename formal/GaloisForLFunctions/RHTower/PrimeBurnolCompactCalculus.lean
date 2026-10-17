import GaloisForLFunctions.RHTower.PrimeBurnolCayleyOrbit
import GaloisForLFunctions.HTGeometry.DenseRankOneCompactClosure
import Mathlib.Topology.Algebra.StarSubalgebra

/-! Exact compact-operator realization by corners of the literal prime Burnol Cayley defect. -/

noncomputable section
open Complex Set InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

def primeBurnolCayleyCorner (m n : ℕ) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  (star primeBurnolCayley)^m * primeBurnolCayleyDefect * primeBurnolCayley^n

theorem primeBurnolCayleyCorner_eq_rankOne (m n : ℕ) :
    primeBurnolCayleyCorner m n =
      (4 : ℂ) • rankOne ℂ (burnolCayleyOrbit m) (burnolCayleyOrbit n) := by
  have hn : (star primeBurnolCayley)^n = ContinuousLinearMap.adjoint (primeBurnolCayley^n) := by
    rw [← star_pow,ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  simp only [primeBurnolCayleyCorner,primeBurnolCayleyDefect_eq_rankOne,
    mul_apply_eq_comp,smul_apply,rankOne_apply,map_smul,burnolCayleyOrbit]
  rw [hn,ContinuousLinearMap.adjoint_inner_left]

def primeBurnolCompactWordSpan : Submodule ℂ (BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :=
  Submodule.span ℂ (Set.range fun mn : ℕ × ℕ => primeBurnolCayleyCorner mn.1 mn.2)

theorem primeBurnolCompactWordSpan_eq_rankOneFamilySpan :
    primeBurnolCompactWordSpan = rankOneFamilySpan burnolCayleyOrbit := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨m,n⟩,rfl⟩
    change primeBurnolCayleyCorner m n ∈ rankOneFamilySpan burnolCayleyOrbit
    rw [primeBurnolCayleyCorner_eq_rankOne]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(m,n),rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨m,n⟩,rfl⟩
    change rankOne ℂ (burnolCayleyOrbit m) (burnolCayleyOrbit n) ∈ primeBurnolCompactWordSpan
    have he : rankOne ℂ (burnolCayleyOrbit m) (burnolCayleyOrbit n) =
        (1/4 : ℂ) • primeBurnolCayleyCorner m n := by
      rw [primeBurnolCayleyCorner_eq_rankOne,smul_smul]
      norm_num
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(m,n),rfl⟩)

/-- Exact classification: the norm closure of literal defect corners is all compact operators. -/
theorem primeBurnolCompactWordSpan_closure_eq :
    primeBurnolCompactWordSpan.topologicalClosure =
      compactOperator (RingHom.id ℂ) BurnolHalfLineL2 BurnolHalfLineL2 := by
  rw [primeBurnolCompactWordSpan_eq_rankOneFamilySpan]
  exact closed_rankOneFamilySpan_eq_compactOperator _ dense_burnolCayleyOrbit_span

theorem primeBurnol_compact_iff_mem_closedWordSpan
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :
    IsCompactOperator T ↔ T ∈ primeBurnolCompactWordSpan.topologicalClosure := by
  rw [primeBurnolCompactWordSpan_closure_eq]
  rfl

/-- Every compact mixing operator has finite, literal star-word approximants in operator norm. -/
theorem primeBurnol_compact_finite_word_approximation
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (hT : IsCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : (ℕ × ℕ) →₀ ℂ,
      ‖T-Finsupp.linearCombination ℂ (fun mn : ℕ × ℕ =>
        primeBurnolCayleyCorner mn.1 mn.2) a‖ < ε := by
  have ht : T ∈ closure (primeBurnolCompactWordSpan : Set
      (BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2)) :=
    (primeBurnol_compact_iff_mem_closedWordSpan T).mp hT
  obtain ⟨S,hS,hTS⟩ := Metric.mem_closure_iff.mp ht ε hε
  have hr : S ∈ (Finsupp.linearCombination ℂ
      (fun mn : ℕ × ℕ => primeBurnolCayleyCorner mn.1 mn.2)).range := by
    rw [Finsupp.range_linearCombination]
    exact hS
  obtain ⟨a,ha⟩ := hr
  refine ⟨a,?_⟩
  rw [ha]
  exact (dist_eq_norm T S) ▸ hTS

/-- A single actual-prime Cayley operator generates the entire compact correction class. -/
theorem primeBurnol_compact_mem_elemental
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (hT : IsCompactOperator T) :
    T ∈ StarAlgebra.elemental ℂ primeBurnolCayley := by
  let A := StarAlgebra.elemental ℂ primeBurnolCayley
  have hc : primeBurnolCayley ∈ A := StarAlgebra.elemental.self_mem _ _
  have hs : star primeBurnolCayley ∈ A := StarAlgebra.elemental.star_self_mem _ _
  have hd : primeBurnolCayleyDefect ∈ A :=
    A.sub_mem (A.add_mem (A.sub_mem A.one_mem (A.smul_mem (A.mul_mem hs hc) _))
      (A.smul_mem (A.mul_mem (A.pow_mem hs 2) (A.pow_mem hc 2)) _))
      (A.mul_mem (A.pow_mem hs 3) (A.pow_mem hc 3))
  have hle : primeBurnolCompactWordSpan ≤ A.toSubalgebra.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨m,n⟩,rfl⟩
    exact A.mul_mem (A.mul_mem (A.pow_mem hs m) hd) (A.pow_mem hc n)
  exact primeBurnolCompactWordSpan.topologicalClosure_minimal hle
    (StarAlgebra.elemental.isClosed _ _) ((primeBurnol_compact_iff_mem_closedWordSpan T).mp hT)

end RHTower
