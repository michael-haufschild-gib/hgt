import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpValuationDiagonal
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveBuildingCarrier

/-!
# Integral shear transport for completed pseudodifferential lattices

Row shears preserve the integral span of a family.  Column shears are actual completed-skew
linear equivalences, preserve the standard valuation lattice, and carry the integral row span to
the sheared row span.  Hence every finite row-column reduction is realized by one standard-
lattice-preserving ambient linear equivalence.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Ambient right-coordinate shear corresponding to an integral column operation. -/
def completedValuationColShearLinearEquiv (j₀ : κ)
    (c : κ → CompletedPseudoDiffOpInteger (K := K)) (hc0 : c j₀ = 0) :
    (κ → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (κ → CompletedPseudoDiffOp K) where
  toFun x j := x j - x j₀ * (c j : CompletedPseudoDiffOp K)
  invFun x j := x j + x j₀ * (c j : CompletedPseudoDiffOp K)
  left_inv x := by
    funext j
    simp only
    rw [hc0]
    change (x j - x j₀ * (c j : CompletedPseudoDiffOp K)) +
      (x j₀ - x j₀ * 0) * (c j : CompletedPseudoDiffOp K) = x j
    noncomm_ring
  right_inv x := by
    funext j
    simp only
    rw [hc0]
    change (x j + x j₀ * (c j : CompletedPseudoDiffOp K)) -
      (x j₀ + x j₀ * 0) * (c j : CompletedPseudoDiffOp K) = x j
    noncomm_ring
  map_add' x y := by
    funext j
    simp only [Pi.add_apply]
    noncomm_ring
  map_smul' a x := by
    funext j
    change a * x j - (a * x j₀) * (c j : CompletedPseudoDiffOp K) =
      a * (x j - x j₀ * (c j : CompletedPseudoDiffOp K))
    noncomm_ring

@[simp] theorem completedValuationColShearLinearEquiv_apply (j₀ : κ)
    (c : κ → CompletedPseudoDiffOpInteger (K := K)) (hc0 : c j₀ = 0)
    (x : κ → CompletedPseudoDiffOp K) (j : κ) :
    completedValuationColShearLinearEquiv j₀ c hc0 x j =
      x j - x j₀ * (c j : CompletedPseudoDiffOp K) := rfl

@[simp] theorem completedValuationColShearLinearEquiv_symm_apply (j₀ : κ)
    (c : κ → CompletedPseudoDiffOpInteger (K := K)) (hc0 : c j₀ = 0)
    (x : κ → CompletedPseudoDiffOp K) (j : κ) :
    (completedValuationColShearLinearEquiv j₀ c hc0).symm x j =
      x j + x j₀ * (c j : CompletedPseudoDiffOp K) := rfl

/-- An integral coordinate shear preserves the standard valuation lattice exactly. -/
theorem map_standardCompletedPseudoDiffOpLattice_completedValuationColShear
    (j₀ : κ) (c : κ → CompletedPseudoDiffOpInteger (K := K)) (hc0 : c j₀ = 0) :
    mapCompletedPseudoDiffOpLatticeLinear
      (completedValuationColShearLinearEquiv j₀ c hc0)
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := κ)) =
        standardCompletedPseudoDiffOpLattice (K := K) (ι := κ) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext x
  rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_standardCompletedPseudoDiffOpLattice_iff] at hy ⊢
    intro j
    exact sub_mem (hy j) (mul_mem (hy j₀) (c j).property)
  · intro hx
    let y := (completedValuationColShearLinearEquiv j₀ c hc0).symm x
    refine ⟨y, ?_, (completedValuationColShearLinearEquiv j₀ c hc0).apply_symm_apply x⟩
    rw [mem_standardCompletedPseudoDiffOpLattice_iff] at hx ⊢
    intro j
    change x j + x j₀ * (c j : CompletedPseudoDiffOp K) ∈
      CompletedPseudoDiffOpInteger (K := K)
    exact add_mem (hx j) (mul_mem (hx j₀) (c j).property)

/-- An integral row shear does not change the integral span of the rows. -/
theorem span_completedValuationRowShear
    (i₀ : ι) (c : ι → CompletedPseudoDiffOpInteger (K := K)) (hc0 : c i₀ = 0)
    (P : ι → κ → CompletedPseudoDiffOp K) :
    Submodule.span (CompletedPseudoDiffOpInteger (K := K))
        (Set.range (completedValuationRowShear i₀ c P)) =
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range P) := by
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro y ⟨i, rfl⟩
    exact Submodule.sub_mem _
      (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i₀, rfl⟩))
  · rintro y ⟨i, rfl⟩
    have hi : completedValuationRowShear i₀ c P i +
        c i • completedValuationRowShear i₀ c P i₀ = P i := by
      funext j
      change (P i j - (c i : CompletedPseudoDiffOp K) * P i₀ j) +
        (c i : CompletedPseudoDiffOp K) *
          (P i₀ j - (c i₀ : CompletedPseudoDiffOp K) * P i₀ j) = P i j
      rw [hc0]
      simp
    rw [← hi]
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i₀, rfl⟩))

/-- An integral column shear carries the integral row span to the sheared row span. -/
theorem map_span_completedValuationColShear
    (j₀ : κ) (c : κ → CompletedPseudoDiffOpInteger (K := K)) (hc0 : c j₀ = 0)
    (P : ι → κ → CompletedPseudoDiffOp K) :
    (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range P)).map
        (restrictCompletedPseudoVecLinearEquiv
          (completedValuationColShearLinearEquiv j₀ c hc0)).toLinearMap =
      Submodule.span (CompletedPseudoDiffOpInteger (K := K))
        (Set.range (completedValuationColShear j₀ c P)) := by
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨P i, ⟨i, rfl⟩, rfl⟩

/-- Mapping a submodule by a composite completed-skew equivalence is successive mapping. -/
theorem map_restrictCompletedPseudoVecLinearEquiv_trans
    (e f : (κ → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (κ → CompletedPseudoDiffOp K))
    (N : Submodule (CompletedPseudoDiffOpInteger (K := K))
      (κ → CompletedPseudoDiffOp K)) :
    N.map (restrictCompletedPseudoVecLinearEquiv (e.trans f)).toLinearMap =
      (N.map (restrictCompletedPseudoVecLinearEquiv e).toLinearMap).map
        (restrictCompletedPseudoVecLinearEquiv f).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- A finite integral row-column equivalence is realized on row spans by one ambient linear
equivalence preserving the standard lattice. -/
theorem exists_linearEquiv_of_completedValuationRowColEquiv
    {P Q : ι → κ → CompletedPseudoDiffOp K}
    (h : CompletedValuationRowColEquiv P Q) :
    ∃ e : (κ → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
        (κ → CompletedPseudoDiffOp K),
      mapCompletedPseudoDiffOpLatticeLinear e
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := κ)) =
        standardCompletedPseudoDiffOpLattice (K := K) (ι := κ) ∧
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range P)).map
          (restrictCompletedPseudoVecLinearEquiv e).toLinearMap =
        Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range Q) := by
  induction h with
  | refl =>
      refine ⟨LinearEquiv.refl (CompletedPseudoDiffOp K) _,
        mapCompletedPseudoDiffOpLatticeLinear_refl _, ?_⟩
      ext y
      simp [restrictCompletedPseudoVecLinearEquiv]
  | tail _ hstep ih =>
      obtain ⟨e, hestd, hespan⟩ := ih
      rcases hstep with ⟨i₀, c, hc0, rfl⟩ | ⟨j₀, c, hc0, rfl⟩
      · refine ⟨e, hestd, ?_⟩
        rw [hespan, span_completedValuationRowShear i₀ c hc0]
      · let f := completedValuationColShearLinearEquiv j₀ c hc0
        refine ⟨e.trans f, ?_, ?_⟩
        · rw [← mapCompletedPseudoDiffOpLatticeLinear_trans, hestd]
          exact map_standardCompletedPseudoDiffOpLattice_completedValuationColShear j₀ c hc0
        · rw [map_restrictCompletedPseudoVecLinearEquiv_trans, hespan]
          exact map_span_completedValuationColShear j₀ c hc0 _

end

end DiffOp

end GaloisForLFunctions.HTGeometry
