import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLatticeFrame
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpValuationShear

/-!
# Cartan reduction of completed pseudodifferential valuation lattices

Integral row-column diagonal reduction is converted here into a statement about actual valuation
lattices.  Relative to the standard lattice, every full lattice is carried by a standard-lattice-
preserving completed-skew linear equivalence to a diagonal uniformizer coweight lattice.

This is the arbitrary-lattice noncommutative Cartan decomposition needed by the differential
variational building.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard valuation lattice is the integral span of the coordinate basis. -/
theorem standardCompletedPseudoDiffOpLattice_carrier_eq_span_basisFun :
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier =
      Submodule.span (CompletedPseudoDiffOpInteger (K := K))
        (Set.range (Pi.basisFun (CompletedPseudoDiffOp K) ι)) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← (Pi.basisFun (CompletedPseudoDiffOp K) ι).sum_repr x]
    apply Submodule.sum_mem
    intro i _
    have hxi : x i ∈ CompletedPseudoDiffOpInteger (K := K) :=
      (mem_standardCompletedPseudoDiffOpLattice_iff x).1 hx i
    let c : CompletedPseudoDiffOpInteger (K := K) := ⟨x i, hxi⟩
    have hb := Submodule.smul_mem
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K))
        (Set.range (Pi.basisFun (CompletedPseudoDiffOp K) ι))) c
      (Submodule.subset_span ⟨i, rfl⟩)
    change (c : CompletedPseudoDiffOp K) •
      (Pi.basisFun (CompletedPseudoDiffOp K) ι) i ∈ _ at hb
    simpa [c] using hb
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact basisFun_mem_completedPseudoDiffOpIntegralCarrier i

/-- A coweight lattice is the integral span of its coordinate coweight basis. -/
theorem standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_eq_span_basis
    (m : ι → ℤ) :
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier =
      Submodule.span (CompletedPseudoDiffOpInteger (K := K))
        (Set.range (completedPseudoDiffOpCoweightBasisVector (K := K) m)) := by
  classical
  change (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier.map
      (diagonalRightMulCompletedPseudoIntegerVecLinearEquiv
        (completedPseudoDiffOpUniformizerCoweight m)).toLinearMap = _
  rw [
    standardCompletedPseudoDiffOpLattice_carrier_eq_span_basisFun,
    Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(Pi.basisFun (CompletedPseudoDiffOp K) ι) i, ⟨i, rfl⟩, rfl⟩

/-- Extending the integral span of a full lattice family to the skew field gives the whole ambient
space. -/
theorem span_completedPseudoDiffOp_eq_top_of_span_integer_eq_lattice
    (P : ι → (ι → CompletedPseudoDiffOp K))
    (L : CompletedPseudoDiffOpLattice K ι)
    (hP : Submodule.span (CompletedPseudoDiffOpInteger (K := K))
      (Set.range P) = L.carrier) :
    Submodule.span (CompletedPseudoDiffOp K) (Set.range P) = ⊤ := by
  classical
  rw [← L.full]
  apply le_antisymm
  · apply Submodule.span_mono
    intro x hx
    rw [← hP]
    exact Submodule.subset_span hx
  · apply Submodule.span_le.mpr
    intro x hx
    rw [← hP] at hx
    exact Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span (CompletedPseudoDiffOp K) (Set.range P))
      (fun y hy => Submodule.subset_span hy)
      (Submodule.zero_mem _)
      (fun _ _ _ _ hy hz => Submodule.add_mem _ hy hz)
      (fun c y _ hy => by
        change (c : CompletedPseudoDiffOp K) • y ∈
          Submodule.span (CompletedPseudoDiffOp K) (Set.range P)
        exact Submodule.smul_mem _ (c : CompletedPseudoDiffOp K) hy)
      hx

/-- A spanning square matrix has a nonzero entry in every coordinate column. -/
theorem exists_row_ne_zero_of_span_completedPseudoDiffOp_eq_top
    (P : ι → (ι → CompletedPseudoDiffOp K))
    (hP : Submodule.span (CompletedPseudoDiffOp K) (Set.range P) = ⊤)
    (j : ι) : ∃ i, P i j ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hb : (Pi.basisFun (CompletedPseudoDiffOp K) ι) j ∈
      Submodule.span (CompletedPseudoDiffOp K) (Set.range P) := by
    rw [hP]
    trivial
  have hz : (Pi.basisFun (CompletedPseudoDiffOp K) ι) j j = 0 :=
    Submodule.span_induction
      (p := fun x _ => x j = 0)
      (fun x hx => by obtain ⟨i, rfl⟩ := hx; exact h i)
      rfl
      (fun _ _ _ _ hx hy => by simp [hx, hy])
      (fun a _ _ hx => by simp [hx])
      hb
  simpa using hz

/-- A diagonalized square spanning family has exactly one nonzero pivot in every row and column,
and its integral row span is a uniformizer coweight lattice. -/
theorem span_completedValuationDiagonalized_eq_standardCoweight
    (P : ι → (ι → CompletedPseudoDiffOp K))
    (hdiag : CompletedValuationDiagonalized P)
    (hfull : Submodule.span (CompletedPseudoDiffOp K) (Set.range P) = ⊤) :
    ∃ m : ι → ℤ,
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range P) =
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier := by
  classical
  choose r hr using fun j => exists_row_ne_zero_of_span_completedPseudoDiffOp_eq_top P hfull j
  have hrinj : Function.Injective r := by
    intro j k hjk
    by_contra hjk'
    have hz := (hdiag (r j) j (hr j)).2 k (Ne.symm hjk')
    rw [hjk] at hz
    exact (hr k) hz
  have hrbij : Function.Bijective r :=
    ⟨hrinj, (Finite.injective_iff_surjective.mp hrinj)⟩
  let er : ι ≃ ι := Equiv.ofBijective r hrbij
  let a : ι → CompletedPseudoDiffOp K := fun j => P (er j) j
  have ha : ∀ j, a j ≠ 0 := fun j => hr j
  let m : ι → ℤ := fun j =>
    completedPseudoDiffOpUnitAddValue (Units.mk0 (a j) (ha j))
  let w : ι → (ι → CompletedPseudoDiffOp K) :=
    completedPseudoDiffOpCoweightBasisVector (K := K) m
  have hrow : ∀ j k, P (er j) k = if k = j then a j else 0 := by
    intro j k
    by_cases hkj : k = j
    · subst k
      simp [a]
    · rw [if_neg hkj]
      exact (hdiag (er j) j (ha j)).2 k hkj
  have hwrow : ∀ j k, w j k = if k = j then
      (completedPseudoDiffOpUniformizerCoweight (K := K) m j :
        CompletedPseudoDiffOp K) else 0 := by
    intro j k
    by_cases hkj : k = j
    · subst k
      simp [w, completedPseudoDiffOpCoweightBasisVector,
        diagonalRightMulCompletedPseudoIntegerVecLinearEquiv]
    · simp [w, completedPseudoDiffOpCoweightBasisVector,
        diagonalRightMulCompletedPseudoIntegerVecLinearEquiv, hkj]
  have hval : ∀ j,
      completedPseudoDiffOpAddValue (a j) =
        completedPseudoDiffOpAddValue
          (completedPseudoDiffOpUniformizerCoweight (K := K) m j :
            CompletedPseudoDiffOp K) := by
    intro j
    have hvala : completedPseudoDiffOpAddValue (a j) = (m j : WithTop ℤ) := by
      change completedPseudoDiffOpAddValue
        ((Units.mk0 (a j) (ha j) : (CompletedPseudoDiffOp K)ˣ) :
          CompletedPseudoDiffOp K) = _
      simpa only [m] using completedPseudoDiffOpAddValue_unit_eq_coe
        (K := K) (Units.mk0 (a j) (ha j))
    have hvalpi : completedPseudoDiffOpAddValue
        (completedPseudoDiffOpUniformizerCoweight (K := K) m j :
          CompletedPseudoDiffOp K) = (m j : WithTop ℤ) := by
      rw [completedPseudoDiffOpAddValue_unit_eq_coe,
        completedPseudoDiffOpUniformizerCoweight,
        completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
    exact hvala.trans hvalpi.symm
  have hleft : ∀ j, ∃ c : CompletedPseudoDiffOpInteger (K := K),
      (c : CompletedPseudoDiffOp K) *
          (completedPseudoDiffOpUniformizerCoweight (K := K) m j :
            CompletedPseudoDiffOp K) = a j := by
    intro j
    apply exists_completedPseudoDiffOpInteger_left_factor
    · exact Units.ne_zero _
    · rw [hval j]
  have hright : ∀ j, ∃ c : CompletedPseudoDiffOpInteger (K := K),
      (c : CompletedPseudoDiffOp K) * a j =
        (completedPseudoDiffOpUniformizerCoweight (K := K) m j :
          CompletedPseudoDiffOp K) := by
    intro j
    apply exists_completedPseudoDiffOpInteger_left_factor (ha j)
    rw [hval j]
  have hrange : Set.range P = Set.range (fun j => P (er j)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨er.symm i, by simp⟩
    · rintro ⟨j, rfl⟩
      exact ⟨er j, rfl⟩
  refine ⟨m, ?_⟩
  rw [hrange, standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_eq_span_basis]
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro x ⟨j, rfl⟩
    change P (er j) ∈ Submodule.span (CompletedPseudoDiffOpInteger (K := K))
      (Set.range w)
    obtain ⟨c, hc⟩ := hleft j
    have hwmem : w j ∈ Submodule.span (CompletedPseudoDiffOpInteger (K := K))
        (Set.range w) := Submodule.subset_span ⟨j, rfl⟩
    have hcmem := Submodule.smul_mem _ c hwmem
    have heq : P (er j) = c • w j := by
      funext k
      change P (er j) k = (c : CompletedPseudoDiffOp K) * w j k
      rw [hrow, hwrow]
      by_cases hkj : k = j
      · subst k
        simpa using hc.symm
      · simp [hkj]
    rw [heq]
    exact hcmem
  · rintro x ⟨j, rfl⟩
    change w j ∈ Submodule.span (CompletedPseudoDiffOpInteger (K := K))
      (Set.range fun j => P (er j))
    obtain ⟨c, hc⟩ := hright j
    have hpmem : P (er j) ∈ Submodule.span (CompletedPseudoDiffOpInteger (K := K))
        (Set.range fun j => P (er j)) := Submodule.subset_span ⟨j, rfl⟩
    have hcmem := Submodule.smul_mem _ c hpmem
    have heq : w j = c • P (er j) := by
      funext k
      change w j k = (c : CompletedPseudoDiffOp K) * P (er j) k
      rw [hwrow, hrow]
      by_cases hkj : k = j
      · subst k
        simpa using hc.symm
      · simp [hkj]
    rw [heq]
    exact hcmem

/-- **Cartan reduction relative to the standard lattice.**  Every full completed valuation lattice
is simultaneously reduced with the standard lattice to a uniformizer coweight lattice. -/
theorem exists_completedPseudoDiffOpLattice_cartan_standard
    (L : CompletedPseudoDiffOpLattice K ι) :
    ∃ (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
        (ι → CompletedPseudoDiffOp K)) (m : ι → ℤ),
      mapCompletedPseudoDiffOpLatticeLinear e
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)) =
        standardCompletedPseudoDiffOpLattice (K := K) (ι := ι) ∧
      mapCompletedPseudoDiffOpLatticeLinear e L =
        standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m := by
  classical
  obtain ⟨b, hb⟩ := exists_completedPseudoDiffOpLattice_integral_basis L
  obtain ⟨Q, hbQ, hQdiag⟩ := exists_completedValuation_diagonalized b
  obtain ⟨e, hestd, heQ⟩ :=
    exists_linearEquiv_of_completedValuationRowColEquiv hbQ
  let L' := mapCompletedPseudoDiffOpLatticeLinear e L
  have hL' : Submodule.span (CompletedPseudoDiffOpInteger (K := K))
      (Set.range Q) = L'.carrier := by
    change _ = L.carrier.map (restrictCompletedPseudoVecLinearEquiv e).toLinearMap
    rw [← hb, heQ]
  have hQfull : Submodule.span (CompletedPseudoDiffOp K) (Set.range Q) = ⊤ :=
    span_completedPseudoDiffOp_eq_top_of_span_integer_eq_lattice Q L' hL'
  obtain ⟨m, hm⟩ :=
    span_completedValuationDiagonalized_eq_standardCoweight Q hQdiag hQfull
  refine ⟨e, m, hestd, ?_⟩
  apply CompletedPseudoDiffOpLattice.ext
  rw [← hL', hm]

/-- **Arbitrary-pair Cartan decomposition.**  One completed-skew frame sends the first lattice to
the standard lattice and the second to a uniformizer coweight lattice. -/
theorem exists_completedPseudoDiffOpLattice_pair_cartan
    (L M : CompletedPseudoDiffOpLattice K ι) :
    ∃ (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
        (ι → CompletedPseudoDiffOp K)) (m : ι → ℤ),
      mapCompletedPseudoDiffOpLatticeLinear e L =
          standardCompletedPseudoDiffOpLattice (K := K) (ι := ι) ∧
      mapCompletedPseudoDiffOpLatticeLinear e M =
          standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m := by
  classical
  obtain ⟨f, hf⟩ := exists_completedPseudoDiffOp_linearEquiv_map_standard L
  let N := mapCompletedPseudoDiffOpLatticeLinear f.symm M
  obtain ⟨e, m, hestd, heN⟩ := exists_completedPseudoDiffOpLattice_cartan_standard N
  have hfL : mapCompletedPseudoDiffOpLatticeLinear f.symm L =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := ι) := by
    rw [← hf, mapCompletedPseudoDiffOpLatticeLinear_trans,
      LinearEquiv.self_trans_symm, mapCompletedPseudoDiffOpLatticeLinear_refl]
  refine ⟨f.symm.trans e, m, ?_, ?_⟩
  · rw [← mapCompletedPseudoDiffOpLatticeLinear_trans, hfL, hestd]
  · rw [← mapCompletedPseudoDiffOpLatticeLinear_trans]
    exact heN

end

end DiffOp

end GaloisForLFunctions.HTGeometry
