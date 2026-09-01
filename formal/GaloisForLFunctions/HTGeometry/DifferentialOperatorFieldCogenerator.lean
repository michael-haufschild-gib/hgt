import GaloisForLFunctions.HTGeometry.DifferentialOperatorNonzeroKernel
import GaloisForLFunctions.HTGeometry.DifferentialOperatorTorsionFreeQuotient

/-!
# A differential field cogenerates finite free Ore modules

Over a differentially closed field, every proper submodule of a finite free module over the Ore
ring has a nonzero common solution.  Diagonal reduction leaves either an unused coordinate or a
nonunit scalar operator; the latter has a nonzero field-valued solution.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

open GaloisForLFunctions

variable {K : Type*} [Field K] [Algebra ℚ K] [Differential K]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Pair an operator row with a field-valued solution vector. -/
def fieldPairing (x : κ → K) : (κ → DiffOp K) →ₗ[DiffOp K] K where
  toFun w := ∑ j, fieldApply (w j) (x j)
  map_add' w z := by
    simp only [Pi.add_apply, fieldApply_add_op]
    exact Finset.sum_add_distrib
  map_smul' p w := by
    change (∑ j, fieldApply (p * w j) (x j)) = fieldApply p (∑ j, fieldApply (w j) (x j))
    rw [fieldApply_finset_sum]
    exact Finset.sum_congr rfl fun j _ => fieldApply_mul p (w j) (x j)

theorem fieldPairing_apply (x : κ → K) (w : κ → DiffOp K) :
    fieldPairing x w = ∑ j, fieldApply (w j) (x j) := rfl

theorem fieldPairing_single_source (x : K) (j : κ) (w : κ → DiffOp K) :
    fieldPairing (Pi.single j x) w = fieldApply (w j) x := by
  classical
  rw [fieldPairing_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, fieldApply_zero]
  · simp

theorem fieldPairing_single_operator (x : κ → K) (j : κ) (p : DiffOp K) :
    fieldPairing x (Pi.single j p) = fieldApply p (x j) := by
  classical
  rw [fieldPairing_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, fieldApply_zero_op]
  · simp

/-- A diagonal proper row span has a nonzero field-valued annihilator. -/
theorem exists_ne_zero_fieldPairing_of_diagonalized
    [IsDifferentiallyClosed K] {P : ι → κ → DiffOp K}
    (hdiag : Diagonalized P) (hproper : rowSpanR P ≠ ⊤) :
    ∃ x : κ → K, x ≠ 0 ∧ rowSpanR P ≤ LinearMap.ker (fieldPairing x) := by
  classical
  by_cases hunit : ∀ i j, P i j ≠ 0 → IsUnit (P i j)
  · have hcoord : rowSpanR P = coordSupport (hitCols P) :=
      rowSpanR_eq_coordSupport hdiag hunit
    have hmiss : ∃ j : κ, j ∉ hitCols P := by
      by_contra h
      push Not at h
      apply hproper
      rw [hcoord]
      ext w
      constructor
      · intro; trivial
      · intro _ j hj
        exact absurd (h j) hj
    obtain ⟨j, hj⟩ := hmiss
    let x : κ → K := Pi.single j 1
    refine ⟨x, ?_, rowSpanR_le fun i => ?_⟩
    · intro hx
      have := congrFun hx j
      exact (one_ne_zero : (1 : K) ≠ 0) (by simpa [x] using this)
    · rw [LinearMap.mem_ker, fieldPairing_single_source]
      have hP : P i j = 0 := by
        by_contra hne
        exact hj (mem_hitCols.mpr ⟨i, hne⟩)
      rw [hP, fieldApply_zero_op]
  · push Not at hunit
    obtain ⟨i, j, hij, hnonunit⟩ := hunit
    obtain ⟨y, hy, hPy⟩ := exists_ne_zero_fieldApply_eq_zero (K := K) hnonunit
    let x : κ → K := Pi.single j y
    refine ⟨x, ?_, rowSpanR_le fun i' => ?_⟩
    · intro hx
      have := congrFun hx j
      exact hy (by simpa [x] using this)
    · rw [LinearMap.mem_ker, fieldPairing_single_source]
      by_cases hi : i' = i
      · subst hi
        exact hPy
      · rw [(hdiag i j hij).1 i' hi, fieldApply_zero_op]

/-- Every proper submodule of a finite free Ore module is killed by a nonzero field-valued linear
functional. -/
theorem exists_ne_zero_linearMap_ker_of_ne_top [IsDifferentiallyClosed K]
    (N : Submodule (DiffOp K) (κ → DiffOp K)) (hN : N ≠ ⊤) :
    ∃ φ : (κ → DiffOp K) →ₗ[DiffOp K] K, φ ≠ 0 ∧ N ≤ LinearMap.ker φ := by
  classical
  obtain ⟨n, v, _, _, hspan⟩ := exists_basis_of_submodule N
  obtain ⟨P, hvP, hdiag⟩ := exists_diagonalized v
  obtain ⟨e, he⟩ := exists_equiv_of_rowColEquiv hvP
  have hmap : Submodule.map e.toLinearMap N = rowSpanR P := by
    rw [← hspan]
    exact he
  have hproper : rowSpanR P ≠ ⊤ := by
    intro htop
    apply hN
    have hpre : Submodule.map e.symm.toLinearMap (rowSpanR P) = N := by
      rw [← hmap, ← Submodule.map_comp]
      simp
    rw [← hpre, htop]
    simp
  obtain ⟨x, hx, hker⟩ := exists_ne_zero_fieldPairing_of_diagonalized hdiag hproper
  let φ : (κ → DiffOp K) →ₗ[DiffOp K] K := (fieldPairing x).comp e.toLinearMap
  refine ⟨φ, ?_, ?_⟩
  · intro hφ
    apply hx
    funext j
    have hpair : fieldPairing x (Pi.single j 1) = 0 := by
      obtain ⟨w, hw⟩ := e.surjective (Pi.single j 1)
      have := LinearMap.congr_fun hφ w
      simpa [φ, hw] using this
    simpa [fieldPairing_single_operator] using hpair
  · intro w hw
    rw [LinearMap.mem_ker]
    change fieldPairing x (e w) = 0
    have hew : e w ∈ Submodule.map e.toLinearMap N := ⟨w, hw, rfl⟩
    rw [hmap] at hew
    exact hker hew

/-- Every linear functional on a finite free operator module is pairing with its values on the
coordinate vectors. -/
theorem linearMap_eq_fieldPairing (φ : (κ → DiffOp K) →ₗ[DiffOp K] K) :
    φ = fieldPairing (fun j => φ (Pi.single j 1)) := by
  apply LinearMap.ext
  intro w
  have hsum : w = ∑ j : κ, (w j) • (Pi.single j 1 : κ → DiffOp K) := by
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Pi.smul_apply, hj]
    · simp
  calc
    φ w = φ (∑ j : κ, (w j) • (Pi.single j 1 : κ → DiffOp K)) := congrArg φ hsum
    _ = ∑ j : κ, φ ((w j) • (Pi.single j 1 : κ → DiffOp K)) := by rw [map_sum]
    _ = ∑ j : κ, fieldApply (w j) (φ (Pi.single j 1)) := by
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, field_smul_def]
    _ = fieldPairing (fun j => φ (Pi.single j 1)) w := rfl

/-- **Finite-free cogenerator theorem.**  Every proper operator submodule has a nonzero common
solution in the differentially closed coefficient field. -/
theorem exists_ne_zero_commonKernel_of_ne_top [IsDifferentiallyClosed K]
    (N : Submodule (DiffOp K) (κ → DiffOp K)) (hN : N ≠ ⊤) :
    ∃ x : κ → K, x ≠ 0 ∧ ∀ p ∈ N, ∑ j, fieldApply (p j) (x j) = 0 := by
  obtain ⟨φ, hφ, hker⟩ := exists_ne_zero_linearMap_ker_of_ne_top N hN
  let x : κ → K := fun j => φ (Pi.single j 1)
  refine ⟨x, ?_, fun p hp => ?_⟩
  · intro hx
    apply hφ
    rw [linearMap_eq_fieldPairing φ]
    simp only [x, hx]
    ext w
    simp [fieldPairing_apply]
  · have hp0 : φ p = 0 := hker hp
    rw [linearMap_eq_fieldPairing φ, fieldPairing_apply] at hp0
    exact hp0

end

end DiffOp

end GaloisForLFunctions.HTGeometry
