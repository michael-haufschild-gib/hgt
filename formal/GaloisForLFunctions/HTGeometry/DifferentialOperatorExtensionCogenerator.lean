import GaloisForLFunctions.HTGeometry.DifferentialOperatorMap
import GaloisForLFunctions.HTGeometry.DifferentialOperatorTorsionFreeQuotient

/-!
# Differential-closure cogenerators for Ore modules

A differential field extension `E/K` is naturally a left `K[∂;δ]`-module.  When `E` is
differentially closed, it detects every proper submodule of a finite free `K[∂;δ]`-module.  This is
the extension-valued form needed for generic-point tangent arguments.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

open GaloisForLFunctions

variable {K E : Type*} [Field K] [Field E] [Differential K] [Differential E]
  [Algebra K E] [DifferentialAlgebra K E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem algebraMap_deriv (a : K) :
    algebraMap K E (Differential.deriv a) = Differential.deriv (algebraMap K E a) :=
  (DifferentialAlgebra.deriv_algebraMap a).symm

/-- A differential extension as a module over the lower-field Ore ring. -/
@[reducible] def extensionModule : Module (DiffOp K) E :=
  Module.compHom E (mapRingHom (algebraMap K E) algebraMap_deriv)

local instance extensionModuleInstance : Module (DiffOp K) E := extensionModule

theorem extension_smul_def (p : DiffOp K) (x : E) :
    p • x = fieldApply (mapCoeffs (algebraMap K E) p) x := rfl

/-- Pair a lower-field operator row with a solution vector in a differential extension. -/
def fieldPairingOver (x : κ → E) : (κ → DiffOp K) →ₗ[DiffOp K] E where
  toFun w := ∑ j, fieldApply (mapCoeffs (algebraMap K E) (w j)) (x j)
  map_add' w z := by
    simp only [Pi.add_apply, mapCoeffs_add, fieldApply_add_op]
    exact Finset.sum_add_distrib
  map_smul' p w := by
    change (∑ j, fieldApply (mapCoeffs (algebraMap K E) (p * w j)) (x j)) =
      fieldApply (mapCoeffs (algebraMap K E) p)
        (∑ j, fieldApply (mapCoeffs (algebraMap K E) (w j)) (x j))
    simp_rw [mapCoeffs_mul (algebraMap K E) algebraMap_deriv]
    rw [fieldApply_finset_sum]
    exact Finset.sum_congr rfl fun j _ => fieldApply_mul _ _ _

theorem fieldPairingOver_apply (x : κ → E) (w : κ → DiffOp K) :
    fieldPairingOver x w =
      ∑ j, fieldApply (mapCoeffs (algebraMap K E) (w j)) (x j) := rfl

theorem fieldPairingOver_single_source (x : E) (j : κ) (w : κ → DiffOp K) :
    fieldPairingOver (Pi.single j x) w =
      fieldApply (mapCoeffs (algebraMap K E) (w j)) x := by
  classical
  rw [fieldPairingOver_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, fieldApply_zero]
  · simp

theorem fieldPairingOver_single_operator (x : κ → E) (j : κ) (p : DiffOp K) :
    fieldPairingOver x (Pi.single j p) =
      fieldApply (mapCoeffs (algebraMap K E) p) (x j) := by
  classical
  rw [fieldPairingOver_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, mapCoeffs_zero, fieldApply_zero_op]
  · simp

/-- A diagonal proper row span over `K[∂]` has a nonzero annihilator in a differentially closed
extension. -/
theorem exists_ne_zero_fieldPairingOver_of_diagonalized
    [Algebra ℚ E] [IsDifferentiallyClosed E]
    {P : ι → κ → DiffOp K} (hdiag : Diagonalized P) (hproper : rowSpanR P ≠ ⊤) :
    ∃ x : κ → E, x ≠ 0 ∧ rowSpanR P ≤ LinearMap.ker (fieldPairingOver x) := by
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
    let x : κ → E := Pi.single j 1
    refine ⟨x, ?_, rowSpanR_le fun i => ?_⟩
    · intro hx
      have := congrFun hx j
      exact (one_ne_zero : (1 : E) ≠ 0) (by simpa [x] using this)
    · rw [LinearMap.mem_ker, fieldPairingOver_single_source]
      have hP : P i j = 0 := by
        by_contra hne
        exact hj (mem_hitCols.mpr ⟨i, hne⟩)
      rw [hP, mapCoeffs_zero, fieldApply_zero_op]
  · push Not at hunit
    obtain ⟨i, j, hij, hnonunit⟩ := hunit
    have hdegree : 0 < degree (P i j) := degree_pos_of_not_isUnit hij hnonunit
    have hmapped : ¬ IsUnit (mapCoeffs (algebraMap K E) (P i j)) :=
      not_isUnit_mapCoeffs_of_degree_pos (algebraMap K E)
        (RingHom.injective (algebraMap K E)) hdegree
    obtain ⟨y, hy, hPy⟩ := exists_ne_zero_fieldApply_eq_zero hmapped
    let x : κ → E := Pi.single j y
    refine ⟨x, ?_, rowSpanR_le fun i' => ?_⟩
    · intro hx
      have := congrFun hx j
      exact hy (by simpa [x] using this)
    · rw [LinearMap.mem_ker, fieldPairingOver_single_source]
      by_cases hi : i' = i
      · subst hi
        exact hPy
      · rw [(hdiag i j hij).1 i' hi, mapCoeffs_zero, fieldApply_zero_op]

/-- Every proper submodule of a finite free lower-field Ore module is killed by a nonzero linear
functional valued in a differentially closed extension. -/
theorem exists_ne_zero_linearMap_kerOver_of_ne_top
    [Algebra ℚ E] [IsDifferentiallyClosed E]
    (N : Submodule (DiffOp K) (κ → DiffOp K)) (hN : N ≠ ⊤) :
    ∃ φ : (κ → DiffOp K) →ₗ[DiffOp K] E, φ ≠ 0 ∧ N ≤ LinearMap.ker φ := by
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
  obtain ⟨x, hx, hker⟩ :=
    exists_ne_zero_fieldPairingOver_of_diagonalized (K := K) (E := E) hdiag hproper
  let φ : (κ → DiffOp K) →ₗ[DiffOp K] E :=
    (fieldPairingOver (K := K) (E := E) x).comp e.toLinearMap
  refine ⟨φ, ?_, ?_⟩
  · intro hφ
    apply hx
    funext j
    have hpair : fieldPairingOver (K := K) (E := E) x (Pi.single j 1) = 0 := by
      obtain ⟨w, hw⟩ := e.surjective (Pi.single j 1)
      have := LinearMap.congr_fun hφ w
      simpa [φ, hw] using this
    simpa [fieldPairingOver_single_operator] using hpair
  · intro w hw
    rw [LinearMap.mem_ker]
    change fieldPairingOver x (e w) = 0
    have hew : e w ∈ Submodule.map e.toLinearMap N := ⟨w, hw, rfl⟩
    rw [hmap] at hew
    exact hker hew

/-- Every lower-field linear functional on a finite free operator module is extension-valued
pairing with its values on coordinate vectors. -/
theorem linearMap_eq_fieldPairingOver
    (φ : (κ → DiffOp K) →ₗ[DiffOp K] E) :
    φ = fieldPairingOver (fun j => φ (Pi.single j 1)) := by
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
    _ = ∑ j : κ, fieldApply (mapCoeffs (algebraMap K E) (w j))
        (φ (Pi.single j 1)) := by
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, extension_smul_def]
    _ = fieldPairingOver (fun j => φ (Pi.single j 1)) w := rfl

/-- Extension-valued finite-free cogenerator theorem. -/
theorem exists_ne_zero_commonKernelOver_of_ne_top
    [Algebra ℚ E] [IsDifferentiallyClosed E]
    (N : Submodule (DiffOp K) (κ → DiffOp K)) (hN : N ≠ ⊤) :
    ∃ x : κ → E, x ≠ 0 ∧ ∀ p ∈ N,
      ∑ j, fieldApply (mapCoeffs (algebraMap K E) (p j)) (x j) = 0 := by
  obtain ⟨φ, hφ, hker⟩ :=
    exists_ne_zero_linearMap_kerOver_of_ne_top (K := K) (E := E) N hN
  let x : κ → E := fun j => φ (Pi.single j 1)
  refine ⟨x, ?_, fun p hp => ?_⟩
  · intro hx
    apply hφ
    rw [linearMap_eq_fieldPairingOver φ]
    simp only [x, hx]
    ext w
    simp [fieldPairingOver_apply]
  · have hp0 : φ p = 0 := hker hp
    rw [linearMap_eq_fieldPairingOver φ, fieldPairingOver_apply] at hp0
    exact hp0

end

end DiffOp

end GaloisForLFunctions.HTGeometry
