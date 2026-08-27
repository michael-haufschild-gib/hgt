import GaloisForLFunctions.HTGeometry.OffMatrixLift
import GaloisForLFunctions.HTGeometry.SiteSupportedLocalHamiltonian

/-!
# Operators supported away from a cut are complement lifts

If a matrix acts only on a packet disjoint from a cut, it is literally the identity on the cut
tensor a matrix on the complement.  For a unitary matrix the complement factor is unitary.  This
turns intrinsic site support into the exact `offMatrixLift` factor required by prefix stripping.
-/

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Extend a complement configuration by `false` on the cut. -/
def falseOnExtension (A : Finset Q) (x : Off A) : Config Q :=
  (splitConfig A).symm (fun _ => false, x)

/-- Complement block read from a matrix by fixing `false` on the cut. -/
def offMatrixRestriction (A : Finset Q)
    (V : Matrix (Config Q) (Config Q) ℂ) : Matrix (Off A) (Off A) ℂ :=
  fun x y => V (falseOnExtension A x) (falseOnExtension A y)

theorem offMatrixLift_injective (A : Finset Q) :
    Function.Injective (offMatrixLift A) := by
  intro B C h
  ext x y
  have hentry := congr_fun (congr_fun h (falseOnExtension A x)) (falseOnExtension A y)
  simpa [offMatrixLift, falseOnExtension] using hentry

/-- A matrix supported on a packet disjoint from `A` is exactly its complement lift. -/
theorem eq_offMatrixLift_offMatrixRestriction_of_isSiteSupported
    {A P : Finset Q} {V : Matrix (Config Q) (Config Q) ℂ}
    (hdisj : Disjoint P A) (hV : IsSiteSupported P V) :
    V = offMatrixLift A (offMatrixRestriction A V) := by
  ext x y
  by_cases hOn : (splitConfig A x).1 = (splitConfig A y).1
  · rw [offMatrixLift, if_pos hOn]
    by_cases hOffP : ∀ w, w ∉ P → x w = y w
    · apply hV.2 x y (falseOnExtension A (splitConfig A x).2)
        (falseOnExtension A (splitConfig A y).2)
      · intro w hwP
        have hwA : w ∉ A := fun hwA =>
          (Finset.disjoint_left.mp hdisj) hwP hwA
        simp [falseOnExtension, splitConfig, hwA]
      · intro w hwP
        have hwA : w ∉ A := fun hwA =>
          (Finset.disjoint_left.mp hdisj) hwP hwA
        simp [falseOnExtension, splitConfig, hwA]
      · exact hOffP
      · intro w hwP
        by_cases hwA : w ∈ A
        · simp [falseOnExtension, splitConfig, hwA]
        · simp [falseOnExtension, splitConfig, hwA, hOffP w hwP]
    · push Not at hOffP
      obtain ⟨w, hwP, hxy⟩ := hOffP
      have hzero : V x y = 0 := hV.1 x y ⟨w, hwP, hxy⟩
      have hwA : w ∉ A := by
        intro hwA
        have hw := congrFun hOn ⟨w, hwA⟩
        exact hxy hw
      have hzero' : offMatrixRestriction A V (splitConfig A x).2
          (splitConfig A y).2 = 0 := by
        apply hV.1
        refine ⟨w, hwP, ?_⟩
        simpa [falseOnExtension, splitConfig, hwA] using hxy
      exact hzero.trans hzero'.symm
  · rw [offMatrixLift, if_neg hOn]
    apply hV.1
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hOn
    refine ⟨w.1, ?_, ?_⟩
    · intro hwP
      exact (Finset.disjoint_left.mp hdisj) hwP w.2
    · simpa [splitConfig] using hw

/-- The complement factor of a supported unitary is unitary. -/
theorem offMatrixRestriction_unitary_of_isSiteSupported
    {A P : Finset Q} {V : Matrix (Config Q) (Config Q) ℂ}
    (hdisj : Disjoint P A) (hVsupport : IsSiteSupported P V)
    (hVunit : V ∈ Matrix.unitaryGroup (Config Q) ℂ) :
    offMatrixRestriction A V ∈ Matrix.unitaryGroup (Off A) ℂ := by
  let B := offMatrixRestriction A V
  have hEq : V = offMatrixLift A B :=
    eq_offMatrixLift_offMatrixRestriction_of_isSiteSupported hdisj hVsupport
  rw [Matrix.mem_unitaryGroup_iff] at hVunit ⊢
  rw [Matrix.star_eq_conjTranspose] at hVunit ⊢
  have hLiftEq : offMatrixLift A (B * Bᴴ) = offMatrixLift A 1 := by
    rw [offMatrixLift_mul, offMatrixLift_conjTranspose, offMatrixLift_one]
    simpa [hEq] using hVunit
  exact offMatrixLift_injective A hLiftEq

/-- Exact supported-unitary complement factorization. -/
theorem exists_unitary_offMatrixLift_of_isSiteSupported
    {A P : Finset Q} {V : Matrix (Config Q) (Config Q) ℂ}
    (hdisj : Disjoint P A) (hVsupport : IsSiteSupported P V)
    (hVunit : V ∈ Matrix.unitaryGroup (Config Q) ℂ) :
    ∃ B : Matrix (Off A) (Off A) ℂ,
      B ∈ Matrix.unitaryGroup (Off A) ℂ ∧ V = offMatrixLift A B := by
  exact ⟨offMatrixRestriction A V,
    offMatrixRestriction_unitary_of_isSiteSupported hdisj hVsupport hVunit,
    eq_offMatrixLift_offMatrixRestriction_of_isSiteSupported hdisj hVsupport⟩

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
