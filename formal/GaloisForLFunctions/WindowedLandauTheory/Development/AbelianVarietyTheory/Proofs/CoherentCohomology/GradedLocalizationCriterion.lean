import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedPresentations
import Mathlib.Algebra.Module.LocalizedModule.Away

/-! For a graded map, the universal properties of localization can be checked on homogeneous elements. -/

open DirectSum MvPolynomial

namespace GlobalTheory

variable {ι R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module (MvPolynomial ι R) M] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  {D : ℤ → Submodule R M} {E : ℤ → Submodule R N}
  [Decomposition D] [Decomposition E] [PolyGradedSMul ι E]
  {u : MvPolynomial ι R} {d : ℤ} (hu : u ∈ polyGrading ι R d)

private theorem isUnit_of_homogeneous_smul
    (hinj : ∀ j, ∀ y ∈ E j, u • y = 0 → y = 0)
    (hsurj : ∀ j, ∀ y ∈ E (j + d), ∃ z ∈ E j, u • z = y) :
    IsUnit (algebraMap (MvPolynomial ι R) (Module.End (MvPolynomial ι R) N) u) := by
  classical
  rw [Module.End.isUnit_iff]
  change Function.Bijective (LinearMap.lsmul (MvPolynomial ι R) N u)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    change u • y = 0 at hy
    rw [← sum_support_gradedProj E y]
    refine Finset.sum_eq_zero fun j _ => hinj j _ (gradedProj_mem E j y) ?_
    have e := proj_smul_of_mem (D := E) hu j y
    rw [hy, map_zero] at e
    exact e.symm
  · intro y
    induction y using Decomposition.inductionOn E with
    | zero => exact ⟨0, map_zero _⟩
    | @homogeneous j y =>
      obtain ⟨x, _, h⟩ := hsurj (j - d) y (by rwa [sub_add_cancel])
      exact ⟨x, h⟩
    | add a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x + y, map_add _ _ _⟩

theorem isLocalizedModuleAway_of_graded
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap D E f)
    (hinj : ∀ j, ∀ y ∈ E j, u • y = 0 → y = 0)
    (hsurj : ∀ j, ∀ y ∈ E (j + d), ∃ z ∈ E j, u • z = y)
    (hlift : ∀ j, ∀ y ∈ E j, ∃ (k : ℕ) x, u ^ k • y = f x)
    (hkill : ∀ j, ∀ x ∈ D j, f x = 0 → ∃ k : ℕ, u ^ k • x = 0) :
    IsLocalizedModule.Away u f := by
  classical
  refine IsLocalizedModule.Away.mk_of_addCommGroup (isUnit_of_homogeneous_smul hu hinj hsurj) ?_ ?_
  · intro y
    induction y using Decomposition.inductionOn E with
    | zero => exact ⟨0, 0, by rw [smul_zero, map_zero]⟩
    | homogeneous y => exact hlift _ y y.2
    | add y z hy hz =>
      obtain ⟨k, a, ha⟩ := hy
      obtain ⟨l, b, hb⟩ := hz
      refine ⟨k + l, u ^ l • a + u ^ k • b, ?_⟩
      simp only [smul_add, map_add, map_smul, ← ha, ← hb, smul_smul, ← pow_add, add_comm l k]
  · intro x hx
    have step (j : ℤ) : ∃ k : ℕ, u ^ k • gradedProj D j x = 0 := by
      apply hkill j _ (gradedProj_mem D j x)
      rw [← hf.proj_apply, hx, map_zero]
    choose k hk using step
    let s := (decompose D x).support
    refine ⟨s.sup k, ?_⟩
    rw [← sum_support_gradedProj D x, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hle : k i ≤ s.sup k := Finset.le_sup hi
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hk, smul_zero]

end GlobalTheory
