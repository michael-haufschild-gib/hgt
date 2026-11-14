import GaloisForLFunctions.RHTower.OperatorTheory.HexablockTranslationCompact
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninToeplitzKernel
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninCutoffTraceFormula

/-!
# Hexablock coordinates of physical CCM dilations

The physical logarithmic dilation group on even `L²` satisfies both polynomial
parametrizations. Logarithmic conjugacy transfers the absence of translation
eigenvectors. Consequently the only compact Brown–Halmos operators at a
nonzero dilation parameter are zero.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.Hexablock
open ContinuousLinearMap

private theorem dilation_star (u : ℝ) : star (ccmLogDilation u) = ccmLogDilation (-u) := by
  rw [_root_.ContinuousLinearMap.star_eq_adjoint, adjoint_ccmLogDilation]

private theorem dilation_isometry (u : ℝ) : star (ccmLogDilation u) * ccmLogDilation u = 1 := by
  rw [dilation_star]
  change ccmLogDilation (-u) ∘L ccmLogDilation u = 1
  rw [ccmLogDilation_comp, neg_add_cancel, ccmLogDilation_zero]

private theorem dilation_coisometry (u : ℝ) : ccmLogDilation u * star (ccmLogDilation u) = 1 := by
  rw [dilation_star]
  change ccmLogDilation u ∘L ccmLogDilation (-u) = 1
  rw [ccmLogDilation_comp, add_neg_cancel, ccmLogDilation_zero]

private theorem dilation_commute (u v : ℝ) : Commute (ccmLogDilation u) (ccmLogDilation v) := by
  change ccmLogDilation u ∘L ccmLogDilation v = ccmLogDilation v ∘L ccmLogDilation u
  rw [ccmLogDilation_comp, ccmLogDilation_comp, add_comm]

/-- Four physical dilation parameters satisfy the hexablock energy and cross relations. -/
theorem hexablock_ccmDilation_relations (b c d e : ℝ) :
    let u := ccmLogDilation b
    let v := ccmLogDilation c
    let w := ccmLogDilation d
    let z := ccmLogDilation e
    (star (a u w) * a u w + star (x₁ u v) * x₁ u v = 1) ∧
    (star (a u w) * a u w + star (x₂ u w z) * x₂ u w z = 1) ∧
    star (x₃ u v w z) * x₃ u v w z = 1 ∧
    star (x₁ u v) * x₃ u v w z = x₂ u w z := by
  dsimp only
  obtain ⟨h₁, h₂, h₃⟩ := energy _ _ _ _ (dilation_isometry b) (dilation_isometry c)
    (dilation_isometry d) (dilation_isometry e)
  exact ⟨h₁, h₂, h₃, cross _ _ _ _ (dilation_isometry b) (dilation_isometry c)
    (dilation_commute b c) (dilation_commute b d) (dilation_commute b e)⟩

/-- Three physical dilations satisfy the tetrablock coordinate identities. -/
theorem tetrablock_ccmDilation_relations (b c d : ℝ) :
    let u := ccmLogDilation b
    let v := ccmLogDilation c
    let z := ccmLogDilation d
    (star (halfDiff u v) * halfDiff u v +
      star (Tetrablock.x₂ u v) * Tetrablock.x₂ u v = 1) ∧
    (star (Tetrablock.x₂ u v) * Tetrablock.x₃ u v z = Tetrablock.x₁ u v z) ∧
    star (Tetrablock.x₃ u v z) * Tetrablock.x₃ u v z = 1 := by
  dsimp only
  exact ⟨Tetrablock.energy _ _ (dilation_isometry b) (dilation_isometry c),
    Tetrablock.cross _ _ _ (dilation_isometry b) (dilation_isometry c)
      (dilation_commute b c) (dilation_commute b d) (dilation_commute c d),
    Tetrablock.last_isometry _ _ _ (dilation_isometry b) (dilation_isometry c) (dilation_isometry d)⟩

/-- A nonzero physical logarithmic dilation has no eigenvectors. -/
theorem ccmLogDilation_hasNoEigenvectors {u : ℝ} (hu : u ≠ 0) :
    HasNoEigenvectors (evenDilationUnitary (Real.exp (-u)) (Real.exp_pos (-u))) := by
  intro x μ hx
  have h := congrArg logEvenUnitary hx
  change logEvenUnitary (ccmLogDilationOrbit x u) = logEvenUnitary (μ • x) at h
  rw [logEvenUnitary_ccmLogDilationOrbit, map_smul] at h
  have hz := additiveTranslation_hasNoEigenvectors (neg_ne_zero.mpr hu) _ _ h
  apply logEvenUnitary.injective
  simpa only [map_zero] using hz

/-- Compact fixed operators have the exact zero-parameter boundary in the physical scaling model. -/
theorem hexablock_ccmDilation_compact_iff (u : ℝ) (T : evenSubspace →L[ℂ] evenSubspace) :
    (BrownHalmos (halfDiff (ccmLogDilation u) 1) (halfSum (ccmLogDilation u) 1)
      (halfSum (ccmLogDilation u) 1) (ccmLogDilation u) T ∧ IsCompactOperator T) ↔
      IsCompactOperator T ∧ (u = 0 ∨ T = 0) := by
  rw [slice_brownHalmos_iff]
  constructor
  · rintro ⟨hfix, hc⟩
    refine ⟨hc, ?_⟩
    by_cases hu : u = 0
    · exact Or.inl hu
    · right
      have hcomm : T * ccmLogDilation u = ccmLogDilation u * T := by
        calc
          T * ccmLogDilation u = ccmLogDilation u *
              (star (ccmLogDilation u) * T * ccmLogDilation u) := by
            rw [← mul_assoc, ← mul_assoc, dilation_coisometry, one_mul]
          _ = ccmLogDilation u * T := by rw [hfix]
      apply eq_zero_of_isCompactOperator_of_comm (ccmLogDilation_hasNoEigenvectors hu) hc
      intro x
      exact congrArg (fun R : evenSubspace →L[ℂ] evenSubspace => R x) hcomm
  · rintro ⟨hc, hu | hT⟩
    · subst u
      refine ⟨?_, hc⟩
      rw [ccmLogDilation_zero]
      change star (1 : evenSubspace →L[ℂ] evenSubspace) * T * 1 = T
      simp only [star_one, one_mul, mul_one]
    · subst T
      exact ⟨by simp only [mul_zero, zero_mul], hc⟩

end RHTower

#print axioms RHTower.hexablock_ccmDilation_relations
#print axioms RHTower.tetrablock_ccmDilation_relations
#print axioms RHTower.ccmLogDilation_hasNoEigenvectors
#print axioms RHTower.hexablock_ccmDilation_compact_iff
