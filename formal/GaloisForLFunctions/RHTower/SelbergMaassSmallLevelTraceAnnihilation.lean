import GaloisForLFunctions.RHTower.SelbergMaassHeckeEigenspace
import GaloisForLFunctions.RHTower.SelbergMaassStripGap

/-!
# Small-level annihilation of exceptional Maass traces

The strip argument excludes exceptional Maass cusp eigenforms at principal
levels one through seven. Consequently any finite principal trace from an
exceptional Maass source to one of those targets must vanish: a nonzero trace
would itself be an exceptional target-level cusp form. The zero-inclusive
form states that the entire finite trace operator is zero.

This isolates the surviving part of the Selberg route. It does not descend an
arbitrary-level form, construct a newspace decomposition, or impose a local
factor condition on the joint trace-zero component.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups ContDiff

noncomputable section

/-- Every finite principal trace to a principal level from one through seven
annihilates an exceptional Maass cusp eigenform. -/
theorem small_level_principalMaassTrace_eq_zero
    (m : Fin 7) {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [𝒢.IsFiniteRelIndex (principalCongruenceGL m)]
    (lam : Ioo (0 : ℝ) (1 / 4))
    (f : GLMaassCuspEigenform 𝒢 (lam : ℝ)) :
    maassTraceFunction (H := principalCongruenceGL m) f.1 = 0 := by
  rcases principalMaassTrace_zero_or_eigenform m (lam : ℝ) f with hzero | ⟨F, hF⟩
  · exact hzero
  · let fsmall := glIntegralMaassCuspEigenformToMaass
      (CongruenceSubgroup.Gamma (m.val + 1)) (lam : ℝ) F
    exact (SelbergMaassStripGap.small_level_no_exceptional m lam).elim fsmall

/-- On a sub-quarter eigenspace, the complete finite trace linear map to every
principal level from one through seven is zero. -/
theorem small_level_principalMaassTraceLinear_eq_zero
    (m : Fin 7) {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [𝒢.IsFiniteRelIndex (principalCongruenceGL m)]
    (lam : Ioo (0 : ℝ) (1 / 4)) :
    @principalMaassTraceLinear (m : ℕ) (lam : ℝ) 𝒢 _ = 0 := by
  ext u z
  by_cases hu : u = 0
  · subst u
    change maassTraceFunction (H := principalCongruenceGL m)
      (maassEigenspaceToInvariant (0 : glMaassCuspEigenspace 𝒢 (lam : ℝ))) z = 0
    rw [show maassEigenspaceToInvariant
      (0 : glMaassCuspEigenspace 𝒢 (lam : ℝ)) = 0 by rfl, principalMaassTrace_zero]
    rfl
  · let F : GLMaassCuspEigenform 𝒢 (lam : ℝ) :=
      ⟨maassEigenspaceToInvariant u, by
        refine ⟨?_, u.2.2.1, u.2.2.2⟩
        intro hzero
        apply hu
        apply Subtype.ext
        exact hzero⟩
    change maassTraceFunction (H := principalCongruenceGL m)
      (maassEigenspaceToInvariant u) z = 0
    simpa only [F, Pi.zero_apply] using
      congrFun (small_level_principalMaassTrace_eq_zero m lam F) z

end

end GaloisForLFunctions.RHTower
