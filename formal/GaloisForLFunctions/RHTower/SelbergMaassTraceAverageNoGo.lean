import GaloisForLFunctions.RHTower.SelbergMaassBoundaryPositivity
import GaloisForLFunctions.RHTower.SelbergMaassGLCorrespondence
import GaloisForLFunctions.RHTower.SelbergMaassRationalTrace

/-!
# Positive rational-trace averages cannot supply compact-core coercivity

Every nonzero rational trace lands again in the principal Maass eigenspace.  At an exceptional
eigenvalue its canonical compact-core quarter form is strictly negative after the Bessel
transition.  Hence no finite positive average of such outputs can prove the missing nonnegative
core bound: it has the opposite sign term-by-term.
-/

namespace GaloisForLFunctions.RHTower

open SelbergMaassBoundaryPositivity SelbergMaassTraceArea

noncomputable section

/-- Every exceptional principal-level `GL(2, ℝ)` Maass source has strictly negative compact-core
quarter form at the canonical Bessel cutoff. -/
theorem glPrincipal_coreQuarter_strict_neg_at_transitionCutoff
    (N : ℕ) (lam : Set.Ioo (0 : ℝ) (1 / 4))
    (f : GLMaassCuspEigenform (principalCongruenceGL N) (lam : ℝ)) :
    coreQuarter N
      (glIntegralMaassCuspEigenformToMaass (CongruenceSubgroup.Gamma (N + 1)) lam f)
      (Real.exp (transitionCutoff N)) < 0 :=
  coreQuarter_strict_neg_at_transitionCutoff N lam
    (glIntegralMaassCuspEigenformToMaass (CongruenceSubgroup.Gamma (N + 1)) lam f)

/-- A rational principal trace of an exceptional source vanishes or has strictly negative
compact-core quarter form at the canonical cutoff. -/
theorem rationalPrincipalTrace_zero_or_coreQuarter_strict_neg_at_transitionCutoff
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : Set.Ioo (0 : ℝ) (1 / 4))
    (f : GLMaassCuspEigenform (principalCongruenceGL N) (lam : ℝ)) :
    rationalPrincipalTraceFunction N g hg (lam : ℝ) f = 0 ∨
      ∃ F : GLMaassCuspEigenform (principalCongruenceGL N) (lam : ℝ),
        F.1.1 = rationalPrincipalTraceFunction N g hg (lam : ℝ) f ∧
          coreQuarter N
            (glIntegralMaassCuspEigenformToMaass (CongruenceSubgroup.Gamma (N + 1)) lam F)
            (Real.exp (transitionCutoff N)) < 0 := by
  rcases rationalPrincipalTrace_zero_or_eigenform N g hg (lam : ℝ) f with hzero | ⟨F, hF⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨F, hF, glPrincipal_coreQuarter_strict_neg_at_transitionCutoff N lam F⟩

/-- A finite positively weighted family of exceptional principal-level Maass sources has
strictly negative total compact-core quarter form at the canonical Bessel cutoff. -/
theorem weighted_coreQuarter_sum_strict_neg_at_transitionCutoff
    {ι : Type*} (N : ℕ) (lam : Set.Ioo (0 : ℝ) (1 / 4)) (s : Finset ι)
    (w : ι → ℝ)
    (f : ι → GLMaassCuspEigenform (principalCongruenceGL N) (lam : ℝ))
    (hw : ∀ i ∈ s, 0 ≤ w i) (hpos : ∃ i ∈ s, 0 < w i) :
    ∑ i ∈ s, w i * coreQuarter N
      (glIntegralMaassCuspEigenformToMaass (CongruenceSubgroup.Gamma (N + 1)) lam (f i))
      (Real.exp (transitionCutoff N)) < 0 := by
  apply Finset.sum_neg'
  · intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hw i hi)
      (le_of_lt (glPrincipal_coreQuarter_strict_neg_at_transitionCutoff N lam (f i)))
  · obtain ⟨i, hi, hwi⟩ := hpos
    have hcore := glPrincipal_coreQuarter_strict_neg_at_transitionCutoff N lam (f i)
    exact ⟨i, hi, mul_neg_of_pos_of_neg hwi hcore⟩

end

end GaloisForLFunctions.RHTower
