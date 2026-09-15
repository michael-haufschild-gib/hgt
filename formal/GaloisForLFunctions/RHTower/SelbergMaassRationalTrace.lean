import GaloisForLFunctions.RHTower.SelbergMaassPrincipalTrace

/-!
# Rational finite trace of the actual principal Maass source

A positive rational matrix pulls a principal-congruence Maass source to its
conjugate subgroup. That subgroup has finite relative index in the original
principal group, so the finite principal trace returns an invariant Maass object
at the original level. The trace can vanish; no Hecke eigenvector or adelic lift
is asserted here.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- The conjugate subgroup on which a rational pullback of a principal source is invariant. -/
abbrev rationalConjugateGroup (N : ℕ) (g : GL (Fin 2) ℚ) :
    Subgroup (GL (Fin 2) ℝ) :=
  ConjAct.toConjAct (g.map (algebraMap ℚ ℝ))⁻¹ • principalCongruenceGL N

/-- The rational conjugate of the principal group has finite relative index in the
original principal group. -/
theorem rationalConjugateGroup_isFiniteRelIndex (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) := by
  apply Subgroup.IsFiniteRelIndex.mk
  have hg := rationalGL_mem_commensurator_principalCongruenceGL N g⁻¹
  rw [Subgroup.Commensurable.commensurator_mem_iff] at hg
  simpa only [Matrix.GeneralLinearGroup.map_inv] using hg.1

/-- Rational pullback is invariant under the rationally conjugated principal group. -/
def rationalMaassPullbackInvariant (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ} (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    upperHalfPlaneInvariantFunctions (rationalConjugateGroup N g) :=
  ⟨fun z => f.1.1 (g.map (algebraMap ℚ ℝ) • z), by
    intro γ z
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at γ
    let h : GL (Fin 2) ℝ :=
      g.map (algebraMap ℚ ℝ) * γ.val * (g.map (algebraMap ℚ ℝ))⁻¹
    have hh : h ∈ principalCongruenceGL N := by
      simpa only [h, ConjAct.toConjAct_smul] using γ.2
    change f.1.1 (g.map (algebraMap ℚ ℝ) • (γ.val • z)) =
      f.1.1 (g.map (algebraMap ℚ ℝ) • z)
    rw [← mul_smul]
    have hmul : g.map (algebraMap ℚ ℝ) * γ.val = h * g.map (algebraMap ℚ ℝ) := by
      dsimp only [h]
      group
    rw [hmul, mul_smul]
    exact f.1.2 ⟨h, hh⟩ _⟩

/-- Positive rational pullback gives a nonzero Maass cusp eigenform for the
rationally conjugated principal group. -/
def rationalMaassPullback (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ)
    (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    GLMaassCuspEigenform (rationalConjugateGroup N g) lam :=
  ⟨rationalMaassPullbackInvariant N g f, by
    intro hpull
    apply f.2.1
    apply Subtype.ext
    funext z
    have hz := congrArg (fun F : upperHalfPlaneInvariantFunctions (rationalConjugateGroup N g) =>
      F.1 ((g.map (algebraMap ℚ ℝ))⁻¹ • z)) hpull
    simpa only [rationalMaassPullbackInvariant, ZeroMemClass.coe_zero, Pi.zero_apply,
      mul_smul, inv_mul_cancel, one_smul] using hz,
    (rationalGL_maass_eigenfunction_cuspidal_pullback g hg lam f.1.1 f.2.2.1 f.2.2.2).1,
    (rationalGL_maass_eigenfunction_cuspidal_pullback g hg lam f.1.1 f.2.2.1 f.2.2.2).2⟩

/-- The rational trace function returned to the original principal group. -/
def rationalPrincipalTraceFunction (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ)
    (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) : ℍ → ℂ := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  exact maassTraceFunction (rationalMaassPullback N g hg lam f).1

/-- The rational trace with its exact target invariance, eigen-equation, and cusp decay. -/
def rationalPrincipalTraceData (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ)
    (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    {F : upperHalfPlaneInvariantFunctions (principalCongruenceGL N) //
      IsMaassEigenfunction lam F.1 ∧ IsCuspidalAtIntegralCusps F.1} := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  exact principalMaassTraceData N lam (rationalMaassPullback N g hg lam f)

/-- The rational principal trace either vanishes or gives a nonzero Maass cusp
 eigenform at the original principal level and eigenvalue. -/
theorem rationalPrincipalTrace_zero_or_eigenform (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ)
    (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    rationalPrincipalTraceFunction N g hg lam f = 0 ∨
      ∃ F : GLMaassCuspEigenform (principalCongruenceGL N) lam,
        F.1.1 = rationalPrincipalTraceFunction N g hg lam f := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  exact principalMaassTrace_zero_or_eigenform N lam (rationalMaassPullback N g hg lam f)

end

end GaloisForLFunctions.RHTower
