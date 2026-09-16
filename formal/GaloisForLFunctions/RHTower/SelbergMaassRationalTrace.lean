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

/-- A target subgroup whose every element is represented by an
orientation-preserving rational matrix. -/
def HasPositiveRationalLifts (H : Subgroup (GL (Fin 2) ℝ)) : Prop :=
  ∀ h : H, ∃ a : GL (Fin 2) ℚ,
    a.map (algebraMap ℚ ℝ) = h.val ∧ 0 < (a.map (algebraMap ℚ ℝ)).val.det

/-- The subgroup under which pullback by a rational matrix is invariant. -/
abbrev rationalPullbackConjugateGroup (Γ : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℚ) :
    Subgroup (GL (Fin 2) ℝ) :=
  ConjAct.toConjAct (g.map (algebraMap ℚ ℝ))⁻¹ • Γ

/-- Rational pullback transports invariant functions to the conjugated subgroup.
This is independent of a choice of congruence level. -/
def rationalMaassPullbackInvariant_general (Γ : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℚ)
    (f : glUpperHalfPlaneInvariantFunctions Γ) :
    glUpperHalfPlaneInvariantFunctions (rationalPullbackConjugateGroup Γ g) :=
  ⟨fun z => f.1 (g.map (algebraMap ℚ ℝ) • z), by
    intro γ z
    have hγ := γ.2
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hγ
    let h : GL (Fin 2) ℝ :=
      g.map (algebraMap ℚ ℝ) * γ.val * (g.map (algebraMap ℚ ℝ))⁻¹
    have hh : h ∈ Γ := by
      simpa only [h, ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul] using hγ
    change f.1 (g.map (algebraMap ℚ ℝ) • (γ.val • z)) =
      f.1 (g.map (algebraMap ℚ ℝ) • z)
    rw [← mul_smul]
    have hmul : g.map (algebraMap ℚ ℝ) * γ.val = h * g.map (algebraMap ℚ ℝ) := by
      dsimp only [h]
      group
    rw [hmul, mul_smul]
    exact f.2 ⟨h, hh⟩ _⟩

/-- Conjugating the source subgroup by two successive rational pullbacks is
conjugation by their product. -/
theorem rationalPullbackConjugateGroup_mul (Γ : Subgroup (GL (Fin 2) ℝ))
    (g h : GL (Fin 2) ℚ) :
    rationalPullbackConjugateGroup (rationalPullbackConjugateGroup Γ g) h =
      rationalPullbackConjugateGroup Γ (g * h) := by
  simp [rationalPullbackConjugateGroup, Matrix.GeneralLinearGroup.map_mul]
  rw [← mul_smul]

/-- Positivity of the real determinant is closed under rational matrix products. -/
theorem rationalGL_map_det_mul_pos (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det) :
    0 < ((g * h).map (algebraMap ℚ ℝ)).val.det := by
  rw [Matrix.GeneralLinearGroup.map_mul]
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul]
  exact mul_pos hg hh

/-- The conjugate subgroup on which a rational pullback of a principal source is invariant. -/
abbrev rationalConjugateGroup (N : ℕ) (g : GL (Fin 2) ℚ) :
    Subgroup (GL (Fin 2) ℝ) :=
  rationalPullbackConjugateGroup (principalCongruenceGL N) g

/-- The rational conjugate of the principal group has finite relative index in the
original principal group. -/
theorem rationalConjugateGroup_isFiniteRelIndex (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) := by
  apply Subgroup.IsFiniteRelIndex.mk
  have hg := rationalGL_mem_commensurator_principalCongruenceGL N g⁻¹
  rw [Subgroup.Commensurable.commensurator_mem_iff] at hg
  have hmap : g.map (algebraMap ℚ ℝ) = g.map (Rat.castHom ℝ) := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  unfold rationalConjugateGroup rationalPullbackConjugateGroup
  rw [hmap]
  simpa only [Matrix.GeneralLinearGroup.map_inv] using hg.1

/-- A rational conjugate principal subgroup is commensurable with the original
principal subgroup in both relative-index directions. -/
theorem rationalConjugateGroup_commensurable (N : ℕ) (g : GL (Fin 2) ℚ) :
    Subgroup.Commensurable (rationalConjugateGroup N g) (principalCongruenceGL N) := by
  have hg := rationalGL_mem_commensurator_principalCongruenceGL N g⁻¹
  rw [Subgroup.Commensurable.commensurator_mem_iff] at hg
  have hmap : g.map (algebraMap ℚ ℝ) = g.map (Rat.castHom ℝ) := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  unfold rationalConjugateGroup rationalPullbackConjugateGroup
  rw [hmap]
  simpa only [Matrix.GeneralLinearGroup.map_inv] using hg

/-- Any two rational conjugates of one principal subgroup are commensurable. -/
theorem rationalConjugateGroups_commensurable (N : ℕ) (g h : GL (Fin 2) ℚ) :
    Subgroup.Commensurable (rationalConjugateGroup N g) (rationalConjugateGroup N h) :=
  (rationalConjugateGroup_commensurable N g).trans
    (rationalConjugateGroup_commensurable N h).symm

/-- A finite trace is available in either direction between two rational conjugate
principal subgroups. -/
theorem rationalConjugateGroups_isFiniteRelIndex (N : ℕ) (g h : GL (Fin 2) ℚ) :
    (rationalConjugateGroup N g).IsFiniteRelIndex (rationalConjugateGroup N h) :=
  ⟨(rationalConjugateGroups_commensurable N g h).1⟩

/-- Every element of a rational conjugate principal subgroup is the real image
of an explicit rational invertible matrix. -/
theorem rationalConjugateGroup_exists_rational_lift (N : ℕ) (g : GL (Fin 2) ℚ)
    (γ : rationalConjugateGroup N g) :
    ∃ q : GL (Fin 2) ℚ, q.map (algebraMap ℚ ℝ) = γ.val := by
  have hγ := γ.2
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hγ
  let h : GL (Fin 2) ℝ :=
    g.map (algebraMap ℚ ℝ) * γ.val * (g.map (algebraMap ℚ ℝ))⁻¹
  have hh : h ∈ principalCongruenceGL N := by
    simpa only [h, ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul] using hγ
  obtain ⟨A, hA, hAeq⟩ := hh
  refine ⟨g⁻¹ * mapGL ℚ A * g, ?_⟩
  have hmapA : (mapGL ℚ A).map (algebraMap ℚ ℝ) = mapGL ℝ A := by
    simpa only [one_mul, map_one] using rationalGL_mul_integral_real (1 : GL (Fin 2) ℚ) A
  rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
    Matrix.GeneralLinearGroup.map_inv, hmapA]
  rw [hAeq]
  dsimp [h]
  group

/-- Rational conjugation preserves the determinant-one condition of the
principal subgroup. -/
theorem rationalConjugateGroup_det_eq_one (N : ℕ) (g : GL (Fin 2) ℚ)
    (γ : rationalConjugateGroup N g) :
    γ.val.det = 1 := by
  have hγ := γ.2
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hγ
  let h : GL (Fin 2) ℝ :=
    g.map (algebraMap ℚ ℝ) * γ.val * (g.map (algebraMap ℚ ℝ))⁻¹
  have hh : h ∈ principalCongruenceGL N := by
    simpa only [h, ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul] using hγ
  have hdet : GeneralLinearGroup.det h = 1 := Subgroup.HasDetOne.det_eq hh
  change GeneralLinearGroup.det γ.val = 1
  simpa [h, map_mul, mul_assoc] using hdet

/-- Every element of a rationally conjugated principal group has a rational
lift with positive real determinant. -/
theorem rationalConjugateGroup_exists_positive_rational_lift (N : ℕ) (g : GL (Fin 2) ℚ)
    (γ : rationalConjugateGroup N g) :
    ∃ q : GL (Fin 2) ℚ,
      q.map (algebraMap ℚ ℝ) = γ.val ∧ 0 < (q.map (algebraMap ℚ ℝ)).val.det := by
  obtain ⟨q, hq⟩ := rationalConjugateGroup_exists_rational_lift N g γ
  refine ⟨q, hq, ?_⟩
  rw [hq]
  have hdet := congrArg Units.val (rationalConjugateGroup_det_eq_one N g γ)
  norm_num at hdet
  rw [hdet]
  norm_num

/-- Every rationally conjugated principal group has positive rational lifts. -/
theorem rationalConjugateGroup_hasPositiveRationalLifts (N : ℕ) (g : GL (Fin 2) ℚ) :
    HasPositiveRationalLifts (rationalConjugateGroup N g) :=
  fun γ => rationalConjugateGroup_exists_positive_rational_lift N g γ

/-- Positive rational lifts descend to every mapped subgroup. -/
theorem HasPositiveRationalLifts.map_subgroup
    {H : Subgroup (GL (Fin 2) ℝ)} (hH : HasPositiveRationalLifts H)
    (J : Subgroup H) :
    HasPositiveRationalLifts (J.map H.subtype) := by
  intro γ
  rcases γ.2 with ⟨j, hj, hjEq⟩
  obtain ⟨a, ha, hapos⟩ := hH j
  refine ⟨a, ?_, hapos⟩
  change a.map (algebraMap ℚ ℝ) = γ.val
  rw [ha]
  exact hjEq

/-- Rational pullback invariance for zero-inclusive principal-level source data. -/
def rationalMaassPullbackInvariant_of_data (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    glUpperHalfPlaneInvariantFunctions (rationalConjugateGroup N g) :=
  rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f

/-- Rational pullback is invariant under the rationally conjugated principal group. -/
def rationalMaassPullbackInvariant (N : ℕ) (g : GL (Fin 2) ℚ)
    {lam : ℝ} (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    glUpperHalfPlaneInvariantFunctions (rationalConjugateGroup N g) :=
  rationalMaassPullbackInvariant_of_data N g f.1

/-- Positive rational pullback gives a nonzero Maass cusp eigenform for the
rationally conjugated principal group. -/
def rationalMaassPullback (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ)
    (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    GLMaassCuspEigenform (rationalConjugateGroup N g) lam :=
  ⟨rationalMaassPullbackInvariant N g f, by
    intro hpull
    apply f.2.1
    funext z
    have hz := congrFun hpull ((g.map (algebraMap ℚ ℝ))⁻¹ • z)
    calc
      f.1.1 z = f.1.1 ((g.map (algebraMap ℚ ℝ) * (g.map (algebraMap ℚ ℝ))⁻¹) • z) := by
        rw [mul_inv_cancel, one_smul]
      _ = f.1.1 (g.map (algebraMap ℚ ℝ) • ((g.map (algebraMap ℚ ℝ))⁻¹ • z)) := by
        rw [mul_smul]
      _ = 0 := by
        simpa only [rationalMaassPullbackInvariant, rationalMaassPullbackInvariant_of_data,
          rationalMaassPullbackInvariant_general, Pi.zero_apply] using hz,
    (rationalGL_maass_eigenfunction_cuspidal_pullback g hg lam f.1.1 f.2.2.1 f.2.2.2).1,
    (rationalGL_maass_eigenfunction_cuspidal_pullback g hg lam f.1.1 f.2.2.1 f.2.2.2).2⟩

/-- The rational trace function returned to the original principal group. -/
def rationalPrincipalTraceFunction (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ)
    (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) : ℍ → ℂ := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  exact maassTraceFunction (H := principalCongruenceGL N) (rationalMaassPullback N g hg lam f).1

/-- The rational trace with its exact target invariance, eigen-equation, and cusp decay. -/
def rationalPrincipalTraceData (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ)
    (f : GLMaassCuspEigenform (principalCongruenceGL N) lam) :
    {F : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N) //
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
  simpa only [rationalPrincipalTraceFunction] using
    principalMaassTrace_zero_or_eigenform N lam (rationalMaassPullback N g hg lam f)

end

end GaloisForLFunctions.RHTower
