import GaloisForLFunctions.RHTower.SelfDualAnalyticRealZeros
import GaloisForLFunctions.RHTower.DirichletLZeroExistence
import GaloisForLFunctions.RHTower.MirrorPencil

noncomputable section

open Complex Set

namespace GaloisForLFunctions.RHTower

variable {N : ℕ} [NeZero N]

/-- Actual self-dual primitive nontrivial Dirichlet data.  These are completed automorphic
GL(1) L-functions, not abstract analytic carriers. -/
structure SelfDualPrimitiveDirichletDatum (N : ℕ) [NeZero N] where
  character : DirichletCharacter ℂ N
  nontrivial : character ≠ 1
  primitive : character.IsPrimitive
  selfDual : character⁻¹ = character

theorem SelfDualPrimitiveDirichletDatum.dirichletXi_differentiable
    (χ : SelfDualPrimitiveDirichletDatum N) :
    Differentiable ℂ (_root_.RHTower.dirichletXi χ.character) := by
  change Differentiable ℂ (fun s : ℂ =>
    (N : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ.character s)
  apply Differentiable.mul
  · apply Differentiable.const_cpow
      (differentiable_id.div_const (2 : ℂ))
    exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N))
  · exact DirichletCharacter.differentiable_completedLFunction χ.nontrivial

theorem SelfDualPrimitiveDirichletDatum.exists_dirichletXi_ne_zero
    (χ : SelfDualPrimitiveDirichletDatum N) :
    ∃ z, _root_.RHTower.dirichletXi χ.character z ≠ 0 := by
  obtain ⟨σ, _, hcompleted⟩ :=
    _root_.RHTower.exists_completedLFunction_ne_zero_ray (χ := χ.character)
  refine ⟨(σ : ℂ), ?_⟩
  rw [_root_.RHTower.dirichletXi]
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N))))
    hcompleted

/-- The analytic Real-zero family extracted from all actual nontrivial primitive self-dual
Dirichlet L-functions of fixed modulus. -/
def selfDualPrimitiveDirichletAnalyticFamily
    (radius : ℝ) (hradius : 0 ≤ radius) :
    CompletedSelfDualAnalyticFamily (SelfDualPrimitiveDirichletDatum N) where
  completed := fun χ => _root_.RHTower.dirichletXi χ.character
  center := 1 / 2
  radius := radius
  radius_nonneg := hradius
  analytic := fun χ => χ.dirichletXi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  nontrivial := SelfDualPrimitiveDirichletDatum.exists_dirichletXi_ne_zero
  rootNumber := fun χ => χ.character.rootNumber
  rootNumber_ne_zero := fun χ => _root_.RHTower.rootNumber_ne_zero χ.primitive
  functionalEquation := by
    intro χ z
    have h := _root_.RHTower.dirichletXi_one_sub χ.primitive z
    rw [χ.selfDual] at h
    convert h using 1
    all_goals norm_num

theorem selfDualPrimitiveDirichlet_defectRank_eq_analyticRank_add_twice_upper
    (radius : ℝ) (hradius : 0 ≤ radius)
    (χ : SelfDualPrimitiveDirichletDatum N) :
    SelfDualRealZeroFamily.defectRank
        (selfDualPrimitiveDirichletAnalyticFamily radius hradius).toSelfDualRealZeroFamily χ =
      (analyticOrderAt (_root_.RHTower.dirichletXi χ.character) (1 / 2 : ℂ)).toNat +
        2 * SelfDualRealZeroFamily.upperOffCentralMultiplicity
          (selfDualPrimitiveDirichletAnalyticFamily radius hradius).toSelfDualRealZeroFamily χ := by
  simpa [selfDualPrimitiveDirichletAnalyticFamily] using
    CompletedSelfDualAnalyticFamily.defectRank_eq_orderAt_center_add_twice_upper
      (selfDualPrimitiveDirichletAnalyticFamily radius hradius) χ

theorem selfDualPrimitiveDirichlet_analyticRank_parity_rootNumber
    (radius : ℝ) (hradius : 0 ≤ radius)
    (χ : SelfDualPrimitiveDirichletDatum N) :
    (-1 : ℂ) ^
        SelfDualRealZeroFamily.analyticRank
          (selfDualPrimitiveDirichletAnalyticFamily radius hradius).toSelfDualRealZeroFamily χ =
      χ.character.rootNumber := by
  exact CompletedSelfDualAnalyticFamily.analyticRank_parity_sign
    (selfDualPrimitiveDirichletAnalyticFamily radius hradius) χ

end GaloisForLFunctions.RHTower

