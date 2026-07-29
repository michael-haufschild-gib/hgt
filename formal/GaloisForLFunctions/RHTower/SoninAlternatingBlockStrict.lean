/-
Strictness of the alternating block for two Hilbert-space constraints.

The block `P_B P_A P_B` is a positive self-adjoint contraction.  If it is compact and has no
eigenvalue one, its norm is strictly below one.  This converts the two analytic facts in the
time--band problem -- compactness and the bounded-support uncertainty theorem -- into the strict
contraction required by `SoninProjectionCorrection`.
-/
import GaloisForLFunctions.RHTower.SoninProjectionCorrection
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The alternating block `P_B P_A P_B` is symmetric. -/
theorem soninAlternatingBlock_isSymmetric
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection] :
    (soninAlternatingBlock A B : H →ₗ[ℂ] H).IsSymmetric := by
  intro x y
  change inner ℂ (B.starProjection (A.starProjection (B.starProjection x))) y =
    inner ℂ x (B.starProjection (A.starProjection (B.starProjection y)))
  rw [B.inner_starProjection_left_eq_right]
  rw [A.inner_starProjection_left_eq_right]
  rw [B.inner_starProjection_left_eq_right]

/-- The quadratic form of the alternating block is nonnegative. -/
theorem soninAlternatingBlock_re_inner_nonneg
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection] (x : H) :
    0 ≤ Complex.re (inner ℂ x (soninAlternatingBlock A B x)) := by
  change 0 ≤ Complex.re (inner ℂ x
    (B.starProjection (A.starProjection (B.starProjection x))))
  rw [← B.inner_starProjection_left_eq_right]
  have h := A.re_inner_starProjection_nonneg (B.starProjection x)
  simpa [inner_re_symm] using h

/-- The alternating block is a contraction. -/
theorem norm_soninAlternatingBlock_le_one
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection] :
    ‖soninAlternatingBlock A B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  calc
    ‖soninAlternatingBlock A B x‖
        = ‖B.starProjection (A.starProjection (B.starProjection x))‖ := rfl
    _ ≤ ‖A.starProjection (B.starProjection x)‖ := B.norm_starProjection_apply_le _
    _ ≤ ‖B.starProjection x‖ := A.norm_starProjection_apply_le _
    _ ≤ ‖x‖ := B.norm_starProjection_apply_le _
    _ = 1 * ‖x‖ := by ring

/-- A vector fixed by an alternating projection block lies in both projected subspaces.  This is
the eigenvalue-one sector before any common-mode subtraction. -/
theorem mem_inf_of_soninAlternatingBlock_apply_eq_self
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    {x : H} (hx : soninAlternatingBlock A B x = x) :
    x ∈ A ⊓ B := by
  have hxB : x ∈ B := by
    rw [← hx]
    exact B.starProjection_apply_mem _
  have hBx : B.starProjection x = x := B.starProjection_eq_self_iff.mpr hxB
  have hnorm_ge : ‖x‖ ≤ ‖A.starProjection x‖ := by
    calc
      ‖x‖ = ‖soninAlternatingBlock A B x‖ := congrArg norm hx.symm
      _ = ‖B.starProjection (A.starProjection (B.starProjection x))‖ := rfl
      _ = ‖B.starProjection (A.starProjection x)‖ := by rw [hBx]
      _ ≤ ‖A.starProjection x‖ := B.norm_starProjection_apply_le _
  have hnorm_eq : ‖A.starProjection x‖ = ‖x‖ :=
    le_antisymm (A.norm_starProjection_apply_le x) hnorm_ge
  have hxA : x ∈ A := (A.mem_iff_norm_starProjection x).mpr hnorm_eq
  exact ⟨hxA, hxB⟩

/-- Compactness of the two-factor block `P_B P_A` propagates to the alternating block
`P_B P_A P_B`. -/
theorem isCompactOperator_soninAlternatingBlock_of_compact_left
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hBA : IsCompactOperator (B.starProjection * A.starProjection)) :
    IsCompactOperator (soninAlternatingBlock A B) := by
  simpa [soninAlternatingBlock, Function.comp_def] using!
    hBA.comp_clm B.starProjection

/-- If the two forbidden subspaces have trivial intersection, the alternating block has no
eigenvalue one. -/
theorem not_hasEigenvalue_one_soninAlternatingBlock_of_inf_eq_bot
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hAB : A ⊓ B = ⊥) :
    ¬ Module.End.HasEigenvalue (soninAlternatingBlock A B : H →ₗ[ℂ] H) 1 := by
  intro heig
  obtain ⟨x, hx, hxne⟩ := heig.exists_hasEigenvector
  simp only [Module.End.mem_genEigenspace_one, one_smul] at hx
  have hxinf : x ∈ A ⊓ B := mem_inf_of_soninAlternatingBlock_apply_eq_self A B hx
  rw [hAB] at hxinf
  exact hxne (by simpa using hxinf)

variable [CompleteSpace H] [Nontrivial H]

/-- A compact positive symmetric contraction with no eigenvalue one is strictly contractive.
This is the reusable spectral core of the alternating-block strictness argument. -/
theorem norm_lt_one_of_compact_of_symmetric_of_nonnegative_of_not_eigenvalue_one
    (T : H →L[ℂ] H)
    (hle : ‖T‖ ≤ 1)
    (hcompact : IsCompactOperator T)
    (hsymm : (T : H →ₗ[ℂ] H).IsSymmetric)
    (hnonneg : ∀ x, 0 ≤ Complex.re (inner ℂ x (T x)))
    (hno : ¬ Module.End.HasEigenvalue (T : H →ₗ[ℂ] H) 1) :
    ‖T‖ < 1 := by
  by_contra hnot
  have hnorm : ‖T‖ = 1 := le_antisymm hle (le_of_not_gt hnot)
  obtain ⟨μ, hμspec, hμrad⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty T)
  have hμnorm : ‖μ‖ = 1 := by
    have hsrad := T.spectralRadius_eq_nnnorm hsymm.isSelfAdjoint
    rw [hsrad] at hμrad
    have hμnn : ‖μ‖₊ = ‖T‖₊ := ENNReal.coe_injective hμrad
    calc
      ‖μ‖ = (‖μ‖₊ : ℝ) := rfl
      _ = (‖T‖₊ : ℝ) := congrArg (fun r : NNReal => (r : ℝ)) hμnn
      _ = ‖T‖ := rfl
      _ = 1 := hnorm
  have hμne : μ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hμnorm
    norm_num at hμnorm
  have hμeig : Module.End.HasEigenvalue (T : H →ₗ[ℂ] H) μ :=
    (hcompact.hasEigenvalue_iff_mem_spectrum hμne).mpr hμspec
  have hμreal : (μ.re : ℂ) = μ :=
    Complex.conj_eq_iff_re.mp (hsymm.conj_eigenvalue_eq_self hμeig)
  have hreig : Module.End.HasEigenvalue (T : H →ₗ[ℂ] H) μ.re := by
    simpa [hμreal] using hμeig
  have hrnonneg : 0 ≤ μ.re := eigenvalue_nonneg_of_nonneg hreig hnonneg
  have hrabs : |μ.re| = 1 := by
    rw [← hμreal, Complex.norm_real, Real.norm_eq_abs] at hμnorm
    exact hμnorm
  have hre : μ.re = 1 := by
    rw [abs_of_nonneg hrnonneg] at hrabs
    exact hrabs
  apply hno
  simpa [hre] using hreig

/-- A compact alternating block without eigenvalue one is a strict contraction. -/
theorem norm_soninAlternatingBlock_lt_one_of_compact_of_not_eigenvalue_one
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (soninAlternatingBlock A B))
    (hno : ¬ Module.End.HasEigenvalue (soninAlternatingBlock A B : H →ₗ[ℂ] H) 1) :
    ‖soninAlternatingBlock A B‖ < 1 :=
  norm_lt_one_of_compact_of_symmetric_of_nonnegative_of_not_eigenvalue_one
    (soninAlternatingBlock A B)
    (norm_soninAlternatingBlock_le_one A B)
    hcompact
    (soninAlternatingBlock_isSymmetric A B)
    (soninAlternatingBlock_re_inner_nonneg A B)
    hno

/-- Compactness plus trivial intersection makes the alternating block a strict contraction. -/
theorem norm_soninAlternatingBlock_lt_one_of_compact_of_inf_eq_bot
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (soninAlternatingBlock A B)) (hAB : A ⊓ B = ⊥) :
    ‖soninAlternatingBlock A B‖ < 1 :=
  norm_soninAlternatingBlock_lt_one_of_compact_of_not_eigenvalue_one A B hcompact
    (not_hasEigenvalue_one_soninAlternatingBlock_of_inf_eq_bot A B hAB)

end RHTower
