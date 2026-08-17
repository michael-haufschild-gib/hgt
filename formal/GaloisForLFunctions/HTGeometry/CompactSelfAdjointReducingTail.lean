import GaloisForLFunctions.HTGeometry.CompactOperatorGeneralSpectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum

open Complex Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem selfAdjoint_norm_or_neg_norm_mem_spectrum
    (T : E →L[ℂ] E) [Nontrivial E] (hT : IsSelfAdjoint T) :
    ((‖T‖ : ℂ) ∈ spectrum ℂ T) ∨ ((-‖T‖ : ℂ) ∈ spectrum ℂ T) := by
  simp_rw [spectrum, Set.mem_compl_iff]
  by_contra! h
  obtain ⟨c, hc0, hc⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
  grind [ciSup_le hc, ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT)]

/-- Peripheral spectral span of a compact operator at threshold `eps`. -/
def compactPeripheralSpectralSubspace (K : E →L[ℂ] E) (eps : ℝ) : Submodule ℂ E :=
  ⨆ mu : {mu : ℂ // mu ∈ spectrum ℂ K ∧ eps ≤ ‖mu‖},
    Module.End.eigenspace K.toLinearMap mu

set_option maxHeartbeats 1000000 in
/-- A compact self-adjoint operator has a finite-codimensional reducing tail on which its norm is
strictly below any positive threshold. -/
theorem exists_finiteCodimensional_reducing_strictContraction
    (K : E →L[ℂ] E) (hcompact : IsCompactOperator K) (hself : K.adjoint = K)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ M : Submodule ℂ E,
      IsClosed (M : Set E) ∧
      FiniteDimensional ℂ M.orthogonal ∧
      M.orthogonal = compactPeripheralSpectralSubspace K eps ∧
      (∀ x ∈ M, K x ∈ M) ∧
      (∀ x ∈ M.orthogonal, K x ∈ M.orthogonal) ∧
      ∀ x ∈ M, x ≠ 0 → ‖K x‖ < eps * ‖x‖ := by
  let I := {mu : ℂ // mu ∈ spectrum ℂ K ∧ eps ≤ ‖mu‖}
  have hIfinite : Set.Finite {mu : ℂ | mu ∈ spectrum ℂ K ∧ eps ≤ ‖mu‖} :=
    finite_setOf_mem_spectrum_norm_ge_general hcompact heps
  letI : Fintype I := hIfinite.fintype
  let N : Submodule ℂ E := ⨆ mu : I, Module.End.eigenspace K.toLinearMap mu
  letI heigFinite (mu : I) :
      FiniteDimensional ℂ (Module.End.eigenspace K.toLinearMap mu) := by
    have hmu0 : (mu : ℂ) ≠ 0 := by
      intro hzero
      have := mu.property.2
      rw [hzero, norm_zero] at this
      linarith
    exact ContinuousLinearMap.finite_dimensional_eigenspace hcompact mu hmu0
  letI : FiniteDimensional ℂ N := Submodule.finiteDimensional_iSup _
  have hNclosed : IsClosed (N : Set E) := N.closed_of_finiteDimensional
  let M : Submodule ℂ E := N.orthogonal
  have hMclosed : IsClosed (M : Set E) := N.isClosed_orthogonal
  have hMperp : M.orthogonal = N := by
    change N.orthogonal.orthogonal = N
    rw [Submodule.orthogonal_orthogonal_eq_closure, N.topologicalClosure_eq_self]
  have hKsymm : K.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (ContinuousLinearMap.isSelfAdjoint_iff'.mpr hself)
  have hNinv : ∀ x ∈ N, K x ∈ N := by
    intro x hx
    refine Submodule.iSup_induction
      (motive := fun z => K z ∈ N)
      (fun mu : I ↦ Module.End.eigenspace K.toLinearMap mu) hx ?_ ?_ ?_
    · intro mu y hy
      apply le_iSup (fun nu : I ↦ Module.End.eigenspace K.toLinearMap nu) mu
      exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem K.toLinearMap).mp
        (Module.End.eigenspace_mem_invtSubmodule K.toLinearMap mu) y hy
    · simp
    · intro x y hx hy
      simpa using N.add_mem hx hy
  have hMinv : ∀ x ∈ M, K x ∈ M := by
    intro x hx
    change x ∈ N.orthogonal at hx
    change K x ∈ N.orthogonal
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro n hn
    calc
      inner ℂ n (K x) = inner ℂ (K n) x := (hKsymm n x).symm
      _ = 0 := hx (K n) (hNinv n hn)
  have hMperpinv : ∀ x ∈ M.orthogonal, K x ∈ M.orthogonal := by
    rw [hMperp]
    exact hNinv
  have hMperpFinite : FiniteDimensional ℂ M.orthogonal := by
    rw [hMperp]
    infer_instance
  have hMperipheral : M.orthogonal = compactPeripheralSpectralSubspace K eps := by
    rw [hMperp]
    rfl
  letI : CompleteSpace M := hMclosed.completeSpace_coe
  let R : M →L[ℂ] M := K.restrict hMinv
  have hRcompact : IsCompactOperator R := hcompact.restrict' hMinv
  have hRself : IsSelfAdjoint R :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (hKsymm.restrict_invariant hMinv)
  have hRnorm : ‖R‖ < eps := by
    by_cases hsub : Subsingleton M
    · have hRzero : R = 0 := Subsingleton.elim _ _
      simpa [hRzero] using heps
    · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
      by_contra hnot
      have hepsle : eps ≤ ‖R‖ := le_of_not_gt hnot
      obtain hspec | hspec := selfAdjoint_norm_or_neg_norm_mem_spectrum R hRself
      · let mu : ℂ := (‖R‖ : ℂ)
        have hmu0 : mu ≠ 0 := by
          simpa [mu] using (lt_of_lt_of_le heps hepsle).ne'
        have heig : Module.End.HasEigenvalue R.toLinearMap mu :=
          (hRcompact.hasEigenvalue_iff_mem_spectrum hmu0).2 hspec
        obtain ⟨v, hv, hvne⟩ := heig.exists_hasEigenvector
        have hKv : K (v : E) = mu • (v : E) := by
          have := Module.End.mem_eigenspace_iff.mp hv
          exact congrArg Subtype.val this
        have hKheig : Module.End.HasEigenvalue K.toLinearMap mu :=
          Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hKv,
            fun hz => hvne (Subtype.ext hz)⟩
        have hmuspec : mu ∈ spectrum ℂ K :=
          (hcompact.hasEigenvalue_iff_mem_spectrum hmu0).1 hKheig
        let imu : I := ⟨mu, hmuspec, by
          simpa [mu, abs_of_nonneg (norm_nonneg R)] using hepsle⟩
        have hvN : (v : E) ∈ N := by
          apply le_iSup (fun nu : I ↦ Module.End.eigenspace K.toLinearMap nu) imu
          exact Module.End.mem_eigenspace_iff.mpr hKv
        have hz : inner ℂ (v : E) (v : E) = 0 :=
          (Submodule.mem_orthogonal N (v : E)).mp v.property (v : E) hvN
        exact hvne (Subtype.ext (inner_self_eq_zero.mp hz))
      · let mu : ℂ := (-‖R‖ : ℂ)
        have hmu0 : mu ≠ 0 := by
          simpa [mu] using (lt_of_lt_of_le heps hepsle).ne'
        have heig : Module.End.HasEigenvalue R.toLinearMap mu :=
          (hRcompact.hasEigenvalue_iff_mem_spectrum hmu0).2 hspec
        obtain ⟨v, hv, hvne⟩ := heig.exists_hasEigenvector
        have hKv : K (v : E) = mu • (v : E) := by
          have := Module.End.mem_eigenspace_iff.mp hv
          exact congrArg Subtype.val this
        have hKheig : Module.End.HasEigenvalue K.toLinearMap mu :=
          Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hKv,
            fun hz => hvne (Subtype.ext hz)⟩
        have hmuspec : mu ∈ spectrum ℂ K :=
          (hcompact.hasEigenvalue_iff_mem_spectrum hmu0).1 hKheig
        let imu : I := ⟨mu, hmuspec, by
          simpa [mu, abs_of_nonneg (norm_nonneg R)] using hepsle⟩
        have hvN : (v : E) ∈ N := by
          apply le_iSup (fun nu : I ↦ Module.End.eigenspace K.toLinearMap nu) imu
          exact Module.End.mem_eigenspace_iff.mpr hKv
        have hz : inner ℂ (v : E) (v : E) = 0 :=
          (Submodule.mem_orthogonal N (v : E)).mp v.property (v : E) hvN
        exact hvne (Subtype.ext (inner_self_eq_zero.mp hz))
  refine ⟨M, hMclosed, hMperpFinite, hMperipheral, hMinv, hMperpinv, ?_⟩
  intro x hx hxne
  let xm : M := ⟨x, hx⟩
  have hxmpos : 0 < ‖xm‖ := norm_pos_iff.mpr (fun h => hxne (congrArg Subtype.val h))
  calc
    ‖K x‖ = ‖R xm‖ := rfl
    _ ≤ ‖R‖ * ‖xm‖ := ContinuousLinearMap.le_opNorm R xm
    _ < eps * ‖xm‖ := mul_lt_mul_of_pos_right hRnorm hxmpos
    _ = eps * ‖x‖ := rfl

end GaloisForLFunctions.HTGeometry
