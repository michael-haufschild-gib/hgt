import GaloisForLFunctions.HTGeometry.PaperFiniteNegativePart
import GaloisForLFunctions.HTGeometry.CfcEigenvectorRankOneAssembly

/-! # The full above-one spectral space of a compact self-adjoint operator

The range of the canonical negative part of `1-K` is exactly the sum of all
eigenspaces of `K` above one, with their full multiplicities. Compactness makes
this entire spectral subspace finite-dimensional.
-/

noncomputable section

open scoped CStarAlgebra

namespace GaloisForLFunctions.HTGeometry.PaperNegativePart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def aboveOneSpace (K : E →L[ℂ] E) : Submodule ℂ E :=
  ⨆ t : {t : ℝ // 1 < t}, Module.End.eigenspace K.toLinearMap (t.val : ℂ)

theorem repair_apply_eigenvector (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    {t : ℝ} {x : E} (hx : Q x = (t : ℂ) • x) :
    repair Q x = ((max (-t) 0 : ℝ) : ℂ) • x := by
  rw [repair, CFC.negPart_def, cfcₙ_eq_cfc]
  exact cfc_apply_eigenvector_rankOne Q hQ hx (by fun_prop)

theorem aboveOneSpace_le_negativeSpace (K : E →L[ℂ] E) (hK : IsSelfAdjoint K) :
    aboveOneSpace K ≤ negativeSpace (1 - K) := by
  apply iSup_le
  intro t x hx
  have hKx := Module.End.mem_eigenspace_iff.1 hx
  change K x = (t.val : ℂ) • x at hKx
  have hQx : (1 - K : E →L[ℂ] E) x = ((1 - t.val : ℝ) : ℂ) • x := by
    rw [sub_apply, one_apply_eq_self, hKx]
    push_cast
    module
  have hC := repair_apply_eigenvector (1 - K) ((IsSelfAdjoint.one _).sub hK) hQx
  have hm : max (-(1 - t.val)) 0 = t.val - 1 := by
    rw [max_eq_left (by linarith [t.property])]
    ring
  rw [hm] at hC
  have hc : ((t.val - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (sub_pos.2 t.property)
  refine ⟨((t.val - 1 : ℝ) : ℂ)⁻¹ • x, ?_⟩
  change repair (1 - K) (((t.val - 1 : ℝ) : ℂ)⁻¹ • x) = x
  rw [map_smul, hC, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem compact_preserves_negativeSpace (K : E →L[ℂ] E) (hK : IsSelfAdjoint K)
    {x : E} (hx : x ∈ negativeSpace (1 - K)) : K x ∈ negativeSpace (1 - K) := by
  have h := source_apply_negative (1 - K) ((IsSelfAdjoint.one _).sub hK) hx
  change x - K x = -(repair (1 - K) x) at h
  have he : K x = x + repair (1 - K) x := by
    calc
      K x = x - (x - K x) := by abel
      _ = x + repair (1 - K) x := by rw [h, sub_neg_eq_add]
  rw [he]
  exact (negativeSpace (1 - K)).add_mem hx ⟨x, rfl⟩

theorem negativeSpace_eq_aboveOneSpace (K : E →L[ℂ] E)
    (hK : IsSelfAdjoint K) (hcompact : IsCompactOperator K) :
    negativeSpace (1 - K) = aboveOneSpace K := by
  have hQ := (IsSelfAdjoint.one (E →L[ℂ] E)).sub hK
  have hc : IsCompactOperator (1 - (1 - K) : E →L[ℂ] E) := by
    simpa only [sub_sub_cancel] using hcompact
  letI := finiteDimensional_negativeSpace (1 - K) hQ hc
  apply le_antisymm
  · let N := negativeSpace (1 - K)
    let L : N →ₗ[ℂ] N := K.toLinearMap.restrict (fun _ hx => compact_preserves_negativeSpace K hK hx)
    have hL : L.IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hK).restrict_invariant _
    let b := hL.eigenvectorBasis rfl
    have hb : ∀ i, (b i : E) ∈ aboveOneSpace K := by
      intro i
      have heig := hL.apply_eigenvectorBasis rfl i
      have heig' : K (b i : E) = ((hL.eigenvalues rfl i : ℝ) : ℂ) • (b i : E) :=
        congrArg Subtype.val heig
      have hne : (b i : E) ≠ 0 := fun h => b.orthonormal.ne_zero i (Subtype.ext h)
      have hneg := negativeSpace_strict (1 - K) hQ (b i).property hne
      have hnorm : ‖(b i : E)‖ = 1 := b.orthonormal.1 i
      have hi : inner ℂ (b i : E) (b i : E) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hnorm]
        norm_num
      simp only [sub_apply, one_apply_eq_self, heig', inner_sub_left, inner_smul_left,
        Complex.conj_ofReal, hi, mul_one, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hneg
      have ht : 1 < hL.eigenvalues rfl i := by linarith
      exact Submodule.mem_iSup_of_mem ⟨hL.eigenvalues rfl i, ht⟩
        (Module.End.mem_eigenspace_iff.2 heig')
    intro x hx
    have hexp := congrArg (fun y : N => (y : E)) (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hexp
    rw [← hexp]
    exact (aboveOneSpace K).sum_mem fun i _ => (aboveOneSpace K).smul_mem _ (hb i)
  · exact aboveOneSpace_le_negativeSpace K hK

end GaloisForLFunctions.HTGeometry.PaperNegativePart
