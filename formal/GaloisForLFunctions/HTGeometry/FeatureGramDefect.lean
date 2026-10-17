import GaloisForLFunctions.HTGeometry.PSDKernelOperations
import GaloisForLFunctions.HTGeometry.SchurNevanlinnaPick

/-! Positive Gram defects characterize bounded maps between dense Hilbert feature families. -/

noncomputable section
open Complex
open scoped InnerProductSpace ComplexOrder

namespace GaloisForLFunctions.HTGeometry
variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The difference of two feature Gram kernels at a prescribed norm bound. -/
def featureGramDefect (v w : X → H) (M : ℝ) (x y : X) : ℂ :=
  (M : ℂ)^2 * inner ℂ (v y) (v x) - inner ℂ (w y) (w x)

private theorem featureGramDefect_form (v w : X → H) (M : ℝ) (c : X →₀ ℂ) :
    kernelForm (featureGramDefect v w M) c c =
      (M : ℂ)^2 * inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) -
      inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) := by
  classical
  rw [inner_linearCombination, inner_linearCombination]
  simp only [kernelForm, featureGramDefect, Finsupp.sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Kernel positivity is exactly the finite-synthesis norm bound. -/
theorem isPSDKernel_featureGramDefect_iff (v w : X → H) {M : ℝ} (hM : 0 ≤ M) :
    IsPSDKernel (featureGramDefect v w M) ↔
      ∀ c : X →₀ ℂ, ‖Finsupp.linearCombination ℂ w c‖ ≤
        M * ‖Finsupp.linearCombination ℂ v c‖ := by
  have heq (c : X →₀ ℂ) : (kernelForm (featureGramDefect v w M) c c).re =
      M^2 * ‖Finsupp.linearCombination ℂ v c‖^2 -
      ‖Finsupp.linearCombination ℂ w c‖^2 := by
    rw [featureGramDefect_form, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  constructor
  · intro h c
    have hh := h.nonneg c
    change 0 ≤ (kernelForm (featureGramDefect v w M) c c).re at hh
    rw [heq] at hh
    have h0 := norm_nonneg (Finsupp.linearCombination ℂ w c)
    have h1 := mul_nonneg hM (norm_nonneg (Finsupp.linearCombination ℂ v c))
    nlinarith
  · intro h
    refine ⟨?_, fun c => ?_⟩
    · intro x y
      simp only [featureGramDefect, map_sub, map_mul, map_pow, Complex.conj_ofReal,
        inner_conj_symm]
    · change 0 ≤ (kernelForm (featureGramDefect v w M) c c).re
      rw [heq]
      have hh := h c
      have h0 := norm_nonneg (Finsupp.linearCombination ℂ w c)
      have h1 := mul_nonneg hM (norm_nonneg (Finsupp.linearCombination ℂ v c))
      nlinarith

/-- A positive Gram defect produces a bounded operator on the complete feature span. -/
theorem exists_bounded_feature_map [CompleteSpace H] (v w : X → H)
    (hd : DenseRange (Finsupp.linearCombination ℂ v)) {M : ℝ} (hM : 0 ≤ M)
    (hK : IsPSDKernel (featureGramDefect v w M)) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ M ∧ ∀ x, T (v x) = w x := by
  let e := Finsupp.linearCombination ℂ v
  let f := Finsupp.linearCombination ℂ w
  have hb : ∀ c, ‖f c‖ ≤ M * ‖e c‖ := (isPSDKernel_featureGramDefect_iff v w hM).mp hK
  refine ⟨f.extendOfNorm e, LinearMap.opNorm_extendOfNorm_le hd hM hb, fun x => ?_⟩
  simpa [e, f] using LinearMap.extendOfNorm_eq hd ⟨M, hb⟩ (Finsupp.single x (1 : ℂ))

/-- Transposing a complex positive kernel preserves positivity. -/
theorem IsPSDKernel.transpose {K : X → X → ℂ} (hK : IsPSDKernel K) :
    IsPSDKernel (fun x y => K y x) :=
  isPSDKernel_of_forall_posSemidef (fun x y => hK.conj_symm y x)
    (fun _ w => (hK.posSemidef w).transpose)

end GaloisForLFunctions.HTGeometry
