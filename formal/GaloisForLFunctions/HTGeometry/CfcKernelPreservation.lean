import GaloisForLFunctions.HTGeometry.CfcNormBound
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Kernel preservation under continuous functional calculus

A real continuous symbol whose spectral zeros are confined to zero creates no
new kernel vectors for a bounded self-adjoint operator. The proof uses Dini
convergence of `x² / (1 + n g(x)²)` on the compact spectrum and an exact
functional-calculus factorization. No lower bound away from zero is assumed.
Consequently an injective source operator remains injective with dense range.
This supplies graph domains for unbounded transforms defined through a bounded
reciprocal symbol; it does not assert spectral occurrence for an external source.
-/

open Filter Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private def kernelRegularizer (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 : ℕ) / (1 + (n : ℝ) * g x ^ (2 : ℕ))

private theorem kernelRegularizer_den_pos (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 < 1 + (n : ℝ) * g x ^ (2 : ℕ) := by positivity

private theorem kernelRegularizer_continuousOn {K : Set ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g K) (n : ℕ) : ContinuousOn (kernelRegularizer g n) K :=
  (continuousOn_id.pow 2).div (continuousOn_const.add (continuousOn_const.mul (hg.pow 2)))
    (fun x _ => ne_of_gt (kernelRegularizer_den_pos g n x))

private theorem kernelRegularizer_antitone (g : ℝ → ℝ) (x : ℝ) :
    Antitone (fun n => kernelRegularizer g n x) := by
  intro m n hmn
  apply div_le_div_of_nonneg_left (sq_nonneg x) (kernelRegularizer_den_pos g m x)
  have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
  simpa only [add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_right hcast (sq_nonneg (g x))) 1

private theorem kernelRegularizer_tendsto {g : ℝ → ℝ} {x : ℝ}
    (hzero : g x = 0 → x = 0) :
    Tendsto (fun n => kernelRegularizer g n x) atTop (𝓝 0) := by
  by_cases hg : g x = 0
  · simp [kernelRegularizer, hzero hg]
  · have hs : 0 < g x ^ (2 : ℕ) := sq_pos_of_ne_zero hg
    have hn : Tendsto (fun n : ℕ => (n : ℝ) * g x ^ (2 : ℕ)) atTop atTop :=
      Tendsto.atTop_mul_const hs tendsto_natCast_atTop_atTop
    have hd : Tendsto (fun n : ℕ => 1 + (n : ℝ) * g x ^ (2 : ℕ)) atTop atTop := by
      exact tendsto_atTop_add_const_left atTop (1 : ℝ) hn
    exact Tendsto.div_atTop tendsto_const_nhds hd

private theorem kernelRegularizer_uniform {K : Set ℝ} {g : ℝ → ℝ}
    (hK : IsCompact K) (hg : ContinuousOn g K)
    (hzero : ∀ x ∈ K, g x = 0 → x = 0) :
    TendstoUniformlyOn (kernelRegularizer g) (fun _ => 0) atTop K :=
  Antitone.tendstoUniformlyOn_of_forall_tendsto hK
    (kernelRegularizer_continuousOn hg) (fun x _ => kernelRegularizer_antitone g x)
    continuousOn_const (fun x hx => kernelRegularizer_tendsto (hzero x hx))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A continuous real symbol with no new spectral zeros creates no new vector in the kernel. -/
theorem cfc_apply_eq_zero_imp_of_no_new_zeros
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (g : ℝ → ℝ)
    (hg : ContinuousOn g (spectrum ℝ B))
    (hzero : ∀ x ∈ spectrum ℝ B, g x = 0 → x = 0)
    (v : H) (hv : cfc g B v = 0) : B v = 0 := by
  nontriviality H
  have hnorm : Tendsto (fun n => ‖cfc (kernelRegularizer g n) B‖) atTop (𝓝 0) := by
    apply tendsto_norm_cfc_zero _ B hB
    · exact Filter.Eventually.of_forall (kernelRegularizer_continuousOn hg)
    · intro ε hε
      have hu := (Metric.tendstoUniformlyOn_iff.mp
        (kernelRegularizer_uniform (spectrum.isCompact B) hg hzero)) ε hε
      filter_upwards [hu] with n hn x hx
      simpa only [dist_zero_left] using (hn x hx).le
  have heq (n : ℕ) : (B ^ (2 : ℕ)) v = cfc (kernelRegularizer g n) B v := by
    let q : ℝ → ℝ := fun x => (n : ℝ) * x ^ (2 : ℕ) * g x / (1 + (n : ℝ) * g x ^ (2 : ℕ))
    have hq : ContinuousOn q (spectrum ℝ B) := by
      exact ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hg).div
        (continuousOn_const.add (continuousOn_const.mul (hg.pow 2)))
        (fun x _ => ne_of_gt (kernelRegularizer_den_pos g n x))
    have hid : cfc (fun x : ℝ => x ^ (2 : ℕ) - kernelRegularizer g n x) B =
        cfc q B * cfc g B := by
      rw [← cfc_mul q g B hq hg]
      apply cfc_congr
      intro x _
      dsimp [q, kernelRegularizer]
      field_simp [ne_of_gt (kernelRegularizer_den_pos g n x)]
      ring
    rw [cfc_sub (fun x : ℝ => x ^ (2 : ℕ)) (kernelRegularizer g n) B
      (continuousOn_id.pow 2) (kernelRegularizer_continuousOn hg n),
      cfc_pow_id B 2 hB] at hid
    have hap := congrArg (fun T : H →L[ℂ] H => T v) hid
    simp only [sub_apply, mul_apply_eq_comp, hv, map_zero] at hap
    exact sub_eq_zero.mp hap
  have hlim : Tendsto (fun _ : ℕ => ‖(B ^ (2 : ℕ)) v‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by
      simpa using hnorm.mul_const ‖v‖)
    rw [heq n]
    exact (cfc (kernelRegularizer g n) B).le_opNorm v
  have hsq : (B ^ (2 : ℕ)) v = 0 := norm_eq_zero.mp (tendsto_const_nhds_iff.mp hlim)
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB
  have hpair : inner ℂ (B (B v)) v = inner ℂ (B v) (B v) := hsym (B v) v
  have hsq' : B (B v) = 0 := by simpa only [pow_two, mul_apply_eq_comp] using hsq
  rw [← hpair, hsq', inner_zero_left]

/-- Injectivity survives any continuous real symbol having no new zero on the spectrum. -/
theorem cfc_injective_of_no_new_zeros
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (hBinj : Function.Injective B)
    (g : ℝ → ℝ) (hg : ContinuousOn g (spectrum ℝ B))
    (hzero : ∀ x ∈ spectrum ℝ B, g x = 0 → x = 0) :
    Function.Injective (cfc g B : H →L[ℂ] H) := by
  intro u v huv
  have hz : cfc g B (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hBz := cfc_apply_eq_zero_imp_of_no_new_zeros B hB g hg hzero (u - v) hz
  exact sub_eq_zero.mp (hBinj (by simpa only [map_zero] using hBz))

/-- The transformed covariance also has dense range; this is the domain of its graph inverse. -/
theorem cfc_dense_range_of_no_new_zeros
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (hBinj : Function.Injective B)
    (g : ℝ → ℝ) (hg : ContinuousOn g (spectrum ℝ B))
    (hzero : ∀ x ∈ spectrum ℝ B, g x = 0 → x = 0) :
    Dense ((cfc g B).range : Set H) := by
  have hself : IsSelfAdjoint (cfc g B) := IsSelfAdjoint.cfc
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff,
    (cfc g B).orthogonal_range, hself.adjoint_eq]
  exact LinearMap.ker_eq_bot.mpr (cfc_injective_of_no_new_zeros B hB hBinj g hg hzero)

end
end GaloisForLFunctions.HTGeometry
