import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.HTGeometry.InertiaScalingSwap

/-!
# Negative index under amplifying group maps

If positive rescalings of group pullbacks recover a Hermitian kernel, adding a
positive-definite kernel preserves its negative index. Boundedness of the positive
part and lower semicontinuity of finite Gram inertia give the reverse inequality.
-/

open Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- Positive bounded additions preserve the index of a kernel amplified by group maps. -/
theorem negIndex_posDef_add_of_rescaling {G : Type*} [Group G] {k p : G → ℂ}
    (hk : IsHermKernel k) (hp : IsPosDefKernel p)
    (φ : ℕ → G →* G) (s : ℕ → ℝ) (hspos : ∀ N, 0 < s N)
    (hs : Tendsto s atTop (𝓝 0))
    (hscale : ∀ N g, (s N : ℂ) * k (φ N g) = k g) :
    negIndex (fun g => p g + k g) = negIndex k := by
  apply le_antisymm (negIndex_add_posDef_le hp)
  apply negIndex_le_iff.mpr
  intro n x
  let y (N : ℕ) : Fin n → G := fun a => φ N (x a)
  let P (N : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
    (s N : ℂ) • gram p (y N)
  let M (N : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
    (s N : ℂ) • gram (fun g => p g + k g) (y N)
  have hM (N : ℕ) : M N = gram k x + P N := by
    ext a b
    change (s N : ℂ) * (p ((φ N (x a))⁻¹ * φ N (x b)) +
      k ((φ N (x a))⁻¹ * φ N (x b))) =
      k ((x a)⁻¹ * x b) + (s N : ℂ) * p ((φ N (x a))⁻¹ * φ N (x b))
    have hq : (φ N (x a))⁻¹ * φ N (x b) = φ N ((x a)⁻¹ * x b) := by
      rw [map_mul, map_inv]
    simp only [hq, mul_add, hscale, add_comm]
  have hP (N : ℕ) (a b : Fin n) : ‖P N a b‖ ≤ s N * (p 1).re := by
    change ‖(s N : ℂ) * p ((y N a)⁻¹ * y N b)‖ ≤ s N * (p 1).re
    rw [norm_mul, Complex.norm_of_nonneg (hspos N).le]
    exact mul_le_mul_of_nonneg_left (hp.norm_le _) (hspos N).le
  have hsC : Tendsto (fun N => s N * (p 1).re) atTop (𝓝 0) := by
    simpa only [zero_mul] using hs.mul_const (p 1).re
  have hPlim (a b : Fin n) : Tendsto (fun N => P N a b) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hsC.eventually (gt_mem_nhds hε)] with N hN
    simpa only [dist_zero_right] using (hP N a b).trans_lt hN
  have hconv (a b : Fin n) : Tendsto (fun N => M N a b) atTop (𝓝 (gram k x a b)) := by
    simp only [hM, Matrix.add_apply]
    simpa only [add_zero] using tendsto_const_nhds.add (hPlim a b)
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex (gram_isHermitian hk x) hconv).exists
  have hMN : hermNegIndex (M N) = hermNegIndex (gram (fun g => p g + k g) (y N)) :=
    negIndex_smul_pos (hspos N) _
  rw [hMN] at hN
  exact (Nat.cast_le.mpr hN).trans (hermNegIndex_gram_le_negIndex _ _)

#print axioms negIndex_posDef_add_of_rescaling
end GaloisForLFunctions.HeckeKreinToeplitz
