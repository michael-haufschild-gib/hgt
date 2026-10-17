import GaloisForLFunctions.HTGeometry.FeatureGramDefect
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurKernel
import GaloisForLFunctions.HTGeometry.CaratheodoryNevanlinnaPick
import GaloisForLFunctions.RHTower.PrimeLogHolomorphicUniqueness

/-! Bounded holomorphic half-plane symbols have positive first-order Pick kernels. -/

noncomputable section
open Complex Set
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry
variable {X : Type*}

/-- The actual Hardy multiplier norm is bounded by its declared pointwise bound. -/
theorem norm_hardyMul_le_bound (F : DiskMultiplier) : ‖hardyMul F‖ ≤ F.bd := by
  unfold hardyMul
  exact LinearMap.mkContinuous_norm_le _ F.bd_nonneg _

/-- Positivity of the Pick kernel follows from the Hardy multiplication operator. -/
theorem hardyMultiplier_pickKernel_pos (F : DiskMultiplier) (u : X → ℂ)
    (hu : ∀ x, ‖u x‖ < 1) :
    IsPSDKernel (fun x y => ((F.bd : ℂ)^2 - F.fn (u x) * conj (F.fn (u y))) /
      (1 - u x * conj (u y))) := by
  let v : X → HardyDisk := fun x => hardyKernel (hu x)
  let A := ContinuousLinearMap.adjoint (hardyMul F)
  have hA : ‖A‖ ≤ F.bd := by
    rw [show ‖A‖ = ‖hardyMul F‖ from ContinuousLinearMap.adjoint.norm_map _]
    exact norm_hardyMul_le_bound F
  have hD : IsPSDKernel (featureGramDefect v (fun x => A (v x)) F.bd) := by
    apply (isPSDKernel_featureGramDefect_iff _ _ F.bd_nonneg).mpr
    intro c
    have hmap : Finsupp.linearCombination ℂ (fun x => A (v x)) c =
        A (Finsupp.linearCombination ℂ v c) := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
    rw [hmap]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  refine hD.transpose.congr (fun x y => ?_)
  simp only [featureGramDefect, v, A, adjoint_hardyMul_hardyKernel,
    inner_smul_left, inner_smul_right, Complex.conj_conj, inner_hardyKernel_hardyKernel,
    div_eq_mul_inv]
  ring

/-- Every bounded holomorphic half-plane function has a positive first-order Pick kernel. -/
theorem halfPlane_holomorphic_pickKernel_pos {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ RHTower.PrimeBlindCarlson.rightHalf)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z ∈ RHTower.PrimeBlindCarlson.rightHalf, ‖φ z‖ ≤ M)
    (q : X → ℂ) (hq : ∀ x, 0 < (q x).re) :
    IsPSDKernel (fun x y => ((M : ℂ)^2 - φ (q x) * conj (φ (q y))) /
      (q x + conj (q y))) := by
  let F : DiskMultiplier :=
    { fn := φ ∘ RHTower.PrimeBlindCarlson.cayley
      diff := fun z hz =>
        ((RHTower.PrimeBlindCarlson.analyticOnNhd_comp_cayley hφ) z hz).differentiableAt.differentiableWithinAt
      bd := M
      bd_nonneg := hM
      bd_le := fun z hz => hb _ (RHTower.PrimeBlindCarlson.re_cayley_pos
        (by simpa [Metric.mem_ball, dist_zero_right] using hz)) }
  have hv : ∀ x, F.fn (cayleyRight (q x)) = φ (q x) := by
    intro x
    change φ (RHTower.PrimeBlindCarlson.cayley ((q x - 1) / (q x + 1))) = φ (q x)
    rw [RHTower.PrimeBlindCarlson.cayley_inverseCayley (hq x)]
  have hD := hardyMultiplier_pickKernel_pos F (fun x => cayleyRight (q x))
    (fun x => norm_cayleyRight_lt_one (hq x))
  have hqne : ∀ x, q x + 1 ≠ 0 := fun x => add_one_ne_zero_of_re_nonneg (hq x).le
  have hsum : ∀ x y, q x + conj (q y) ≠ 0 := by
    intro x y he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hh
    have hx := hq x
    have hy := hq y
    linarith
  refine ((hD.mul_diag (fun x => (q x + 1)⁻¹)).const_mul (c := 2) (by norm_num)).congr
    (fun x y => ?_)
  rw [hv x, hv y]
  have h1 : conj (q y) + 1 ≠ 0 := by
    simpa using (map_ne_zero (starRingEnd ℂ)).mpr (hqne y)
  have hqx := hqne x
  have hdq : (1 : ℂ) - (q x - 1) / (q x + 1) *
      ((conj (q y) - 1) / (conj (q y) + 1)) =
      2 * (q x + conj (q y)) / ((q x + 1) * (conj (q y) + 1)) := by
    field_simp
    ring
  simp only [cayleyRight, map_inv₀, map_add, map_one, map_div₀, map_sub]
  rw [hdq]
  change (2 : ℂ) * ((q x + 1)⁻¹ * (conj (q y) + 1)⁻¹ *
      (((M : ℂ)^2 - φ (q x) * conj (φ (q y))) /
        (2 * (q x + conj (q y)) / ((q x + 1) * (conj (q y) + 1))))) = _
  field_simp [hsum x y]

end GaloisForLFunctions.HTGeometry
