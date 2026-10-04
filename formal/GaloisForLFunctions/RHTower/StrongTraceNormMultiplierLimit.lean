import GaloisForLFunctions.RHTower.StrongTraceClassMultiplierLimit
import GaloisForLFunctions.HTGeometry.SchattenOneBanach

/-!
# Bounded strong limits through a fixed nuclear factor

Dominated convergence on the actual Hilbert basis upgrades bounded strong
convergence to Hilbert--Schmidt convergence after a fixed HS factor. The
genuine Schatten product bound then gives trace-norm convergence after a
fixed nuclear factor. Adjoint transport gives the right-action version.

This is the ideal-limit ingredient for the original Gamma clock phase
products; convergence of their varying Schwartz symbols remains separate.
-/

noncomputable section
set_option autoImplicit false
open ContinuousLinearMap Filter Topology
namespace RHTower
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded strong convergence becomes Hilbert--Schmidt convergence after a fixed HS factor. -/
theorem hsNorm_comp_tendsto_of_strong_tendsto_of_uniform_bound
    {ι : Type*} {l : Filter ι} {Aι : ι → H →L[ℂ] H} {A S : H →L[ℂ] H}
    (hS : S.IsHilbertSchmidt) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ i in l, ‖Aι i‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun i => Aι i x) l (𝓝 (A x))) :
    Tendsto (fun i => hsNorm ((Aι i-A) ∘L S)) l (𝓝 0) := by
  let b := hsBasis ℂ H
  let D := C+‖A‖
  have hD : 0 ≤ D := add_nonneg hC (norm_nonneg _)
  have hpoint (j) : Tendsto (fun i => ‖((Aι i-A) ∘L S) (b j)‖^2) l (𝓝 0) := by
    have h := ((hstrong (S (b j))).sub_const (A (S (b j)))).norm.pow 2
    simpa only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using h
  have hdom : ∀ᶠ i in l, ∀ j,
      ‖‖((Aι i-A) ∘L S) (b j)‖^2‖ ≤ D^2*‖S (b j)‖^2 := by
    filter_upwards [hbound] with i hi j
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb : ‖Aι i-A‖ ≤ D := (norm_sub_le _ _).trans (add_le_add hi (le_refl ‖A‖))
    have hp : ‖((Aι i-A) ∘L S) (b j)‖ ≤ D*‖S (b j)‖ :=
      ((Aι i-A).le_opNorm (S (b j))).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    nlinarith [norm_nonneg (((Aι i-A) ∘L S) (b j)), mul_nonneg hD (norm_nonneg (S (b j)))]
  have hsum := tendsto_tsum_of_dominated_convergence
    ((hS.summable b).mul_left (D^2)) hpoint hdom
  have hs : Tendsto (fun i => hsNormSq ((Aι i-A) ∘L S)) l (𝓝 0) := by
    simpa only [hsNormSq,tsum_zero] using hsum
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_apply,hsNorm,Real.sqrt_zero] using! hsqrt

/-- Bounded strong convergence passes through a fixed nuclear factor in genuine trace norm. -/
theorem traceNorm_comp_tendsto_of_strong_tendsto_of_uniform_bound
    {ι : Type*} {l : Filter ι} {Aι : ι → H →L[ℂ] H} {A T : H →L[ℂ] H}
    (hT : T.IsTraceClass) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ i in l, ‖Aι i‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun i => Aι i x) l (𝓝 (A x))) :
    Tendsto (fun i => traceNorm H ((Aι i-A) ∘L T)) l (𝓝 0) := by
  obtain ⟨S,V,hS,hV,hfac⟩ := hT
  have hs := hsNorm_comp_tendsto_of_strong_tendsto_of_uniform_bound hS C hC hbound hstrong
  have ht : Tendsto (fun i => hsNorm V * hsNorm ((Aι i-A) ∘L S)) l (𝓝 0) := by
    simpa only [mul_zero] using hs.const_mul (hsNorm V)
  apply squeeze_zero (fun i => traceNorm_nonneg _) (fun i => ?_) ht
  rw [hfac,← ContinuousLinearMap.comp_assoc,← rectTraceNorm_eq_traceNorm]
  exact rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted hV (hS.comp_left (Aι i-A))

/-- Strong adjoint convergence gives the corresponding right-action trace-norm limit. -/
theorem traceNorm_comp_right_tendsto_of_adjoint_strong_tendsto_of_uniform_bound
    {ι : Type*} {l : Filter ι} {Aι : ι → H →L[ℂ] H} {A T : H →L[ℂ] H}
    (hT : T.IsTraceClass) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ i in l, ‖Aι i‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun i => adjoint (Aι i) x) l (𝓝 (adjoint A x))) :
    Tendsto (fun i => traceNorm H (T ∘L (Aι i-A))) l (𝓝 0) := by
  have ht : (adjoint T).IsTraceClass := by
    obtain ⟨S,V,hS,hV,hfac⟩ := hT
    refine ⟨adjoint V,adjoint S,hV.adjoint,hS.adjoint,?_⟩
    rw [hfac,adjoint_comp]
  have hb : ∀ᶠ i in l, ‖adjoint (Aι i)‖ ≤ C := by
    filter_upwards [hbound] with i hi
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hi
  have h := traceNorm_comp_tendsto_of_strong_tendsto_of_uniform_bound ht C hC hb hstrong
  apply h.congr
  intro i
  rw [← adjoint.map_sub,← adjoint_comp]
  rw [← rectTraceNorm_eq_traceNorm,rectTraceNorm_adjoint,rectTraceNorm_eq_traceNorm]
end RHTower
