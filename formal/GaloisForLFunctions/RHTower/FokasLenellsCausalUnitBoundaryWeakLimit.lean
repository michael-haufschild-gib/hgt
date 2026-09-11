import GaloisForLFunctions.RHTower.FokasLenellsCausalStrongStability
import GaloisForLFunctions.RHTower.FokasLenellsCausalUnitBoundaryRates
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
open scoped NNReal
open Complex Set Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section WeakBoundary
variable {H J I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem decaying_adjoint_test_span_dense (T : J → H →L[ℂ] H)
    (g : Filter J) [g.NeBot] (hT : ∀ u, Tendsto (fun t => T t u) g (𝓝 0))
    (μ : J → ℂ) (hμ : ∀ t, ‖μ t‖ = 1) :
    (Submodule.span ℂ (Set.range (fun p : J × H =>
      (T p.1).adjoint p.2 - star (μ p.1) • p.2))).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  have he : ∀ t, T t u = μ t • u := by
    intro t
    apply ext_inner_left ℂ
    intro y
    have hy := (Submodule.mem_orthogonal _ _).mp hu
      ((T t).adjoint y - star (μ t) • y) (Submodule.subset_span (Set.mem_range_self (t, y)))
    simpa [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
      inner_smul_left, inner_smul_right, sub_eq_zero] using hy
  have hz : Tendsto (fun _ : J => ‖u‖) g (𝓝 (0 : ℝ)) := by
    simpa only [he, norm_smul, hμ, one_mul, norm_zero] using (hT u).norm
  exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hz)

private theorem boundary_pairing_test_tendsto (T : J → H →L[ℂ] H)
    (μ : J → ℂ) (α : J → I → ℂ) (v : I → H) (f : Filter I)
    (hv : ∀ i, ‖v i‖ ≤ 1) (he : ∀ t i, T t (v i) = α t i • v i)
    (hα : ∀ t, Tendsto (α t) f (𝓝 (μ t))) (t : J) (y : H) :
    Tendsto (fun i => inner ℂ ((T t).adjoint y - star (μ t) • y) (v i)) f (𝓝 0) := by
  have hp : ∀ i, inner ℂ ((T t).adjoint y - star (μ t) • y) (v i) =
      (α t i - μ t) * inner ℂ y (v i) := by
    intro i
    simp [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
      inner_smul_left, inner_smul_right, he, sub_mul] <;> exact mul_comm _ _
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb : ∀ i, ‖inner ℂ ((T t).adjoint y - star (μ t) • y) (v i)‖ ≤
      ‖α t i - μ t‖ * ‖y‖ := by
    intro i
    rw [hp, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (hv i) (norm_nonneg y)).trans_eq (mul_one ‖y‖))
  have hlim : Tendsto (fun i => ‖α t i - μ t‖ * ‖y‖) f (𝓝 (0 : ℝ)) := by
    have hsub : Tendsto (fun i => α t i - μ t) f (𝓝 (0 : ℂ)) := by
      simpa using (hα t).sub (tendsto_const_nhds :
        Tendsto (fun _ : I => μ t) f (𝓝 (μ t)))
    simpa using hsub.norm.mul_const ‖y‖
  exact squeeze_zero (fun i => norm_nonneg _) hb hlim

omit [CompleteSpace H] in
private theorem bounded_pairing_tendsto_of_dense_span (v : I → H) (f : Filter I)
    (hv : ∀ i, ‖v i‖ ≤ 1) (D : Submodule ℂ H) (hD : D.topologicalClosure = ⊤)
    (hd : ∀ y ∈ D, Tendsto (fun i => inner ℂ y (v i)) f (𝓝 0)) (y : H) :
    Tendsto (fun i => inner ℂ y (v i)) f (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hy : y ∈ closure (D : Set H) := by
    rw [← Submodule.topologicalClosure_coe, hD]
    trivial
  obtain ⟨z, hz, hyz⟩ := Metric.mem_closure_iff.mp hy (ε / 2) (half_pos hε)
  have hs := Metric.tendsto_nhds.mp (hd z hz) (ε / 2) (half_pos hε)
  filter_upwards [hs] with i hi
  rw [dist_zero_right] at hi ⊢
  rw [dist_eq_norm] at hyz
  have hsmall : ‖inner ℂ (y - z) (v i)‖ < ε / 2 :=
    lt_of_le_of_lt ((norm_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (hv i) (norm_nonneg (y - z))).trans_eq (mul_one ‖y - z‖))) hyz
  calc
    ‖inner ℂ y (v i)‖ = ‖inner ℂ (y - z) (v i) + inner ℂ z (v i)‖ := by
      rw [inner_sub_left, sub_add_cancel]
    _ ≤ ‖inner ℂ (y - z) (v i)‖ + ‖inner ℂ z (v i)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hsmall hi
    _ = ε := add_halves ε

private theorem bounded_boundary_eigenfamily_weak_null (T : J → H →L[ℂ] H)
    (g : Filter J) [g.NeBot] (hT : ∀ u, Tendsto (fun t => T t u) g (𝓝 0))
    (μ : J → ℂ) (hμ : ∀ t, ‖μ t‖ = 1) (α : J → I → ℂ)
    (v : I → H) (f : Filter I) (hv : ∀ i, ‖v i‖ ≤ 1)
    (he : ∀ t i, T t (v i) = α t i • v i)
    (hα : ∀ t, Tendsto (α t) f (𝓝 (μ t))) (y : H) :
    Tendsto (fun i => inner ℂ y (v i)) f (𝓝 0) := by
  let D := Submodule.span ℂ (Set.range (fun p : J × H =>
    (T p.1).adjoint p.2 - star (μ p.1) • p.2))
  apply bounded_pairing_tendsto_of_dense_span v f hv D
    (decaying_adjoint_test_span_dense T g hT μ hμ) _ y
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨t, w⟩, rfl⟩ := hz
    exact boundary_pairing_test_tendsto T μ α v f hv he hα t w
  | zero => simpa only [inner_zero_left] using (tendsto_const_nhds :
      Tendsto (fun _ : I => (0 : ℂ)) f (𝓝 0))
  | add u w _ _ hu hw => simpa only [inner_add_left, zero_add] using hu.add hw
  | smul c u _ hu => simpa only [inner_smul_left, mul_zero] using hu.const_mul ((starRingEnd ℂ) c)
end WeakBoundary

/-- Every normalized unit-boundary datum has the exact actual causal semigroup orbit. -/
theorem causalLowerCauchyEvolution_unitBoundaryEigenvector (t : ℝ≥0) (b ω : ℝ) :
    causalLowerCauchyEvolution t (causalUnitBoundaryEigenvector b ω).val =
      Complex.exp (((t : ℝ) : ℂ) * (causalUnitBoundaryRate b ω).val) •
        (causalUnitBoundaryEigenvector b ω).val := by
  let r := causalUnitBoundaryRate b ω
  let c : ℂ := ((‖causalLeftEigenvector r‖ : ℝ) : ℂ)⁻¹
  change causalLowerCauchyEvolution t (c • causalCauchyEigenvector (causalEigenPole r)) =
    Complex.exp (((t : ℝ) : ℂ) * r.val) • (c • causalCauchyEigenvector (causalEigenPole r))
  rw [map_smul, causalLowerCauchyEvolution_eigenvector, causalAnalyticPhase_rate,
    causalPoleRate_eigenPole]
  exact smul_comm _ _ _

private theorem actual_boundary_weak_transfer (ω : ℝ) (ζ : ℂ) (hζ : ζ.re = 0)
    (h : Tendsto (fun b : ℝ => (causalUnitBoundaryRate b ω).val) atBot (𝓝 ζ))
    (y : hardyL2ᗮ) :
    Tendsto (fun b : ℝ => inner ℂ y (causalUnitBoundaryEigenvector b ω).val) atBot (𝓝 0) := by
  letI : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
  apply bounded_boundary_eigenfamily_weak_null causalLowerCauchyEvolution atTop
    causalLowerCauchyEvolution_strong_tendsto
    (fun t => Complex.exp (((t : ℝ) : ℂ) * ζ))
    (fun t => by simp [Complex.norm_exp, Complex.mul_re, hζ])
    (fun t b => Complex.exp (((t : ℝ) : ℂ) * (causalUnitBoundaryRate b ω).val))
    (fun b => (causalUnitBoundaryEigenvector b ω).val) atBot
    (fun b => (norm_causalUnitBoundaryEigenvector b ω).le)
    (fun t b => causalLowerCauchyEvolution_unitBoundaryEigenvector t b ω) _ y
  intro t
  exact (Complex.continuous_exp.tendsto _).comp (h.const_mul (((t : ℝ) : ℂ)))

/-- At the positive imaginary spectral endpoint, normalized actual Hilbert data
vanish weakly while retaining unit norm. -/
theorem causalUnitBoundaryEigenvector_weak_tendsto_pos (y : hardyL2ᗮ) :
    Tendsto (fun b : ℝ => inner ℂ y (causalUnitBoundaryEigenvector b 1).val) atBot (𝓝 0) :=
  actual_boundary_weak_transfer 1 I (by simp) causalUnitBoundaryRate_tendsto_pos y

/-- The negative imaginary endpoint has the same weak-vanishing law for actual
normalized Hilbert data. -/
theorem causalUnitBoundaryEigenvector_weak_tendsto_neg (y : hardyL2ᗮ) :
    Tendsto (fun b : ℝ => inner ℂ y (causalUnitBoundaryEigenvector b (-1)).val) atBot (𝓝 0) :=
  actual_boundary_weak_transfer (-1) (-I) (by simp) causalUnitBoundaryRate_tendsto_neg y

end RHTower.FokasLenells
